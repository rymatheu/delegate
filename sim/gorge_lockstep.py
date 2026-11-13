#!/usr/bin/env python3
"""Fly a lock-step vehicle (default: the translated whole vehicle through sim/lean_vehicle.py) through leanfc's gorge
world in gym-pybullet-drones, on the gorge mission, with the scripted ground station of sim/lockstep_gcs.py.

    build/reference/venv/bin/python sim/gorge_lockstep.py --out sim/out/gorge-port-x500/flight
        [--vehicle x500|cf2x] [--bin sim/lean_vehicle.py | build/reference/copter_ref] [--storage IMAGE]
        [--params FILE]... [--set NAME VALUE]... [--seed N] [--wind MEAN GUST] [--duration S] [--replay-check] [--ref-check]

Harness code only (no vehicle logic). What it shares with sim/fly_reference.py: the vehicle protocol
(sim/lockstep_proto.py), the sensor layer (fly_reference.Sensors: IMU after every 1200 Hz physics substep, barometer and
compass at 100 Hz, GPS at 5 Hz, RC at 50 Hz, battery; optional seeded noise), the PWM -> propeller-speed map, the
environment set-up (CtrlAviary, Physics.PYB, gravity GRAVITY_MSS, PyBullet damping removed, 0.25 s settling) of
sim/run_copter.py, and the ground station (sim/lockstep_gcs.py). What differs:

- the world: leanfc's gorge (LEANFC_ROOT, default /Users/ryan/Research/leanfc; sim/world/gorge.py, seed 7), imported from
  that checkout, never copied: the environment is leanfc's fly_gorge.GorgeAviary (the package's ground plane replaced by
  the gorge's collision bodies: concave terrain trimesh, boulder hulls, rock and vegetation compounds);
- the vehicle (--vehicle): x500 (default), leanfc's X500 as its gorge flies it: urdf=run_leanfc.AIRFRAMES["x500"]["urdf"]
  (mass, inertia, motor constants, collision cylinder of LEANFC_ROOT/sim/assets/x500.urdf), lag=fly_gorge.LAG (first-order
  motor lag 12.5 ms up, 25 ms down), wind leanfc's wind.Wind with --wind, none otherwise; its four propellers are PX4's
  rotor_0..3 (front right CCW, rear left CCW, front left CW, rear right CW), ArduPilot's quad-X motor slots 0..3 in the
  same order and spins, through run_copter.SLOT_TO_SIM; actuator a = (PWM - 1000) / 1000, propeller speed MAX_RPM sqrt(a),
  so thrust a x 8.54858 N per motor. cf2x: the package's CF2X, no lag, no wind;
- the start: the vehicle resting on the gorge floor at the plan's start (Gorge.path[0], world ENU (0, 0)), level, nose
  north, then settled on its contact (motors off, the lag starting at zero thrust): the X500's base 5 mm above
  gorge_plan.start_rest_z, as gorge_session.py places it; the CF2X's 5 mm above the highest ground point under its
  collision disc plus the base height of the package's place();
- the geography: home of the sensor layer = the gorge's geographic origin (leanfc params/ground.params ORIGIN line, read
  with leanfc's geo.Origin: 38.8405556, -105.0441667, 4302 m), which is world ENU (0, 0, 0): GPS latitude, longitude and
  altitude, and the barometer's 1976 atmosphere, are taken about it; the compass's earth field is ArduPilot's at that
  location (build/reference/magfield 38.8405556 -105.0441667: 0.508486092 G, declination 7.42202234 deg, inclination
  65.1364594 deg);
- the mission (gorge_mission): gorge_plan.plan_items' items (the plan's latitudes and longitudes, leanfc's own
  geo.Origin.latlon_e7 integers, and for the X500 its relative altitudes), uploaded as MISSION_ITEM_INT: NAV_TAKEOFF at the start, the 10 NAV_SPLINE_WAYPOINTs,
  NAV_LAND at the last waypoint (the plan's param4 null of the spline items is sent as 0: AP_Mission::sanity_check_params
  allows NaN in param4 only for WAYPOINT, LOITER_UNLIM, LAND, TAKEOFF, ARC_WAYPOINT and the VTOL items, and answers a NaN
  param4 of NAV_SPLINE_WAYPOINT with MAV_MISSION_INVALID_PARAM4). The plan's relative altitudes
  refer to the X500's rest height (base 0.2 m above the floor): the X500 flies them unchanged; for the CF2X they are
  referred to its rest height (the settled start) instead, so that every waypoint is where the plan puts it in the world,
  3.5 m above the floor on the centerline;
- the ground-station script (script_gorge): heartbeat, streams, parameter download, the PARAM_SETs of --params and --set,
  EKF3 using GPS, mission upload and download back, GUIDED, arm, NAV_TAKEOFF to the takeoff item's altitude, AUTO; it
  records MISSION_CURRENT and MISSION_ITEM_REACHED and waits for the disarm;
- the record: every 4th step (100 Hz) the true pose (ENU position, PyBullet quaternion), NED velocity, actuators, the
  clearance (closest distance from the vehicle's collision cylinder to every body of the gorge, up to 4 m, PyBullet
  getClosestPoints, as leanfc's gorge_session.py), the contact count, armed state, mode and mission item, in
  track.csv; flight.json has the metrics (gorge_metrics).

Outputs in --out: inputs.txt, outputs.txt (the lock-step record: replaying inputs.txt through the binary with
storage_in.bin reproduces outputs.txt), storage_in.bin, log.txt, summary.txt, track.csv, mission.json, flight.json.
"""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import math
import os
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
ROOT = SIM_DIR.parent
sys.path.insert(0, str(SIM_DIR))
sys.dont_write_bytecode = True           # nothing is written into the leanfc checkout

import run_copter as rc  # noqa: E402
import fly_reference as fr  # noqa: E402
import lockstep_gcs  # noqa: E402
from lockstep_proto import encode_input, decode_output  # noqa: E402

LEANFC_ROOT = Path(os.environ.get("LEANFC_ROOT", "/Users/ryan/Research/leanfc"))
GORGE_SEED = 7
CLEAR_MAX = 4.0
BATTERY = dict(x500=(16.0, 0.5), cf2x=(12.6, 0.5))   # the battery stand-in's (V, A): 4S for the X500, as fly_reference.py for the CF2X
REC_EVERY = 4                            # steps per record row (100 Hz)
STEP_US = fr.STEP_US

# ArduPilot's earth field at the gorge's origin (AP_Declination tables through build/reference/magfield), NED as
# fly_reference.MAG_NED is built (Matrix3f::from_euler(0, -inclination, declination) applied to (intensity, 0, 0))
_I, _D, _INC = 508.486092, math.radians(7.42202234), math.radians(65.1364594)
MAG_NED_GORGE = np.array([_I * math.cos(_INC) * math.cos(_D), _I * math.cos(_INC) * math.sin(_D), _I * math.sin(_INC)])


def import_leanfc():
    """leanfc's world modules, from the checkout at LEANFC_ROOT (read only: no bytecode is written there)."""
    for d in (LEANFC_ROOT / "sim" / "world", LEANFC_ROOT / "sim"):
        if not d.is_dir():
            sys.exit(f"gorge_lockstep: {d} not found (set LEANFC_ROOT)")
        if str(d) not in sys.path:
            sys.path.append(str(d))
    import gorge as G
    import gorge_plan as GP
    import geo
    from fly_gorge import GorgeAviary, LAG
    import run_leanfc as R
    from wind import Wind
    return G, GP, geo, GorgeAviary, LAG, R, Wind


def gorge_origin(geo):
    return geo.Origin.from_params([LEANFC_ROOT / "params" / "x500.params", LEANFC_ROOT / "params" / "ground.params"])


class GorgeSensors(fr.Sensors):
    """fly_reference.Sensors about the gorge's origin: the same IMU, and the slow sensors of Sensors.slow with the home
    location and earth field of the gorge (the statements are Sensors.slow's with those constants)."""

    def __init__(self, seed, substep_s, home, mag_ned):
        super().__init__(seed, substep_s)
        self.home_lat, self.home_lon, self.home_alt = home
        self.mag_ned = mag_ned

    def slow(self, k, obs):
        pos, vel, att, rates, R = self.state(obs)
        out = dict(pos=pos, vel=vel, att=att)
        if k % 4 == 0:
            P, T = fr.pressure_temperature(self.home_alt - pos[2])
            out["baro"] = (P + self.n(fr.NOISE["baro_pa"]), T)
            out["mag"] = tuple(R.T @ self.mag_ned - fr.MAG_OFS + self.n(fr.NOISE["mag"], 3))
        if k % 80 == 0:
            pn = pos + self.n(fr.NOISE["gps_pos"], 3)
            vn = np.asarray(vel) + self.n(fr.NOISE["gps_vel"], 3)
            lat = self.home_lat + pn[0] * 1e-7 * fr.LOCATION_SCALING_FACTOR_INV
            lon = self.home_lon + pn[1] * 1e-7 * fr.LOCATION_SCALING_FACTOR_INV / math.cos(math.radians(self.home_lat))
            out["gps"] = (lat, lon, self.home_alt - pn[2], vn[0], vn[1], vn[2])
        if k % 8 == 0:
            out["rc"] = fr.RC_NEUTRAL
        return out


def make_env(GorgeAviary, GP, g, pyb_hz, vehicle="x500", urdf=None, lag=None, wind=None):
    """run_copter.make_env with leanfc's GorgeAviary, resting on the floor at the start. vehicle "x500": leanfc's X500
    (urdf = run_leanfc.AIRFRAMES["x500"]["urdf"], lag = fly_gorge.LAG, placed as gorge_session.py places it: its base
    5 mm above gorge_plan.start_rest_z); "cf2x": the package's CF2X, no motor lag. wind: leanfc's wind.Wind or None."""
    import warnings
    warnings.filterwarnings("ignore", module="gymnasium")
    from gym_pybullet_drones.utils.enums import DroneModel, Physics
    rc.CTRL_HZ = pyb_hz                       # stepped at the physics rate, as fly_reference.py
    with contextlib.redirect_stdout(io.StringIO()):
        env = GorgeAviary(g, wind=wind, urdf=urdf, lag=lag, drone_model=DroneModel.CF2X, num_drones=1,
                          physics=Physics.PYB, pyb_freq=pyb_hz, ctrl_freq=pyb_hz, gui=False, record=False,
                          obstacles=False, user_debug_gui=False, output_folder=str(SIM_DIR / "out" / "pyb"))
    env.G = rc.GRAVITY_MSS
    env.GRAVITY = env.G * env.M
    env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
    env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
    env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
    env.rest_alt = 0.0
    start = g.path[0]                         # ENU
    rc.place(env, (float(start[1]), float(start[0]), None), (0.0, 0.0, 0.0), "freefall")
    base = env.COLLISION_H / 2 - env.COLLISION_Z_OFFSET     # place()'s base height above a ground plane at z = 0
    ang = np.linspace(0, 2 * np.pi, 13)[:-1]
    xy = start[:2]
    pts = [xy] + [xy + r * np.array([math.cos(a), math.sin(a)]) for r in (0.03, env.COLLISION_R) for a in ang]
    env.INIT_XYZS[0, 2] = float(np.max(g.ground_z(np.array(pts)))) + base + 0.005
    if vehicle == "x500":
        env.INIT_XYZS[0, 2] = GP.start_rest_z(g, np.array(xy)) + 0.005
    return env


def gorge_mission(m, GP, g, origin, home_z, rereference):
    """The plan's items (gorge_plan.plan_items) as (command, frame, params, lat, lon, alt) for lockstep_gcs.upload_mission,
    seq 0 home. rereference False (the X500): the plan's relative altitudes unchanged (they refer to the X500's rest
    height, gorge_plan.start_rest_z) and home at the plan's planned home; True (the CF2X): relative altitudes about the
    vehicle's home height home_z (ENU z of the settled start)."""
    items, plan_home_z = GP.plan_items(g, origin)
    if not rereference:
        home_z = plan_home_z
    lat0, lon0 = origin.latlon_e7(g.path[0, 1], g.path[0, 0])
    FR = m.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT
    out = [(m.MAV_CMD_NAV_WAYPOINT, m.MAV_FRAME_GLOBAL, (0, 0, 0, 0), lat0 / 1e7, lon0 / 1e7, origin.alt_m + home_z)]
    wz = [g.path[0, 2]] + [w[2] for w in g.path[1:]]
    for k, it in enumerate(items):
        q = it["params"]
        rel = 0.0 if it["command"] == 21 else (round(float(wz[k]) - home_z, 3) if rereference else float(q[6]))
        p4 = 0.0 if q[3] is None else float(q[3])       # the plan's null: ArduPilot refuses NaN here (see docstring)
        out.append((it["command"], FR, (float(q[0]), float(q[1]), float(q[2]), p4), float(q[4]), float(q[5]), rel))
    return out, items


def script_gorge(g: lockstep_gcs.GCS, m, items, sets, rec):
    """The gorge mission from the ground: parameters, EKF3 using GPS, upload and download back, GUIDED, arm, takeoff, AUTO
    through the splines, land, disarm. rec collects MISSION_CURRENT changes and MISSION_ITEM_REACHED."""
    yield from g.wait_until(lambda: "HEARTBEAT" in g.latest, 60, "first heartbeat")
    g.event("heartbeat")
    g.request_streams(4)
    yield from g.download_params()
    for name, want in (("FRAME_CLASS", 1), ("GPS1_TYPE", 100), ("BATT_MONITOR", 4)):
        if name not in g.params or g.params[name][0] != want:
            raise lockstep_gcs.GCSError(f"parameter {name} is {g.params.get(name)}, expected {want}")
    for name, value in sets:
        old = g.params.get(name, (None,))[0]
        yield from g.set_param(name, value)
        g.event(f"parameter {name} {old} -> {value:g}")
    yield from g.wait_until(lambda: any("is using GPS" in x[2] for x in g.texts), 120, "EKF3 using GPS")
    g.event("EKF3 using GPS")
    yield from g.upload_mission(items)
    back = yield from g.download_mission()
    if len(back) != len(items) or any(b.command != it[0] or (s > 0 and (b.x != int(round(it[3] * 1e7)) or
                                                                         b.y != int(round(it[4] * 1e7))))
                                      for s, (b, it) in enumerate(zip(back, items))):
        raise lockstep_gcs.GCSError("downloaded mission differs from the uploaded one")
    yield from g.set_mode("GUIDED")
    t0 = g.t
    while not g.armed:
        r = yield from g.command(m.MAV_CMD_COMPONENT_ARM_DISARM, 1)
        if r == m.MAV_RESULT_ACCEPTED:
            yield from g.wait_until(lambda: g.armed, 3, "armed heartbeat")
            break
        if g.t - t0 > 60:
            raise lockstep_gcs.GCSError("arming refused for 60 s")
        yield from g.wait_s(2.0)
    g.event("armed")
    rec["t_arm"] = g.t
    alt = items[1][5]
    r = yield from g.command(m.MAV_CMD_NAV_TAKEOFF, p7=alt)
    if r != m.MAV_RESULT_ACCEPTED:
        raise lockstep_gcs.GCSError(f"takeoff refused ({r})")
    yield from g.wait_until(lambda: "GLOBAL_POSITION_INT" in g.latest and
                            g.latest["GLOBAL_POSITION_INT"].relative_alt > (alt - 0.3) * 1000, 30, f"{alt - 0.3:.2f} m")
    g.event(f"reached {alt - 0.3:.2f} m in GUIDED")
    yield from g.set_mode("AUTO")
    rec["t_auto"] = g.t
    t0 = g.t
    while g.armed:
        for msg in g.msgs:
            typ = msg.get_type()
            if typ == "MISSION_ITEM_REACHED" and (not rec["reached"] or rec["reached"][-1][1] != msg.seq):
                rec["reached"].append((g.t, msg.seq))
                g.event(f"MISSION_ITEM_REACHED {msg.seq}")
            elif typ == "MISSION_CURRENT" and (not rec["current"] or rec["current"][-1][1] != msg.seq):
                rec["current"].append((g.t, msg.seq))
                g.event(f"MISSION_CURRENT {msg.seq}")
        if g.t - t0 > 300:
            raise lockstep_gcs.GCSError("timeout (300 s) waiting for the disarm after the mission")
        yield
    rec["t_disarm"] = g.t
    g.event("disarmed")
    yield from g.wait_s(2.0)


def seg_dist(q, route):
    """Distance of each point of q (N x 3) to the polyline route (M x 3)."""
    best = np.full(len(q), np.inf)
    for p0, p1 in zip(route[:-1], route[1:]):
        v = p1 - p0
        s = np.clip((q - p0) @ v / (v @ v), 0, 1)
        best = np.minimum(best, np.linalg.norm(q - (p0 + s[:, None] * v), axis=1))
    return best


def gorge_metrics(track, rec, gpath, home_z, n_spline):
    """Flight numbers from the 100 Hz record. 'In the air' (leanfc test_gorge_flight.py: landed state IN_AIR, i.e. after
    the takeoff and before the landing) is here from the takeoff item's MISSION_ITEM_REACHED to the MISSION_CURRENT of the
    land item; contacts are counted from the liftoff (the first record without contact after arming) to the touchdown
    (the first contact after the land item began)."""
    t = track["t"]
    pos = np.column_stack([track["x"], track["y"], track["z"]])
    out = {}
    reached = [s for _, s in rec["reached"]]
    out["reached"] = reached
    out["current"] = [s for _, s in rec["current"]]
    land_seq = n_spline + 2
    t_to = next((tt for tt, s in rec["reached"] if s == 1), None)
    t_land = next((tt for tt, s in rec["current"] if s == land_seq), None)
    if rec.get("t_arm") is not None and rec.get("t_disarm") is not None:
        out["arm_to_disarm_s"] = rec["t_disarm"] - rec["t_arm"]
    armed = track["armed"] > 0
    contact = track["contacts"] > 0
    if armed.any():
        k_arm = int(np.argmax(armed))
        free = np.nonzero(~contact[k_arm:])[0]
        k_lift = k_arm + int(free[0]) if len(free) else None
        k_td = None
        if k_lift is not None and t_land is not None:
            after = np.nonzero(contact & (t >= t_land))[0]
            k_td = int(after[0]) if len(after) else None
        if k_lift is not None:
            k_end = k_td if k_td is not None else len(t)
            out["liftoff_t"] = float(t[k_lift])
            out["touchdown_t"] = float(t[k_td]) if k_td is not None else None
            out["contacts_between_liftoff_and_touchdown"] = int(contact[k_lift:k_end].sum())
            if k_td is not None:
                out["touchdown_speed_down_ms"] = float(-track["vz_up"][max(k_td - 1, 0)])
                out["landing_error_m"] = float(np.hypot(*(pos[k_td, :2] - gpath[-1, :2])))
    if t_to is not None and t_land is not None:
        air = (t >= t_to) & (t < t_land)
        out["air_window_s"] = [float(t_to), float(t_land)]
        out["clearance_min_in_air_m"] = float(track["clearance"][air].min())
        k = int(np.nonzero(air)[0][np.argmin(track["clearance"][air])])
        out["clearance_min_at"] = dict(t=float(t[k]), north=float(pos[k, 1]), east=float(pos[k, 0]), up=float(pos[k, 2]))
        route = np.vstack([[gpath[0, 0], gpath[0, 1], home_z], gpath])
        d = seg_dist(pos[air], route)
        out["route_distance_in_air_max_m"] = float(d.max())
        out["route_distance_in_air_rms_m"] = float(math.sqrt((d ** 2).mean()))
        k = int(np.nonzero(air)[0][np.argmax(d)])
        out["route_distance_max_at"] = dict(t=float(t[k]), north=float(pos[k, 1]), east=float(pos[k, 0]), up=float(pos[k, 2]))
        gs = np.hypot(track["vn"], track["ve"])
        sp = np.sqrt(track["vn"] ** 2 + track["ve"] ** 2 + track["vz_up"] ** 2)
        out["ground_speed_max_ms"] = float(gs[air].max())
        out["speed_3d_max_ms"] = float(sp[air].max())
        tilt = np.degrees(np.arccos(np.clip(1 - 2 * (track["qx"] ** 2 + track["qy"] ** 2), -1, 1)))
        out["tilt_max_in_air_deg"] = float(tilt[air].max())
        m = np.column_stack([track[f"m{i}"] for i in range(1, 5)])
        out["actuator_range_in_air"] = [float(m[air].min()), float(m[air].max())]
    out["clearance_min_whole_record_m"] = float(track["clearance"].min())
    return out


def ref_check(out: Path, log):
    """The recorded input lines replayed through the C++ reference (copter_ref, the same storage image): its output lines
    against the recorded ones (the flown vehicle's), and its estimation trace (--est) for vehicle_replay.py."""
    ref = ROOT / "build" / "reference" / "copter_ref"
    t0 = time.perf_counter()
    with open(out / "inputs.txt") as fi, open(out / "ref_outputs.txt", "w") as fo:
        subprocess.run([str(ref), "--storage", str(out / "storage_in.bin"), "--est", str(out / "est.txt")], stdin=fi, stdout=fo,
                       check=True)
    a, b = (out / "outputs.txt").read_bytes(), (out / "ref_outputs.txt").read_bytes()
    if a == b:
        log(f"ref check: copter_ref on inputs.txt gives {b.count(b'\n')} output lines, identical to outputs.txt byte for byte "
            f"({time.perf_counter() - t0:.2f} s wall)")
    else:
        al, bl = a.split(b"\n"), b.split(b"\n")
        first = next((i for i, (x, y) in enumerate(zip(al, bl)) if x != y), min(len(al), len(bl)))
        log(f"ref check: copter_ref's output DIFFERS from outputs.txt, first at line {first + 1}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--bin", default=str(SIM_DIR / "lean_vehicle.py"))
    ap.add_argument("--out", required=True)
    ap.add_argument("--vehicle", choices=("x500", "cf2x"), default="x500",
                    help="x500: leanfc's X500 (its URDF, motor lag; the gorge's vehicle, default); cf2x: the package's CF2X")
    ap.add_argument("--storage", default=None, help="boot image (default: build/gorge-port/storage-x500.bin for the x500, "
                                                     "build/reference/storage-cf2x.bin for the cf2x)")
    ap.add_argument("--wind", type=float, nargs=2, metavar=("MEAN", "GUST"), default=None,
                    help="leanfc's gorge wind (wind.Wind, gust seed = noise seed (0 without --seed) + 1000); x500 only")
    ap.add_argument("--params", action="append", default=[], help="file of NAME VALUE lines to PARAM_SET (repeatable)")
    ap.add_argument("--set", nargs=2, action="append", default=[], metavar=("NAME", "VALUE"),
                    help="PARAM_SET through the parameter protocol after the download (repeatable, after --params)")
    ap.add_argument("--seed", type=int, help="sensor noise seed (default: no noise)")
    ap.add_argument("--duration", type=float, default=240.0, help="limit, simulated seconds")
    ap.add_argument("--pyb-hz", type=int, default=1200)
    ap.add_argument("--replay-check", action="store_true")
    ap.add_argument("--ref-check", action="store_true",
                    help="replay inputs.txt through build/reference/copter_ref (with --est est.txt) and compare its output "
                         "lines with outputs.txt")
    args = ap.parse_args()
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    logf = open(out / "log.txt", "w")

    def log(s):
        logf.write(s + "\n")
        logf.flush()
        print(s, flush=True)

    G, GP, geo, GorgeAviary, LAG, R, Wind = import_leanfc()
    if args.storage is None:
        args.storage = str(ROOT / "build" / ("gorge-port/storage-x500.bin" if args.vehicle == "x500" else "reference/storage-cf2x.bin"))
    if args.wind and args.vehicle != "x500":
        sys.exit("gorge_lockstep: leanfc's wind model is the X500's (--vehicle x500)")
    from pymavlink.dialects.v20 import ardupilotmega as m
    gz = G.Gorge(GORGE_SEED)
    origin = gorge_origin(geo)
    home = (origin.lat_e7 / 1e7, origin.lon_e7 / 1e7, origin.alt_m)
    log(f"gorge seed {gz.seed} from {LEANFC_ROOT}; origin {home} (world ENU 0, 0, 0); start {gz.path[0].tolist()} (ENU)")

    substeps = args.pyb_hz // 400
    wind = Wind(gz, args.wind[0], args.wind[1], (args.seed or 0) + 1000) if args.wind else None
    if args.vehicle == "x500":
        env = make_env(GorgeAviary, GP, gz, args.pyb_hz, "x500", R.AIRFRAMES["x500"]["urdf"], LAG, wind)
    else:
        env = make_env(GorgeAviary, GP, gz, args.pyb_hz, "cf2x")
    log(f"vehicle {args.vehicle}: mass {env.M:.4f} kg, inertia {np.round(np.diag(env.J), 5).tolist()}, kf {env.KF:.6g} N/RPM^2, "
        f"km {env.KM:.6g}, thrust-to-weight {env.THRUST2WEIGHT_RATIO:.4f}, MAX_RPM {env.MAX_RPM:.2f}, motor lag {env.lag}, "
        f"collision r {env.COLLISION_R} h {env.COLLISION_H}, wind {args.wind}, storage {args.storage}")
    obs = rc.reset_env(env)
    home_z = float(obs[0][2])
    drone, client = env.DRONE_IDS[0], env.CLIENT
    world = list(env.world)
    import pybullet as pb
    log(f"start: vehicle settled at ENU {np.round(obs[0][0:3], 4).tolist()}, {len(world)} world bodies; "
        f"floor at start {float(gz.ground_z(gz.path[None, 0, :2])[0]):.4f}")

    items, plan_items = gorge_mission(m, GP, gz, origin, home_z, args.vehicle == "cf2x")
    _, plan_home_z = GP.plan_items(gz, origin)
    (out / "mission.json").write_text(json.dumps(dict(
        vehicle=args.vehicle, home_z_settled=home_z, plan_home_z_x500=plan_home_z, origin=home,
        items=[dict(seq=s, command=int(c), frame=int(f), params=[None if isinstance(q, float) and math.isnan(q) else q for q in p],
                    lat=la, lon=lo, alt=al) for s, (c, f, p, la, lo, al) in enumerate(items)],
        plan_items=plan_items), indent=1, default=float) + "\n")
    log(f"mission: {len(items)} items (home, takeoff {items[1][5]:.3f} m, {len(items) - 3} spline waypoints, land); settled "
        f"start z {home_z:.4f}; relative altitudes " + (f"about it (the plan's are about the X500's rest z {plan_home_z:.4f})"
                                                        if args.vehicle == "cf2x" else f"the plan's (about z {plan_home_z:.4f})"))

    (out / "storage_in.bin").write_bytes(Path(args.storage).read_bytes())
    env_vars = dict(os.environ)
    env_vars.setdefault("LEAN_VEHICLE_OUT", str(out / "lean"))
    cmd = [args.bin, "--timing-file", str(out / "timing.txt"), "--storage", args.storage]
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1, env=env_vars)

    sensors = GorgeSensors(args.seed, 1.0 / args.pyb_hz, home, MAG_NED_GORGE)
    imu_buf = [sensors.imu(obs)] * substeps
    gcs = lockstep_gcs.GCS(m, log)
    rec = dict(reached=[], current=[], t_arm=None, t_auto=None, t_disarm=None)
    sets = list(fr.read_params(args.params).items()) + [(n, float(v)) for n, v in args.set]
    gcs.script = script_gorge(gcs, m, items, sets, rec)

    fin = open(out / "inputs.txt", "w")
    fout = open(out / "outputs.txt", "w")
    cols = "t,x,y,z,qx,qy,qz,qw,vn,ve,vz_up,m1,m2,m3,m4,clearance,contacts,armed,mode,item".split(",")
    rows = []
    up = b""
    n_ticks = int(args.duration * 1e6 / STEP_US)
    w0 = time.perf_counter()
    k = 0
    end = "time limit"
    act = [0.0] * 4
    try:
        for k in range(n_ticks):
            t_us = STEP_US * (k + 1)
            s = sensors.slow(k, obs)
            line = encode_input(t_us, imu=imu_buf, baro=s.get("baro"), mag=s.get("mag"), gps=s.get("gps"),
                                rc=s.get("rc"), bat=BATTERY[args.vehicle], up=up)
            proc.stdin.write(line + "\n")
            reply = proc.stdout.readline()
            if not reply:
                end = f"vehicle exited (code {proc.wait()})"
                break
            fin.write(line + "\n")
            fout.write(reply)
            t_out, pwm, down = decode_output(reply)
            rpm, act = fr.pwm_to_rpm(env, pwm)
            up = gcs.step(t_us * 1e-6, down)
            imu_buf = []
            for _ in range(substeps):
                obs, *_ = env.step(rpm.reshape(1, 4))
                imu_buf.append(sensors.imu(obs))
            if k % REC_EVERY == 0:
                st = obs[0]
                dist = [q[8] for b in world for q in pb.getClosestPoints(drone, b, CLEAR_MAX, physicsClientId=client)]
                ncon = len(pb.getContactPoints(bodyA=drone, physicsClientId=client))
                cur = rec["current"][-1][1] if rec["current"] else -1
                rows.append([(k + 1) * STEP_US * 1e-6, *st[0:3], *st[3:7], st[11], st[10], st[12], *act,
                             min(dist) if dist else CLEAR_MAX, ncon, int(gcs.armed), gcs.mode if gcs.mode is not None else -1, cur])
            if gcs.done:
                end = "script failed: " + gcs.error if gcs.error else "script finished"
                break
    except KeyboardInterrupt:
        end = "interrupted"
    finally:
        wall = time.perf_counter() - w0
        proc.stdin.close()
        tail = proc.stdout.read()
        code = proc.wait()
        fin.close()
        fout.close()
        env.close()
    with open(out / "track.csv", "w") as f:
        f.write(",".join(cols) + "\n")
        for r in rows:
            f.write(",".join(repr(float(v)) if i < 16 else str(int(v)) for i, v in enumerate(r)) + "\n")
    steps = k + 1
    summary = [f"end: {end}", f"steps: {steps} ({steps * STEP_US * 1e-6:.2f} s simulated), wall {wall:.2f} s "
               f"({steps * STEP_US * 1e-6 / wall:.1f}x real time)",
               f"vehicle exit code {code}" + (f", unread output {len(tail)} bytes" if tail else "")]
    tf = out / "timing.txt"
    if tf.exists():
        summary.append(tf.read_text().splitlines()[0])
    summary.append("events: " + "; ".join(f"{t:.2f} {w}" for t, w in gcs.events))
    summary.append("messages received: " + ", ".join(f"{k}:{v}" for k, v in sorted(gcs.counts.items())))
    track = np.genfromtxt(out / "track.csv", delimiter=",", names=True)
    met = gorge_metrics(track, rec, gz.path, home_z, len(items) - 3)
    n_spl = len(items) - 3
    spl = list(range(2, 2 + n_spl))
    met["completed"] = bool(rec["t_disarm"] is not None and all(s in met["reached"] for s in [1] + spl)
                            and met.get("contacts_between_liftoff_and_touchdown") == 0 and met.get("touchdown_t") is not None)
    flight = dict(end=end, vehicle=args.vehicle, wind=args.wind, bin=args.bin, storage=args.storage, seed=args.seed, gorge_seed=gz.seed, origin=home,
                  home_z=home_z, params_set=dict(sets), events=gcs.events, record=dict(rec), metrics=met,
                  wall_s=wall, simulated_s=steps * STEP_US * 1e-6)
    (out / "flight.json").write_text(json.dumps(flight, indent=1, default=float) + "\n")
    summary.append(f"mission: completed {met['completed']}; MISSION_ITEM_REACHED {met['reached']}; "
                   f"spline waypoints reached {sum(s in met['reached'] for s in spl)} of {n_spl}")
    if "arm_to_disarm_s" in met:
        summary.append(f"arm to disarm {met['arm_to_disarm_s']:.2f} s (simulated)")
    if "clearance_min_in_air_m" in met:
        summary.append(f"in the air ({met['air_window_s'][0]:.2f} to {met['air_window_s'][1]:.2f} s): clearance min "
                       f"{met['clearance_min_in_air_m']:.3f} m at N {met['clearance_min_at']['north']:.2f}; distance to the "
                       f"planned route max {met['route_distance_in_air_max_m']:.3f} m, rms {met['route_distance_in_air_rms_m']:.3f} m; "
                       f"ground speed max {met['ground_speed_max_ms']:.2f} m/s, 3D {met['speed_3d_max_ms']:.2f} m/s; "
                       f"tilt max {met['tilt_max_in_air_deg']:.1f} deg; actuators {met['actuator_range_in_air'][0]:.3f}.."
                       f"{met['actuator_range_in_air'][1]:.3f}")
    if "contacts_between_liftoff_and_touchdown" in met:
        summary.append(f"contacts between liftoff ({met['liftoff_t']:.2f} s) and touchdown ({met.get('touchdown_t')}): "
                       f"{met['contacts_between_liftoff_and_touchdown']}; touchdown {met.get('touchdown_speed_down_ms', float('nan')):.2f} m/s "
                       f"down, {met.get('landing_error_m', float('nan')):.2f} m from the land item")
    for line in summary:
        log(line)
    if args.replay_check:
        rargs = argparse.Namespace(bin=args.bin, storage=args.storage)
        os.environ.setdefault("LEAN_VEHICLE_OUT", str(out / "lean-replay"))
        fr.replay_check(rargs, out, log)
    if args.ref_check:
        ref_check(out, log)
    (out / "summary.txt").write_text("\n".join(summary) + "\n")
    if gcs.error:
        sys.exit(1)


if __name__ == "__main__":
    main()
