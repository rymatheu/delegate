#!/usr/bin/env python3
"""Fly two X500s through leanfc's gorge at the same time, each controlled by its own instance of the translated whole
vehicle (sim/lean_vehicle.py), on leanfc's two formation plans (abreast, staggered), with one scripted ground station per
vehicle.

    build/reference/venv/bin/python sim/gorge_formation_lockstep.py --plan abreast|staggered
        --out sim/out/gorge-formation-x500/abreast/flight [--storage IMAGE] [--params FILE]... [--set NAME VALUE]...
        [--seed N] [--duration S] [--replay-check] [--ref-check]

Harness code only (no vehicle logic). Everything per vehicle is sim/gorge_lockstep.py's (imported): the sensor layer
(GorgeSensors about the gorge's origin; with --seed N vehicle 1 draws its noise from seed N and vehicle 2 from N + 100, as
leanfc's formation.py), the PWM -> propeller-speed map, the lock-step protocol, the ground-station script (script_gorge:
heartbeat, streams, parameter download, the PARAM_SETs of --params and --set, EKF3 using GPS, mission upload and download
back, GUIDED, arm, NAV_TAKEOFF, AUTO, until the disarm), the record (track.csv, 100 Hz) and the flight numbers
(gorge_metrics). What is new:

- the world: one gym-pybullet-drones world (Physics.PYB, 1200 Hz physics, the gorge's collision bodies, seed 7) holding
  both vehicles, leanfc's formation.FormationAviary (imported from LEANFC_ROOT): GorgeAviary with the X500's first-order
  motor lag (12.5 ms up, 25 ms down) kept per vehicle; no wind. Contact between the vehicles and with the terrain is
  PyBullet's; no aerodynamic interaction between the vehicles is modeled (leanfc's formation.py says the same);
- the vehicles: two independent processes of sim/lean_vehicle.py, each with its own copy of the boot image
  (OUT/vN/storage_in.bin, a copy of --storage, default build/gorge-port/storage-x500.bin: copter_ref's image with the
  overrides of sim/params/reference-x500.txt, WP_SPD 2), its own LEAN_VEHICLE_OUT (OUT/vN/lean: the driver's outputs.txt,
  tasks.txt, outputs.txt.storage), its own timing file and its own record (OUT/vN/inputs.txt, outputs.txt); each has its
  own ground station (lockstep_gcs.GCS) that sees only that vehicle's downlink. There is no link between the vehicles and
  nothing synchronizes them besides the common world tick: at every 400 Hz tick both get their input line (the sensor
  sample of the same world state), both compute, then the world steps three physics substeps with both vehicles' motors;
- the missions: leanfc's formation_plan (imported) for --plan: the route centre (Gorge.path with its first point moved to
  the level start site, formation_plan.centre), the two routes (vehicle 2's = vehicle 1's + one constant offset whose
  vertical component equalizes the takeoff climbs, formation_plan.routes) and the level land sites (formation_plan.
  land_sites), written as QGroundControl plans by formation_plan.write_plan into OUT/vN/ (not into leanfc) and translated
  to ArduCopter items as gorge_lockstep.gorge_mission translates the single route: NAV_TAKEOFF, the 10
  NAV_SPLINE_WAYPOINTs (param4 0, not NaN), NAV_LAND at the vehicle's land site, relative altitudes about the vehicle's
  own rest height. Heading: ArduCopter's WP_YAW_BEHAVIOR default (face the next waypoint) for both vehicles; leanfc's
  staggered plan turned vehicle 2's nose backward with its own nav.yawReverse, which has no ArduCopter counterpart and is
  not reproduced;
- the start: each vehicle resting on the floor at its route's first point (level start site), level, nose north, its
  base 5 mm above gorge_plan.start_rest_z (as gorge_lockstep and formation.py place it), settled with the motors off for
  0.25 s;
- the record: per vehicle OUT/vN/track.csv (gorge_lockstep's columns; `contacts` counts vehicle-world contact points
  only), flight.json, summary.txt, log.txt, mission.json; for the pair OUT/formation.csv (every 4th tick: t, centre
  distance, closest distance of the two collision cylinders, contact points vehicle-vehicle, vehicle 1-world,
  vehicle 2-world, both clearances; leanfc formation.py's columns), OUT/formation.json (outcome, the pair's numbers and
  the fields leanfc's render_formation.Setup reads: plan, gorge_seed, nominal_distance, reverse = [0, 0], seed);
  OUT/vN/act.npy, the actuators of every tick (for the peak and saturation numbers).

--replay-check: each vehicle's inputs.txt replayed through sim/lean_vehicle.py (no simulator) from its storage_in.bin,
with its own LEAN_VEHICLE_OUT (OUT/vN/lean-replay), output compared with outputs.txt byte for byte. --ref-check:
gorge_lockstep.ref_check per vehicle (copter_ref on inputs.txt; est.txt for ardupilot/vehicle/vehicle_replay.py).
"""
from __future__ import annotations

import argparse
import contextlib
import io
import json
import math
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
ROOT = SIM_DIR.parent
sys.path.insert(0, str(SIM_DIR))
sys.dont_write_bytecode = True           # nothing is written into the leanfc checkout

import gorge_lockstep as GL  # noqa: E402

rc, fr, lockstep_gcs = GL.rc, GL.fr, GL.lockstep_gcs
STEP_US = GL.STEP_US
REC_EVERY = GL.REC_EVERY
CLEAR_MAX = GL.CLEAR_MAX
SAT_HI, SAT_LO = 0.999, 0.001            # a saturated tick: some actuator at or above SAT_HI or at or below SAT_LO (formation.summarize)


def import_formation():
    """leanfc's world modules (gorge_lockstep.import_leanfc) and its formation modules, from LEANFC_ROOT (read only).
    formation.py puts LEANFC_ROOT/sim first on sys.path; that entry is moved back behind this directory afterwards, so
    that this harness keeps resolving its own modules first."""
    mods = GL.import_leanfc()
    before = list(sys.path)
    import formation_plan as FP
    import formation as FM
    sys.path[:] = before + [d for d in sys.path if d not in before]
    return mods, FP, FM


def make_env(FM, GP, g, pyb_hz, urdf, lag, starts_xy, yaws_deg=None):
    """formation.FormationAviary (per-vehicle motor lag, no wind) with two X500s, set up as gorge_lockstep.make_env sets up
    one: stepped at the physics rate, gravity GRAVITY_MSS and the derived constants; each vehicle level, nose north (place's
    default) or at yaws_deg[i] (NED heading, deg), its base 5 mm above gorge_plan.start_rest_z at its start."""
    import warnings
    warnings.filterwarnings("ignore", module="gymnasium")
    from gym_pybullet_drones.utils.enums import DroneModel, Physics
    rc.CTRL_HZ = pyb_hz
    with contextlib.redirect_stdout(io.StringIO()):
        env = FM.FormationAviary(g, winds=None, urdf=urdf, lag=lag, drone_model=DroneModel.CF2X, num_drones=len(starts_xy),
                                 physics=Physics.PYB, pyb_freq=pyb_hz, ctrl_freq=pyb_hz, gui=False, record=False,
                                 obstacles=False, user_debug_gui=False, output_folder=str(SIM_DIR / "out" / "pyb"))
    env.G = rc.GRAVITY_MSS
    env.GRAVITY = env.G * env.M
    env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
    env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
    env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
    env.rest_alt = 0.0
    xyz, rpy = [], []
    for i, xy in enumerate(starts_xy):
        yaw = 0.0 if yaws_deg is None else float(yaws_deg[i])
        rc.place(env, (float(xy[1]), float(xy[0]), None), (0.0, 0.0, yaw), "freefall")
        q = env.INIT_XYZS[0].copy()
        q[2] = GP.start_rest_z(g, np.asarray(xy, float)) + 0.005
        xyz.append(q)
        rpy.append(env.INIT_RPYS[0].copy())
    env.INIT_XYZS, env.INIT_RPYS = np.array(xyz), np.array(rpy)
    env.on_ground_at_start, env.hover_at_start = True, False
    return env


def reset_env(env):
    """run_copter.reset_env for every vehicle: no PyBullet velocity damping, motors off for SETTLE_S on the contact."""
    import pybullet as pb
    obs, _ = env.reset()
    for d in env.DRONE_IDS:
        pb.changeDynamics(d, -1, linearDamping=0.0, angularDamping=0.0, physicsClientId=env.CLIENT)
    for _ in range(int(rc.SETTLE_S * rc.CTRL_HZ)):
        obs, *_ = env.step(np.zeros((env.NUM_DRONES, 4)))
    return obs


def leg_headings(route):
    """NED compass heading (deg, 0..360) of each leg of a route (ENU waypoints, the first the takeoff point): leg k from
    route[k - 1] to route[k], k = 1..len - 1."""
    d = np.diff(np.asarray(route, float)[:, :2], axis=0)
    return np.degrees(np.arctan2(d[:, 0], d[:, 1])) % 360.0


def formation_missions(FP, GP, g, origin, plan, m, out, reverse=(0, 0), yaw_rate=10.0):
    """The two vehicles' plans (formation_plan: route centre, routes, land sites; write_plan into OUT/vN/) and their
    ArduCopter items as gorge_lockstep.gorge_mission builds them (seq 0 home at the planned home, then the plan's items in
    MAV_FRAME_GLOBAL_RELATIVE_ALT_INT, the spline items' param4 null sent as 0). A vehicle with reverse[v] set gets, before
    each spline waypoint item k, a MAV_CMD_CONDITION_YAW item (absolute heading = the direction of leg k + 180 deg,
    yaw_rate deg/s, shortest way). AP_Mission starts the do and condition commands that follow a nav command when that nav
    command completes (it runs them while the next nav command flies), so the item placed after nav item k - 1 (the
    takeoff for k = 1) turns the nose while the vehicle flies leg k toward waypoint k (a first flight with the items after
    the waypoints, build/gorge-formation/stag-rev-try1, turned one leg late); with WP_YAW_BEHAVIOR 0 the spline waypoint
    keeps the FIXED heading (ModeAuto::sl_start: the yaw mode is reset to the default unless it is ROI, or
    FIXED with WP_YAW_BEHAVIOR NONE); its start heading (`start_yaw_deg`) is leg 1's + 180 deg."""
    c = FP.centre(g, plan)
    r1, r2, o, rest_z = FP.routes(g, plan, c)
    lands = FP.land_sites(g, r1, r2)
    FR = m.MAV_FRAME_GLOBAL_RELATIVE_ALT_INT
    res = []
    for v, (r, land) in enumerate(zip((r1, r2), lands), start=1):
        (out / f"v{v}").mkdir(parents=True, exist_ok=True)
        qplan = FP.write_plan(g, origin, r, out / f"v{v}" / f"formation-{plan}-v{v}.plan", land)
        home = qplan["mission"]["plannedHomePosition"]
        items = [(m.MAV_CMD_NAV_WAYPOINT, m.MAV_FRAME_GLOBAL, (0, 0, 0, 0), home[0], home[1], home[2])]
        rev = bool(reverse[v - 1])
        heads = (leg_headings(r) + 180.0) % 360.0
        n_spl = 0
        for it in qplan["mission"]["items"]:
            q = it["params"]
            rel = 0.0 if it["command"] == 21 else float(q[6])
            p4 = 0.0 if q[3] is None else float(q[3])
            if it["command"] == 82:
                n_spl += 1
                if rev:
                    items.append((m.MAV_CMD_CONDITION_YAW, m.MAV_FRAME_MISSION, (round(float(heads[n_spl - 1]), 2), float(yaw_rate), 0.0, 0.0),
                                  0.0, 0.0, 0.0))
            items.append((it["command"], FR, (float(q[0]), float(q[1]), float(q[2]), p4), float(q[4]), float(q[5]), rel))
        nav = {s: k for k, s in enumerate([s for s, it in enumerate(items) if s == 0 or it[0] in (16, 21, 22, 82)])}
        res.append(dict(route=r, land=np.asarray(land, float), items=items, plan_items=qplan["mission"]["items"],
                        rest_z=float(rest_z[v - 1]), planned_home=home, reverse=rev, nav_index=nav, n_spline=n_spl,
                        start_yaw_deg=float(heads[0]) if rev else 0.0, yaw_items_deg=[float(h) for h in heads] if rev else []))
    return res, np.asarray(o, float)


class Vehicle:
    """One vehicle: its process, sensor layer, ground station, record files and numbers."""

    def __init__(self, i, out, args, mission, m, home):
        self.i, self.name = i, f"v{i + 1}"
        self.out = out / self.name
        self.out.mkdir(parents=True, exist_ok=True)
        self.logf = open(self.out / "log.txt", "w")
        self.mission = mission
        self.items = mission["items"]
        self.storage = self.out / "storage_in.bin"
        shutil.copyfile(args.storage, self.storage)
        self.lean_out = self.out / "lean"
        env = dict(os.environ, LEAN_VEHICLE_OUT=str(self.lean_out))
        cmd = [args.bin, "--timing-file", str(self.out / "timing.txt"), "--storage", str(self.storage)]
        self.proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1, env=env)
        seed = None if args.seed is None else args.seed + 100 * i
        self.seed = seed
        self.sensors = GL.GorgeSensors(seed, 1.0 / args.pyb_hz, home, GL.MAG_NED_GORGE)
        self.gcs = lockstep_gcs.GCS(m, self.log)
        self.rec = dict(reached=[], current=[], t_arm=None, t_auto=None, t_disarm=None)
        self.sets = list(fr.read_params(args.params).items()) + [(n, float(v)) for n, v in args.set]
        if mission["reverse"]:
            self.sets.append(("WP_YAW_BEHAVIOR", 0.0))       # NONE: keep the FIXED heading of CONDITION_YAW across spline legs
        self.gcs.script = GL.script_gorge(self.gcs, m, self.items, self.sets, self.rec)
        self.fin = open(self.out / "inputs.txt", "w")
        self.fout = open(self.out / "outputs.txt", "w")
        self.up = b""
        self.rows = []
        self.act = []
        self.imu_buf = None
        self.exited = None

    def log(self, s):
        self.logf.write(s + "\n")
        self.logf.flush()
        print(f"[{self.name}] {s}", flush=True)


def seg_heading_error(track, mask, vmin=0.5):
    """Per row: the angle (deg) between the true heading (body x, horizontal) and the direction of travel (horizontal
    velocity), NaN below vmin m/s (formation.heading_error's measure, ENU here)."""
    qx, qy, qz, qw = track["qx"], track["qy"], track["qz"], track["qw"]
    yaw = np.arctan2(2 * (qw * qz + qx * qy), 1 - 2 * (qy ** 2 + qz ** 2))          # of body x, from east, CCW
    trav = np.arctan2(track["vn"], track["ve"])
    e = np.degrees(np.abs((yaw - trav + math.pi) % (2 * math.pi) - math.pi))
    e = np.where((np.hypot(track["vn"], track["ve"]) > vmin) & mask, e, np.nan)
    return e


def vehicle_numbers(V, track, act, met):
    """What gorge_metrics does not give: the route start, the landing at the land site, the slide after touchdown, the
    actuators of every tick from liftoff to touchdown, the heading against the direction of travel on the route."""
    t = track["t"]
    pos = np.column_stack([track["x"], track["y"], track["z"]])
    rec = V.rec
    out = {}
    out["t_arm"], out["t_auto"], out["t_disarm"] = rec["t_arm"], rec["t_auto"], rec["t_disarm"]
    # the vehicle's own texts (to the step; the armed and disarmed heartbeats above are at 1 Hz)
    out["t_arming_text"] = next((tt for tt, _, x in V.gcs.texts if x.startswith("Arming motors")), None)
    out["t_disarming_text"] = next((tt for tt, _, x in V.gcs.texts if x.startswith("Disarming motors")), None)
    if out["t_arming_text"] is not None and out["t_disarming_text"] is not None:
        out["arm_to_disarm_texts_s"] = out["t_disarming_text"] - out["t_arming_text"]
    out["route_start_t"] = next((tt for tt, s in rec["reached"] if s == 1), None)     # takeoff item reached
    land_seq = len(V.items) - 1
    out["land_item_t"] = next((tt for tt, s in rec["current"] if s == land_seq), None)
    td = met.get("touchdown_t")
    if td is not None:
        k_td = int(np.argmin(np.abs(t - td)))
        out["landing_error_to_land_site_m"] = float(np.hypot(*(pos[k_td, :2] - V.mission["land"][:2])))
        d = np.hypot(*(pos[k_td:, :2] - pos[k_td, :2]).T)
        out["slide_after_touchdown_max_m"] = float(d.max())
        out["slide_after_touchdown_final_m"] = float(d[-1])
        tilt = np.degrees(np.arccos(np.clip(1 - 2 * (track["qx"][-1] ** 2 + track["qy"][-1] ** 2), -1, 1)))
        out["tilt_at_end_deg"] = float(tilt)
    lo = met.get("liftoff_t")
    if lo is not None:
        ta = act[:, 0]
        a = act[:, 1:]
        sel = (ta >= lo) & (ta <= (td if td is not None else ta[-1]))
        if sel.any():
            out["actuator_max_air"] = float(a[sel].max())
            out["actuator_min_air"] = float(a[sel].min())
            sat = np.any((a >= SAT_HI) | (a <= SAT_LO), axis=1) & sel
            out["saturated_ticks_air"] = int(sat.sum())
            out["saturated_ticks_air_times"] = [float(x) for x in ta[sat][:20]]
            # the landing: from the land item's start to touchdown
            if out["land_item_t"] is not None:
                sl = (ta >= out["land_item_t"]) & sel
                out["saturated_ticks_landing"] = int((np.any((a >= SAT_HI) | (a <= SAT_LO), axis=1) & sl).sum())
    if out["route_start_t"] is not None and out["land_item_t"] is not None:
        mask = (t >= out["route_start_t"]) & (t < out["land_item_t"])
        he = seg_heading_error(track, mask)
        fin = he[np.isfinite(he)]
        if len(fin):
            out["heading_vs_travel_route_deg"] = dict(max=float(fin.max()), p95=float(np.percentile(fin, 95)),
                                                      rms=float(np.sqrt((fin ** 2).mean())), min=float(fin.min()))
            if V.mission["reverse"]:
                b = 180.0 - fin                             # deviation from exactly backward
                out["heading_deviation_from_backward_route_deg"] = dict(max=float(b.max()), p95=float(np.percentile(b, 95)),
                                                                        rms=float(np.sqrt((b ** 2).mean())))
    return out


def pair_numbers(f, vn, Vs):
    """Separation and contacts of the pair from formation.csv rows, over the whole record, while both are airborne (the
    later liftoff to the earlier touchdown) and while both are on their routes (both takeoff items reached, neither land
    item started)."""
    t = f["t"]
    res = {}
    k = int(np.argmin(f["dist"]))
    res["dist_min_whole_m"] = float(f["dist"][k])
    res["dist_min_whole_t"] = float(t[k])
    res["gap_min_whole_m"] = float(f["gap"].min())
    res["contact_rows"] = dict(vv=int((f["contact_vv"] > 0).sum()), v1_world=int((f["contact_v1"] > 0).sum()),
                               v2_world=int((f["contact_v2"] > 0).sum()))
    lifts = [x["met"].get("liftoff_t") for x in vn]
    tds = [x["met"].get("touchdown_t") for x in vn]
    if all(x is not None for x in lifts):
        t0 = max(lifts)
        t1 = min([x for x in tds if x is not None], default=t[-1])
        sel = (t >= t0) & (t < t1)
        if sel.any():
            k = int(np.nonzero(sel)[0][np.argmin(f["dist"][sel])])
            res["airborne_window"] = [float(t0), float(t1)]
            res["dist_min_airborne_m"] = float(f["dist"][k])
            res["dist_min_airborne_t"] = float(t[k])
            res["dist_max_airborne_m"] = float(f["dist"][sel].max())
            res["gap_min_airborne_m"] = float(f["gap"][sel].min())
            res["contact_vv_rows_airborne"] = int((f["contact_vv"][sel] > 0).sum())
    rs = [x["num"].get("route_start_t") for x in vn]
    le = [x["num"].get("land_item_t") for x in vn]
    if all(x is not None for x in rs + le):
        sel = (t >= max(rs)) & (t < min(le))
        if sel.any():
            d = f["dist"][sel]
            k = int(np.nonzero(sel)[0][np.argmin(d)])
            res["route_window"] = [float(max(rs)), float(min(le))]
            res["dist_route_m"] = dict(min=float(d.min()), mean=float(d.mean()), max=float(d.max()), t_min=float(t[k]))
        res["route_start_diff_s"] = float(rs[1] - rs[0])
        res["land_item_diff_s"] = float(le[1] - le[0])
    ta = [x["num"].get("t_arming_text") for x in vn]
    if all(x is not None for x in ta):
        res["arm_diff_s"] = float(ta[1] - ta[0])
    td = [x["met"].get("touchdown_t") for x in vn]
    if all(x is not None for x in td):
        res["touchdown_diff_s"] = float(td[1] - td[0])
    tau = [x["num"].get("t_auto") for x in vn]
    if all(x is not None for x in tau):
        res["auto_diff_s"] = float(tau[1] - tau[0])
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--plan", choices=("abreast", "staggered"), required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--bin", default=str(SIM_DIR / "lean_vehicle.py"))
    ap.add_argument("--storage", default=str(ROOT / "build" / "gorge-port" / "storage-x500.bin"),
                    help="boot image, copied for each vehicle (default build/gorge-port/storage-x500.bin)")
    ap.add_argument("--params", action="append", default=[], help="file of NAME VALUE lines to PARAM_SET (both vehicles)")
    ap.add_argument("--set", nargs=2, action="append", default=[], metavar=("NAME", "VALUE"),
                    help="PARAM_SET after the download (both vehicles; repeatable, after --params)")
    ap.add_argument("--seed", type=int, help="sensor noise seed (vehicle 1: N, vehicle 2: N + 100; default: no noise)")
    ap.add_argument("--duration", type=float, default=240.0, help="limit, simulated seconds")
    ap.add_argument("--pyb-hz", type=int, default=1200)
    ap.add_argument("--noses-forward", action="store_true",
                    help="staggered: fly vehicle 2 nose forward too (default: nose against the direction of travel, as the plan's reverse flag)")
    ap.add_argument("--yaw-rate", type=float, default=10.0, help="turn rate of the CONDITION_YAW items of a reversed vehicle (deg/s)")
    ap.add_argument("--replay-check", action="store_true")
    ap.add_argument("--ref-check", action="store_true")
    args = ap.parse_args()
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    logf = open(out / "log.txt", "w")

    def log(s):
        logf.write(s + "\n")
        logf.flush()
        print(s, flush=True)

    (G, GP, geo, GorgeAviary, LAG, R, Wind), FP, FM = import_formation()
    from pymavlink.dialects.v20 import ardupilotmega as m
    import pybullet as pb
    gz = G.Gorge(GL.GORGE_SEED)
    origin = GL.gorge_origin(geo)
    home = (origin.lat_e7 / 1e7, origin.lon_e7 / 1e7, origin.alt_m)
    reverse = (0, 0) if args.noses_forward else tuple(int(x) for x in FP.PLANS[args.plan]["reverse"])
    log(f"gorge seed {gz.seed} from {GL.LEANFC_ROOT}; origin {home}; plan {args.plan} {FP.PLANS[args.plan]}; reversed vehicles "
        f"{reverse} (a reversed vehicle: start facing backward, CONDITION_YAW items at {args.yaw_rate:g} deg/s, WP_YAW_BEHAVIOR 0; "
        f"the others ArduCopter's default heading)")
    t0 = time.perf_counter()
    missions, offset = formation_missions(FP, GP, gz, origin, args.plan, m, out, reverse, args.yaw_rate)
    log(f"formation_plan ({time.perf_counter() - t0:.1f} s): offset ENU {np.round(offset, 4).tolist()}, |o| "
        f"{np.linalg.norm(offset):.3f} m; starts ENU {[np.round(x['route'][0], 3).tolist() for x in missions]}; land sites "
        f"{[np.round(x['land'], 3).tolist() for x in missions]}; takeoff rel alt {[x['items'][1][5] for x in missions]}")

    substeps = args.pyb_hz // 400
    env = make_env(FM, GP, gz, args.pyb_hz, R.AIRFRAMES["x500"]["urdf"], LAG, [x["route"][0, :2] for x in missions],
                   [x["start_yaw_deg"] for x in missions])
    log(f"vehicles x500 x2: mass {env.M:.4f} kg, thrust-to-weight {env.THRUST2WEIGHT_RATIO:.4f}, motor lag {env.lag}, "
        f"collision r {env.COLLISION_R} h {env.COLLISION_H}; storage {args.storage} (copied per vehicle)")
    obs = reset_env(env)
    drones, client = list(env.DRONE_IDS), env.CLIENT
    world = list(env.world)
    wset = set(world)
    home_z = [float(obs[i][2]) for i in range(2)]
    log(f"start: settled at ENU {[np.round(obs[i][0:3], 4).tolist() for i in range(2)]}, tilt "
        f"{[round(math.degrees(math.acos(min(1.0, 1 - 2 * (obs[i][3] ** 2 + obs[i][4] ** 2)))), 2) for i in range(2)]} deg; "
        f"{len(world)} world bodies")

    Vs = [Vehicle(i, out, args, missions[i], m, home) for i in range(2)]
    for V in Vs:
        V.home_z = home_z[V.i]
        (V.out / "mission.json").write_text(json.dumps(dict(
            vehicle="x500", plan=args.plan, index=V.i + 1, home_z_settled=V.home_z, rest_z_plan=V.mission["rest_z"],
            planned_home=V.mission["planned_home"], origin=home, route_enu=V.mission["route"].tolist(),
            land_site_enu=V.mission["land"].tolist(), offset_enu=offset.tolist(), reverse=V.mission["reverse"],
            start_yaw_deg=V.mission["start_yaw_deg"], condition_yaw_deg=V.mission["yaw_items_deg"], yaw_rate_dps=args.yaw_rate,
            items=[dict(seq=s, command=int(c), frame=int(f), params=list(p), lat=la, lon=lo, alt=al)
                   for s, (c, f, p, la, lo, al) in enumerate(V.items)],
            plan_items=V.mission["plan_items"]), indent=1, default=float) + "\n")
        V.imu_buf = [V.sensors.imu(obs[V.i:V.i + 1])] * substeps
        V.log(f"mission: {len(V.items)} items ({V.mission['n_spline']} spline waypoints"
              + (f", {len(V.mission['yaw_items_deg'])} CONDITION_YAW {np.round(V.mission['yaw_items_deg'], 1).tolist()} deg, start heading "
                 f"{V.mission['start_yaw_deg']:.1f} deg" if V.mission["reverse"] else "") + f"), takeoff {V.items[1][5]:.3f} m, "
              f"land at {np.round(V.mission['land'], 3).tolist()}; "
              f"settled z {V.home_z:.4f} (plan rest z {V.mission['rest_z']:.4f})")

    cols = "t,x,y,z,qx,qy,qz,qw,vn,ve,vz_up,m1,m2,m3,m4,clearance,contacts,armed,mode,item".split(",")
    frows = []
    n_ticks = int(args.duration * 1e6 / STEP_US)
    w0 = time.perf_counter()
    k = 0
    end = "time limit"
    try:
        for k in range(n_ticks):
            t_us = STEP_US * (k + 1)
            for V in Vs:
                s = V.sensors.slow(k, obs[V.i:V.i + 1])
                V.line = encode_line = GL.encode_input(t_us, imu=V.imu_buf, baro=s.get("baro"), mag=s.get("mag"), gps=s.get("gps"),
                                                       rc=s.get("rc"), bat=GL.BATTERY["x500"], up=V.up)
                V.proc.stdin.write(encode_line + "\n")
            rpm = np.zeros((2, 4))
            for V in Vs:
                reply = V.proc.stdout.readline()
                if not reply:
                    V.exited = V.proc.wait()
                    end = f"vehicle {V.i + 1} exited (code {V.exited})"
                    break
                V.fin.write(V.line + "\n")
                V.fout.write(reply)
                _, pwm, down = GL.decode_output(reply)
                r, a = fr.pwm_to_rpm(env, pwm)
                rpm[V.i] = r
                V.act.append((t_us * 1e-6, *a))
                V.up = V.gcs.step(t_us * 1e-6, down)
            if any(V.exited is not None for V in Vs):
                break
            for V in Vs:
                V.imu_buf = []
            for _ in range(substeps):
                obs, *_ = env.step(rpm)
                for V in Vs:
                    V.imu_buf.append(V.sensors.imu(obs[V.i:V.i + 1]))
            if k % REC_EVERY == 0:
                tk = (k + 1) * STEP_US * 1e-6
                clear = []
                cw = []
                for V in Vs:
                    d = drones[V.i]
                    dist = [q[8] for b in world for q in pb.getClosestPoints(d, b, CLEAR_MAX, physicsClientId=client)]
                    clear.append(min(dist) if dist else CLEAR_MAX)
                    cw.append(len([q for q in pb.getContactPoints(bodyA=d, physicsClientId=client) if q[2] in wset]))
                    st = obs[V.i]
                    cur = V.rec["current"][-1][1] if V.rec["current"] else -1
                    V.rows.append([tk, *st[0:3], *st[3:7], st[11], st[10], st[12], *V.act[-1][1:], clear[-1], cw[-1],
                                   int(V.gcs.armed), V.gcs.mode if V.gcs.mode is not None else -1, cur])
                gap = pb.getClosestPoints(drones[0], drones[1], 10.0, physicsClientId=client)
                gap = min(q[8] for q in gap) if gap else 10.0
                cvv = len(pb.getContactPoints(bodyA=drones[0], bodyB=drones[1], physicsClientId=client))
                frows.append([tk, float(np.linalg.norm(obs[1][0:3] - obs[0][0:3])), gap, cvv, cw[0], cw[1], clear[0], clear[1]])
            if all(V.gcs.done for V in Vs):
                end = "both scripts finished" if not any(V.gcs.error for V in Vs) else \
                    "scripts ended: " + "; ".join(f"v{V.i + 1} {V.gcs.error or 'finished'}" for V in Vs)
                break
    except KeyboardInterrupt:
        end = "interrupted"
    finally:
        wall = time.perf_counter() - w0
        for V in Vs:
            V.proc.stdin.close()
        for V in Vs:
            V.tail = V.proc.stdout.read()
            V.code = V.proc.wait()
            V.fin.close()
            V.fout.close()
        env.close()
    steps = k + 1
    log(f"end: {end}; steps {steps} ({steps * STEP_US * 1e-6:.2f} s simulated), wall {wall:.2f} s "
        f"({steps * STEP_US * 1e-6 / wall:.2f}x real time)")

    with open(out / "formation.csv", "w") as f:
        f.write(",".join(FM.FCOLS) + "\n")
        for r in frows:
            f.write(",".join(str(int(x)) if 3 <= i <= 5 else repr(float(x)) for i, x in enumerate(r)) + "\n")
    fcsv = np.genfromtxt(out / "formation.csv", delimiter=",", names=True)
    vn = []
    for V in Vs:
        with open(V.out / "track.csv", "w") as f:
            f.write(",".join(cols) + "\n")
            for r in V.rows:
                f.write(",".join(repr(float(x)) if i < 16 else str(int(x)) for i, x in enumerate(r)) + "\n")
        act = np.array(V.act, float)
        np.save(V.out / "act.npy", act)
        track = np.genfromtxt(V.out / "track.csv", delimiter=",", names=True)
        n_spl = V.mission["n_spline"]
        nav = V.mission["nav_index"]       # mission seq -> index among the nav items (gorge_metrics numbers them so)
        rec_nav = dict(V.rec, reached=[(tt, nav[s]) for tt, s in V.rec["reached"] if s in nav],
                       current=[(tt, nav[s]) for tt, s in V.rec["current"] if s in nav])
        met = GL.gorge_metrics(track, rec_nav, V.mission["route"], V.home_z, n_spl)
        met["reached_seq"] = [s for _, s in V.rec["reached"]]
        met.pop("landing_error_m", None)          # gorge_metrics measures it to the last spline waypoint; see num
        spl = list(range(2, 2 + n_spl))
        met["completed"] = bool(V.rec["t_disarm"] is not None and all(s in met["reached"] for s in [1] + spl)
                                and met.get("contacts_between_liftoff_and_touchdown") == 0 and met.get("touchdown_t") is not None)
        num = vehicle_numbers(V, track, act, met)
        vn.append(dict(met=met, num=num))
        summary = [f"end: {end}", f"vehicle exit code {V.code}" + (f", unread output {len(V.tail)} bytes" if V.tail else "")]
        tf = V.out / "timing.txt"
        if tf.exists():
            summary.append(tf.read_text().splitlines()[0])
        summary.append("events: " + "; ".join(f"{t:.2f} {w}" for t, w in V.gcs.events))
        summary.append(f"mission: completed {met['completed']}; MISSION_ITEM_REACHED {met['reached']}; "
                       f"spline waypoints reached {sum(s in met['reached'] for s in spl)} of {n_spl}")
        if "arm_to_disarm_s" in met:
            summary.append(f"arm to disarm {met['arm_to_disarm_s']:.2f} s (simulated, heartbeats), "
                           f"{num.get('arm_to_disarm_texts_s', float('nan')):.3f} s (vehicle texts {num['t_arming_text']} to "
                           f"{num['t_disarming_text']}); route start (takeoff item reached) {num['route_start_t']} s")
        if "clearance_min_in_air_m" in met:
            summary.append(f"in the air ({met['air_window_s'][0]:.2f} to {met['air_window_s'][1]:.2f} s): clearance min "
                           f"{met['clearance_min_in_air_m']:.3f} m at N {met['clearance_min_at']['north']:.2f}; distance to the "
                           f"planned route max {met['route_distance_in_air_max_m']:.3f} m, rms {met['route_distance_in_air_rms_m']:.3f} m; "
                           f"ground speed max {met['ground_speed_max_ms']:.2f} m/s; tilt max {met['tilt_max_in_air_deg']:.1f} deg")
        if "contacts_between_liftoff_and_touchdown" in met:
            summary.append(f"terrain contacts between liftoff ({met['liftoff_t']:.2f} s) and touchdown ({met.get('touchdown_t')}): "
                           f"{met['contacts_between_liftoff_and_touchdown']}; touchdown {met.get('touchdown_speed_down_ms', float('nan')):.2f} m/s "
                           f"down, {num.get('landing_error_to_land_site_m', float('nan')):.2f} m from the land site; slide after "
                           f"touchdown max {num.get('slide_after_touchdown_max_m', float('nan')):.3f} m")
        if "actuator_max_air" in num:
            summary.append(f"actuators liftoff to touchdown (400 Hz) {num['actuator_min_air']:.3f}..{num['actuator_max_air']:.3f}, "
                           f"saturated ticks {num['saturated_ticks_air']} (landing {num.get('saturated_ticks_landing')})")
        if "heading_vs_travel_route_deg" in num:
            h = num["heading_vs_travel_route_deg"]
            summary.append(f"heading vs direction of travel on the route: min {h['min']:.1f}, max {h['max']:.1f}, p95 {h['p95']:.1f}, rms {h['rms']:.1f} deg")
        if "heading_deviation_from_backward_route_deg" in num:
            h = num["heading_deviation_from_backward_route_deg"]
            summary.append(f"nose against the direction of travel: deviation from exactly backward max {h['max']:.1f}, p95 {h['p95']:.1f}, "
                           f"rms {h['rms']:.1f} deg; MISSION_ITEM_REACHED (mission seq) {met['reached_seq']}")
        for line in summary:
            V.log(line)
        (V.out / "summary.txt").write_text("\n".join(summary) + "\n")
        flight = dict(end=end, plan=args.plan, vehicle="x500", index=V.i + 1, bin=args.bin, storage=str(V.storage),
                      storage_source=args.storage, seed=V.seed, gorge_seed=gz.seed, origin=home, home_z=V.home_z,
                      params_set=dict(V.sets), events=V.gcs.events, record=dict(V.rec), metrics=met, numbers=num,
                      wall_s=wall, simulated_s=steps * STEP_US * 1e-6)
        (V.out / "flight.json").write_text(json.dumps(flight, indent=1, default=float) + "\n")
        V.flight = flight

    pair = pair_numbers(fcsv, vn, Vs)
    nominal = float(np.linalg.norm(offset))
    fm = dict(plan=args.plan, gorge_seed=gz.seed, seed=0 if args.seed is None else args.seed, noise_seed=args.seed,
              offset_enu=offset.tolist(), nominal_distance=nominal, reverse=list(reverse), yaw_rate_dps=args.yaw_rate, end=end,
              completed=[x["met"]["completed"] for x in vn], pair=pair, downwash_modeled=False,
              simulated_s=steps * STEP_US * 1e-6, wall_s=wall)
    (out / "formation.json").write_text(json.dumps(fm, indent=1, default=float) + "\n")
    log(f"pair: completed {fm['completed']}; centre distance min whole record {pair['dist_min_whole_m']:.3f} m "
        f"(t {pair['dist_min_whole_t']:.2f}), both airborne {pair.get('dist_min_airborne_m', float('nan')):.3f} m "
        f"(t {pair.get('dist_min_airborne_t', float('nan')):.2f}), on the routes {pair.get('dist_route_m')}; nominal {nominal:.3f} m; "
        f"contact rows {pair['contact_rows']}; v2 - v1: arming text {pair.get('arm_diff_s')} s, route start "
        f"{pair.get('route_start_diff_s')} s, land item {pair.get('land_item_diff_s')} s, touchdown {pair.get('touchdown_diff_s')} s")

    if args.replay_check:
        for V in Vs:
            os.environ["LEAN_VEHICLE_OUT"] = str(V.out / "lean-replay")
            fr.replay_check(argparse.Namespace(bin=args.bin, storage=str(V.storage)), V.out, V.log)
    if args.ref_check:
        for V in Vs:
            GL.ref_check(V.out, V.log)
    if any(V.gcs.error for V in Vs):
        sys.exit(1)


if __name__ == "__main__":
    main()
