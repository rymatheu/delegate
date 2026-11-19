#!/usr/bin/env python3
"""Fly two X500s through the gorge at the same time, each controlled by its own ArduLean (sim/bridge/vehicle.py), on
one of the two formation plans of ../sim/world/formation_plan.py (abreast, staggered), with one scripted ground station per
vehicle; or in real time for QGroundControl (--udp, started by ./fly_qgc.sh abreast|staggered).

    ../sim/.venv/bin/python sim/fly_gorge_formation.py --plan abreast|staggered
        [--out DIR] [--udp [--udp-port 14550] [--pose-ports P1 P2]] [--storage IMAGE] [--params FILE]... [--set NAME VALUE]...
        [--seed N] [--duration S] [--noses-forward] [--yaw-rate DEG_S] [--replay-check]

No vehicle logic here. Everything per vehicle is as in sim/fly_gorge.py, from the same modules of ../sim/gorgesim/: the
sensor layer (with --seed N vehicle 1 draws its noise from seed N and vehicle 2 from N + 100), the motor map, the
lock-step protocol, the ground-station script (script_gorge: heartbeat, streams, parameter download, the PARAM_SETs of
--params and --set, EKF3 using GPS, mission upload and download back, GUIDED, arm, NAV_TAKEOFF, AUTO, until the disarm),
the record (track.csv, 100 Hz) and the flight numbers (record.gorge_metrics). What is new:

- the world: one gym-pybullet-drones world (Physics.PYB, 1200 Hz physics, the gorge's collision bodies, seed 7) holding
  both vehicles, ../sim/world/gorge_aviary.FormationAviary: GorgeAviary with the X500's first-order motor lag (12.5 ms up,
  25 ms down) kept per vehicle; no wind. Contact between the vehicles and with the terrain is PyBullet's; no aerodynamic
  interaction between the vehicles is modeled;
- the vehicles: two independent processes of sim/bridge/vehicle.py, each with its own copy of the boot image
  (OUT/vN/storage_in.bin, a copy of --storage, default sim/storage/storage-x500.bin, whose parameters
  sim/params/storage-x500.txt lists: WP_SPD 2), its own LEAN_VEHICLE_OUT (OUT/vN/lean: the driver's outputs.txt,
  tasks.txt, outputs.txt.storage), its own timing file and its own record (OUT/vN/inputs.txt, outputs.txt); each has its
  own ground station (ground_station.GCS) that sees only that vehicle's downlink. There is no link between the vehicles
  and nothing synchronizes them besides the common world tick: at every 400 Hz tick both get their input line (the sensor
  sample of the same world state), both compute, then the world steps three physics substeps with both vehicles' motors;
- the missions (../sim/gorgesim/missions.py, formation_missions): the route centre (Gorge.path with its first point moved to
  the level start site, formation_plan.centre), the two routes (vehicle 2's = vehicle 1's + one constant offset whose
  vertical component equalizes the takeoff climbs, formation_plan.routes) and the level land sites
  (formation_plan.land_sites), written as QGroundControl plans by formation_plan.write_plan into OUT/vN/ and translated
  to ArduCopter items as missions.gorge_mission translates the single route: NAV_TAKEOFF, the 10 NAV_SPLINE_WAYPOINTs
  (param4 0, not NaN), NAV_LAND at the vehicle's land site, relative altitudes about the vehicle's own rest height.
  Heading: ArduCopter's WP_YAW_BEHAVIOR default (face the next waypoint) for both vehicles, except a vehicle the plan
  marks reversed (`reverse`, the staggered plan's vehicle 2), which gets CONDITION_YAW items at --yaw-rate and
  WP_YAW_BEHAVIOR 0 (--noses-forward turns this off);
- the start: each vehicle resting on the floor at its route's first point (level start site), level, nose north (a
  reversed vehicle: leg 1's heading + 180 deg), its base 5 mm above gorge_plan.start_rest_z, settled with the motors off
  for 0.25 s;
- the record: per vehicle OUT/vN/track.csv (record.TRACK_COLS; `contacts` counts vehicle-world contact points only),
  flight.json, summary.txt, log.txt, mission.json; for the pair OUT/formation.csv (every 4th tick: t, centre distance,
  closest distance of the two collision cylinders, contact points vehicle-vehicle, vehicle 1-world, vehicle 2-world,
  both clearances; gorge_aviary.FCOLS), OUT/formation.json (outcome, the pair's numbers and the fields
  ../sim/world/render_formation.Setup reads: plan, gorge_seed, nominal_distance, reverse, seed); OUT/vN/act.npy, the
  actuators of every tick (for the peak and saturation numbers).

--udp (./fly_qgc.sh abreast|staggered): real time, both vehicles for one ground station (QGroundControl), no scripted
stations: each vehicle's SERIAL0 bridged from its own UDP socket (../sim/gorgesim/udp_bridge.py) to 127.0.0.1:--udp-port, so
the ground station sees two sources; vehicle k has MAVLink system id k (vehicle 2's storage_in.bin is --storage with
MAV_SYSID 2 written into it, sim/bridge/storage_params.py) and a reversed vehicle has the WP_YAW_BEHAVIOR 0 that the
scripted station sets by PARAM_SET written into its image the same way. The loop is paced to the wall clock, no time
limit unless --duration (Ctrl-C or SIGTERM ends the run, the records are written). The plans the scripted stations
upload are ../sim/world/formation-PLAN-v1.plan and -v2.plan (../sim/gorgesim/write_qgc_plans.py). Default --out:
out/runs/formation-<date>-<time>. --pose-ports P1 P2 (./fly_qgc.sh, for the cameras
../sim/world/camera_component.py): every 4th tick (100 Hz) vehicle k's true pose sent as one datagram to UDP 127.0.0.1:Pk
(udp_bridge.PoseSender); it does not change what the vehicles see.

--replay-check: each vehicle's inputs.txt replayed through sim/bridge/vehicle.py (no simulator) from its
storage_in.bin, with its own LEAN_VEHICLE_OUT (OUT/vN/lean-replay), output compared with outputs.txt byte for byte.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
ROOT = SIM_DIR.parent
sys.dont_write_bytecode = True           # no __pycache__ in the source tree

from bridge import storage_params, vehicle  # noqa: E402   (puts the shared sim/ on sys.path)
from bridge.protocol import encode_input, decode_output  # noqa: E402
from gorgesim import ground_station, record, simulator  # noqa: E402
from gorgesim.missions import FP, formation_missions  # noqa: E402
from gorgesim.motors import pwm_to_rpm  # noqa: E402
from gorgesim.plant import FormationPlant  # noqa: E402
from gorgesim.sensor_layer import BATTERY  # noqa: E402
from gorgesim.udp_bridge import UdpBridge, Pacer  # noqa: E402

STEP_US = simulator.STEP_US
REC_EVERY = record.REC_EVERY
CLEAR_MAX = record.CLEAR_MAX
VEHICLE = SIM_DIR / "bridge" / "vehicle.py"
SAT_HI, SAT_LO = 0.999, 0.001            # a saturated tick: some actuator at or above SAT_HI or at or below SAT_LO (formation.summarize)


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
        self.image_params = {}
        if args.udp:
            # one ground station sees both vehicles: each its own MAVLink system id (vehicle k: MAV_SYSID k), and a
            # reversed vehicle the WP_YAW_BEHAVIOR 0 the scripted station sets by PARAM_SET (below), both in its image
            self.image_params = {"MAV_SYSID": i + 1} if i > 0 else {}
            if mission["reverse"]:
                self.image_params["WP_YAW_BEHAVIOR"] = 0
            self.storage.write_bytes(storage_params.with_params(Path(args.storage).read_bytes(), self.image_params))
        else:
            shutil.copyfile(args.storage, self.storage)
        self.lean_out = self.out / "lean"
        env = dict(os.environ, LEAN_VEHICLE_OUT=str(self.lean_out))
        cmd = [str(VEHICLE), "--timing-file", str(self.out / "timing.txt"), "--storage", str(self.storage)]
        self.proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1, env=env,
                                     start_new_session=args.udp)
        self.seed = None if args.seed is None else args.seed + 100 * i     # the plant's noise seed of this vehicle
        self.gcs = ground_station.GCS(m, self.log)
        self.rec = dict(reached=[], current=[], t_arm=None, t_auto=None, t_disarm=None)
        self.sets = list(ground_station.read_param_file(args.params).items()) + [(n, float(v)) for n, v in args.set]
        if mission["reverse"]:
            self.sets.append(("WP_YAW_BEHAVIOR", 0.0))       # NONE: keep the FIXED heading of CONDITION_YAW across spline legs
        self.bridge = None
        if args.udp:
            self.bridge = UdpBridge(args.udp_port)      # its own socket: its own source port at the ground station
            self.log(f"UDP bridge: vehicle at {self.bridge.addr} (MAV_SYSID {self.image_params.get('MAV_SYSID', 1)}"
                     + (", WP_YAW_BEHAVIOR 0" if "WP_YAW_BEHAVIOR" in self.image_params else "")
                     + f" in its image), ground station at {self.bridge.gcs_addr}")
        else:
            self.gcs.script = ground_station.script_gorge(self.gcs, m, self.items, self.sets, self.rec)
        self.fin = open(self.out / "inputs.txt", "w")
        self.fout = open(self.out / "outputs.txt", "w")
        self.up = b""
        self.rows = []
        self.act = []
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
    ap.add_argument("--out", default=None, help="folder for the run's record (default: out/runs/formation-<date>-<time>)")
    ap.add_argument("--udp", action="store_true",
                    help="real time, no scripted ground stations: each vehicle's SERIAL0 bridged from its own UDP socket to "
                         "one ground station on 127.0.0.1:--udp-port (QGroundControl), vehicle k with MAVLink system id k; "
                         "runs until Ctrl-C or SIGTERM unless --duration is given")
    ap.add_argument("--udp-port", type=int, default=14550, help="the ground station's UDP port on 127.0.0.1 (--udp)")
    ap.add_argument("--pose-ports", type=int, nargs=2, default=None, metavar=("P1", "P2"),
                    help="send each vehicle's true pose at 100 Hz to UDP 127.0.0.1:Pk for its camera (./fly_qgc.sh; default: off)")
    ap.add_argument("--storage", default=str(SIM_DIR / "storage" / "storage-x500.bin"),
                    help="boot image, copied for each vehicle (default sim/storage/storage-x500.bin)")
    ap.add_argument("--params", action="append", default=[], help="file of NAME VALUE lines to PARAM_SET (both vehicles)")
    ap.add_argument("--set", nargs=2, action="append", default=[], metavar=("NAME", "VALUE"),
                    help="PARAM_SET after the download (both vehicles; repeatable, after --params)")
    ap.add_argument("--seed", type=int, help="sensor noise seed (vehicle 1: N, vehicle 2: N + 100; default: no noise)")
    ap.add_argument("--duration", type=float, default=None,
                    help="limit, simulated seconds (default 240; with --udp none; 0: no limit)")
    ap.add_argument("--pyb-hz", type=int, default=1200)
    ap.add_argument("--noses-forward", action="store_true",
                    help="staggered: fly vehicle 2 nose forward too (default: nose against the direction of travel, as the plan's reverse flag)")
    ap.add_argument("--yaw-rate", type=float, default=10.0, help="turn rate of the CONDITION_YAW items of a reversed vehicle (deg/s)")
    ap.add_argument("--replay-check", action="store_true",
                    help="after the flight, replay each vehicle's inputs.txt through its vehicle and compare with outputs.txt")
    args = ap.parse_args()
    if args.out is None:
        args.out = str(ROOT / "out" / "runs" / time.strftime("formation-%Y%m%d-%H%M%S"))
    if args.duration is None:
        args.duration = 0.0 if args.udp else 240.0
    if args.udp and (args.params or args.set or args.replay_check):
        sys.exit("fly_gorge_formation: --params, --set and --replay-check belong to the scripted mode, not --udp")
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    logf = open(out / "log.txt", "w")

    def log(s):
        logf.write(s + "\n")
        logf.flush()
        print(s, flush=True)

    import gorge as G
    import gorge_aviary as FM
    from pymavlink.dialects.v20 import ardupilotmega as m
    import pybullet as pb
    gz = G.Gorge(simulator.GORGE_SEED)
    origin = simulator.gorge_origin()
    home = (origin.lat_e7 / 1e7, origin.lon_e7 / 1e7, origin.alt_m)
    reverse = (0, 0) if args.noses_forward else tuple(int(x) for x in FP.PLANS[args.plan]["reverse"])
    log(f"gorge seed {gz.seed} (../sim/world/gorge.py, world key {G.source_key(gz.seed)}); origin {home}; plan {args.plan} {FP.PLANS[args.plan]}; reversed vehicles "
        f"{reverse} (a reversed vehicle: start facing backward, CONDITION_YAW items at {args.yaw_rate:g} deg/s, WP_YAW_BEHAVIOR 0; "
        f"the others ArduCopter's default heading)")
    t0 = time.perf_counter()
    missions, offset = formation_missions(gz, origin, args.plan, m, out, reverse, args.yaw_rate)
    log(f"formation_plan ({time.perf_counter() - t0:.1f} s): offset ENU {np.round(offset, 4).tolist()}, |o| "
        f"{np.linalg.norm(offset):.3f} m; starts ENU {[np.round(x['route'][0], 3).tolist() for x in missions]}; land sites "
        f"{[np.round(x['land'], 3).tolist() for x in missions]}; takeoff rel alt {[x['items'][1][5] for x in missions]}")

    plant = FormationPlant([x["route"][0, :2] for x in missions], [x["start_yaw_deg"] for x in missions],
                           seeds=[None if args.seed is None else args.seed + 100 * i for i in range(2)], gorge=gz,
                           pyb_hz=args.pyb_hz, pose_ports=args.pose_ports)
    env = plant.env
    log(f"vehicles x500 x2: mass {env.M:.4f} kg, thrust-to-weight {env.THRUST2WEIGHT_RATIO:.4f}, motor lag {env.lag}, "
        f"collision r {env.COLLISION_R} h {env.COLLISION_H}; storage {args.storage} (copied per vehicle)")
    samples = plant.reset()
    obs = plant.obs
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
        V.log(f"mission: {len(V.items)} items ({V.mission['n_spline']} spline waypoints"
              + (f", {len(V.mission['yaw_items_deg'])} CONDITION_YAW {np.round(V.mission['yaw_items_deg'], 1).tolist()} deg, start heading "
                 f"{V.mission['start_yaw_deg']:.1f} deg" if V.mission["reverse"] else "") + f"), takeoff {V.items[1][5]:.3f} m, "
              f"land at {np.round(V.mission['land'], 3).tolist()}; "
              f"settled z {V.home_z:.4f} (plan rest z {V.mission['rest_z']:.4f})")

    cols = record.TRACK_COLS
    frows = []
    n_ticks = int(args.duration * 1e6 / STEP_US)
    pacer = None
    poses = plant.poses
    if args.udp:
        def stop(*_):
            raise KeyboardInterrupt
        signal.signal(signal.SIGTERM, stop)
        log("real time" + (f", {args.duration:g} s" if args.duration > 0 else ", until Ctrl-C"))
    w0 = time.perf_counter()
    k = 0
    end = "time limit"
    try:
        if args.udp:
            pacer = Pacer(STEP_US * 1e-6)
        for k in (itertools.count() if args.duration <= 0 else range(n_ticks)):
            t_us = STEP_US * (k + 1)
            for V in Vs:
                s = samples[V.i]
                V.line = encode_line = encode_input(t_us, imu=s.imu, baro=s.baro, mag=s.mag, gps=s.gps,
                                                    rc=s.rc, bat=BATTERY, up=V.up)
                V.proc.stdin.write(encode_line + "\n")
            pwms = [None, None]
            for V in Vs:
                reply = V.proc.stdout.readline()
                if not reply:
                    V.exited = V.proc.wait()
                    end = f"vehicle {V.i + 1} exited (code {V.exited})"
                    break
                V.fin.write(V.line + "\n")
                V.fout.write(reply)
                _, pwm, down = decode_output(reply)
                _, a = pwm_to_rpm(env, pwm)            # the actuators, for the record (the plant applies pwm)
                pwms[V.i] = pwm
                V.act.append((t_us * 1e-6, *a))
                if V.bridge is None:
                    V.up = V.gcs.step(t_us * 1e-6, down)
                else:
                    V.gcs.step(t_us * 1e-6, down)       # reads the downlink only; its own uplink is discarded
                    ground_station.watch(V.gcs, V.rec)
                    V.bridge.send(down)
            if any(V.exited is not None for V in Vs):
                break
            if pacer is not None:
                pacer.wait(k)
                for V in Vs:
                    V.up = V.bridge.receive()
            samples = plant.tick(pwms)               # three physics substeps; poses to the cameras every 4th tick
            obs = plant.obs
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
            if V.bridge is not None:
                V.bridge.close()
        plant.close()
    steps = k + 1
    log(f"end: {end}; steps {steps} ({steps * STEP_US * 1e-6:.2f} s simulated), wall {wall:.2f} s "
        f"({steps * STEP_US * 1e-6 / wall:.2f}x real time)")
    if pacer is not None:
        log(pacer.summary(steps))
        log("UDP: " + "; ".join(f"v{V.i + 1} {V.bridge.sent} datagrams sent, {V.bridge.received} received" for V in Vs))
    if poses is not None:
        log("poses: " + "; ".join(f"v{i + 1} {ps.sent} sent to {ps.addr}" for i, ps in enumerate(poses)))

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
        spl = list(range(2, 2 + n_spl))
        try:
            met = record.gorge_metrics(track, rec_nav, V.mission["route"], V.home_z, n_spl)
            met["reached_seq"] = [s for _, s in V.rec["reached"]]
            met.pop("landing_error_m", None)          # gorge_metrics measures it to the last spline waypoint; see num
            met["completed"] = bool(V.rec["t_disarm"] is not None and all(s in met["reached"] for s in [1] + spl)
                                    and met.get("contacts_between_liftoff_and_touchdown") == 0 and met.get("touchdown_t") is not None)
            num = vehicle_numbers(V, track, act, met)
        except Exception as e:                    # --udp: a session of any length and any mission
            if not args.udp:
                raise
            met = dict(reached=[s for _, s in rec_nav["reached"]], reached_seq=[s for _, s in V.rec["reached"]],
                       completed=False, error=repr(e))
            num = {}
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
        flight = dict(end=end, plan=args.plan, vehicle="x500", index=V.i + 1, storage=str(V.storage),
                      storage_source=args.storage, seed=V.seed, gorge_seed=gz.seed, origin=home, home_z=V.home_z,
                      params_set=dict(V.sets), events=V.gcs.events, record=dict(V.rec), metrics=met, numbers=num,
                      wall_s=wall, simulated_s=steps * STEP_US * 1e-6)
        if args.udp:
            flight.update(params_set={}, image_params=V.image_params, udp=dict(port=args.udp_port, vehicle=list(V.bridge.addr)))
        (V.out / "flight.json").write_text(json.dumps(flight, indent=1, default=float) + "\n")
        V.flight = flight

    try:
        pair = pair_numbers(fcsv, vn, Vs)
    except Exception as e:                        # --udp: a session of any length
        if not args.udp:
            raise
        pair = dict(error=repr(e))
    nominal = float(np.linalg.norm(offset))
    fm = dict(plan=args.plan, gorge_seed=gz.seed, seed=0 if args.seed is None else args.seed, noise_seed=args.seed,
              offset_enu=offset.tolist(), nominal_distance=nominal, reverse=list(reverse), yaw_rate_dps=args.yaw_rate, end=end,
              completed=[x["met"]["completed"] for x in vn], pair=pair, downwash_modeled=False,
              simulated_s=steps * STEP_US * 1e-6, wall_s=wall)
    (out / "formation.json").write_text(json.dumps(fm, indent=1, default=float) + "\n")
    if "error" in pair:
        log(f"pair: numbers not available ({pair['error']})")
    else:
        log(f"pair: completed {fm['completed']}; centre distance min whole record {pair['dist_min_whole_m']:.3f} m "
            f"(t {pair['dist_min_whole_t']:.2f}), both airborne {pair.get('dist_min_airborne_m', float('nan')):.3f} m "
            f"(t {pair.get('dist_min_airborne_t', float('nan')):.2f}), on the routes {pair.get('dist_route_m')}; nominal {nominal:.3f} m; "
            f"contact rows {pair['contact_rows']}; v2 - v1: arming text {pair.get('arm_diff_s')} s, route start "
            f"{pair.get('route_start_diff_s')} s, land item {pair.get('land_item_diff_s')} s, touchdown {pair.get('touchdown_diff_s')} s")

    if args.replay_check:
        for V in Vs:
            os.environ["LEAN_VEHICLE_OUT"] = str(V.out / "lean-replay")
            vehicle.replay_check(V.out, V.storage, V.log)
    if any(V.gcs.error for V in Vs):
        sys.exit(1)


if __name__ == "__main__":
    main()
