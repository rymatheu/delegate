#!/usr/bin/env python3
"""Fly one X500 through the gorge: ArduLean (sim/bridge/vehicle.py) in gym-pybullet-drones, in lock step, on the gorge
mission, with a scripted ground station; or in real time for QGroundControl (--udp, started by ./fly_qgc.sh).

    ../sim/.venv/bin/python sim/fly_gorge.py [--out DIR] [--udp [--udp-port 14550] [--pose-port P]] [--storage IMAGE]
        [--params FILE]... [--set NAME VALUE]... [--seed N] [--wind MEAN GUST] [--duration S] [--replay-check]
        [--spline-north Y1,Y2,... | --straight-north Y1,Y2,...]

No vehicle logic here. One protocol line per 400 Hz step (sim/bridge/protocol.py), the vehicle's output line back:
- the world: the gorge of ../sim/world/gorge.py (seed 7; generated from the seed on first use and cached in
  ../sim/build/world-cache/); the environment (../sim/gorgesim/simulator.py) is ../sim/world/gorge_aviary.GorgeAviary, the package's
  ground plane replaced by the gorge's collision bodies (concave terrain trimesh, boulder hulls, rock and vegetation
  compounds), Physics.PYB at 1200 Hz, gravity GRAVITY_MSS, PyBullet damping removed;
- the vehicle: the X500 of ../sim/world/x500/x500.urdf (mass, inertia, motor constants, collision cylinder) with the
  first-order motor lag airframes.LAG (12.5 ms up, 25 ms down), wind ../sim/world/wind.Wind with --wind, none otherwise;
  its four propellers are PX4's rotor_0..3, ArduPilot's quad-X motor slots 0..3 through ../sim/gorgesim/motors.py:
  actuator a = (PWM - 1000) / 1000, propeller speed MAX_RPM sqrt(a), so thrust a x 8.54858 N per motor; it boots from
  --storage (default sim/storage/storage-x500.bin);
- the sensors (../sim/gorgesim/sensor_layer.py): IMU after every physics substep, barometer and compass at 100 Hz, GPS at
  5 Hz, RC at 50 Hz, battery; home is the gorge's geographic origin (../sim/world/origin.params: 38.8405556, -105.0441667,
  4302 m), world ENU (0, 0, 0); --seed adds seeded noise;
- the start: resting on the gorge floor at the plan's start (Gorge.path[0], world ENU (0, 0)), level, nose north, its
  base 5 mm above gorge_plan.start_rest_z, settled on its contact for 0.25 s with the motors off;
- the mission (../sim/gorgesim/missions.py): NAV_TAKEOFF at the start, the 10 NAV_SPLINE_WAYPOINTs, NAV_LAND at the last
  waypoint, every waypoint 3.5 m above the floor on the centerline (the items of ../sim/world/gorge.plan);
- --spline-north (off by default): the spline waypoints re-spaced on the same centerline, at the given north
  coordinates y (m, world ENU): each at (Gorge.xc_fn(y), y, Gorge.floor_c(y) + gorge.FLIGHT_H), the points
  Gorge.flight_path chooses its waypoints from; the takeoff point and the last waypoint (the plan's, where NAV_LAND is)
  unchanged; the route of the metrics is then this path (flight.json "path");
- --straight-north (off by default; the S-curve flight of sim/README.md): the same, with the waypoints sent as
  MAV_CMD_NAV_WAYPOINT (straight legs flown by ArduPilot's S-curves with corner blending) in place of
  NAV_SPLINE_WAYPOINT; param1 (hold time) 0, so every waypoint is a fast waypoint;
- the ground station (../sim/gorgesim/ground_station.py, script_gorge): heartbeat, streams, parameter download, the
  PARAM_SETs of --params and --set, EKF3 using GPS, mission upload and download back, GUIDED, arm, NAV_TAKEOFF to the
  takeoff item's altitude, AUTO; it records MISSION_CURRENT and MISSION_ITEM_REACHED and waits for the disarm;
- the record (../sim/gorgesim/record.py): every 4th step (100 Hz) the true pose, NED velocity, actuators, the clearance to
  the gorge, the contact count, armed state, mode and mission item in track.csv; flight.json has the flight numbers.

--udp (./fly_qgc.sh): real time, for a ground station (QGroundControl). No scripted ground station, no mission upload
and no parameter set by this program: the vehicle's SERIAL0 is bridged to UDP 127.0.0.1:--udp-port
(../sim/gorgesim/udp_bridge.py: the downlink of each step one datagram, the datagrams received before a step in that step's
input line), the loop paced to the wall clock; no time limit unless --duration (Ctrl-C or SIGTERM ends the run and the
record is written). The person flies the mission from the ground station (../sim/world/gorge.plan holds the scripted
station's items). The record is the same files; track.csv's armed, mode and item columns and flight.json's record come
from the downlink (ground_station.watch), and summary.txt adds the real-time margin. --pose-port P (./fly_qgc.sh, for
the camera ../sim/world/camera_component.py): every 4th step the vehicle's true pose, as recorded in track.csv, sent as
one datagram to UDP 127.0.0.1:P (udp_bridge.PoseSender); it does not change what the vehicle sees.

Outputs in --out (default out/runs/gorge-<date>-<time>): inputs.txt, outputs.txt (the lock-step record: replaying
inputs.txt through the vehicle with storage_in.bin reproduces outputs.txt; --replay-check does it after the run),
storage_in.bin, log.txt, summary.txt, track.csv, mission.json, flight.json.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
ROOT = SIM_DIR.parent
sys.dont_write_bytecode = True           # no __pycache__ in the source tree

from bridge import vehicle  # noqa: E402   (puts the shared sim/ on sys.path)
from bridge.protocol import encode_input, decode_output  # noqa: E402
from gorgesim import ground_station, missions, record, simulator  # noqa: E402
from gorgesim.plant import Plant  # noqa: E402
from gorgesim.sensor_layer import BATTERY  # noqa: E402
from gorgesim.udp_bridge import UdpBridge, Pacer  # noqa: E402

STEP_US = simulator.STEP_US
VEHICLE = SIM_DIR / "bridge" / "vehicle.py"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out", default=None, help="folder for the run's record (default: out/runs/gorge-<date>-<time>)")
    ap.add_argument("--udp", action="store_true",
                    help="real time, no scripted ground station: the vehicle's SERIAL0 bridged to a ground station on UDP "
                         "127.0.0.1:--udp-port (QGroundControl); runs until Ctrl-C or SIGTERM unless --duration is given")
    ap.add_argument("--udp-port", type=int, default=14550, help="the ground station's UDP port on 127.0.0.1 (--udp)")
    ap.add_argument("--pose-port", type=int, default=0,
                    help="send the true pose at 100 Hz to UDP 127.0.0.1:P for the camera (./fly_qgc.sh; default 0: off)")
    ap.add_argument("--storage", default=str(SIM_DIR / "storage" / "storage-x500.bin"),
                    help="boot image (default: sim/storage/storage-x500.bin)")
    ap.add_argument("--wind", type=float, nargs=2, metavar=("MEAN", "GUST"), default=None,
                    help="the gorge's wind (../sim/world/wind.Wind, gust seed = noise seed (0 without --seed) + 1000)")
    ap.add_argument("--params", action="append", default=[], help="file of NAME VALUE lines to PARAM_SET (repeatable)")
    ap.add_argument("--set", nargs=2, action="append", default=[], metavar=("NAME", "VALUE"),
                    help="PARAM_SET through the parameter protocol after the download (repeatable, after --params)")
    ap.add_argument("--seed", type=int, help="sensor noise seed (default: no noise)")
    ap.add_argument("--duration", type=float, default=None,
                    help="limit, simulated seconds (default 240; with --udp none; 0: no limit)")
    ap.add_argument("--pyb-hz", type=int, default=1200)
    ap.add_argument("--replay-check", action="store_true",
                    help="after the flight, replay inputs.txt through the vehicle and compare the output with outputs.txt")
    ap.add_argument("--spline-north", default=None, metavar="Y1,Y2,...",
                    help="re-spaced spline waypoints at these north coordinates (m) on the gorge's centerline, the last "
                         "the plan's last waypoint (default: off, the plan's waypoints Gorge.path)")
    ap.add_argument("--straight-north", default=None, metavar="Y1,Y2,...",
                    help="as --spline-north, with the waypoints sent as NAV_WAYPOINT (straight S-curve legs) (default: off)")
    args = ap.parse_args()
    if args.out is None:
        args.out = str(ROOT / "out" / "runs" / time.strftime("gorge-%Y%m%d-%H%M%S"))
    if args.duration is None:
        args.duration = 0.0 if args.udp else 240.0
    if args.udp and (args.params or args.set or args.replay_check):
        sys.exit("fly_gorge: --params, --set and --replay-check belong to the scripted mode, not --udp")
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    logf = open(out / "log.txt", "w")

    def log(s):
        logf.write(s + "\n")
        logf.flush()
        print(s, flush=True)

    import gorge as G
    import gorge_plan as GP
    from pymavlink.dialects.v20 import ardupilotmega as m
    gz = G.Gorge(simulator.GORGE_SEED)
    origin = simulator.gorge_origin()
    home = (origin.lat_e7 / 1e7, origin.lon_e7 / 1e7, origin.alt_m)
    log(f"gorge seed {gz.seed} (../sim/world/gorge.py, world key {G.source_key(gz.seed)}); origin {home} (world ENU 0, 0, 0); start {gz.path[0].tolist()} (ENU)")
    gplan, spline_north, leg_cmd = gz, None, None
    if args.spline_north and args.straight_north:
        sys.exit("fly_gorge: --spline-north and --straight-north exclude each other")
    if args.spline_north or args.straight_north:
        spline_north = [float(v) for v in (args.spline_north or args.straight_north).split(",")]
        gplan = missions.PathView(gz, missions.respaced_path(gz, spline_north))
        leg_cmd = int(m.MAV_CMD_NAV_WAYPOINT) if args.straight_north else None
        kind = "straight NAV_WAYPOINT" if args.straight_north else "spline"
        log(f"--{'straight' if args.straight_north else 'spline'}-north: {len(spline_north)} {kind} waypoints on the centerline at "
            f"north {spline_north} (ENU {np.round(gplan.path[1:], 3).tolist()}) in place of the plan's {len(gz.path) - 1} spline waypoints")

    plant = Plant(seed=args.seed, wind=tuple(args.wind) if args.wind else None, gorge=gz, pyb_hz=args.pyb_hz,
                  pose_ports=[args.pose_port] if args.pose_port else None)
    env = plant.env
    log(f"vehicle x500: mass {env.M:.4f} kg, inertia {np.round(np.diag(env.J), 5).tolist()}, kf {env.KF:.6g} N/RPM^2, "
        f"km {env.KM:.6g}, thrust-to-weight {env.THRUST2WEIGHT_RATIO:.4f}, MAX_RPM {env.MAX_RPM:.2f}, motor lag {env.lag}, "
        f"collision r {env.COLLISION_R} h {env.COLLISION_H}, wind {args.wind}, storage {args.storage}")
    sample = plant.reset()
    obs = plant.obs
    home_z = float(obs[0][2])
    drone, client = env.DRONE_IDS[0], env.CLIENT
    world = list(env.world)
    import pybullet as pb
    log(f"start: vehicle settled at ENU {np.round(obs[0][0:3], 4).tolist()}, {len(world)} world bodies; "
        f"floor at start {float(gz.ground_z(gz.path[None, 0, :2])[0]):.4f}")

    items, plan_items = missions.gorge_mission(m, gplan, origin, leg_cmd)
    _, plan_home_z = GP.plan_items(gplan, origin)
    (out / "mission.json").write_text(json.dumps(dict(
        vehicle="x500", home_z_settled=home_z, plan_home_z=plan_home_z, origin=home,
        items=[dict(seq=s, command=int(c), frame=int(f), params=[None if isinstance(q, float) and math.isnan(q) else q for q in p],
                    lat=la, lon=lo, alt=al) for s, (c, f, p, la, lo, al) in enumerate(items)],
        plan_items=plan_items), indent=1, default=float) + "\n")
    log(f"mission: {len(items)} items (home, takeoff {items[1][5]:.3f} m, {len(items) - 3} spline waypoints, land); settled "
        f"start z {home_z:.4f}; relative altitudes the plan's (about z {plan_home_z:.4f})")

    (out / "storage_in.bin").write_bytes(Path(args.storage).read_bytes())
    env_vars = dict(os.environ)
    env_vars.setdefault("LEAN_VEHICLE_OUT", str(out / "lean"))
    cmd = [str(VEHICLE), "--timing-file", str(out / "timing.txt"), "--storage", args.storage]
    # --udp: the vehicle in its own session, so that Ctrl-C reaches only this harness, which then ends the vehicle by
    # closing its input
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1, env=env_vars,
                            start_new_session=args.udp)

    gcs = ground_station.GCS(m, log)
    rec = dict(reached=[], current=[], t_arm=None, t_auto=None, t_disarm=None)
    sets = list(ground_station.read_param_file(args.params).items()) + [(n, float(v)) for n, v in args.set]
    bridge = pacer = None
    poses = plant.poses[0] if plant.poses else None
    if args.udp:
        # no script: gcs only reads the downlink (armed, mode, mission item, texts) for the record; its own uplink is
        # discarded, the vehicle's uplink is what the ground station sends
        bridge = UdpBridge(args.udp_port)
        log(f"UDP bridge: vehicle at {bridge.addr}, ground station at {bridge.gcs_addr}; real time"
            + (f", {args.duration:g} s" if args.duration > 0 else ", until Ctrl-C"))

        def stop(*_):
            raise KeyboardInterrupt
        signal.signal(signal.SIGTERM, stop)
    else:
        gcs.script = ground_station.script_gorge(gcs, m, items, sets, rec)

    fin = open(out / "inputs.txt", "w")
    fout = open(out / "outputs.txt", "w")
    cols = record.TRACK_COLS
    rows = []
    up = b""
    n_ticks = int(args.duration * 1e6 / STEP_US)
    w0 = time.perf_counter()
    k = 0
    end = "time limit"
    act = [0.0] * 4
    if bridge is not None:
        pacer = Pacer(STEP_US * 1e-6)
    try:
        for k in (itertools.count() if args.duration <= 0 else range(n_ticks)):
            t_us = STEP_US * (k + 1)
            line = encode_input(t_us, imu=sample.imu, baro=sample.baro, mag=sample.mag, gps=sample.gps,
                                rc=sample.rc, bat=BATTERY, up=up)
            proc.stdin.write(line + "\n")
            reply = proc.stdout.readline()
            if not reply:
                end = f"vehicle exited (code {proc.wait()})"
                break
            fin.write(line + "\n")
            fout.write(reply)
            t_out, pwm, down = decode_output(reply)
            if bridge is None:
                up = gcs.step(t_us * 1e-6, down)
            else:
                gcs.step(t_us * 1e-6, down)
                ground_station.watch(gcs, rec)
                bridge.send(down)
                pacer.wait(k)
                up = bridge.receive()
            sample = plant.tick(pwm)                 # three physics substeps; poses to the camera every 4th tick
            obs, act = plant.obs, sample.actuators
            if k % record.REC_EVERY == 0:
                st = obs[0]
                dist = [q[8] for b in world for q in pb.getClosestPoints(drone, b, record.CLEAR_MAX, physicsClientId=client)]
                ncon = len(pb.getContactPoints(bodyA=drone, physicsClientId=client))
                cur = rec["current"][-1][1] if rec["current"] else -1
                rows.append([(k + 1) * STEP_US * 1e-6, *st[0:3], *st[3:7], st[11], st[10], st[12], *act,
                             min(dist) if dist else record.CLEAR_MAX, ncon, int(gcs.armed), gcs.mode if gcs.mode is not None else -1, cur])
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
        sent = poses.sent if poses is not None else 0
        plant.close()
        if bridge is not None:
            bridge.close()
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
    if pacer is not None:
        summary.append(pacer.summary(steps))
        summary.append(f"UDP: {bridge.sent} datagrams sent to {bridge.gcs_addr}, {bridge.received} received")
    if poses is not None:
        summary.append(f"poses: {sent} sent to {poses.addr}")
    track = np.genfromtxt(out / "track.csv", delimiter=",", names=True)
    try:
        met = record.gorge_metrics(track, rec, gplan.path, home_z, len(items) - 3)
    except Exception as e:                     # --udp: a session of any length and any mission
        if not args.udp:
            raise
        met = dict(reached=[s for _, s in rec["reached"]], current=[s for _, s in rec["current"]], error=repr(e))
    n_spl = len(items) - 3
    spl = list(range(2, 2 + n_spl))
    met["completed"] = bool(rec["t_disarm"] is not None and all(s in met["reached"] for s in [1] + spl)
                            and met.get("contacts_between_liftoff_and_touchdown") == 0 and met.get("touchdown_t") is not None)
    flight = dict(end=end, vehicle="x500", wind=args.wind, storage=args.storage, seed=args.seed, gorge_seed=gz.seed, origin=home,
                  home_z=home_z, params_set=dict(sets), events=gcs.events, record=dict(rec), metrics=met,
                  n_spline=n_spl, spline_north=spline_north, path=gplan.path.tolist(), leg_command=leg_cmd or 82,
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
        os.environ.setdefault("LEAN_VEHICLE_OUT", str(out / "lean-replay"))
        vehicle.replay_check(out, args.storage, log)
    (out / "summary.txt").write_text("\n".join(summary) + "\n")
    if gcs.error:
        sys.exit(1)


if __name__ == "__main__":
    main()
