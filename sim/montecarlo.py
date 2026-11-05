#!/usr/bin/env python3
"""Monte Carlo validation of the course contract (sim/spec/mission-course.json, sim/monitor.py) on the
two copter vehicles.

N initial positions are drawn uniformly from the takeoff box of the spec's assumption, and then N
headings uniformly from [-pi, pi) (numpy's default_rng with a fixed seed, written to the output; the
positions are those of the same seed without headings); the vehicle starts level, at the sampled
heading and at rest at each of them (run_copter.place: in the air, or resting on the ground at the sampled north
and east when the sampled altitude is below the resting height of about 0.0135 m, where the
vehicle's collision cylinder would overlap the ground plane). An in-air start reports the specific
force (0, 0, -g) at tick 0 (--first-accel hover, the default): the reading of a vehicle held at rest
by its hover thrust, which is what the controllers' takeover assumes (run.start_hover) and what their
first actuators apply; --first-accel freefall reports (0, 0, 0), the reading of a vehicle released
with no thrust, after which both vehicles cut the throttle and sink to the ground before climbing
(RESULTS.md of a freefall run). Each sample is flown with both vehicles,
copter_lean and copter_ref, with the course parameters of sim/fly.sh's course-1ms flight
(copter-cf2x.txt, copter-course-speed.txt, copter-cf2x-tuned.txt, --exact), for the horizon of the
contract (K + 1 ticks, 30 s) unless the vehicle crashes (roll or pitch beyond 80 degrees) or is still
on the ground after 3 s, the end conditions of run_copter.py; the hold end condition of run_copter.py
is not used, so every trace covers the whole horizon of the formula.

The flights run in parallel (multiprocessing, default: physical cores minus one); each worker keeps
one PyBullet DIRECT environment (made once by run_copter.make_env, reset for every flight) and starts
one controller process per flight. The driver loop is run_copter.fly's (the same state lines,
actuator conversion and physics settings: CtrlAviary CF2X, PYB physics at 1200 Hz, gravity
GRAVITY_MSS, damping off) without its recording, trace replay and plots, and with byte pipes.

Outputs in --out (default sim/out/montecarlo):
- runs/<lean|ref>-<i>.csv.gz: per tick t, x_n, y_e, z_d (NED m, shortest round-trip decimals), yaw
  (rad), m1..m4 (the actuators as float32 bit patterns in hex); runs/<lean|ref>-<i>.txt: one line;
- summary.csv: one row per run and vehicle (sample index, sampled and realized initial position,
  verdict, every margin of monitor.monitor, leg times, ticks whose actuators differ from the paired
  run of the other vehicle);
- RESULTS.md: the spec, N, the seed, the pass counts, the margin distributions, parity, timing and
  the command.

Usage: sim/.venv/bin/python sim/montecarlo.py [--n 200] [--seed 20261105] [--workers K] [--out DIR]
"""
from __future__ import annotations

import argparse
import csv
import gzip
import json
import math
import os
import platform
import shlex
import subprocess
import sys
import time
from multiprocessing import get_context
from pathlib import Path

import numpy as np

SIM = Path(__file__).resolve().parent
ROOT = SIM.parent
sys.path.insert(0, str(SIM))
import monitor as M          # noqa: E402
import run_copter as R       # noqa: E402

BINS = {"lean": ROOT / "lean" / ".lake" / "build" / "bin" / "copter_lean",
        "ref": ROOT / "build" / "vehicle" / "copter_ref"}
NAMES = {"lean": "copter_lean", "ref": "copter_ref"}
DT = 1.0 / R.CTRL_HZ
CRASH = math.radians(80)
GROUND_TIMEOUT = 3.0


def physical_cores() -> int:
    try:
        return int(subprocess.run(["sysctl", "-n", "hw.physicalcpu"], capture_output=True, text=True,
                                  check=True).stdout)
    except Exception:
        return os.cpu_count() or 2


# --------------------------------------------------------------------------------------------
# Worker


_ENV = None


def _worker_init(pyb_hz: int):
    global _ENV
    import warnings
    warnings.filterwarnings("ignore")
    _ENV = R.make_env(False, pyb_hz)
    R.ground_rest_altitude(_ENV)


NOISE_KEYS = ("bp", "bv", "bq", "bw", "bf")


def perturb(rng, b, pos, vel, acc, quat, rates):
    """The sample the controller receives under bounded sensing noise: independent errors uniform in
    [-b, b] per component, added to the true state: position (bp, m), velocity (bv, m/s), specific
    force (bf, m/s^2), body rates (bw, rad/s); the attitude is rotated by a small body-frame rotation
    whose three angles are uniform in [-bq, bq] degrees (q' = q * dq, renormalized, scalar part >= 0).
    Fifteen uniforms are drawn every tick whatever the bounds, so the stream depends only on the seed
    and the tick."""
    u = rng.uniform(-1.0, 1.0, 15)
    # a zero bound leaves the component untouched (adding 0 * u would turn -0.0 into +0.0)
    if b["bp"]:
        pos = np.asarray(pos, float) + b["bp"] * u[0:3]
    if b["bv"]:
        vel = np.asarray(vel, float) + b["bv"] * u[3:6]
    if b["bf"]:
        acc = np.asarray(acc, float) + b["bf"] * u[6:9]
    if b["bw"]:
        rates = np.asarray(rates, float) + b["bw"] * u[12:15]
    rv = np.radians(b["bq"]) * u[9:12]
    ang = math.sqrt(float(rv @ rv))
    if ang > 0.0:
        ax = rv / ang
        dq = (math.cos(ang / 2), *(math.sin(ang / 2) * ax))
        q = R.qmul(quat, dq)
        nq = math.sqrt(sum(c * c for c in q))
        sgn = 1.0 if q[0] >= 0 else -1.0
        quat = tuple(sgn * c / nq for c in q)
    return pos, vel, acc, quat, rates


def fly_fast(env, cmd: list[str], init_ned, n_ticks: int, first_accel: str = "hover", yaw_deg: float = 0.0,
             noise: dict | None = None):
    """One closed-loop flight: run_copter.fly's loop (same state lines, same actuator conversion, the
    crash and ground end conditions) for n_ticks ticks, keeping only position, yaw and actuators. With
    `noise` ({bp, bv, bq, bw, bf, seed}), the sample sent to the controller is perturbed (perturb) from a
    generator seeded with `seed`; the physics, the end conditions and the recorded positions use the
    true state."""
    rng = np.random.default_rng(noise["seed"]) if noise else None
    R.place(env, init_ned, (0.0, 0.0, yaw_deg), first_accel)
    obs = R.reset_env(env)
    ground_start = bool(env.on_ground_at_start)
    sf = R.SpecificForce(env.G, DT)
    proc = subprocess.Popen(cmd, cwd=SIM, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    wfd = proc.stdin.fileno()
    readline = proc.stdout.readline
    sim_state, to_rpm, step = R.sim_state, R.actuators_to_rpm, env.step
    dt_s = " " + repr(DT) + "\n"
    P, Y, A = [], [], []
    end = "horizon"
    w0 = time.perf_counter()
    try:
        for k in range(n_ticks):
            pos, vel, acc, quat, att, rates = sim_state(env, obs, sf)
            if rng is None:
                line = " ".join([repr(float(v)) for v in (*pos, *vel, *acc, *quat, *rates)]) + dt_s
            else:
                sp, sv, sa, sq, sw = perturb(rng, noise, pos, vel, acc, quat, rates)
                line = " ".join([repr(float(v)) for v in (*sp, *sv, *sa, *sq, *sw)]) + dt_s
            os.write(wfd, line.encode())
            out = readline()
            ws = out.split()
            if len(ws) < 4:
                raise RuntimeError(f"bad controller line at tick {k}: {out!r} (exit {proc.poll()})")
            m = [float(v) for v in ws[:4]]
            P.append((float(pos[0]), float(pos[1]), float(pos[2])))
            Y.append(att[2])
            A.append(m)
            if abs(att[0]) > CRASH or abs(att[1]) > CRASH:
                end = f"crash: attitude beyond 80 deg at t={k * DT:.4f}"
                break
            if k * DT > GROUND_TIMEOUT and -pos[2] < 0.03 and abs(vel[2]) < 0.05:
                end = f"on the ground at t={k * DT:.4f}"
                break
            obs, *_ = step(to_rpm(env, m).reshape(1, 4))
    finally:
        wall = time.perf_counter() - w0
        try:
            proc.stdin.close()
        except BrokenPipeError:
            pass
        proc.wait(timeout=30)
    pos = np.array(P)
    acts = np.array(A, dtype=np.float64).astype(np.float32).view(np.uint32)
    return pos, np.array(Y), acts, end, wall, ground_start


def run_task(task: dict) -> dict:
    """Fly one sample with one vehicle, write its trace, monitor it."""
    t0 = time.perf_counter()
    v, i = task["vehicle"], task["index"]
    pos, yaw, acts, end, wall, ground = fly_fast(_ENV, task["cmd"], task["init"], task["n_ticks"],
                                                 task["first_accel"], math.degrees(task["heading"]),
                                                 task["noise"])
    spec = task["spec"]
    t = np.arange(len(pos)) / spec["tick_hz"]
    res = M.monitor(t, pos, task["waypoints"], spec)
    runs = Path(task["out"]) / "runs"
    if task["traces"]:
        with gzip.open(runs / f"{v}-{i:03d}.csv.gz", "wt", compresslevel=6, newline="") as f:
            f.write("t,x_n,y_e,z_d,yaw,m1,m2,m3,m4\n")
            f.write("".join(f"{k / 400:.4f},{p[0]!r},{p[1]!r},{p[2]!r},{float(y)!r},"
                            f"{a[0]:08x},{a[1]:08x},{a[2]:08x},{a[3]:08x}\n"
                            for k, (p, y, a) in enumerate(zip(pos.tolist(), yaw, acts.tolist()))))
    realized = pos[0].tolist()
    line = (f"{NAMES[v]} sample {i:03d}: sampled NED {' '.join(f'{x:.4f}' for x in task['init'])}, "
            f"heading {math.degrees(task['heading']):.2f} deg, "
            f"start {'on the ground' if ground else 'in the air'} at {' '.join(f'{x:.4f}' for x in realized)}; "
            f"{len(pos)} ticks, end {end}; verdict {res['verdict']} (safety {res['safety']}, reach {res['reach']}, "
            f"hold {res['hold']}){'; ' + res['failure'] if res['failure'] else ''}; flight {wall:.2f} s wall")
    (runs / f"{v}-{i:03d}.txt").write_text(line + "\n")
    return {"vehicle": v, "index": i, "init": task["init"], "heading": task["heading"], "realized": realized, "ground_start": ground,
            "end": end, "wall_fly": wall, "wall_task": time.perf_counter() - t0, "res": res,
            "acts": acts, "pid": os.getpid()}


# --------------------------------------------------------------------------------------------
# Report


def fmt_m(x: float, nd: int = 4) -> str:
    return "" if x is None or (isinstance(x, float) and math.isnan(x)) else f"{x:.{nd}f}"


def dist_row(name: str, vals, unit_scale=100.0, unit="cm", bound: str = "") -> str:
    a = np.array([v for v in vals if not math.isnan(v)])
    if not len(a):
        return f"| {name} | | | | {bound} |"
    s = unit_scale
    return f"| {name} | {a.min() * s:.2f} {unit} | {np.median(a) * s:.2f} {unit} | {a.max() * s:.2f} {unit} | {bound} |"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=200, help="number of initial positions (default 200)")
    ap.add_argument("--seed", type=int, default=20261105, help="seed of numpy's default_rng (default 20261105)")
    ap.add_argument("--workers", type=int, default=max(1, physical_cores() - 1),
                    help="parallel workers (default physical cores minus one)")
    ap.add_argument("--vehicles", nargs="+", default=["lean", "ref"], choices=["lean", "ref"])
    ap.add_argument("--spec", default=str(M.SPEC_PATH))
    ap.add_argument("--out", default=str(SIM / "out" / "montecarlo"))
    ap.add_argument("--pyb-hz", type=int, default=1200)
    ap.add_argument("--worst-case", action="store_true",
                    help="fly the 8 corners of the box and the 4 midpoints of its top edges instead of random "
                         "samples (--n and --seed are ignored)")
    ap.add_argument("--noise", default=None, metavar="LEVEL",
                    help="bounded sensing noise: a level of the spec's `sensing` entry (L1..L4)")
    for k_, unit in zip(NOISE_KEYS, ("m", "m/s", "deg", "rad/s", "m/s^2")):
        ap.add_argument(f"--noise-{k_}", type=float, default=None, help=f"noise bound {k_} ({unit}); overrides the level")
    ap.add_argument("--yaw0", action="store_true",
                    help="start every sample facing north (heading 0) instead of the sampled heading")
    ap.add_argument("--no-traces", action="store_true",
                    help="do not write the per-tick traces (runs/*.csv.gz), only the one-line summaries")
    ap.add_argument("--first-accel", choices=["hover", "freefall"], default="hover",
                    help="specific force reported at tick 0 for an in-air start: hover (0, 0, -g), the "
                         "reading of a vehicle held at rest by its hover thrust (default), or freefall "
                         "(0, 0, 0), run_copter.py's reading for a vehicle released with no thrust")
    args = ap.parse_args()

    spec = M.load_spec(Path(args.spec))
    files = [str((SIM / p).resolve()) for p in spec["params"]]
    mission = R.read_param_files(files, [])
    wps = [list(w) for w in mission["waypoints"]]
    if wps != spec["waypoints_ned_m"]:
        raise SystemExit("the parameter files' waypoints differ from the spec's")
    cmds = {}
    for v in args.vehicles:
        cmd = [str(BINS[v]), "--exact"]
        for f in files:
            cmd += ["--params", f]
        eff = R.effective_params(cmd, SIM, files, [])
        if [list(w) for w in eff["waypoints"]] != wps:
            raise SystemExit(f"{NAMES[v]} --print-params: mission differs from the spec's")
        cmds[v] = cmd

    out = Path(args.out)
    (out / "runs").mkdir(parents=True, exist_ok=True)
    lo, hi = M.box_bounds(spec)
    if args.worst_case:
        mid = (lo + hi) / 2
        corners = [[n_, e_, d_] for d_ in (hi[2], lo[2]) for n_ in (lo[0], hi[0]) for e_ in (lo[1], hi[1])]
        edges = [[lo[0], mid[1], lo[2]], [hi[0], mid[1], lo[2]], [mid[0], lo[1], lo[2]], [mid[0], hi[1], lo[2]]]
        pts = corners + edges
        cases = [(p_, h) for p_ in pts for h in (0.0, 90.0, 180.0, -90.0)]
        cases += [(p_, h) for p_ in corners[4:] for h in (45.0, -135.0)]
        samples = np.array([c[0] for c in cases], dtype=float)
        headings = np.radians([c[1] for c in cases])
        args.n = len(samples)
        sampling = ("a worst-case set (`--worst-case`): the 8 corners of the box (4 on the ground, 4 at its top) and "
                    "the 4 midpoints of its top edges, each at the headings 0, 90, 180 and -90 degrees, and the 4 top "
                    "corners also at 45 and -135 degrees")
    else:
        rng = np.random.default_rng(args.seed)
        samples = rng.uniform(lo, hi, size=(args.n, 3))
        headings = rng.uniform(-math.pi, math.pi, size=args.n)
        if args.yaw0:
            headings = np.zeros(args.n)
        sampling = (f"uniform in the box, `numpy.random.default_rng({args.seed})"
                    f".uniform(lo, hi, size=(N, 3))` with lo, hi the box corners (north, east, down), and then the "
                    f"headings from the same generator, `.uniform(-pi, pi, size=N)` (radians, from north, clockwise "
                    f"seen from above)" + ("; headings set to 0 (`--yaw0`)" if args.yaw0 else ""))
    n_ticks = spec["horizon_ticks"] + 1
    bounds = None
    if args.noise or any(getattr(args, f"noise_{k_}") is not None for k_ in NOISE_KEYS):
        bounds = {k_: 0.0 for k_ in NOISE_KEYS}
        if args.noise:
            bounds.update(spec["sensing"]["levels"][args.noise])
        for k_ in NOISE_KEYS:
            if getattr(args, f"noise_{k_}") is not None:
                bounds[k_] = getattr(args, f"noise_{k_}")
    def noise_of(i):
        # the same stream for both vehicles of a pair: seeded from the run's seed and the sample index
        return None if bounds is None else {**bounds, "seed": [args.seed, 1, i]}
    tasks = [{"vehicle": v, "index": i, "init": samples[i].tolist(), "heading": float(headings[i]),
              "cmd": cmds[v], "n_ticks": n_ticks, "noise": noise_of(i),
              "spec": spec, "waypoints": wps, "out": str(out), "first_accel": args.first_accel,
              "traces": not args.no_traces}
             for v in args.vehicles for i in range(args.n)]       # the slower lean flights first
    print(f"{len(tasks)} flights ({args.n} samples x {len(args.vehicles)} vehicles), {n_ticks} ticks each, "
          f"{args.workers} workers", flush=True)
    W0 = time.perf_counter()
    results = []
    ctx = get_context("spawn")
    with ctx.Pool(args.workers, initializer=_worker_init, initargs=(args.pyb_hz,)) as pool:
        for j, r in enumerate(pool.imap_unordered(run_task, tasks, chunksize=1)):
            results.append(r)
            if (j + 1) % 20 == 0 or not r["res"]["verdict"]:
                print(f"  {j + 1}/{len(tasks)} done, {time.perf_counter() - W0:.1f} s"
                      + ("" if r["res"]["verdict"] else
                         f"; VIOLATION {NAMES[r['vehicle']]} sample {r['index']}: {r['res']['failure']}"),
                      flush=True)
    wall_total = time.perf_counter() - W0

    by = {(r["vehicle"], r["index"]): r for r in results}
    # parity: actuator bit patterns of the paired runs, tick by tick
    diff = {}
    for i in range(args.n):
        if all((v, i) in by for v in ("lean", "ref")):
            a, b = by[("lean", i)]["acts"], by[("ref", i)]["acts"]
            n = min(len(a), len(b))
            d = int(np.any(a[:n] != b[:n], axis=1).sum()) + abs(len(a) - len(b))
            diff[i] = d

    # summary.csv
    nW = len(wps)
    head = (["index", "vehicle", "sampled_n", "sampled_e", "sampled_d", "heading_rad", "heading_deg", "start", "init_n", "init_e", "init_d",
             "verdict", "safety", "reach", "hold", "ceiling_clearance_m", "max_alt_m", "max_dist_S_m",
             "max_dist_path_m", "box_exit_s", "max_dist_path_after_box_m", "corridor_margin_m"]
            + [f"reach{i}_s" for i in range(nW)] + [f"leg{i}_s" for i in range(nW)]
            + [f"slack{i}_s" for i in range(nW)]
            + ["hold_first_s", "hold_best_start_s", "hold_max_dist_m", "hold_margin_m", "ticks", "end",
               "differing_ticks", "flight_wall_s", "failure"])
    with open(out / "summary.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(head)
        for v in args.vehicles:
            for i in range(args.n):
                r = by[(v, i)]
                q = r["res"]
                w.writerow([i, NAMES[v], *(repr(x) for x in r["init"]), repr(r["heading"]),
                            f"{math.degrees(r['heading']):.4f}",
                            "ground" if r["ground_start"] else "air", *(repr(x) for x in r["realized"]),
                            int(q["verdict"]), int(q["safety"]), int(q["reach"]), int(q["hold"]),
                            repr(q["ceiling_clearance_m"]), repr(q["max_alt_m"]), repr(q["max_dist_S_m"]),
                            repr(q["max_dist_path_m"]), repr(q["box_exit_s"]), repr(q["max_dist_path_after_box_m"]),
                            repr(q["corridor_margin_m"]), *map(repr, q["reach_s"]), *map(repr, q["leg_s"]),
                            *map(repr, q["leg_slack_s"]), repr(q["hold_first_s"]), repr(q["hold_start_s"]),
                            repr(q["hold_max_dist_m"]), repr(q["hold_margin_m"]), q["ticks"], r["end"],
                            diff.get(i, ""), f"{r['wall_fly']:.3f}", q["failure"]])

    # RESULTS.md
    cmd_line = "sim/.venv/bin/python sim/montecarlo.py " + " ".join(
        shlex.quote(a) for a in sys.argv[1:]) if sys.argv[1:] else "sim/.venv/bin/python sim/montecarlo.py"
    sim_s = {v: [len(by[(v, i)]["acts"]) * DT for i in range(args.n)] for v in args.vehicles}
    fly_w = {v: [by[(v, i)]["wall_fly"] for i in range(args.n)] for v in args.vehicles}
    task_w = {v: [by[(v, i)]["wall_task"] for i in range(args.n)] for v in args.vehicles}
    L = []
    w = L.append
    w("# Monte Carlo validation of the course contract")
    w("")
    w("Closed loop: each vehicle (`copter_lean`, the Lean translations; `copter_ref`, ArduPilot's classes compiled "
      "unmodified) in lock step with the CF2X in gym-pybullet-drones (PYB physics at 1200 Hz, control at 400 Hz, "
      "gravity 9.80665 m/s², no damping), flying the figure-eight course of `sim/params/copter-cf2x.txt` at 1 m/s "
      "with the tuned gains (`copter-cf2x.txt`, `copter-course-speed.txt`, `copter-cf2x-tuned.txt`, `--exact`), "
      "the parameters of `sim/fly.sh`'s course-1ms flight. Spec: `sim/spec/mission-course.json`; monitor: "
      "`sim/monitor.py` (the formula in STL notation is in its docstring); runner: `sim/montecarlo.py`.")
    w("")
    w("## The contract")
    w("")
    b = spec["box_ned_m"]
    w(f"- Assumption A, on the state at tick 0: level (roll and pitch 0), any heading (the attitude a rotation "
      f"about the down axis), at rest (zero velocity and body rates, the hover actuators held), position in the box north {b['north']}, east {b['east']}, down {b['down']} m (NED from "
      f"the takeoff point).")
    w(f"- Safety, every tick 0..K: altitude at most {spec['ceiling_m']} m, and distance 0 to S, the union of the "
      f"box and the corridor of radius {spec['corridor_radius_m']} m around the path (the takeoff point, then "
      f"w0..w7).")
    w(f"- Ordered reach: nested eventually operators, waypoint i within r = {spec['r_m']} m within its allowance "
      f"T_i after waypoint i-1 is reached (w0 from tick 0). Allowances "
      f"{', '.join(f'T{i} = {a} s' for i, a in enumerate(spec['allowances_s']))} "
      f"(rule: {spec['allowance_rule']}; nominal legs "
      f"{', '.join(f'{x:g}' for x in spec['nominal']['leg_s'])} s from `{spec['nominal']['run']}`).")
    w(f"- Reach and hold: within T = {spec['total_s']} s, within r of w7 and staying within r for "
      f"H = {spec['hold_s']} s.")
    w(f"- Horizon K = T + H = {spec['horizon_ticks']} ticks ({spec['horizon_ticks'] / 400:g} s); every flight "
      f"is simulated for ticks 0..K unless it crashes.")
    w("")
    w("## Samples")
    w("")
    ng = sum(1 for i in range(args.n) if by[(args.vehicles[0], i)]["ground_start"])
    w(f"N = {args.n} initial positions, {sampling}; each flown with {' and '.join(f'`{NAMES[v]}`' for v in args.vehicles)} "
      f"({len(tasks)} flights). {ng} of them lie below the vehicle's resting altitude "
      f"({_ENV_rest_alt(args.pyb_hz):.4f} m), where its collision cylinder would overlap the ground plane; "
      f"those start resting on the ground at the sampled north and east (settled as the nominal flight; "
      f"the realized position is in summary.csv), the other {args.n - ng} start in the air at the sampled "
      f"position. Tick-0 specific force of an in-air start: "
      + ("(0, 0, -g), the reading of a vehicle held at rest by its hover thrust, as the controllers' takeover "
         "assumes (`--first-accel hover`)." if args.first_accel == "hover" else
         "(0, 0, 0), free fall, the reading of a vehicle released with no thrust (`--first-accel freefall`)."))
    w("")
    if bounds is not None:
        w("## Sensing noise")
        w("")
        w(f"Level {args.noise or 'custom'}: every tick the sample sent to the controller is the true state plus "
          f"independent errors uniform in [-b, b] per component: position bp = {bounds['bp']:g} m, velocity "
          f"bv = {bounds['bv']:g} m/s, specific force bf = {bounds['bf']:g} m/s², body rates bw = {bounds['bw']:g} "
          f"rad/s, and the attitude rotated by a small body-frame rotation with angles uniform in [-bq, bq], "
          f"bq = {bounds['bq']:g} deg (quaternion renormalized). The physics, the end conditions and the monitored "
          f"positions use the true state. The noise of sample i comes from `numpy.random.default_rng([{args.seed}, "
          f"1, i])`, 15 uniforms per tick, the same stream for both vehicles of a pair "
          f"(`montecarlo.perturb`).")
        w("")
    w("## Verdicts")
    w("")
    w("| vehicle | runs | ψ holds | safety | ordered reach | reach and hold |")
    w("|---|---|---|---|---|---|")
    for v in args.vehicles:
        qs = [by[(v, i)]["res"] for i in range(args.n)]
        w(f"| `{NAMES[v]}` | {args.n} | {sum(q['verdict'] for q in qs)} | {sum(q['safety'] for q in qs)} | "
          f"{sum(q['reach'] for q in qs)} | {sum(q['hold'] for q in qs)} |")
    w("")
    viol = [(v, i) for v in args.vehicles for i in range(args.n) if not by[(v, i)]["res"]["verdict"]]
    if viol:
        w("Violations:")
        w("")
        for v, i in viol:
            r = by[(v, i)]
            w(f"- `{NAMES[v]}` sample {i}, sampled NED ({', '.join(f'{x:.4f}' for x in r['init'])}), heading {math.degrees(r['heading']):.2f} deg, start "
              f"{'on the ground' if r['ground_start'] else 'in the air'}: {r['res']['failure']}")
        w("")
    else:
        w("No run violates the contract.")
        w("")
    w("## Margins")
    w("")
    if len(args.vehicles) > 1:
        w(f"Over all {args.n} runs of each vehicle; the two vehicles' runs are identical tick by tick (below), so "
          f"their margins are equal and are given once (`{NAMES[args.vehicles[0]]}`).")
    else:
        w(f"Over all {args.n} runs of `{NAMES[args.vehicles[0]]}`.")
    w("")
    w("| margin | min | median | max | bound |")
    w("|---|---|---|---|---|")
    qs = [by[(args.vehicles[0], i)]["res"] for i in range(args.n)]
    w(dist_row("ceiling clearance (2.0 m minus max altitude)", [q["ceiling_clearance_m"] for q in qs],
               bound="> 0"))
    w(dist_row("max distance to S", [q["max_dist_S_m"] for q in qs], bound="= 0"))
    w(dist_row("max distance to the path after leaving the box", [q["max_dist_path_after_box_m"] for q in qs],
               bound=f"≤ {spec['corridor_radius_m'] * 100:g} cm"))
    w(dist_row("corridor margin (25 cm minus the above)", [q["corridor_margin_m"] for q in qs], bound="≥ 0"))
    w(dist_row("max distance to the path, whole run", [q["max_dist_path_m"] for q in qs],
               bound="(includes the start offset)"))
    w(dist_row("time of leaving the box", [q["box_exit_s"] for q in qs], unit_scale=1, unit="s"))
    for k in range(nW):
        w(dist_row(f"leg {k} time", [q["leg_s"][k] for q in qs], unit_scale=1, unit="s",
                   bound=f"≤ {spec['allowances_s'][k]} s"))
    for k in range(nW):
        w(dist_row(f"leg {k} slack", [q["leg_slack_s"][k] for q in qs], unit_scale=1, unit="s", bound="≥ 0"))
    w(dist_row("hold first achieved at", [q["hold_first_s"] for q in qs], unit_scale=1, unit="s",
               bound=f"≤ {spec['total_s']} s"))
    w(dist_row("hold, best window: max distance to w7", [q["hold_max_dist_m"] for q in qs],
               bound=f"≤ {spec['r_m'] * 100:g} cm"))
    w(dist_row("hold margin (10 cm minus the above)", [q["hold_margin_m"] for q in qs], bound="≥ 0"))
    w("")
    w("## Parity")
    w("")
    nd = sum(1 for d in diff.values() if d)
    if not diff:
        w("Not compared: one vehicle flown.")
    else:
        w(f"{len(diff)} paired runs; the four actuators of every tick are compared as float32 bit patterns "
          f"between `copter_lean` and `copter_ref`: {nd} paired runs with any differing tick "
          f"({sum(diff.values())} differing ticks in all, {sum(len(by[('lean', i)]['acts']) for i in diff)} "
          f"ticks compared).")
    w("")
    w("## Timing")
    w("")
    w(f"Machine: {platform.machine()}, {physical_cores()} physical cores, {args.workers} workers, Python "
      f"{platform.python_version()}. Total wall clock {wall_total:.1f} s for {len(tasks)} flights "
      f"({sum(sum(x) for x in sim_s.values()):.0f} simulated seconds).")
    w("")
    w("| vehicle | flights | simulated s per flight | wall s per flight (loop), median | wall s per flight (with trace file and monitor), median | wall s per simulated s, median |")
    w("|---|---|---|---|---|---|")
    for v in args.vehicles:
        ratio = [a / b for a, b in zip(fly_w[v], sim_s[v])]
        w(f"| `{NAMES[v]}` | {args.n} | {np.median(sim_s[v]):.4f} | {np.median(fly_w[v]):.3f} | "
          f"{np.median(task_w[v]):.3f} | {np.median(ratio):.4f} |")
    w("")
    w("The per-flight times are measured inside the workers, which run concurrently; a flight's wall clock "
      "therefore includes the contention of the other workers.")
    w("")
    w("## Reproduce")
    w("")
    w("```")
    w("sim/.venv/bin/python sim/monitor.py --derive-spec     # the spec from sim/out/lean-course-1ms (once)")
    w(cmd_line)
    w("```")
    w("")
    od = Path(out).resolve()
    od = od.relative_to(ROOT) if od.is_relative_to(ROOT) else od
    w(f"Outputs in `{od}`: summary.csv, samples.json, runs/<lean|ref>-<i>.csv.gz (per tick t, NED position, yaw, "
      f"the four actuators as float32 hex{'; not written for this run, --no-traces' if args.no_traces else ''}) and runs/<lean|ref>-<i>.txt (one line per run).")
    (out / "RESULTS.md").write_text("\n".join(L) + "\n")
    (out / "samples.json").write_text(json.dumps({"seed": None if args.worst_case else args.seed, "n": args.n, "box_ned_m": spec["box_ned_m"],
                                                  "samples_ned_m": samples.tolist(),
                                                  "headings_rad": [float(h) for h in headings]}, indent=0) + "\n")
    print("\n".join(L))


_REST = {}


def _ENV_rest_alt(pyb_hz: int) -> float:
    if pyb_hz not in _REST:
        env = R.make_env(False, pyb_hz)
        _REST[pyb_hz] = R.ground_rest_altitude(env)
        env.close()
    return _REST[pyb_hz]


if __name__ == "__main__":
    main()
