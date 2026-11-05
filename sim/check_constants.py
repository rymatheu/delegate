#!/usr/bin/env python3
"""Check the constants of the Lean sub-contracts (contracts/Contracts/Mission/Sub.lean) on every Monte
Carlo start: the 200 samples of sim/out/montecarlo and the worst-case starts of
sim/out/montecarlo-worst-case. Read-only with respect to the spec, the runs and the figures; writes
sim/out/montecarlo/CONSTANTS.md and constants.csv.

Per start: the start is flown again with copter_ref exactly as sim/montecarlo.py flies it (its loop,
recording the state lines); the flown positions and actuator bit patterns are checked equal, tick by
tick, to the recorded run (runs/ref-<i>.csv.gz); the state lines are then replayed through copter_ref
with --exact --trace, as compare_flights.py does, the replayed actuators are checked equal to the
flown ones, and the first three trace numbers are the position target after each tick (AC_PosControl's
get_pos_desired_NED_m). Ticks 0..K (K = horizon_ticks of the spec) are used. With the Lean
definitions (Loop.lean, Spec.lean): err = |pos_t - target_t| (the target after tick t), smpErr =
|sampled position_t - target_t|, polyDist the distance to the polyline through pathPt (the takeoff
point, then w0..w7), `inColumn` the takeoff prism |n|, |e| <= 0.151, -0.8 <= d <= 0.001.

    sim/.venv/bin/python sim/check_constants.py [--workers K]
"""
from __future__ import annotations

import argparse
import csv
import gzip
import json
import math
import os
import subprocess
import time
from multiprocessing import get_context
from pathlib import Path

import numpy as np

import monitor as M
import montecarlo as MC
import run_copter as R

SIM = Path(__file__).resolve().parent
OUT = SIM / "out" / "montecarlo"
# Sub.lean
RHO, DELTA, DELTA0, RPASS, DELTAS = 0.155, 0.095, 0.035, 0.105, 0.096
COL_NE, COL_DOWN_LO, COL_DOWN_HI = 0.151, -0.8, 0.001
R_WP = 0.1


def fly_record(env, cmd, init_ned, n_ticks, yaw_deg=0.0):
    """montecarlo.fly_fast's loop, keeping the state lines and the actuator lines."""
    R.place(env, init_ned, (0.0, 0.0, yaw_deg), "hover")
    obs = R.reset_env(env)
    sf = R.SpecificForce(env.G, MC.DT)
    proc = subprocess.Popen(cmd, cwd=SIM, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    wfd, readline = proc.stdin.fileno(), proc.stdout.readline
    dt_s = " " + repr(MC.DT) + "\n"
    lines, P, A = [], [], []
    try:
        for k in range(n_ticks):
            pos, vel, acc, quat, att, rates = R.sim_state(env, obs, sf)
            line = " ".join([repr(float(v)) for v in (*pos, *vel, *acc, *quat, *rates)]) + dt_s
            os.write(wfd, line.encode())
            m = [float(v) for v in readline().split()[:4]]
            lines.append(line)
            P.append((float(pos[0]), float(pos[1]), float(pos[2])))
            A.append(m)
            if abs(att[0]) > MC.CRASH or abs(att[1]) > MC.CRASH or (
                    k * MC.DT > MC.GROUND_TIMEOUT and -pos[2] < 0.03 and abs(vel[2]) < 0.05):
                break
            obs, *_ = env.step(R.actuators_to_rpm(env, m).reshape(1, 4))
    finally:
        proc.stdin.close()
        proc.wait(timeout=30)
    return lines, np.array(P), np.array(A, dtype=np.float64).astype(np.float32).view(np.uint32)


def read_recorded(path: Path):
    with gzip.open(path, "rt") as f:
        rows = list(csv.reader(f))[1:]
    pos = np.array([[float(r[1]), float(r[2]), float(r[3])] for r in rows])
    acts = np.array([[int(h, 16) for h in r[5:9]] for r in rows], dtype=np.uint32)
    return pos, acts


def windows(mask: np.ndarray):
    """Maximal runs of True: list of (start, end) inclusive."""
    d = np.diff(np.concatenate([[0], mask.astype(int), [0]]))
    return list(zip(np.nonzero(d == 1)[0], np.nonzero(d == -1)[0] - 1))


def check(task):
    spec, set_name, i, init, heading = task["spec"], task["set"], task["index"], task["init"], task["heading"]
    K = spec["horizon_ticks"]
    lines, pos, acts = fly_record(MC._ENV, task["cmd"], init, K + 1, math.degrees(heading))
    rpos, racts = read_recorded(Path(task["run"]))
    same = len(pos) == len(rpos) and np.array_equal(pos, rpos) and np.array_equal(acts, racts)
    rep = subprocess.run(task["cmd"] + ["--trace"], cwd=SIM, input="".join(lines), capture_output=True,
                         text=True, check=True).stdout.splitlines()
    ra = np.array([[float(v) for v in ln.split()[:4]] for ln in rep]).astype(np.float32).view(np.uint32)
    replay_same = np.array_equal(ra, acts)
    tgt = np.array([[float(v) for v in ln.split()[4:7]] for ln in rep])
    smp = np.array([[float(v) for v in ln.split()[:3]] for ln in lines])
    n = min(len(pos), K + 1)
    pos, tgt, smp = pos[:n], tgt[:n], smp[:n]
    V = np.array(spec["path_ned_m"])
    W = np.array(spec["waypoints_ned_m"])
    err = np.linalg.norm(pos - tgt, axis=1)
    serr = np.linalg.norm(smp - tgt, axis=1)
    pd = M.dist_to_polyline(tgt, V)
    pd_nc = M.dist_to_polyline(tgt, V[1:])                 # the polyline without the climb segment
    incol = (np.abs(tgt[:, 0]) <= COL_NE) & (np.abs(tgt[:, 1]) <= COL_NE) & \
            (COL_DOWN_LO <= tgt[:, 2]) & (tgt[:, 2] <= COL_DOWN_HI)
    climb = incol & (pd > RHO)
    climb_nc = incol & (pd_nc > RHO)
    navq = np.where(incol, 0.0, pd)
    res = {"set": set_name, "index": i, "init": init, "heading": heading, "ticks": n, "same_as_recorded": bool(same),
           "replay_same": bool(replay_same),
           "a_max_err": float(err.max()), "a_tick": int(err.argmax()),
           "b_max_err": float(err[climb].max()) if climb.any() else float("nan"), "b_ticks": int(climb.sum()),
           "b2_max_err": float(err[climb_nc].max()) if climb_nc.any() else float("nan"),
           "b2_ticks": int(climb_nc.sum()),
           "c_max": float(navq.max()), "c_tick": int(navq.argmax()),
           "e_max": float(serr.max()), "e_equal_a": bool(np.array_equal(serr, err))}
    viol, lslack, rslack = 0, [], []
    anyv = np.zeros(n, bool)
    per_wp, vmax, tmin = [], [], []
    for j, w in enumerate(W):
        dt_ = np.linalg.norm(tgt - w, axis=1)
        dv = np.linalg.norm(pos - w, axis=1)
        tin = dt_ <= RPASS
        vin = dv <= R_WP
        bad = tin & ~vin
        viol += int(bad.sum())
        anyv |= bad
        per_wp.append(int(bad.sum()))
        vmax.append(float(dv[bad].max()) if bad.any() else None)
        tmin.append(float(dt_[bad].min()) if bad.any() else None)
        # on the vehicle's side: ticks inside the vehicle's r-ball while the target is out of rPass are fine
        vw = windows(vin)
        ls, rs_ = [], []
        for a, b in windows(tin):
            cont = [(c, d) for c, d in vw if c <= a and b <= d]
            if cont:
                c, d = cont[0]
                ls.append(int(a - c))
                rs_.append(None if (d == n - 1 and b == n - 1) else int(d - b))
        lslack.append(min(ls) if ls else None)
        r_ok = [x for x in rs_ if x is not None]
        rslack.append(min(r_ok) if r_ok else None)
    bt = np.nonzero(anyv)[0]
    res.update(d_violations=viol, d_left=lslack, d_right=rslack, d_distinct=int(anyv.sum()), d_per_wp=per_wp,
               d_vmax=vmax, d_tmin=tmin, d_t0=float(bt[0] / 400) if len(bt) else None,
               d_t1=float(bt[-1] / 400) if len(bt) else None)
    return res


def stat(v):
    a = np.array([x for x in v if x is not None and not (isinstance(x, float) and np.isnan(x))], float)
    return (a.min(), np.median(a), a.max()) if len(a) else (np.nan,) * 3


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--workers", type=int, default=max(1, MC.physical_cores() - 1))
    args = ap.parse_args()
    spec = M.load_spec()
    files = [str((SIM / p).resolve()) for p in spec["params"]]
    cmd = [str(MC.BINS["ref"]), "--exact"] + sum([["--params", f] for f in files], [])
    tasks = []
    for set_name, d in [("uniform", SIM / "out" / "montecarlo"), ("worst-case", SIM / "out" / "montecarlo-worst-case")]:
        sj = json.loads((d / "samples.json").read_text())
        for i, (s, h) in enumerate(zip(sj["samples_ned_m"], sj["headings_rad"])):
            tasks.append({"spec": spec, "set": set_name, "index": i, "init": s, "heading": h, "cmd": cmd,
                          "run": str(d / "runs" / f"ref-{i:03d}.csv.gz")})
    t0 = time.perf_counter()
    with get_context("spawn").Pool(args.workers, initializer=MC._worker_init, initargs=(1200,)) as pool:
        res = list(pool.imap(check, tasks, chunksize=1))
    wall = time.perf_counter() - t0
    bad = [r for r in res if not (r["same_as_recorded"] and r["replay_same"])]
    if bad:
        raise SystemExit(f"{len(bad)} re-flights or replays differ from the recorded runs: "
                         + ", ".join(f"{r['set']} {r['index']}" for r in bad[:10]))
    with open(OUT / "constants.csv", "w", newline="") as f:
        wr = csv.writer(f)
        keys = ["set", "index", "init", "heading", "ticks", "a_max_err", "a_tick", "b_max_err", "b_ticks", "b2_max_err",
                "b2_ticks", "c_max", "c_tick", "d_violations", "d_left", "d_right", "e_max"]
        wr.writerow(keys)
        for r in res:
            wr.writerow([r[k] if k not in ("init", "d_left", "d_right") else " ".join(map(str, r[k])) for k in keys])

    def worst(key, sign=1):
        rr = [r for r in res if not np.isnan(r[key])]
        r = max(rr, key=lambda r: sign * r[key])
        return r
    def where(r):
        return (f"{r['set']} start {r['index']} at NED ({', '.join(f'{x:.3f}' for x in r['init'])}), "
                f"heading {math.degrees(r['heading']):.1f} deg")
    L = []
    w = L.append
    w("# The sub-contract constants on every Monte Carlo start")
    w("")
    w("A read-only check of the constants of `contracts/Contracts/Mission/Sub.lean` (tuned on the nominal "
      "flight `sim/out/lean-course-1ms`) against the 200 uniform starts of `sim/out/montecarlo` and the "
      f"{sum(1 for t in tasks if t['set'] == 'worst-case')} worst-case starts of `sim/out/montecarlo-worst-case` (box north and east [-0.15, 0.15] m, down [-0.3, 0] m, any heading), "
      "one vehicle per start since the two are identical on every tick. Each start was flown again with "
      "`copter_ref` (the loop of `sim/montecarlo.py`, recording the state lines); the flown positions and actuator "
      f"bit patterns equal the recorded runs on every tick for all {len(res)} starts, and the state lines replayed "
      "through `copter_ref --exact --trace` give the flown actuators again; the first three trace numbers are "
      f"the position target after each tick. Ticks 0..{spec['horizon_ticks']} of each run. Script: "
      f"`sim/check_constants.py` ({wall:.0f} s with {args.workers} workers); per start: `constants.csv`.")
    w("")
    w("Definitions as in `Loop.lean` and `Spec.lean`: err = |pos(t) - target(t)| with the target after tick t; "
      "the sampled error uses the position of tick t's state line; polyDist is the distance to the polyline "
      "through `pathPt` (the takeoff point, then w0..w7, so the climb segment is part of it); `inColumn` is "
      "|n|, |e| <= 0.151 m and -0.8 <= d <= 0.001 m (the prism over the box up to w0).")
    w("")
    w(f"| quantity | constant | min | median | max over runs | holds |")
    w("|---|---|---|---|---|---|")
    def row(name, key, const, fmt=lambda x: f"{x * 100:.2f} cm", le=True):
        a = stat([r[key] for r in res])
        ok = a[2] <= const if le else a[0] >= const
        w(f"| {name} | {fmt(const)} | {fmt(a[0])} | {fmt(a[1])} | {fmt(a[2])} | {'yes' if ok else 'no'} |")
        return ok
    ok_a = row("(a) max tracking error err", "a_max_err", DELTA)
    nb = sum(1 for r in res if r["b_ticks"])
    ok_b = row(f"(b) max err while the target is in `inColumn` and polyDist > ρ ({nb} of {len(res)} runs have such ticks)",
               "b_max_err", DELTA0)
    nb2 = sum(1 for r in res if r["b2_ticks"])
    row(f"(b') as (b), with the distance to the polyline w0..w7 only, without the climb segment ({nb2} of {len(res)} runs)",
        "b2_max_err", DELTA0)
    ok_c = row("(c) max target distance to polyline-or-prism (0 inside `inColumn`, else polyDist)", "c_max", RHO)
    nv = sum(r["d_violations"] for r in res)
    w(f"| (d) ticks with the target within rPass = 0.105 m of a waypoint and the vehicle not within r = 0.1 m | 0 | "
      f"{min(r['d_violations'] for r in res)} | {int(np.median([r['d_violations'] for r in res]))} | "
      f"{max(r['d_violations'] for r in res)} (total {nv}) | {'yes' if nv == 0 else 'no'} |")
    ok_e = row("(e) max sampled error \\|sampled position - target\\|", "e_max", DELTAS)
    w("")
    w("(d), slack in ticks on each side of each window in which the target is within rPass of a waypoint: before "
      "it, the ticks the vehicle was already within r; after it, the ticks it stays within r (a window that "
      "runs to the end of the trace together with the vehicle's is not counted on the right). Minimum over runs:")
    w("")
    w("| waypoint | " + " | ".join(f"w{j}" for j in range(8)) + " |")
    w("|---|" + "---|" * 8)
    for side, key in [("before", "d_left"), ("after", "d_right")]:
        vals = []
        for j in range(8):
            v = [r[key][j] for r in res if r[key][j] is not None]
            vals.append(str(min(v)) if v else "none")
        w(f"| {side} | " + " | ".join(vals) + " |")
    w("")
    ra = worst("a_max_err"); w(f"- δ = 0.095 m (tracking error): {'holds' if ok_a else 'VIOLATED'}; worst "
                               f"{ra['a_max_err'] * 100:.2f} cm at t = {ra['a_tick'] / 400:.4f} s, {where(ra)}.")
    if nb:
        rb = worst("b_max_err")
        w(f"- δ₀ = 0.035 m (climb out of the box): {'holds' if ok_b else 'VIOLATED'}; worst {rb['b_max_err'] * 100:.2f} cm, "
          f"{where(rb)} ({rb['b_ticks']} ticks in the condition in that run).")
    else:
        w("- δ₀ = 0.035 m (climb out of the box): holds vacuously; no run has a tick with the target in `inColumn` "
          "and more than ρ from the polyline.")
    rc_ = worst("c_max"); w(f"- ρ = 0.155 m (target near the polyline or in the prism): {'holds' if ok_c else 'VIOLATED'}; "
                            f"worst {rc_['c_max'] * 100:.2f} cm at t = {rc_['c_tick'] / 400:.4f} s, {where(rc_)}.")
    if nv:
        vr = [r for r in res if r["d_violations"]]
        rd = max(res, key=lambda r: r["d_distinct"])
        per = [sum(r["d_per_wp"][k] for r in res) for k in range(8)]
        vm = max(x for r in vr for x in r["d_vmax"] if x is not None)
        tm = min(x for r in vr for x in r["d_tmin"] if x is not None)
        alts = [-r["init"][2] for r in vr]
        w(f"- rPass = 0.105 m (transfer near the waypoints): VIOLATED in {len(vr)} of {len(res)} runs "
          f"({sum(1 for r in vr if r['set'] == 'uniform')} uniform, {sum(1 for r in vr if r['set'] == 'worst-case')} worst-case), "
          f"{sum(r['d_distinct'] for r in res)} distinct ticks ({nv} counted per waypoint; by waypoint "
          + ", ".join(f"w{k} {per[k]}" for k in range(8)) + "; w0 and w7 are the same point, so each tick counts for both). "
          + (f"All of them are at w0 (= w7) as the vehicle leaves it toward w1, t = " if all(per[k] == 0 for k in range(1, 7))
           else "NOT all at w0: violating ticks span t = ") + f"{min(r['d_t0'] for r in vr):.4f} to "
          f"{max(r['d_t1'] for r in vr):.4f} s: the vehicle leaves the 0.1 m ball (up to {vm * 100:.2f} cm from w0) "
          f"while the target is still within 0.105 m of it (at least {tm * 100:.2f} cm from w0). Entry into each "
          f"window is fine (slack at least the 'before' row); the failing side is the exit at w0. Most: {where(rd)}, "
          f"{rd['d_distinct']} ticks. The affected starts are in the air at {min(alts):.3f} to {max(alts):.3f} m; "
          f"no start below {min(alts):.3f} m and no ground start is affected. At w0 the property would hold on "
          f"every run with a target radius below {tm * 100:.2f} cm (the target passes through w0 itself on the "
          f"climb, so w0 does not need the corner allowance that sets rPass above 0.1006 m for w1..w6); at "
          f"w1..w6 it holds with rPass = 0.105 m.")
    else:
        mins = [min(x for r in res for x in r[k] if x is not None) for k in ("d_left", "d_right")]
        w(f"- rPass = 0.105 m (transfer near the waypoints): holds; 0 violating ticks; smallest slack "
          f"{mins[0]} ticks before and {mins[1]} ticks after a window.")
    re_ = worst("e_max"); w(f"- δs = 0.096 m (sampled error): {'holds' if ok_e else 'VIOLATED'}; worst "
                            f"{re_['e_max'] * 100:.2f} cm, {where(re_)}; the sampled position is the simulator's "
                            f"position (the state line carries its shortest round-trip decimal), so the sampled "
                            f"error equals err on {sum(r['e_equal_a'] for r in res)} of {len(res)} runs.")
    (OUT / "CONSTANTS.md").write_text("\n".join(L) + "\n")
    print("\n".join(L))


if __name__ == "__main__":
    main()
