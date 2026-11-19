#!/usr/bin/env python3
r"""Monitor of the mission contract of the 1 m/s figure-eight course (sim/spec/mission-course.json).

The contract is an assume-guarantee pair over the closed loop (copter_lean or copter_ref in lock step
with the CF2X in gym-pybullet-drones, the course of params/copter-cf2x.txt at 1 m/s with the tuned
gains). The assumption A is on the state at tick 0: level, any heading (a rotation about the down
axis), at rest (the actuators held before tick 0 are the hover actuators), the position in the takeoff box B = [-0.15, 0.15] x [-0.15, 0.15] x
[-0.3, 0] (NED, m). The guarantee is the STL formula psi below,
evaluated on the vehicle's position x_k at the 400 Hz control ticks k = 0, 1, ..., K; every interval
is in ticks.

Atomic predicates (pos = x_k, NED; altitude = -x_k[2]):

    ceil       :=  -x_k[2] <= c                              (c = 2.0 m)
    inS        :=  dist(x_k, S) = 0,  S = B  U  { x : dist(x, path) <= rho }   (rho = 0.25 m)
    near_i     :=  |x_k - w_i| <= r                          (r = 0.1 m, Euclidean)

where path is the polyline through the spec's path vertices: the takeoff point (the origin, on the
ground) and then the mission waypoints w_0, ..., w_7 in order (w_0 is 0.8 m straight above the
takeoff point, so the first segment is the vertical climb).

    psi  :=  G_[0,K] (ceil /\ inS)                                                       (safety)
         /\  F_[0,T_0] (near_0 /\ F_[0,T_1] (near_1 /\ ... /\ F_[0,T_7] near_7) ... )   (ordered reach)
         /\  F_[0,T] G_[0,H] near_7                                                     (reach and hold)

with T_i the leg allowances of the spec (ticks), T = T_0 + ... + T_7, H the hold time (ticks), and
K = T + H the horizon of psi. The semantics is STL's qualitative semantics over the discrete ticks of
a finite trace x_0 .. x_{n-1}: (x, k) |= F_[a,b] phi iff some j in [k+a, k+b] with j < n has
(x, j) |= phi; (x, k) |= G_[a,b] phi iff every j in [k+a, k+b] has j < n and (x, j) |= phi. A trace
shorter than K + 1 ticks therefore fails G_[0,K] (its unobserved ticks count as violations), and an
F whose window reaches past the end of the trace can only be met by the ticks that exist. The
ordered reach is evaluated exactly, backwards over the ticks: sat_8 = true, and
sat_i(k) = exists j in [k, k + T_i] with near_i(j) and sat_{i+1}(j); its verdict is sat_0(0).

Margins (reported whether or not psi holds):
- ceiling clearance: c - max_k altitude;
- max distance to S over 0..K (0 iff inS holds throughout);
- corridor distance after leaving the box: max distance to the path over the ticks from the first
  tick outside B on (the corridor margin is rho minus it); and the plain max distance to the path
  over all ticks, which includes the start offset inside the box;
- leg times: the first-reach chain k_0 = first tick with near_0, k_i = first tick >= k_{i-1} with
  near_i; leg i takes k_i - k_{i-1} ticks (k_{-1} = 0) and its slack is T_i minus that. When every
  slack is >= 0 the chain is a witness of the ordered reach; the verdict itself is sat_0(0);
- hold: the time the hold is first achieved, the earliest window start j <= T with near_7 on all of
  [j, j + H]; and the hold margin, the robustness of F_[0,T] G_[0,H] near_7: r minus the max
  distance to w_7 over the best window (the start j <= T whose window has the smallest max distance,
  also reported). The earliest window begins where the vehicle crosses into the r-ball, so its own
  max distance is about r; the best window measures how well the hold is kept. The margin is >= 0 iff
  the conjunct holds. Since w_7 = w_0, the conjunct does not order the hold after w_6 by itself; the
  ordered reach does.

Usage:
    sim/.venv/bin/python sim/monitor.py --derive-spec      # write sim/spec/mission-course.json
    sim/.venv/bin/python sim/monitor.py RUN_DIR...         # evaluate recorded flights (flight.csv or *.csv.gz)
"""
from __future__ import annotations

import argparse
import csv
import gzip
import json
import math
import re
from fractions import Fraction
from pathlib import Path

import numpy as np

SIM = Path(__file__).resolve().parent
SPEC_PATH = SIM / "spec" / "mission-course.json"
NOMINAL = SIM / "out" / "lean-course-1ms"
PARAMS = ["params/copter-cf2x.txt", "params/copter-course-speed.txt", "params/copter-cf2x-tuned.txt"]
TICK_HZ = 400
# The takeoff box of the assumption: north and east in [-BOX_HALF, BOX_HALF], down in [-BOX_HEIGHT, 0] (m).
# Half-width 0.15 m: its corners are 0.212 m from the vertical climb axis, inside the 0.25 m corridor
# (the earlier 0.2 m box had corners at 0.283 m, outside it, and starts near its top corners left S).
BOX_HALF = 0.15
BOX_HEIGHT = 0.3


# --------------------------------------------------------------------------------------------
# The spec


def derive_spec(nominal: Path = NOMINAL) -> dict:
    """The spec of the course contract: the leg allowances from the nominal flight's "first within
    0.1 m" times (summary.txt), allowance_i = ceil(1.25 * leg_i + 0.5 s) in whole seconds, computed
    on the decimals as printed (exact rational arithmetic), and the fixed numbers of the contract."""
    s = (nominal / "summary.txt").read_text()
    rows = re.findall(r"^waypoint (\d+) \(([^)]*)\): .*?first within ([\d.]+) m at ([\d.]+) s", s, re.M)
    wps = [[float(v) for v in m[1].split(",")] for m in rows]
    if [int(m[0]) for m in rows] != list(range(len(rows))) or any(m[2] != "0.1" for m in rows):
        raise SystemExit(f"{nominal}/summary.txt: expected every waypoint reached within 0.1 m")
    first = [Fraction(m[3]) for m in rows]
    legs = [first[0]] + [b - a for a, b in zip(first, first[1:])]
    allow = [math.ceil(Fraction(5, 4) * L + Fraction(1, 2)) for L in legs]
    total = sum(allow)
    hold = 3
    box = {"north": [-BOX_HALF, BOX_HALF], "east": [-BOX_HALF, BOX_HALF], "down": [-BOX_HEIGHT, 0.0]}
    return {
        "mission": "figure-eight course of params/copter-cf2x.txt at WP_SPD 1 m/s with the tuned gains",
        "params": PARAMS,
        "tick_hz": TICK_HZ,
        "assumption": {
            "box_ned_m": box,
            "attitude": "level: roll 0, pitch 0",
            "heading": "uniform, any: yaw in [-pi, pi); the attitude quaternion is a rotation about the down axis",
            "rates": "at rest: zero velocity, zero body rates",
            "held_actuators": "the actuators held at tick 0 are the hover actuators (MOT_THST_HOVER, "
                              "run.start_hover 1); an in-air start's tick-0 specific force is (0, 0, -g), "
                              "the sample of a vehicle at rest (run_copter.py --init-accel hover)",
        },
        "r_m": 0.1,
        "ceiling_m": 2.0,
        "corridor_radius_m": 0.25,
        "box_ned_m": box,
        "waypoints_ned_m": wps,
        "path_ned_m": [[0.0, 0.0, 0.0]] + wps,
        "path_note": "the takeoff point (origin, on the ground), then w0..w7 in order",
        "nominal": {"run": "sim/out/" + nominal.name, "first_within_s": [float(f) for f in first],
                    "leg_s": [float(L) for L in legs]},
        "allowance_rule": "allowance_i = ceil(1.25 * leg_i + 0.5) s, leg_i from the nominal first-within times (leg_0 from t = 0)",
        "allowances_s": allow,
        "allowances_ticks": [a * TICK_HZ for a in allow],
        "total_s": total,
        "total_ticks": total * TICK_HZ,
        "hold_s": hold,
        "hold_ticks": hold * TICK_HZ,
        "horizon_ticks": (total + hold) * TICK_HZ,
        "sensing": {
            "note": "not part of the assumption: bounded sensing-noise levels for the Monte Carlo runs "
                    "(sim/montecarlo.py --noise LEVEL, out/montecarlo-noise-<level>/)",
            "model": "every tick, independent errors uniform in [-b, b] per component added to the true state "
                     "in the sample: position bp (m), velocity bv (m/s), specific force bf (m/s^2), body rates "
                     "bw (rad/s); attitude rotated by a body-frame small rotation with angles uniform in "
                     "[-bq, bq] (deg), renormalized",
            "levels": {
                "L1": {"bp": 0.005, "bv": 0.02, "bq": 0.0, "bw": 0.0, "bf": 0.0},
                "L2": {"bp": 0.02, "bv": 0.05, "bq": 0.0, "bw": 0.0, "bf": 0.0},
                "L3": {"bp": 0.02, "bv": 0.05, "bq": 0.5, "bw": 0.01, "bf": 0.0},
                "L4": {"bp": 0.05, "bv": 0.10, "bq": 1.0, "bw": 0.02, "bf": 0.0},
            },
        },
    }


def load_spec(path: Path = SPEC_PATH) -> dict:
    return json.loads(Path(path).read_text())


# --------------------------------------------------------------------------------------------
# Geometry


def dist_to_polyline(pos: np.ndarray, verts: np.ndarray) -> np.ndarray:
    """Euclidean distance of each point (n x 3) to the polyline through verts (m x 3)."""
    best = np.full(len(pos), np.inf)
    for a, b in zip(verts[:-1], verts[1:]):
        ab = b - a
        L2 = float(ab @ ab)
        if L2 == 0.0:
            d = np.linalg.norm(pos - a, axis=1)
        else:
            s = np.clip((pos - a) @ ab / L2, 0.0, 1.0)
            d = np.linalg.norm(pos - (a + s[:, None] * ab), axis=1)
        best = np.minimum(best, d)
    return best


def box_bounds(spec: dict) -> tuple[np.ndarray, np.ndarray]:
    b = spec["box_ned_m"]
    lo = np.array([b["north"][0], b["east"][0], b["down"][0]])
    hi = np.array([b["north"][1], b["east"][1], b["down"][1]])
    return lo, hi


def dist_to_box(pos: np.ndarray, lo: np.ndarray, hi: np.ndarray) -> np.ndarray:
    return np.linalg.norm(np.maximum(0.0, np.maximum(lo - pos, pos - hi)), axis=1)


def next_true(g: np.ndarray) -> np.ndarray:
    """For each k, the smallest j >= k with g[j], or len(g) if there is none."""
    n = len(g)
    idx = np.where(g, np.arange(n), n)
    return np.minimum.accumulate(idx[::-1])[::-1]


# --------------------------------------------------------------------------------------------
# The monitor


def monitor(t, pos, waypoints, spec: dict) -> dict:
    """Verdict of psi on one trace and all margins.

    t: tick times (s), length n, t[k] = k / tick_hz; pos: n x 3 NED positions (m); waypoints: the
    mission's waypoints (checked equal to the spec's). Returns a dict: `verdict` (psi), the conjunct
    verdicts `safety`, `reach`, `hold`, the reason of a failure, and the margins (module docstring)."""
    pos = np.asarray(pos, dtype=float)
    t = np.asarray(t, dtype=float)
    hz = spec["tick_hz"]
    if not np.array_equal(t, np.arange(len(t)) / hz):
        raise ValueError("t must be the tick times k / tick_hz from k = 0")
    W = np.array(spec["waypoints_ned_m"], dtype=float)
    if waypoints is not None and not np.array_equal(np.asarray(waypoints, dtype=float), W):
        raise ValueError("the trace's waypoints differ from the spec's")
    r, c, rho = spec["r_m"], spec["ceiling_m"], spec["corridor_radius_m"]
    T = spec["allowances_ticks"]
    Ttot, H, K = spec["total_ticks"], spec["hold_ticks"], spec["horizon_ticks"]
    n = len(pos)
    m = min(n, K + 1)                       # ticks inside the horizon
    P = pos[:m]
    out: dict = {"ticks": n, "horizon_ticks": K, "complete": n >= K + 1}
    fails = []

    # ---- safety
    alt = -P[:, 2]
    lo, hi = box_bounds(spec)
    in_box = np.all((P >= lo) & (P <= hi), axis=1)
    dpath = dist_to_polyline(P, np.array(spec["path_ned_m"], dtype=float))
    dS = np.where(in_box, 0.0, np.minimum(dist_to_box(P, lo, hi), np.maximum(0.0, dpath - rho)))
    out["max_alt_m"] = float(alt.max())
    out["ceiling_clearance_m"] = float(c - alt.max())
    out["max_dist_S_m"] = float(dS.max())
    out["max_dist_path_m"] = float(dpath.max())
    outside = np.nonzero(~in_box)[0]
    out["box_exit_s"] = float(t[outside[0]]) if len(outside) else math.nan
    out["max_dist_path_after_box_m"] = float(dpath[outside[0]:].max()) if len(outside) else math.nan
    out["corridor_margin_m"] = rho - out["max_dist_path_after_box_m"]
    ok_ceil = bool(np.all(alt <= c))
    ok_S = bool(np.all(dS == 0.0))
    out["safety"] = ok_ceil and ok_S and out["complete"]
    if not ok_ceil:
        k = int(np.argmax(alt > c))
        fails.append(f"ceiling: altitude {alt[k]:.4f} m > {c} m at t = {t[k]:.4f} s")
    if not ok_S:
        k = int(np.argmax(dS > 0))
        fails.append(f"safety region: outside S from t = {t[k]:.4f} s (max distance to S "
                     f"{dS.max() * 100:.2f} cm at t = {t[int(np.argmax(dS))]:.4f} s)")
    if not out["complete"]:
        fails.append(f"trace ends at tick {n - 1} before the horizon K = {K}")

    # ---- ordered reach: exact backward evaluation, then the first-reach chain for the margins
    dW = [np.linalg.norm(P - w, axis=1) for w in W]
    near = [d <= r for d in dW]
    sat = np.ones(m, bool)
    for i in reversed(range(len(W))):
        nt = next_true(near[i] & sat)
        sat = (nt < m) & (nt <= np.arange(m) + T[i])
    out["reach"] = bool(sat[0])
    k_prev, legs, reach_t = 0, [], []
    for i in range(len(W)):
        nx = next_true(near[i][k_prev:])[0] + k_prev if k_prev < m else m
        if nx >= m:
            legs += [math.nan] * (len(W) - i)
            reach_t += [math.nan] * (len(W) - i)
            break
        legs.append(float((nx - k_prev) / hz))
        reach_t.append(float(nx / hz))
        k_prev = nx
    out["reach_s"] = reach_t
    out["leg_s"] = legs
    out["leg_slack_s"] = [float(a / hz - L) for a, L in zip(T, legs)]
    if not out["reach"]:
        bad = [i for i, s in enumerate(out["leg_slack_s"]) if not s >= 0]
        fails.append("ordered reach: " + (f"waypoint {bad[0]} not reached within its allowance "
                                          f"(leg {legs[bad[0]]:.4f} s, allowance {T[bad[0]] / hz:g} s)"
                                          if bad else "no witness"))

    # ---- reach and hold: F_[0,T] G_[0,H] near_7
    d7 = dW[-1]
    jmax = min(Ttot, m - 1 - H)
    if jmax >= 0:
        win = np.lib.stride_tricks.sliding_window_view(d7, H + 1)[:jmax + 1].max(axis=1)
        good = np.nonzero(win <= r)[0]
        jb = int(np.argmin(win))
        out["hold"] = bool(len(good))
        out["hold_first_s"] = float(t[good[0]]) if len(good) else math.nan
        out["hold_start_s"] = float(t[jb])
        out["hold_max_dist_m"] = float(win[jb])
        out["hold_margin_m"] = float(r - win[jb])
    else:
        out.update(hold=False, hold_first_s=math.nan, hold_start_s=math.nan, hold_max_dist_m=math.nan,
                   hold_margin_m=math.nan)
    if not out["hold"]:
        fails.append(f"reach and hold: no {H / hz:g} s window within {r} m of w7 starting by "
                     f"{Ttot / hz:g} s (best window max distance {out['hold_max_dist_m'] * 100:.2f} cm)")

    out["verdict"] = out["safety"] and out["reach"] and out["hold"]
    out["failure"] = "; ".join(fails)
    return out


# --------------------------------------------------------------------------------------------
# Traces on disk


def read_trace(path: Path) -> tuple[np.ndarray, np.ndarray]:
    """t and NED position of a recorded flight: a run directory (flight.csv) or a Monte Carlo trace
    (*.csv or *.csv.gz whose header names t, x_n, y_e, z_d, ...)."""
    path = Path(path)
    if path.is_dir():
        path = path / "flight.csv"
    opener = gzip.open if path.suffix == ".gz" else open
    with opener(path, "rt", newline="") as f:
        rows = csv.reader(f)
        head = next(rows)
        ix = [head.index(c) for c in ("x_n", "y_e", "z_d")]
        it = head.index("t")
        ts, ps = [], []
        for row in rows:
            ts.append(float(row[it]))
            ps.append([float(row[j]) for j in ix])
    n = len(ts)
    t = np.arange(n) / TICK_HZ
    if np.max(np.abs(np.array(ts) - t)) > 1e-9:
        raise ValueError(f"{path}: the times are not the 400 Hz ticks from 0")
    return t, np.array(ps)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--derive-spec", action="store_true", help=f"write {SPEC_PATH.relative_to(SIM.parent)}")
    ap.add_argument("--spec", default=str(SPEC_PATH))
    ap.add_argument("runs", nargs="*")
    a = ap.parse_args()
    if a.derive_spec:
        spec = derive_spec()
        Path(a.spec).parent.mkdir(parents=True, exist_ok=True)
        Path(a.spec).write_text(json.dumps(spec, indent=1) + "\n")
        print(f"{a.spec}: allowances {spec['allowances_s']} s, total {spec['total_s']} s, "
              f"horizon {spec['horizon_ticks']} ticks")
    spec = load_spec(Path(a.spec))
    for run in a.runs:
        t, pos = read_trace(Path(run))
        res = monitor(t, pos, None, spec)
        print(f"{run}: verdict {res['verdict']} (safety {res['safety']}, reach {res['reach']}, "
              f"hold {res['hold']}); {res['failure'] or 'no failure'}")
        for k, v in res.items():
            if k not in ("verdict", "failure"):
                print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
