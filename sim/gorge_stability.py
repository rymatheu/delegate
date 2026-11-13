#!/usr/bin/env python3
"""Stability numbers of gorge flights of sim/gorge_lockstep.py (the speed ladder, sim/README.md "Gorge flight").

    build/reference/venv/bin/python sim/gorge_stability.py RUN_DIR... [--markdown]

Per run, from flight.json, track.csv (100 Hz), outputs.txt (400 Hz PWM) and log.txt:
- the parameter overrides sent (flight.json params_set);
- top speed (ground and 3D, in the air), the gorge segment: from the first spline item's MISSION_ITEM_REACHED (seq 2) to the
  last one's (seq 11), its time, the flown distance and the mean speed;
- least clearance in the air, distance to the planned route (max), tilt max (as gorge_lockstep.gorge_metrics);
- saturated ticks: 400 Hz output lines between liftoff and touchdown with any of motors 1..4 at PWM <= 1001 or >= 1999;
- vehicle texts of severity 0..4 (emergency .. warning: failsafes, "Potential Thrust Loss", EKF warnings) between the arm
  and the disarm;
- heading ringing: over 1 s windows in the air, the std of the heading after removing a quadratic fit (the turn itself),
  worst window (the X500's yaw limit cycle with the frame file's yaw gains, gorge-port-x500/try1, gives 5.1 deg; the 2 m/s
  record flight 1.4 deg); attitude chatter: over 1 s windows, the std of the tilt minus its 0.1 s moving average (content
  above about 10 Hz, where the rate-loop limit cycles were), worst window (bank reversals in the bends are slower and
  are not counted);
- altitude error in the gorge segment: vehicle up minus the up coordinate of the nearest point of the planned route
  (takeoff column and chords between the spline waypoints), largest magnitude.
Verdict: pass when the mission completed (10 of 10 splines, land, disarm), no contact in the air, least clearance >= 1.0 m,
saturated ticks <= 10, no text of severity <= 4, altitude error <= 0.5 m, heading ringing <= 3 deg, attitude chatter <= 0.5 deg.
"""
import json
import math
import re
import sys
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SIM_DIR))


def detrended_max(t, x, win=1.0):
    worst = 0.0
    for a in np.arange(t[0], t[-1] - win, win):
        s = (t >= a) & (t < a + win)
        if s.sum() < 10:
            continue
        r = x[s] - np.polyval(np.polyfit(t[s] - a, x[s], 2), t[s] - a)
        worst = max(worst, float(r.std()))
    return worst


def hf_max(t, x, win=1.0, avg_s=0.1):
    n = max(1, int(round(avg_s / (t[1] - t[0]))))
    hf = x - np.convolve(x, np.ones(n) / n, mode="same")
    worst = 0.0
    for a in np.arange(t[0] + avg_s, t[-1] - win - avg_s, win):
        s = (t >= a) & (t < a + win)
        if s.sum() >= 10:
            worst = max(worst, float(hf[s].std()))
    return worst


def nearest_on_route(q, route):
    best_d, best_p = np.full(len(q), np.inf), np.zeros_like(q)
    for p0, p1 in zip(route[:-1], route[1:]):
        v = p1 - p0
        s = np.clip((q - p0) @ v / (v @ v), 0, 1)
        p = p0 + s[:, None] * v
        d = np.linalg.norm(q - p, axis=1)
        m = d < best_d
        best_d[m], best_p[m] = d[m], p[m]
    return best_p


_PATHS = {}


def route_enu(f):
    """The planned route in ENU (gorge_lockstep.gorge_metrics'): the takeoff column from the settled start, then the
    gorge's path (leanfc's Gorge.path: the takeoff point and the 10 spline waypoints)."""
    seed = f["gorge_seed"]
    if seed not in _PATHS:
        import gorge_lockstep as GL
        G = GL.import_leanfc()[0]
        _PATHS[seed] = G.Gorge(seed).path
    gp = _PATHS[seed]
    return np.vstack([[gp[0, 0], gp[0, 1], f["home_z"]], gp])


def analyze(run):
    run = Path(run)
    f = json.loads((run / "flight.json").read_text())
    met, rec = f["metrics"], f["record"]
    d = np.genfromtxt(run / "track.csv", delimiter=",", names=True)
    t = d["t"]
    pos = np.column_stack([d["x"], d["y"], d["z"]])
    reached = {s: tt for tt, s in rec["reached"]}
    out = dict(run=run.name, params=f.get("params_set", {}), completed=met.get("completed"), reached=met.get("reached"),
               top_speed=met.get("ground_speed_max_ms"), top_speed_3d=met.get("speed_3d_max_ms"),
               clearance=met.get("clearance_min_in_air_m"), route_max=met.get("route_distance_in_air_max_m"),
               tilt_max=met.get("tilt_max_in_air_deg"), contacts=met.get("contacts_between_liftoff_and_touchdown"),
               arm_to_disarm=met.get("arm_to_disarm_s"))
    if 2 in reached and 11 in reached:
        s = (t >= reached[2]) & (t <= reached[11])
        dist = float(np.linalg.norm(np.diff(pos[s], axis=0), axis=1).sum())
        out.update(seg_time=reached[11] - reached[2], seg_dist=dist, seg_speed=dist / (reached[11] - reached[2]))
        near = nearest_on_route(pos[s], route_enu(f))
        out["alt_err_max"] = float(np.abs(pos[s, 2] - near[:, 2]).max())
    # saturated ticks between liftoff and touchdown (400 Hz lines k: t = (k + 1) * 0.0025)
    lo, hi = met.get("liftoff_t"), met.get("touchdown_t") or t[-1]
    sat = 0
    with open(run / "outputs.txt") as fh:
        for k, line in enumerate(fh):
            tk = (k + 1) * 0.0025
            if tk < lo or tk > hi:
                continue
            pwm = re.search(r"pwm=([0-9,]+)", line).group(1).split(",")[:4]
            if any(int(v) <= 1001 or int(v) >= 1999 for v in pwm):
                sat += 1
    out["saturated_ticks"] = sat
    texts = []
    for line in (run / "log.txt").read_text().splitlines():
        m = re.match(r"\s*([0-9.]+)\s+text\[([0-9])\] (.*)", line)
        if m and int(m.group(2)) <= 4 and rec.get("t_arm") and rec["t_arm"] - 1 <= float(m.group(1)) <= (rec.get("t_disarm") or 1e9):
            texts.append(f"{float(m.group(1)):.2f} {m.group(3)}")
    out["warn_texts"] = texts
    air = (t >= met["air_window_s"][0]) & (t < met["air_window_s"][1]) if "air_window_s" in met else np.zeros(len(t), bool)
    if air.any():
        q = np.column_stack([d["qx"], d["qy"], d["qz"], d["qw"]])[air]
        hd = np.degrees(np.unwrap(np.arctan2(2 * (q[:, 3] * q[:, 2] + q[:, 0] * q[:, 1]), 1 - 2 * (q[:, 1] ** 2 + q[:, 2] ** 2))))
        tilt = np.degrees(np.arccos(np.clip(1 - 2 * (q[:, 0] ** 2 + q[:, 1] ** 2), -1, 1)))
        out["heading_ring"] = detrended_max(t[air], hd)
        out["tilt_ring"] = hf_max(t[air], tilt)
    reasons = []
    if not out["completed"]:
        reasons.append("mission not completed")
    if out["contacts"]:
        reasons.append(f"{out['contacts']} contacts")
    if out["clearance"] is None or out["clearance"] < 1.0:
        reasons.append("clearance < 1.0 m")
    if sat > 10:
        reasons.append(f"{sat} saturated ticks")
    if texts:
        reasons.append("vehicle warnings: " + "; ".join(sorted(set(x.split(" ", 1)[1] for x in texts))))
    if out.get("alt_err_max", 0) > 0.5:
        reasons.append(f"altitude error {out['alt_err_max']:.2f} m")
    if out.get("heading_ring", 0) > 3.0:
        reasons.append(f"heading ringing {out['heading_ring']:.1f} deg")
    if out.get("tilt_ring", 0) > 0.5:
        reasons.append(f"attitude chatter {out['tilt_ring']:.2f} deg")
    out["verdict"] = "pass" if not reasons else "fail: " + ", ".join(reasons)
    return out


def main():
    runs = [a for a in sys.argv[1:] if not a.startswith("--")]
    rows = [analyze(r) for r in runs]
    if "--markdown" in sys.argv:
        print("| run | overrides | top speed | gorge segment: time / mean speed | clearance | route max | alt err max | tilt max "
              "| heading ringing / attitude chatter | saturated ticks | verdict |")
        print("|---|---|---|---|---|---|---|---|---|---|---|")
    for o in rows:
        ov = " ".join(f"{k} {v:g}" for k, v in o["params"].items()) or "-"
        seg = f"{o.get('seg_time', float('nan')):.2f} s / {o.get('seg_speed', float('nan')):.2f} m/s"
        cells = [o["run"], ov, f"{o['top_speed']:.2f} m/s", seg, f"{o['clearance']:.2f} m", f"{o['route_max']:.2f} m",
                 f"{o.get('alt_err_max', float('nan')):.2f} m", f"{o['tilt_max']:.1f} deg",
                 f"{o.get('heading_ring', float('nan')):.2f} / {o.get('tilt_ring', float('nan')):.2f} deg", str(o["saturated_ticks"]),
                 o["verdict"]]
        print(("| " + " | ".join(cells) + " |") if "--markdown" in sys.argv else "  ".join(cells))


if __name__ == "__main__":
    main()
