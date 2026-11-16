#!/usr/bin/env python3
"""Stability numbers of gorge flights of sim/gorge_lockstep.py (the speed ladder, sim/README.md "Gorge flight").

    build/reference/venv/bin/python sim/gorge_stability.py RUN_DIR... [--markdown] [--smooth]

Per run, from flight.json, track.csv (100 Hz), outputs.txt (400 Hz PWM) and log.txt:
- the parameter overrides sent (flight.json params_set);
- top speed (ground and 3D, in the air), the gorge segment: from the first spline item's MISSION_ITEM_REACHED (seq 2) to the
  last one's (seq 11; seq n + 1 for a mission of n spline items, flight.json n_spline), its time, the flown distance and
  the mean speed;
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

Smoothness (--smooth: a second table; sim/README.md "The smooth flight"), from track.csv over the gorge segment G (the rows
whose MISSION_CURRENT is one of the spline items 2..11 (2..n + 1), in AUTO: from the takeoff point at rest to the arrival at the last
spline waypoint) and over its cruise part C (G without the initial acceleration from rest and the final deceleration: from
the first to the last row of G with ground speed >= 0.95 x the commanded WP_SPD, i.e. flight.json's params_set or the image's
sim/params/reference-x500.txt; if the vehicle never reaches it, 0.95 x the largest ground speed of G):
- ground speed min / mean / max and the band (max - min) / mean;
- horizontal acceleration and jerk: the NE velocity differentiated after a 0.1 s centered moving average, the acceleration
  smoothed the same way before differentiating again; rms and max of their magnitudes; the acceleration split into the
  along-track part (d|v|/dt, speeding up and braking) and the cross-track part (cornering), rms of each;
- body rates (roll p, pitch q, yaw r: 2 q^-1 dq/dt of the recorded attitude, 0.1 s moving average), rms and max, deg/s;
- pitch (ZYX Euler, nose down positive here = accelerating forward) min / max / rms and the number of sign reversals with a
  3 deg hysteresis (a reversal counts when the pitch goes from below -3 deg to above +3 deg or back): the accelerate /
  brake pattern; a flight at constant speed has about one at the start and one at the stop of G.
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


def movavg(x, n):
    """Centered moving average over n samples (edges: the shorter windows inside the record)."""
    if n <= 1:
        return np.asarray(x, float)
    k = np.ones(n)
    num = np.convolve(x, k, mode="same")
    den = np.convolve(np.ones(len(x)), k, mode="same")
    return num / den


def body_rates(t, q):
    """Body angular velocity (rad/s, the vehicle's x forward, y left, z up of PyBullet) from quaternions (x, y, z, w):
    omega = 2 conj(q) dq/dt, dq/dt by central differences."""
    x, y, z, w = (q[:, i] for i in range(4))
    dx, dy, dz, dw = (np.gradient(q[:, i], t) for i in range(4))
    p = 2 * (w * dx - x * dw - y * dz + z * dy)
    qq = 2 * (w * dy + x * dz - y * dw - z * dx)
    r = 2 * (w * dz - x * dy + y * dx - z * dw)
    return np.column_stack([p, qq, r])


def euler_pitch_roll(q):
    """ZYX Euler roll and pitch (deg) of PyBullet quaternions (x, y, z, w); pitch positive nose down (forward
    acceleration), roll positive right side down."""
    x, y, z, w = (q[:, i] for i in range(4))
    roll = np.degrees(np.arctan2(2 * (w * x + y * z), 1 - 2 * (x * x + y * y)))
    pitch = np.degrees(np.arcsin(np.clip(2 * (w * y - z * x), -1, 1)))
    return roll, pitch


def sign_reversals(x, h=3.0):
    state, n = 0, 0
    for v in x:
        s = 1 if v > h else (-1 if v < -h else 0)
        if s and state and s != state:
            n += 1
        if s:
            state = s
    return n


def commanded_speed(f):
    if "WP_SPD" in f.get("params_set", {}):
        return float(f["params_set"]["WP_SPD"])
    for line in (SIM_DIR / "params" / "reference-x500.txt").read_text().splitlines():
        w = line.split("#")[0].split()
        if len(w) == 2 and w[0] == "WP_SPD":
            return float(w[1])
    return 10.0


def smoothness(d, f):
    """The smoothness numbers of the gorge segment and its cruise part (module docstring)."""
    t = d["t"]
    dt = float(np.median(np.diff(t)))
    n = max(1, int(round(0.1 / dt)))
    vne = np.column_stack([d["vn"], d["ve"]])
    vs = np.column_stack([movavg(vne[:, 0], n), movavg(vne[:, 1], n)])
    acc = np.column_stack([np.gradient(vs[:, 0], t), np.gradient(vs[:, 1], t)])
    accs = np.column_stack([movavg(acc[:, 0], n), movavg(acc[:, 1], n)])
    jerk = np.column_stack([np.gradient(accs[:, 0], t), np.gradient(accs[:, 1], t)])
    gs = np.hypot(vne[:, 0], vne[:, 1])
    spd = np.hypot(vs[:, 0], vs[:, 1])
    u = vs / np.maximum(spd, 1e-6)[:, None]
    a_along = (acc * u).sum(axis=1)
    a_cross = acc[:, 0] * u[:, 1] - acc[:, 1] * u[:, 0]
    q = np.column_stack([d["qx"], d["qy"], d["qz"], d["qw"]])
    q = q * np.where((q[:, 3] < 0), -1.0, 1.0)[:, None]
    w = body_rates(t, q)
    w = np.degrees(np.column_stack([movavg(w[:, i], n) for i in range(3)]))
    roll, pitch = euler_pitch_roll(q)
    item = d["item"].astype(int)
    G = (item >= 2) & (item <= f.get("n_spline", 10) + 1) & (d["mode"].astype(int) == 3)
    if not G.any():
        return None
    vcmd = commanded_speed(f)
    thr = 0.95 * vcmd
    if gs[G].max() < thr:
        thr = 0.95 * gs[G].max()
    idx = np.nonzero(G & (gs >= thr))[0]
    C = np.zeros(len(t), bool)
    C[idx[0]:idx[-1] + 1] = True
    C &= G

    def block(S):
        v = gs[S]
        am, jm = np.hypot(*acc[S].T), np.hypot(*jerk[S].T)
        rms = lambda x: float(np.sqrt(np.mean(np.square(x))))
        return dict(t0=float(t[S][0]), t1=float(t[S][-1]), v_min=float(v.min()), v_mean=float(v.mean()), v_max=float(v.max()),
                    band=float((v.max() - v.min()) / v.mean()), acc_rms=rms(am), acc_max=float(am.max()),
                    acc_along_rms=rms(a_along[S]), acc_cross_rms=rms(a_cross[S]), jerk_rms=rms(jm), jerk_max=float(jm.max()),
                    rate_rms=[rms(w[S, i]) for i in range(3)], rate_max=[float(np.abs(w[S, i]).max()) for i in range(3)],
                    pitch=[float(pitch[S].min()), float(pitch[S].max())], roll=[float(roll[S].min()), float(roll[S].max())],
                    pitch_rms=rms(pitch[S]), pitch_reversals=sign_reversals(pitch[S]))

    return dict(vcmd=vcmd, cruise_threshold=thr, segment=block(G), cruise=block(C))


_PATHS = {}


def route_enu(f):
    """The planned route in ENU (gorge_lockstep.gorge_metrics'): the takeoff column from the settled start, then the
    flight's path (flight.json "path"; older flights: leanfc's Gorge.path, the takeoff point and the 10 spline waypoints)."""
    if f.get("path"):
        gp = np.array(f["path"])
        return np.vstack([[gp[0, 0], gp[0, 1], f["home_z"]], gp])
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
    last = f.get("n_spline", 10) + 1
    if 2 in reached and last in reached:
        s = (t >= reached[2]) & (t <= reached[last])
        dist = float(np.linalg.norm(np.diff(pos[s], axis=0), axis=1).sum())
        out.update(seg_time=reached[last] - reached[2], seg_dist=dist, seg_speed=dist / (reached[last] - reached[2]))
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
    out["smooth"] = smoothness(d, f)
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
    if "--smooth" in sys.argv:
        print()
        print("| run | part | window | speed min / mean / max (band) | acc rms / max (along / cross rms) | jerk rms / max "
              "| roll rate rms / max | pitch rate rms / max | yaw rate rms / max | pitch min / max / rms (reversals) |")
        print("|---|---|---|---|---|---|---|---|---|---|")
        for o in rows:
            sm = o.get("smooth")
            if not sm:
                continue
            for part in ("segment", "cruise"):
                b = sm[part]
                cells = [o["run"], part, f"{b['t0']:.2f}..{b['t1']:.2f} s",
                         f"{b['v_min']:.2f} / {b['v_mean']:.2f} / {b['v_max']:.2f} m/s ({100 * b['band']:.0f} %)",
                         f"{b['acc_rms']:.2f} / {b['acc_max']:.2f} ({b['acc_along_rms']:.2f} / {b['acc_cross_rms']:.2f}) m/s^2",
                         f"{b['jerk_rms']:.2f} / {b['jerk_max']:.1f} m/s^3"]
                cells += [f"{b['rate_rms'][i]:.1f} / {b['rate_max'][i]:.0f} deg/s" for i in range(3)]
                cells.append(f"{b['pitch'][0]:.1f} / {b['pitch'][1]:.1f} / {b['pitch_rms']:.1f} deg ({b['pitch_reversals']})")
                print(("| " + " | ".join(cells) + " |") if "--markdown" in sys.argv else "  ".join(cells))


if __name__ == "__main__":
    main()
