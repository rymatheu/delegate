#!/usr/bin/env python3
"""Flight metrics of a ground-start run (sim/run_leanfc.py --ground --trace-vehicle), one line per flight.

    /Users/ryan/Research/cpp2lean/sim/.venv/bin/python sim/mavlink/flight_metrics.py OUT_DIR [OUT_DIR ...]
    ... flight_metrics.py --summary DET_DIR FIELD_DIR [FIELD_DIR ...]   (a markdown table: the deterministic
        run, then mean / worst over the field runs, per flight)

Reads OUT_DIR/flight.csv (the harness's CSV with the vehicle columns mode, armed, landed, item) and
OUT_DIR/steps.json (test_services.py's step times, to name the flights). A flight is one armed interval
with a liftoff. All quantities are the simulator's truth (binary64), except the target (the controller's).

  time        armed to disarmed (s)
  overshoot   largest altitude above the takeoff's final target while climbing and in the 5 s after (m)
  track       distance from the vehicle to the controller's target (sp) while flying (landed state
              TAKEOFF or IN_AIR): max and rms (m)
  tilt        largest tilt in the air (deg)
  sat         ticks in the air with a motor at 0 or 1
  vtd         vertical speed at touchdown: the true down velocity on the tick the vehicle first comes
              within 5 mm of its resting altitude during the landing (m/s)
  bounce      largest rise of the altitude after any lower point, from that first contact to the disarm (m;
              0 if the vehicle only settles)
  gtilt       largest tilt between the first contact and the disarm (deg; tipping would show here)
  detect      first contact to the touchdown detector's ON_GROUND (s)
  home        horizontal distance of the touchdown point from where the flight took off (m)
"""
import json
import math
import sys
from pathlib import Path

import numpy as np


def load(path):
    with open(path) as f:
        cols = f.readline().strip().split(",")
    data = np.loadtxt(path, delimiter=",", skiprows=1)
    return {c: data[:, i] for i, c in enumerate(cols)}


def tilt_deg(d):
    # body z axis (FRD down) in NED: its down component = 1 - 2 (x^2 + y^2)
    c = 1 - 2 * (d["q_x"] ** 2 + d["q_y"] ** 2)
    return np.degrees(np.arccos(np.clip(c, -1, 1)))


def flights(d):
    armed = d["armed"] > 0.5
    edges = np.flatnonzero(np.diff(armed.astype(int)))
    starts = [i + 1 for i in edges if not armed[i]]
    out = []
    for s in starts:
        e = next((i for i in edges if i >= s and armed[i]), len(armed) - 1)
        if np.any(d["landed"][s:e + 1] != 1):
            out.append((s, e))
    return out


def metrics(d, s, e, rest_alt):
    t = d["t"]
    alt = -d["p_d"]
    landed = d["landed"]
    tilt = tilt_deg(d)
    r = dict(t0=t[s], time=t[e] - t[s])
    air = np.flatnonzero((landed[s:e + 1] == 2) | (landed[s:e + 1] == 3)) + s
    if len(air):
        err = np.sqrt((d["p_n"] - d["sp_n"]) ** 2 + (d["p_e"] - d["sp_e"]) ** 2 + (d["p_d"] - d["sp_d"]) ** 2)[air]
        r["track_max"], r["track_rms"] = float(err.max()), float(np.sqrt(np.mean(err ** 2)))
        r["tilt"] = float(tilt[air].max())
        m = np.stack([d["m1"], d["m2"], d["m3"], d["m4"]], axis=1)[air]
        r["sat"] = int(np.sum(np.any((m >= 0.999) | (m <= 0.001), axis=1)))
    tk = np.flatnonzero(landed[s:e + 1] == 3) + s
    if len(tk):
        k1 = tk[-1]
        goal = -d["sp_d"][k1]
        win = (t >= t[tk[0]]) & (t <= t[k1] + 5.0)
        r["overshoot"] = float(alt[win].max() - goal)
        r["takeoff_alt"] = float(goal - rest_alt)
    ld = np.flatnonzero(landed[s:e + 1] == 4) + s
    if len(ld):
        c = next((i for i in range(ld[0], e + 1) if alt[i] <= rest_alt + 0.005), None)
        if c is not None:
            r["vtd"] = float(d["v_d"][c])
            seg = alt[c:e + 1]
            r["bounce"] = float(np.max(seg - np.minimum.accumulate(seg)))     # largest rise after a dip
            r["gtilt"] = float(tilt[c:e + 1].max())
            g = next((i for i in range(c, e + 1) if landed[i] == 1), None)
            r["detect"] = float(t[g] - t[c]) if g is not None else None
            r["home"] = float(math.hypot(d["p_n"][c] - d["p_n"][s], d["p_e"][c] - d["p_e"][s]))
    return r


def runs(out):
    out = Path(out)
    d = load(out / "flight.csv")
    steps = json.loads((out / "steps.json").read_text())["steps"] if (out / "steps.json").exists() else []
    rest_alt = float(np.median(-d["p_d"][:400]))
    res = {}
    for s, e in flights(d):
        r = metrics(d, s, e, rest_alt)
        name = ""
        for st in steps:
            if st["t"] is not None and st["t"] <= r["t0"] + 1e-9:
                name = st["step"]
        res[name] = r
    return res


COLS = [("time", "time s", "{:.1f}", max), ("overshoot", "overshoot m", "{:+.3f}", max),
        ("track_max", "track max m", "{:.3f}", max), ("track_rms", "track rms m", "{:.3f}", max),
        ("tilt", "tilt max °", "{:.1f}", max), ("sat", "sat ticks", "{:d}", max),
        ("vtd", "touchdown m/s", "{:.2f}", max), ("bounce", "bounce mm", "{:.1f}", max),
        ("gtilt", "tilt on ground °", "{:.1f}", max), ("detect", "detect s", "{:.2f}", max),
        ("home", "touchdown from takeoff m", "{:.2f}", max)]


def summary(det, fields):
    D = runs(det)
    F = [runs(f) for f in fields]
    print("| flight | run | " + " | ".join(c[1] for c in COLS) + " |")
    print("|---|---|" + "---:|" * len(COLS))
    for name, r in D.items():
        cells = []
        for k, _, fmt, _ in COLS:
            v = r.get(k)
            cells.append(("{:.1f}".format(v * 1000) if k == "bounce" else fmt.format(v)) if v is not None else "–")
        print(f"| {name} | deterministic | " + " | ".join(cells) + " |")
        if not F:
            continue
        cells = []
        for k, _, fmt, worst in COLS:
            vs = [f[name][k] for f in F if name in f and f[name].get(k) is not None]
            if not vs:
                cells.append("–")
                continue
            w = max(vs, key=abs) if k in ("overshoot", "vtd") else worst(vs)
            m = float(np.mean(vs))
            if k == "bounce":
                cells.append(f"{m * 1000:.1f} / {w * 1000:.1f}")
            elif k == "sat":
                cells.append(f"{m:.0f} / {w:d}")
            else:
                cells.append(f"{fmt.format(m)} / {fmt.format(w)}")
        print(f"| {name} | field, {len(F)} seeds | " + " | ".join(cells) + " |")


def main():
    if sys.argv[1:2] == ["--summary"]:
        summary(sys.argv[2], sys.argv[3:])
        return
    for out in sys.argv[1:]:
        out = Path(out)
        d = load(out / "flight.csv")
        steps = json.loads((out / "steps.json").read_text())["steps"] if (out / "steps.json").exists() else []
        rest_alt = float(np.median(-d["p_d"][:400]))
        print(f"{out}: resting altitude {rest_alt:.4f} m, {len(d['t'])} ticks ({d['t'][-1]:.0f} s)")
        print("  flight     t0      time  takeoff  overshoot  track max/rms   tilt   sat   vtd     bounce  gtilt  detect  home")
        for s, e in flights(d):
            r = metrics(d, s, e, rest_alt)
            name = ""
            for st in steps:
                if st["t"] is not None and st["t"] <= r["t0"] + 1e-9:
                    name = st["step"]
            f = lambda k, fmt: (fmt.format(r[k]) if r.get(k) is not None else "-")  # noqa: E731
            print(f"  {name:9s} {r['t0']:6.1f} {r['time']:7.1f}  {f('takeoff_alt', '{:5.2f}')}    "
                  f"{f('overshoot', '{:+.3f}')}     {f('track_max', '{:.3f}')}/{f('track_rms', '{:.3f}')}"
                  f"  {f('tilt', '{:5.1f}')}  {f('sat', '{:4d}')}  {f('vtd', '{:+.3f}')}  {f('bounce', '{:.4f}')}  "
                  f"{f('gtilt', '{:4.1f}')}  {f('detect', '{:5.2f}')}  {f('home', '{:.2f}')}")


if __name__ == "__main__":
    main()
