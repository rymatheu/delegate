#!/usr/bin/env python3
"""flight-path.tex: top view of the 1 m/s figure-eight course and altitude against distance flown,
from sim/out/lean-course-1ms and sim/out/ref-course-1ms (flight.csv, summary.txt).

    sim/.venv/bin/python sim/figs/make_path.py [--out DIR]   (default: the staging figs folder)
"""
from __future__ import annotations

import argparse
import math
from pathlib import Path

import numpy as np

import common as C

N_MAX = 300                       # points per curve at most (largest-triangle-three-buckets)
# layout (cm): the drawing is 8.2 cm wide; the plotting areas start at x0 and end at x1
X0, X1 = 0.92, 8.07
TOP_Y0, TOP_Y1 = 3.05, 6.656      # top view, vertical extent of the axes
BOT_Y0, BOT_H = 0.55, 1.55        # altitude panel


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    lean_dir, ref_dir = C.run_dir("lean"), C.run_dir("ref")
    L, R = C.load_flight(lean_dir), C.load_flight(ref_dir)
    ndiff = C.check_same(L, R)
    if ndiff:
        raise SystemExit(f"the two flights differ on {ndiff} ticks; this figure assumes they coincide")
    S = C.summary(lean_dir)
    wps = [w["ned"] for w in S["waypoints"]]
    n_ticks = len(L["t"])

    # ---------------- top view: east right, north up, equal scale
    ex = (-3.0, 2.95)                                     # axis extent in m (east)
    ny = (-1.5, 1.5)                                      # north
    k = (X1 - X0) / (ex[1] - ex[0])                       # cm per m
    cx = X0 - ex[0] * k                                   # cm position of east 0
    cy = TOP_Y0 - ny[0] * k
    def thin_xy(e, n):
        idx = C.lttb(np.stack([e * k, n * k], axis=1), N_MAX)
        return e[idx], n[idx]
    fe, fn = thin_xy(L["y_e"], L["x_n"])
    re_, rn = thin_xy(R["y_e"], R["x_n"])
    te, tn = thin_xy(L["sp_e"], L["sp_n"])

    # altitude panel
    dist = np.concatenate([[0.0], np.cumsum(np.hypot(np.diff(L["x_n"]), np.diff(L["y_e"])))])
    dist_r = np.concatenate([[0.0], np.cumsum(np.hypot(np.diff(R["x_n"]), np.diff(R["y_e"])))])
    dmax = 2 * math.ceil(dist[-1] / 2)
    amax = 1.8
    kx = (X1 - X0) / dmax
    ky = BOT_H / amax
    def thin_da(d, a):
        idx = C.lttb(np.stack([d * kx, a * ky], axis=1), N_MAX)
        return d[idx], a[idx]
    bd, ba = thin_da(dist, -L["z_d"])
    rd, ra = thin_da(dist_r, -R["z_d"])
    td, ta = thin_da(dist, -L["sp_d"])

    # closest approaches (summary.txt) -> distance flown at that tick
    t = L["t"]
    def tick_at(time_s):
        return int(np.argmin(np.abs(t - time_s)))
    d_wp = [dist[tick_at(w["t_closest"])] for w in S["waypoints"]]

    # vehicle glyphs: halfway (in distance flown) between the closest approaches of w0 and w1, w2 and
    # w3, w5 and w6; three quarters of the way from w3 to w4 (its halfway point is over the origin,
    # where w0 and w7 are drawn); and the last tick (the final hover)
    marks = [(0, 1, 0.5), (2, 3, 0.5), (3, 4, 0.75), (5, 6, 0.5)]
    glyph_ticks = [int(np.argmax(dist >= d_wp[i] + f * (d_wp[j] - d_wp[i]))) for i, j, f in marks]
    glyph_ticks.append(n_ticks - 1)

    out = []
    w = out.append
    w("% ==================================================================")
    w("%  Flight path -- one sigconf text width (8.2 cm), pdfLaTeX, plain TikZ")
    w("%  Preamble:  \\usepackage{tikz}  (no pgfplots; coordinates are embedded)")
    w(f"%  Data:      cpp2lean {C.rel(lean_dir / 'flight.csv')} (copter_lean, the")
    w("%             Lean translations of ArduPilot's classes) and")
    w(f"%             {C.rel(ref_dir / 'flight.csv')} (copter_ref, ArduPilot's")
    w("%             classes compiled unmodified), the 1 m/s figure-eight course")
    w("%             with the tuned gains (params copter-cf2x.txt +")
    w("%             copter-course-speed.txt + copter-cf2x-tuned.txt), 400 Hz")
    w(f"%             control, 1200 Hz physics, {n_ticks} ticks each. The two flights")
    w("%             are equal in every field of flight.csv on every tick (checked")
    w("%             by the script; the controller round-trip time is the only")
    w("%             field that differs), so their curves coincide; the copter_ref")
    w("%             path is drawn as a pale wide stroke under the copter_lean")
    w("%             path, and the desired position (equal in both) once.")
    w(f"%             Each curve thinned to at most {N_MAX} points by")
    w("%             largest-triangle-three-buckets (areas measured on the page).")
    w("%  Mission:   the figure-eight course of sim/params/copter-cf2x.txt at")
    w("%             WP_SPD 1 m/s, WP_ACC 1.5 m/s^2 (copter-course-speed.txt).")
    w("%  Top:       top-down view, east right and north up, equal scale; the flown")
    w("%             path (solid; copter_lean in fwBlue over copter_ref in pale")
    w("%             fwBlue) and AC_PosControl's desired position (dashed, trace")
    w("%             fields sp_n, sp_e); waypoints as open circles (w0 and w7")
    w("%             coincide over the origin); the vehicle glyph (heading tick toward")
    w("%             the nose, yaw from flight.csv) halfway in distance flown")
    w("%             between the closest approaches of w0 and w1, of w2 and w3, of w5")
    w("%             and w6, three quarters of the way from w3 to w4 (halfway is over")
    w("%             the origin), and at the last tick: t = "
      + ", ".join(f"{t[j]:.3f}" for j in glyph_ticks) + " s.")
    w("%  Bottom:    altitude above ground versus the horizontal distance the vehicle")
    w("%             has flown, for the vehicle (solid, both flights as above) and")
    w("%             for the desired position at the same tick (dashed); each")
    w("%             waypoint drawn at its altitude and at the distance flown at the")
    w("%             vehicle's closest approach (times from summary.txt: "
      + ", ".join(f"{x['t_closest']:g}" for x in S["waypoints"]) + " s).")
    w("%  Generated by cpp2lean sim/figs/make_path.py from the files above; no")
    w("%  hand-edited coordinates.")
    w("% ==================================================================")
    w(C.PALETTE)
    w("""\\begin{tikzpicture}[
  x=1cm, y=1cm, line cap=round, line join=round,
  tick/.style={font=\\scriptsize, text=fwMute, inner sep=1pt},
  alab/.style={font=\\scriptsize, text=fwInk!80, inner sep=0},
  axis/.style={draw=fwHair, line width=0.4pt},
  mk/.style={draw=fwHair, line width=0.4pt},
  crv/.style={line width=0.5pt},
  ref/.style={line width=1.7pt, draw opacity=0.28},
  tgt/.style={draw=fwMute, line width=0.35pt, dash pattern=on 1.6pt off 1.1pt},
  wp/.style={draw=fwMute, fill=white, line width=0.4pt},
  wpl/.style={font=\\scriptsize, text=fwMute, inner sep=1pt},
]
% vehicle glyph: X arms, four rotors, heading tick; #3 = heading (deg, from north, clockwise)
\\newcommand{\\quadglyph}[3]{%
  \\begin{scope}[shift={(#1,#2)}, x=1cm, y=1cm, rotate=-#3, fwInk, line width=0.4pt]
    \\draw (225:0.11) -- (45:0.11) (135:0.11) -- (315:0.11);
    \\foreach \\a in {45,135,225,315} \\draw (\\a:0.11) circle (0.036);
    \\draw[fwOchre, line width=0.55pt] (90:0.05) -- (90:0.24);
  \\end{scope}}""")
    w("% ---------------- top-down path")
    w(f"\\begin{{scope}}[shift={{({C.num(cx, 4)},{C.num(cy, 4)})}}, x={C.num(k, 5)}cm, y={C.num(k, 5)}cm]")
    w(f"  \\draw[axis] ({ex[0]},{ny[1]}) -- ({ex[0]},{ny[0]}) -- ({ex[1]},{ny[0]});")
    for v in range(-2, 3):
        lab = f"{v}\\,m" if v == 2 else f"${v}$"
        w(f"  \\draw[mk] ({v},{ny[0]}) -- ++(0,-0.06cm) node[tick, anchor=north] {{{lab}}};")
    for v in range(-1, 2):
        lab = f"{v}\\,m" if v == 1 else f"${v}$"
        w(f"  \\draw[mk] ({ex[0]},{v}) -- ++(-0.06cm,0) node[tick, anchor=east] {{{lab}}};")
    w("  % copter_ref, flown (pale, under)")
    w("  \\draw[ref, fwBlue] plot coordinates {\n" + C.coords(re_, rn) + "\n  };")
    w("  % desired position (trace sp_e, sp_n)")
    w("  \\draw[tgt] plot coordinates {\n" + C.coords(te, tn) + "\n  };")
    w("  % copter_lean, flown")
    w("  \\draw[crv, fwBlue] plot coordinates {\n" + C.coords(fe, fn) + "\n  };")
    for j in glyph_ticks:
        w(f"  \\quadglyph{{{C.num(L['y_e'][j])}}}{{{C.num(L['x_n'][j])}}}{{{C.num(math.degrees(L['yaw'][j]) % 360, 2)}}}"
          f"  % t = {t[j]:.4f} s")
    seen = {}
    for i, (n, e, d) in enumerate(wps):
        seen.setdefault((n, e), []).append(i)
    for (n, e), ids in seen.items():
        w(f"  \\draw[wp] ({C.num(e)},{C.num(n)}) circle (0.065cm);")
    for (n, e), ids in seen.items():
        name = ", ".join(f"w_{i}" for i in ids)
        if n == 0 and e == 0:
            w(f"  \\node[wpl, anchor=east] at (-0.17,0) {{${name}$}};")
            continue
        sx, sy = np.sign(e), np.sign(n)
        anchor = {(1, 1): "south west", (1, -1): "north west", (-1, 1): "south east", (-1, -1): "north east",
                  (1, 0): "west", (-1, 0): "east", (0, 1): "south", (0, -1): "north"}[(int(sx), int(sy))]
        w(f"  \\node[wpl, anchor={anchor}] at ({C.num(e + 0.07 * sx)},{C.num(n + 0.05 * sy)}) {{${name}$}};")
    w("\\end{scope}")
    w(f"\\node[alab, anchor=north] at ({C.num(cx)},{C.num(TOP_Y0 - 0.33)}) {{east}};")
    w(f"\\node[alab, rotate=90, anchor=south] at (0.420,{C.num(cy)}) {{north}};")

    # ---------------- altitude panel
    w("% ---------------- altitude versus horizontal distance")
    w(f"\\begin{{scope}}[shift={{({X0},{BOT_Y0})}}, x={C.num(kx, 5)}cm, y={C.num(ky, 5)}cm]")
    w(f"  \\draw[axis] (0,{amax}) -- (0,0) -- ({dmax},0);")
    for v in range(0, dmax + 1, 2):
        lab = f"{v}\\,m" if v == dmax else f"${v}$"
        w(f"  \\draw[mk] ({v},0) -- ++(0,-0.06cm) node[tick, anchor=north] {{{lab}}};")
    for v, lab in [(0, "$0$"), (0.8, "$0.8$"), (1.6, "1.6\\,m")]:
        w(f"  \\draw[mk] (0,{v}) -- ++(-0.06cm,0) node[tick, anchor=east] {{{lab}}};")
    w("  % copter_ref, flown (pale, under)")
    w("  \\draw[ref, fwBlue] plot coordinates {\n" + C.coords(rd, ra) + "\n  };")
    w("  % desired altitude (trace sp_d) at the vehicle's distance flown")
    w("  \\draw[tgt] plot coordinates {\n" + C.coords(td, ta) + "\n  };")
    w("  % copter_lean, flown")
    w("  \\draw[crv, fwBlue] plot coordinates {\n" + C.coords(bd, ba) + "\n  };")
    for i, (wpt, dw) in enumerate(zip(wps, d_wp)):
        alt = -wpt[2]
        w(f"  \\draw[wp] ({C.num(dw)},{C.num(alt)}) circle (0.065cm);")
        if i == 0:
            # below and right of the marker: the flown altitude passes just above w0
            w(f"  \\node[wpl, anchor=north west] at ({C.num(dw + 0.1)},{C.num(alt - 0.06)}) {{$w_{i}$}};")
        else:
            w(f"  \\node[wpl, anchor=south] at ({C.num(dw)},{C.num(alt + 0.08)}) {{$w_{i}$}};")
    # key, in the free space under the curve (data units of this panel)
    ky0 = 0.42
    xk = 2.2
    w("% ---------------- key")
    w(f"  \\quadglyph{{{C.num(xk)}}}{{{ky0}}}{{0}}")
    w(f"  \\node[wpl, anchor=west] at ({C.num(xk + 0.45)},{ky0}) {{vehicle}};")
    xk += 2.45
    w(f"  \\draw[wp] ({C.num(xk)},{ky0}) circle (0.065cm);")
    w(f"  \\node[wpl, anchor=west] at ({C.num(xk + 0.3)},{ky0}) {{waypoint}};")
    xk += 2.75
    w(f"  \\draw[ref, fwBlue] ({C.num(xk)},{ky0}) -- ({C.num(xk + 0.6)},{ky0});")
    w(f"  \\draw[crv, fwBlue] ({C.num(xk)},{ky0}) -- ({C.num(xk + 0.6)},{ky0});")
    w(f"  \\node[wpl, anchor=west, align=left] at ({C.num(xk + 0.8)},{ky0}) {{flown, Lean\\\\[-1pt]over C++}};")
    xk += 3.25
    w(f"  \\draw[tgt] ({C.num(xk)},{ky0}) -- ({C.num(xk + 0.6)},{ky0});")
    w(f"  \\node[wpl, anchor=west] at ({C.num(xk + 0.8)},{ky0}) {{desired}};")
    w("\\end{scope}")
    w(f"\\node[alab, anchor=north] at ({C.num((X0 + X1) / 2)},0.220) {{distance}};")
    w(f"\\node[alab, rotate=90, anchor=south] at (0.420,{C.num(BOT_Y0 + BOT_H / 2)}) {{altitude}};")
    w("\\end{tikzpicture}%")
    dst = Path(args.out) / "flight-path.tex"
    dst.write_text("\n".join(out) + "\n")
    print(f"{dst}: flights equal on all {n_ticks} ticks; glyphs at t = "
          + ", ".join(f"{t[j]:.4f}" for j in glyph_ticks) + f"; distance flown {dist[-1]:.3f} m")


if __name__ == "__main__":
    main()
