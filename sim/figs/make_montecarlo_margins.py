#!/usr/bin/env python3
"""montecarlo-margins.tex: the margins of the course contract over the Monte Carlo runs
(sim/out/montecarlo/summary.csv): one dot strip per quantity against its bound, the failing side of
each bound tinted.

    sim/.venv/bin/python sim/figs/make_montecarlo_margins.py [--mc DIR] [--out DIR]
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path

import numpy as np

import common as C

MC = C.OUT / "montecarlo"
LX = 0.0                  # labels start (cm)
SX0, SX1 = 2.55, 6.35     # strip area
RX = 8.18                 # right edge of the value text (anchor east)
ROW = 0.27                # row pitch (cm)
GOLD = (math.sqrt(5) - 1) / 2


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mc", default=str(MC))
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    mc = Path(args.mc)
    spec = json.loads((C.SIM / "spec" / "mission-course.json").read_text())
    rows = list(csv.DictReader(open(mc / "summary.csv")))
    lean = sorted((r for r in rows if r["vehicle"] == "copter_lean"), key=lambda r: int(r["index"]))
    ref = sorted((r for r in rows if r["vehicle"] == "copter_ref"), key=lambda r: int(r["index"]))
    n = len(lean)
    nW = len(spec["waypoints_ned_m"])
    keys = (["max_alt_m", "max_dist_path_after_box_m", "max_dist_path_m", "hold_max_dist_m"]
            + [f"slack{i}_s" for i in range(nW)])
    for a, b in zip(lean, ref):
        if a["index"] != b["index"] or any(a[k] != b[k] for k in keys + ["verdict"]):
            raise SystemExit(f"sample {a['index']}: the two vehicles' margins differ")
    col = lambda k: np.array([float(r[k]) for r in lean])
    rho, r_m, ceil_m = spec["corridor_radius_m"], spec["r_m"], spec["ceiling_m"]
    allow = spec["allowances_s"]
    passes = (sum(int(r["verdict"]) for r in lean), sum(int(r["verdict"]) for r in ref))

    # groups: (title, axis (lo, hi, ticks, unit, scale), rows: (label, values, bound, fail side, right text))
    alt = col("max_alt_m")
    cor = col("max_dist_path_after_box_m") * 100
    whole = col("max_dist_path_m") * 100
    hold = col("hold_max_dist_m") * 100
    slack = [col(f"slack{i}_s") for i in range(nW)]
    groups = [
        ("Ceiling: highest altitude of the run", (1.0, 2.2, [1.0, 1.5, 2.0], "m"),
         [("max altitude", alt, ceil_m, "above", f"clear {100 * (ceil_m - alt.max()):.1f}\\,cm")]),
        ("Corridor: farthest from the path", (0.0, 30.0, [0, 10, 20, 25, 30], "cm"),
         [("after leaving $A$", cor, rho * 100, "above", f"margin {rho * 100 - cor.max():.2f}\\,cm"),
          ("from the start", whole, None, None, f"max {whole.max():.1f}\\,cm")]),
        ("Ordered reach: slack of each leg", (-0.5, 2.5, [0, 1, 2], "s"),
         [(f"leg {i}, $T_{i} = {allow[i]}$\\,s", slack[i], 0.0, "below", f"min {slack[i].min():.2f}\\,s")
          for i in range(nW)]),
        (f"Reach and hold: best {spec['hold_s']}\\,s window at $w_{nW - 1}$", (0.0, 12.0, [0, 5, 10], "cm"),
         [("max distance", hold, r_m * 100, "above", f"margin {r_m * 100 - hold.max():.2f}\\,cm")]),
    ]

    out = []
    w = out.append
    w("% ==================================================================")
    w("%  Monte Carlo margins of the course contract -- one sigconf text width")
    w("%  (8.2 cm), pdfLaTeX, plain TikZ")
    w("%  Preamble:  \\usepackage{tikz}  (no pgfplots; coordinates are embedded)")
    w(f"%  Data:      cpp2lean {C.rel(mc / 'summary.csv')} (sim/montecarlo.py, monitor")
    w(f"%             sim/monitor.py, spec sim/spec/mission-course.json): N = {n}")
    w("%             initial positions uniform in the takeoff box, each flown by")
    w("%             copter_lean (the Lean translations of ArduPilot's classes) and")
    w("%             copter_ref (ArduPilot's classes compiled unmodified) on the 1 m/s")
    w("%             figure-eight course with the tuned gains. The margins of the two")
    w("%             vehicles are equal for every sample (checked by the script); one")
    w(f"%             dot per sample. The contract holds on {passes[0]} of {n} copter_lean runs")
    w(f"%             and {passes[1]} of {len(ref)} copter_ref runs.")
    w("%  Strips:    each quantity on its own scale with its bound (vermilion line)")
    w("%             and the failing side tinted; dots spread vertically by a")
    w("%             golden-ratio sequence over the rank, so the vertical position")
    w("%             carries no data. Ceiling: highest altitude, bound 2.0 m.")
    w("%             Corridor: largest distance to the path (the takeoff point,")
    w("%             then w0..w7) from the first tick outside the box A on, bound")
    w(f"%             {rho:g} m; and over the whole run, which includes the start offset")
    w("%             inside A (A is part of the safe set, so this one has no bound).")
    w("%             Ordered reach: per leg, allowance minus the time from reaching")
    w("%             the previous waypoint (w0: from t = 0) to first coming within")
    w(f"%             {r_m:g} m of the waypoint, bound 0. Reach and hold: largest distance")
    w(f"%             to w7 over the best {spec['hold_s']} s window starting by {spec['total_s']} s, bound {r_m:g} m.")
    w("%  Values:    " + "; ".join(f"{g[0].split(':')[0]}" for g in groups) + ": ranges")
    for g in groups:
        for lab, v, bound, side, txt in g[2]:
            w(f"%             {lab.replace('$', '').replace(chr(92) + ',', ' ')}: min {v.min():.4f}, median {np.median(v):.4f}, max {v.max():.4f} {g[1][3]}")
    w("%  Generated by cpp2lean sim/figs/make_montecarlo_margins.py from the files")
    w("%  above; no hand-edited coordinates.")
    w("% ==================================================================")
    w(C.PALETTE)
    w("""\\begin{tikzpicture}[
  x=1cm, y=1cm, line cap=round, line join=round,
  tick/.style={font=\\scriptsize, text=fwMute, inner sep=1pt},
  lab/.style={font=\\scriptsize, text=fwInk!85, inner sep=0},
  val/.style={font=\\scriptsize, text=fwMute, inner sep=0},
  grp/.style={font=\\scriptsize\\bfseries, text=fwInk, inner sep=0},
  axis/.style={draw=fwHair, line width=0.4pt},
  mk/.style={draw=fwHair, line width=0.4pt},
  failz/.style={fill=fwVerm, fill opacity=0.10},
  bnd/.style={draw=fwVerm, line width=0.6pt},
  dot/.style={fill=fwBlue, fill opacity=0.35, draw=none},
]""")
    y = 0.0
    w(f"\\node[grp, anchor=north west] at ({LX},{C.num(y)}) {{{n} starts: the contract holds on {passes[0]} Lean and "
      f"{passes[1]} C++ runs}};")
    y -= 0.42
    for title, (lo, hi, ticks, unit), rws in groups:
        k = (SX1 - SX0) / (hi - lo)
        X = lambda v: SX0 + (v - lo) * k
        w(f"% ---------------- {title.split(':')[0]}")
        w(f"\\node[grp, anchor=north west] at ({LX},{C.num(y)}) {{{title}}};")
        y -= 0.30
        top = y
        bot = y - ROW * len(rws)
        # failing side of each row's bound, the bound line
        for j, (lab, v, bound, side, txt) in enumerate(rws):
            yc = top - ROW * (j + 0.5)
            y0, y1 = top - ROW * (j + 1) + 0.02, top - ROW * j - 0.02
            if bound is not None:
                if side == "above":
                    w(f"\\fill[failz] ({C.num(X(bound))},{C.num(y0)}) rectangle ({C.num(SX1)},{C.num(y1)});")
                else:
                    w(f"\\fill[failz] ({C.num(SX0)},{C.num(y0)}) rectangle ({C.num(X(bound))},{C.num(y1)});")
                w(f"\\draw[bnd] ({C.num(X(bound))},{C.num(y0)}) -- ({C.num(X(bound))},{C.num(y1)});")
            w(f"\\node[lab, anchor=east] at ({C.num(SX0 - 0.12)},{C.num(yc)}) {{{lab}}};")
            w(f"\\node[val, anchor=east] at ({C.num(RX)},{C.num(yc)}) {{{txt}}};")
            order = np.argsort(v, kind="stable")
            jit = np.empty(len(v))
            jit[order] = ((np.arange(len(v)) * GOLD) % 1.0 - 0.5) * (ROW - 0.09)
            w("  " + " ".join(f"\\fill[dot] ({C.num(X(x))},{C.num(yc + dy)}) circle (0.55pt);" for x, dy in zip(v, jit)))
        # axis under the group
        w(f"\\draw[axis] ({C.num(SX0)},{C.num(bot)}) -- ({C.num(SX1)},{C.num(bot)});")
        for t in ticks:
            lab = f"{C.num(t, 2)}\\,{unit}" if t == ticks[-1] else f"${C.num(t, 2)}$"
            w(f"\\draw[mk] ({C.num(X(t))},{C.num(bot)}) -- ++(0,-0.06) node[tick, anchor=north] {{{lab}}};")
        y = bot - 0.42
    w("\\end{tikzpicture}%")
    dst = Path(args.out) / "montecarlo-margins.tex"
    dst.write_text("\n".join(out) + "\n")
    print(f"{dst}: {n} samples, margins equal for the two vehicles; passes {passes}; corridor min margin "
          f"{rho * 100 - cor.max():.2f} cm; hold min margin {r_m * 100 - hold.max():.2f} cm; "
          f"min leg slack {min(s.min() for s in slack):.3f} s; ceiling clearance {ceil_m - alt.max():.4f} m")


if __name__ == "__main__":
    main()
