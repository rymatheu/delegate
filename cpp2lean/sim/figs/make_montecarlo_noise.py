#!/usr/bin/env python3
"""montecarlo-noise.tex: the Monte Carlo flights under bounded sensing noise (sim/out/montecarlo-noise-<L>),
top view of the 200 trajectories over the corridor (the set they sweep out), and the spread of the set
against time over the whole run.

The level drawn is, by default, the highest of the spec's sensing levels (L1..L4) whose runs all
satisfy the contract with both vehicles; --level picks one.

Spread: at each tick, the largest distance over the runs from the run's position to the nominal flown
path (sim/out/lean-course-1ms, noise free), as in montecarlo-3d.tex.

    sim/.venv/bin/python sim/figs/make_montecarlo_noise.py [--level L] [--out DIR]
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path

import numpy as np
from scipy.spatial import cKDTree

import common as C
from make_montecarlo_paths import read_run

N_PTS = 200
X0, X1 = 0.92, 8.07
TOP_Y0 = 2.55
STRIP_Y0, STRIP_H = 0.55, 1.25


def level_ok(d: Path) -> tuple[bool, list]:
    rows = list(csv.DictReader(open(d / "summary.csv")))
    return all(r["verdict"] == "1" for r in rows) and all(int(r["differing_ticks"] or 0) == 0 for r in rows), rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--level", default=None)
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    spec = json.loads((C.SIM / "spec" / "mission-course.json").read_text())
    levels = list(spec["sensing"]["levels"])
    status = {}
    for L in levels:
        d = C.OUT / f"montecarlo-noise-{L}"
        if (d / "summary.csv").exists():
            status[L] = level_ok(d)[0]
    if args.level:
        lv = args.level
    else:
        passing = [L for L in levels if status.get(L)]
        if not passing:
            raise SystemExit(f"no level passes everything: {status}")
        lv = passing[-1]
    mc = C.OUT / f"montecarlo-noise-{lv}"
    ok, rows = level_ok(mc)
    b = spec["sensing"]["levels"][lv]
    lean = sorted((r for r in rows if r["vehicle"] == "copter_lean"), key=lambda r: int(r["index"]))
    ref = sorted((r for r in rows if r["vehicle"] == "copter_ref"), key=lambda r: int(r["index"]))
    n = len(lean)
    runs = []
    for r in lean:
        i = int(r["index"])
        a, bb = read_run(mc / "runs" / f"lean-{i:03d}.csv.gz"), read_run(mc / "runs" / f"ref-{i:03d}.csv.gz")
        if not np.array_equal(a, bb):
            raise SystemExit(f"{lv} sample {i}: the two vehicles' positions differ")
        runs.append(a)
    passes = (sum(r["verdict"] == "1" for r in lean), sum(r["verdict"] == "1" for r in ref))
    rho = spec["corridor_radius_m"]
    W = np.array(spec["waypoints_ned_m"])
    box = spec["box_ned_m"]

    # spread against the nominal flown path, every tick
    nom = C.load_flight(C.run_dir("lean"))
    nomp = np.stack([nom["x_n"], nom["y_e"], nom["z_d"]], axis=1)
    dense = [nomp[:1]]
    for a_, b_ in zip(nomp[:-1], nomp[1:]):
        L_ = np.linalg.norm(b_ - a_)
        k = max(1, int(math.ceil(L_ / 1e-4)))
        dense.append(a_ + (b_ - a_) * (np.arange(1, k + 1) / k)[:, None])
    tree = cKDTree(np.vstack(dense))
    m = min(len(x) for x in runs)
    G = np.stack([tree.query(x[:m])[0] for x in runs])
    spread = G.max(axis=0)
    ts = np.arange(m) / spec["tick_hz"]
    after = ts >= 3.0
    j_late = int(np.argmax(np.where(after, spread, -1)))
    cor_after = max(float(r["max_dist_path_after_box_m"]) for r in lean)

    # ---------------- top view (as montecarlo-paths.tex)
    ex, ny = (-3.0, 2.95), (-1.5, 1.5)
    k = (X1 - X0) / (ex[1] - ex[0])
    cx, cy = X0 - ex[0] * k, TOP_Y0 - ny[0] * k
    top = []
    for x in runs:
        e, nn = x[:, 1], x[:, 0]
        idx = C.lttb(np.stack([e * k, nn * k], axis=1), N_PTS)
        top.append((e[idx], nn[idx]))
    bstr = (f"position $\\pm{C.num(b['bp'] * 100, 2)}$\\,cm, velocity $\\pm{C.num(b['bv'] * 100, 2)}$\\,cm/s"
            + (f", attitude $\\pm{C.num(b['bq'], 2)}^\\circ$" if b["bq"] else "")
            + (f", rates $\\pm{C.num(b['bw'], 3)}$\\,rad/s" if b["bw"] else "")
            + (f", specific force $\\pm{C.num(b['bf'], 3)}$\\,m/s$^2$" if b["bf"] else ""))
    out = []
    w = out.append
    w("% ==================================================================")
    w("%  Monte Carlo flights under bounded sensing noise -- one sigconf text width")
    w("%  (8.2 cm), pdfLaTeX, plain TikZ (no pgfplots; coordinates are embedded)")
    w(f"%  Data:      cpp2lean {C.rel(mc / 'runs')}/<lean|ref>-<i>.csv.gz and summary.csv")
    w(f"%             (sim/montecarlo.py --noise {lv}): the {n} starts and headings of")
    w("%             sim/out/montecarlo, flown by copter_lean and copter_ref with the sample")
    w("%             perturbed every tick by independent errors uniform in [-b, b] per")
    w(f"%             component (spec sensing level {lv}: bp {b['bp']:g} m, bv {b['bv']:g} m/s, bq {b['bq']:g} deg,")
    w(f"%             bw {b['bw']:g} rad/s, bf {b['bf']:g} m/s^2), the same noise for both vehicles of a pair;")
    w("%             the true positions are drawn. The two vehicles' positions are equal on")
    w(f"%             every tick (checked by the script). Contract holds on {passes[0]} of {n} copter_lean")
    w(f"%             and {passes[1]} of {len(ref)} copter_ref runs. Levels that pass everything: "
      + ", ".join(L for L in levels if status.get(L)) + "; drawn: " + lv + ".")
    w(f"%             Each trajectory thinned to {N_PTS} points (largest-triangle-three-buckets).")
    w(f"%  Top:       top view as montecarlo-paths.tex: corridor of radius {rho:g} m (the path")
    w("%             stroked with round caps and joins), the box A, the waypoints, the")
    w("%             trajectories as translucent strokes. Largest distance to the path after")
    w(f"%             leaving the box over all runs {cor_after * 100:.2f} cm.")
    w("%  Bottom:    the spread: at each tick the largest distance over the runs from the")
    w("%             run's position to the nominal flown path (sim/out/lean-course-1ms), log")
    w(f"%             scale, the whole run (0 to {ts[-1]:g} s). At t = 0 {spread[0] * 100:.2f} cm; largest after")
    w(f"%             3 s {spread[j_late] * 100:.2f} cm at t = {ts[j_late]:.3f} s.")
    w("%  Generated by cpp2lean sim/figs/make_montecarlo_noise.py; no hand-edited coordinates.")
    w("% ==================================================================")
    w(C.PALETTE)
    w("""\\begin{tikzpicture}[
  x=1cm, y=1cm, line cap=round, line join=round,
  tick/.style={font=\\scriptsize, text=fwMute, inner sep=1pt},
  alab/.style={font=\\scriptsize, text=fwInk!80, inner sep=0},
  lab/.style={font=\\scriptsize, text=fwInk!85, inner sep=1pt},
  axis/.style={draw=fwHair, line width=0.4pt},
  mk/.style={draw=fwHair, line width=0.4pt},
  run/.style={draw=fwBlue, line width=0.3pt, draw opacity=0.10},
  coredge/.style={draw=fwBlue!45},
  corfill/.style={draw=fwBlue!7},
  Afill/.style={fill=fwOchre, fill opacity=0.18},
  Aedge/.style={draw=fwOchre, line width=0.4pt},
  wp/.style={draw=fwInk!70, fill=white, line width=0.4pt},
  spr/.style={draw=fwBlue, line width=0.5pt},
  ref/.style={draw=fwMute, line width=0.3pt, dash pattern=on 1.2pt off 1pt},
]""")
    w("% ---------------- top view")
    w(f"\\begin{{scope}}[shift={{({C.num(cx, 4)},{C.num(cy, 4)})}}, x={C.num(k, 5)}cm, y={C.num(k, 5)}cm]")
    w(f"  \\draw[axis] ({ex[0]},{ny[1]}) -- ({ex[0]},{ny[0]}) -- ({ex[1]},{ny[0]});")
    for v in range(-2, 3):
        lab = f"{v}\\,m" if v == 2 else f"${v}$"
        w(f"  \\draw[mk] ({v},{ny[0]}) -- ++(0,-0.06cm) node[tick, anchor=north] {{{lab}}};")
    for v in range(-1, 2):
        lab = f"{v}\\,m" if v == 1 else f"${v}$"
        w(f"  \\draw[mk] ({ex[0]},{v}) -- ++(-0.06cm,0) node[tick, anchor=east] {{{lab}}};")
    corridor = " -- ".join(f"({C.num(e)},{C.num(nn)})" for e, nn in zip([0.0] + list(W[:, 1]), [0.0] + list(W[:, 0])))
    wcm = 2 * rho * k
    w(f"  \\draw[coredge, line width={C.num(wcm + 0.03, 4)}cm] {corridor};")
    w(f"  \\draw[corfill, line width={C.num(wcm - 0.01, 4)}cm] {corridor};")
    bn, be = box["north"], box["east"]
    w(f"  \\fill[Afill] ({be[0]},{bn[0]}) rectangle ({be[1]},{bn[1]});")
    w(f"  \\draw[Aedge] ({be[0]},{bn[0]}) rectangle ({be[1]},{bn[1]});")
    w(f"  % {n} trajectories")
    for e, nn in top:
        w("  \\draw[run] plot coordinates {" + " ".join(f"({C.num(x)},{C.num(y)})" for x, y in zip(e, nn)) + "};")
    seen = set()
    for (nn, e, d) in W:
        if (nn, e) in seen:
            continue
        seen.add((nn, e))
        w(f"  \\draw[wp] ({C.num(e)},{C.num(nn)}) circle (0.05cm);")
    w(f"  \\node[lab, text=fwOchre!85!black, anchor=east] at ({C.num(be[0] - 0.02)},0) {{$A$}};")
    w("\\end{scope}")
    w(f"\\node[alab, anchor=north] at ({C.num(cx)},{C.num(TOP_Y0 - 0.33)}) {{east}};")
    w(f"\\node[alab, rotate=90, anchor=south] at (0.420,{C.num(cy)}) {{north}};")
    top_y1 = TOP_Y0 + (ny[1] - ny[0]) * k
    w(f"\\node[lab, anchor=south west] at ({C.num(X0 - 0.5)},{C.num(top_y1 + 0.08)}) {{Sensing noise {lv}, per tick and component: {bstr}}};")
    lobe = (f"{n} starts,\\\\[-1pt]all pass,\\\\[-1pt]Lean and C++\\\\[-1pt]identical" if ok else
            f"{n} starts,\\\\[-1pt]{min(passes)} pass")
    w(f"\\node[lab, align=center] at ({C.num(cx - 1.25 * k)},{C.num(cy)}) {{{lobe}}};")

    # ---------------- spread strip
    lmin, lmax = math.log10(0.05), math.log10(30.0)
    T = ts[-1]
    Xs = lambda t: X0 + t / T * (X1 - X0)
    Ys = lambda cm: STRIP_Y0 + (math.log10(max(cm, 10 ** lmin)) - lmin) / (lmax - lmin) * STRIP_H
    w("% ---------------- spread against time")
    w(f"\\draw[axis] ({C.num(X0)},{C.num(STRIP_Y0 + STRIP_H)}) -- ({C.num(X0)},{C.num(STRIP_Y0)}) -- ({C.num(X1)},{C.num(STRIP_Y0)});")
    for cm_, lab in [(0.1, "1\\,mm"), (1, "1\\,cm"), (10, "10\\,cm")]:
        w(f"\\draw[mk] ({C.num(X0)},{C.num(Ys(cm_))}) -- ++(-0.06,0) node[tick, anchor=east] {{{lab}}};")
        w(f"\\draw[ref] ({C.num(X0)},{C.num(Ys(cm_))}) -- ({C.num(X1)},{C.num(Ys(cm_))});")
    for tt in range(0, int(T) + 1, 5):
        lab = f"{tt}\\,s" if tt + 5 > T else f"${tt}$"
        w(f"\\draw[mk] ({C.num(Xs(tt))},{C.num(STRIP_Y0)}) -- ++(0,-0.06) node[tick, anchor=north] {{{lab}}};")
    sp = np.stack([[Xs(t) for t in ts], [Ys(v * 100) for v in spread]], axis=1)
    keep = C.lttb(sp, 500)
    w(f"\\draw[spr] plot coordinates {{{' '.join(f'({C.num(x)},{C.num(y)})' for x, y in sp[keep])}}};")
    w(f"\\node[alab, anchor=north] at ({C.num((X0 + X1) / 2)},0.22) {{time}};")
    w(f"\\node[lab, anchor=south west] at ({C.num(X0 + 0.1)},{C.num(STRIP_Y0 + STRIP_H + 0.02)}) "
      f"{{spread: farthest run from the nominal path}};")
    w("\\end{tikzpicture}%")
    dst = Path(args.out) / "montecarlo-noise.tex"
    dst.write_text("\n".join(out) + "\n")
    print(f"{dst}: level {lv} (passing levels: {[L for L in levels if status.get(L)]}); passes {passes}; "
          f"spread t=0 {spread[0] * 100:.2f} cm, max after 3 s {spread[j_late] * 100:.2f} cm at {ts[j_late]:.3f} s; "
          f"max distance after the box {cor_after * 100:.2f} cm")


if __name__ == "__main__":
    main()
