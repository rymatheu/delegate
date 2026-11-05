#!/usr/bin/env python3
"""montecarlo-paths.tex: the Monte Carlo flights of the course contract (sim/out/montecarlo), every
trajectory drawn over the corridor, the takeoff box, the ceiling and the waypoints; top view and
altitude against distance along the path.

    sim/.venv/bin/python sim/figs/make_montecarlo_paths.py [--mc DIR] [--out DIR]
"""
from __future__ import annotations

import argparse
import csv
import gzip
import json
import math
from pathlib import Path

import numpy as np

import common as C

N_PTS = 150                       # points per trajectory and panel (largest-triangle-three-buckets)
X0, X1 = 0.92, 8.07               # plotting areas, cm (the drawing is 8.2 cm wide)
TOP_Y0, TOP_Y1 = 3.30, 6.906      # top view
BOT_Y0, BOT_H = 0.55, 1.95        # altitude panel
MC = C.OUT / "montecarlo"


def read_run(path: Path) -> np.ndarray:
    with gzip.open(path, "rt") as f:
        rows = list(csv.reader(f))[1:]
    return np.array([[float(r[1]), float(r[2]), float(r[3])] for r in rows])


def path_coordinate(pos: np.ndarray, verts: np.ndarray) -> np.ndarray:
    """Distance along the path of each position: the horizontal arc length of its nearest point on the
    path segment it is flying, where the segment index only moves forward (from segment j to j + 1 once
    the position is nearer to j + 1 than to j). w0 and w7 coincide, so the plain nearest point would jump
    between the start and the end of the path; the forward-only index keeps the climb at 0 and the
    final hover at the end."""
    D, S = [], []
    s0 = 0.0
    for a, b in zip(verts[:-1], verts[1:]):
        ab = b - a
        t = np.clip((pos - a) @ ab / float(ab @ ab), 0.0, 1.0)
        D.append(np.linalg.norm(pos - (a + t[:, None] * ab), axis=1).tolist())
        h = math.hypot(ab[0], ab[1])
        S.append((s0 + t * h).tolist())
        s0 += h
    j, out = 0, []
    for k in range(len(pos)):
        while j + 1 < len(D) and D[j + 1][k] < D[j][k]:
            j += 1
        out.append(S[j][k])
    return np.array(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mc", default=str(MC))
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    mc = Path(args.mc)
    rows = list(csv.DictReader(open(mc / "summary.csv")))
    spec = json.loads((C.SIM / "spec" / "mission-course.json").read_text())
    lean = sorted((r for r in rows if r["vehicle"] == "copter_lean"), key=lambda r: int(r["index"]))
    ref = {int(r["index"]): r for r in rows if r["vehicle"] == "copter_ref"}
    n = len(lean)
    if any(int(r["differing_ticks"]) for r in lean):
        raise SystemExit("some paired runs differ; this figure draws one set for both vehicles")
    runs = []
    for r in lean:
        i = int(r["index"])
        a = read_run(mc / "runs" / f"lean-{i:03d}.csv.gz")
        b = read_run(mc / "runs" / f"ref-{i:03d}.csv.gz")
        if not np.array_equal(a, b):
            raise SystemExit(f"sample {i}: the two vehicles' positions differ")
        runs.append(a)
    passed = sum(int(r["verdict"]) for r in lean), sum(int(ref[i]["verdict"]) for i in ref)
    ticks = sorted({len(a) for a in runs})
    W = np.array(spec["waypoints_ned_m"])
    V = np.array(spec["path_ned_m"])
    rho, ceil_m = spec["corridor_radius_m"], spec["ceiling_m"]
    box = spec["box_ned_m"]

    # ---------------- top view: east right, north up, equal scale (as flight-path.tex)
    ex, ny = (-3.0, 2.95), (-1.5, 1.5)
    k = (X1 - X0) / (ex[1] - ex[0])
    cx, cy = X0 - ex[0] * k, TOP_Y0 - ny[0] * k
    # ---------------- altitude panel: altitude against distance along the path
    hlen = sum(math.hypot(*(b - a)[:2]) for a, b in zip(V[:-1], V[1:]))
    dmin, dmax = -0.6, 2 * math.ceil(hlen / 2)
    amax = 2.2
    kx = (X1 - X0) / (dmax - dmin)
    ky = BOT_H / amax
    bx0 = X0 - dmin * kx
    sV = np.concatenate([[0.0], np.cumsum([math.hypot(*(b - a)[:2]) for a, b in zip(V[:-1], V[1:])])])

    top, side = [], []
    for a in runs:
        e, nn = a[:, 1], a[:, 0]
        idx = C.lttb(np.stack([e * k, nn * k], axis=1), N_PTS)
        top.append((e[idx], nn[idx]))
        s, alt = path_coordinate(a, V), -a[:, 2]
        idx = C.lttb(np.stack([s * kx, alt * ky], axis=1), N_PTS)
        side.append((s[idx], alt[idx]))
    starts = np.array([[float(r["init_n"]), float(r["init_e"]), float(r["init_d"])] for r in lean])
    max_alt = max(float(r["max_alt_m"]) for r in lean)
    max_cor = max(float(r["max_dist_path_after_box_m"]) for r in lean)

    out = []
    w = out.append
    w("% ==================================================================")
    w("%  Monte Carlo flights of the course contract -- one sigconf text width")
    w("%  (8.2 cm), pdfLaTeX, plain TikZ")
    w("%  Preamble:  \\usepackage{tikz}  (no pgfplots; coordinates are embedded)")
    w(f"%  Data:      cpp2lean {C.rel(mc / 'summary.csv')} and")
    w(f"%             {C.rel(mc / 'runs')}/<lean|ref>-<i>.csv.gz, written by")
    w(f"%             sim/montecarlo.py: N = {n} initial positions drawn uniformly")
    w("%             from the takeoff box (seed in RESULTS.md there), each flown")
    w("%             by copter_lean (the Lean translations of ArduPilot's classes)")
    w("%             and by copter_ref (ArduPilot's classes compiled unmodified)")
    w("%             on the 1 m/s figure-eight course with the tuned gains (params")
    w("%             copter-cf2x.txt + copter-course-speed.txt +")
    w("%             copter-cf2x-tuned.txt), 400 Hz control, 1200 Hz physics, for")
    w(f"%             {', '.join(str(t) for t in ticks)} ticks each (the horizon of the contract).")
    w("%             The positions of the two vehicles are equal on every tick of")
    w("%             every pair (checked by the script; their actuators are equal")
    w("%             bit for bit, summary.csv differing_ticks), so one set of")
    w(f"%             {n} trajectories is drawn for both. Verdicts: the contract")
    w(f"%             holds on {passed[0]} of {n} copter_lean runs and {passed[1]} of {len(ref)} copter_ref runs.")
    w(f"%             Each trajectory thinned to {N_PTS} points per panel by")
    w("%             largest-triangle-three-buckets (areas measured on the page).")
    w("%  Spec:      sim/spec/mission-course.json: corridor of radius")
    w(f"%             {rho:g} m around the path (the takeoff point, then w0..w7),")
    w(f"%             box north {box['north']}, east {box['east']}, down {box['down']} m,")
    w(f"%             ceiling {ceil_m:g} m.")
    w("%  Top:       top view, east right and north up, equal scale; the corridor")
    w("%             is the path stroked with round caps and joins at a width of")
    w(f"%             {2 * rho:g} m (its exact top-view projection), the box as its square,")
    w("%             the starts (realized initial positions) as dots, the")
    w("%             trajectories as translucent strokes, waypoints as open circles")
    w("%             (w0 and w7 coincide over the origin).")
    w("%  Bottom:    altitude against distance along the path: the horizontal arc")
    w("%             length of each position's nearest point on the path (3D")
    w("%             distance), so every climb from the box to w0 is drawn at 0;")
    w(f"%             the corridor as the path's altitude profile stroked at {2 * rho:g} m")
    w("%             (to the altitude scale), the box at the takeoff point drawn")
    w(f"%             {box['north'][1] - box['north'][0]:g} m wide on the distance scale, the ceiling as a line, each")
    w("%             waypoint at its altitude and distance. Highest point of all")
    w(f"%             runs {max_alt:.4f} m; largest distance to the path after leaving the box")
    w(f"%             {max_cor * 100:.2f} cm.")
    w("%  Generated by cpp2lean sim/figs/make_montecarlo_paths.py from the files")
    w("%  above; no hand-edited coordinates.")
    w("% ==================================================================")
    w(C.PALETTE)
    w(f"""\\begin{{tikzpicture}}[
  x=1cm, y=1cm, line cap=round, line join=round,
  tick/.style={{font=\\scriptsize, text=fwMute, inner sep=1pt}},
  alab/.style={{font=\\scriptsize, text=fwInk!80, inner sep=0}},
  axis/.style={{draw=fwHair, line width=0.4pt}},
  mk/.style={{draw=fwHair, line width=0.4pt}},
  run/.style={{draw=fwBlue, line width=0.3pt, draw opacity=0.10}},
  coredge/.style={{draw=fwBlue!45}},
  corfill/.style={{draw=fwBlue!7}},
  Afill/.style={{fill=fwOchre, fill opacity=0.18}},
  Aedge/.style={{draw=fwOchre, line width=0.4pt}},
  st/.style={{fill=fwOchre, draw=none}},
  ceil/.style={{draw=fwBlue, line width=0.5pt, dash pattern=on 2pt off 1.2pt}},
  wp/.style={{draw=fwInk!70, fill=white, line width=0.4pt}},
  wpl/.style={{font=\\scriptsize, text=fwMute, inner sep=1pt}},
  key/.style={{font=\\scriptsize, text=fwInk!80, inner sep=1pt, align=left}},
]""")
    # ---- top view
    wcm = 2 * rho * k
    pe = [0.0] + [p[1] for p in W]
    pn = [0.0] + [p[0] for p in W]
    w("% ---------------- top view")
    w(f"\\begin{{scope}}[shift={{({C.num(cx, 4)},{C.num(cy, 4)})}}, x={C.num(k, 5)}cm, y={C.num(k, 5)}cm]")
    w(f"  \\draw[axis] ({ex[0]},{ny[1]}) -- ({ex[0]},{ny[0]}) -- ({ex[1]},{ny[0]});")
    for v in range(-2, 3):
        lab = f"{v}\\,m" if v == 2 else f"${v}$"
        w(f"  \\draw[mk] ({v},{ny[0]}) -- ++(0,-0.06cm) node[tick, anchor=north] {{{lab}}};")
    for v in range(-1, 2):
        lab = f"{v}\\,m" if v == 1 else f"${v}$"
        w(f"  \\draw[mk] ({ex[0]},{v}) -- ++(-0.06cm,0) node[tick, anchor=east] {{{lab}}};")
    corridor = " -- ".join(f"({C.num(e)},{C.num(nn)})" for e, nn in zip(pe, pn))
    w(f"  % corridor: the path (takeoff point, w0..w7) stroked {2 * rho:g} m wide, round caps and joins")
    w(f"  \\draw[coredge, line width={C.num(wcm + 0.03, 4)}cm] {corridor};")
    w(f"  \\draw[corfill, line width={C.num(wcm - 0.01, 4)}cm] {corridor};")
    bn, be = box["north"], box["east"]
    w("  % takeoff box")
    w(f"  \\fill[Afill] ({be[0]},{bn[0]}) rectangle ({be[1]},{bn[1]});")
    w(f"  \\draw[Aedge] ({be[0]},{bn[0]}) rectangle ({be[1]},{bn[1]});")
    w(f"  % {n} trajectories (east, north)")
    for e, nn in top:
        w("  \\draw[run] plot coordinates {" + " ".join(f"({C.num(x)},{C.num(y)})" for x, y in zip(e, nn)) + "};")
    w(f"  % {n} starts")
    w("  " + " ".join(f"\\fill[st] ({C.num(p[1])},{C.num(p[0])}) circle (0.28pt);" for p in starts))
    seen = {}
    for i, (nn, e, d) in enumerate(W):
        seen.setdefault((nn, e), []).append(i)
    for (nn, e), ids in seen.items():
        w(f"  \\draw[wp] ({C.num(e)},{C.num(nn)}) circle (0.055cm);")
    for (nn, e), ids in seen.items():
        name = ", ".join(f"w_{i}" for i in ids)
        if nn == 0 and e == 0:
            # in the notch right of the box, where the corridors of the crossing legs part
            w(f"  \\node[wpl, anchor=west] at ({C.num(box['east'][1] + 0.2)},0) {{${name}$}};")
            continue
        # toward the center of the waypoint's lobe (east +-1.25, north 0): inside the loop
        dx, dy = math.copysign(1.25, e) - e, -nn
        L = math.hypot(dx, dy)
        dx, dy = dx / L, dy / L
        anchor = {(1, 0): "west", (-1, 0): "east", (0, 1): "south", (0, -1): "north"}[(round(dx), round(dy))]
        w(f"  \\node[wpl, anchor={anchor}] at ({C.num(e + 0.09 * dx)},{C.num(nn + 0.09 * dy)}) {{${name}$}};")
    # direct labels inside the two lobes, and A at the box
    w("  % labels")
    w(f"  \\draw[draw=fwBlue, line width=0.5pt, draw opacity=0.6] (-1.62,0.42) -- ++(0.36,0);")
    w(f"  \\node[key, anchor=north, align=center] at (-1.25,0.30) {{{n} starts,\\\\[-1pt]Lean and C++\\\\[-1pt]identical}};")
    w(f"  \\draw[coredge, line width=0.2cm, line cap=butt] (1.30,0.25) -- ++(0.36,0);")
    w(f"  \\draw[corfill, line width=0.17cm, line cap=butt] (1.30,0.25) -- ++(0.36,0);")
    w(f"  \\node[key, anchor=north, align=center] at (1.48,0.09) {{corridor,\\\\[-1pt]{C.num(rho)}\\,m}};")
    w(f"  \\node[key, text=fwOchre!85!black, anchor=east] at ({C.num(be[0] - 0.02)},0) {{$A$}};")
    w("\\end{scope}")
    w(f"\\node[alab, anchor=north] at ({C.num(cx)},{C.num(TOP_Y0 - 0.33)}) {{east}};")
    w(f"\\node[alab, rotate=90, anchor=south] at (0.420,{C.num(cy)}) {{north}};")

    # ---- altitude panel
    w("% ---------------- altitude against distance along the path")
    w(f"\\begin{{scope}}[shift={{({C.num(bx0, 4)},{BOT_Y0})}}, x={C.num(kx, 5)}cm, y={C.num(ky, 5)}cm]")
    w(f"  \\draw[axis] ({dmin},{amax}) -- ({dmin},0) -- ({dmax},0);")
    for v in range(0, dmax + 1, 2):
        lab = f"{v}\\,m" if v == dmax else f"${v}$"
        w(f"  \\draw[mk] ({v},0) -- ++(0,-0.06cm) node[tick, anchor=north] {{{lab}}};")
    for v, lab in [(0, "$0$"), (1, "$1$"), (2, "2\\,m")]:
        w(f"  \\draw[mk] ({dmin},{v}) -- ++(-0.06cm,0) node[tick, anchor=east] {{{lab}}};")
    side_path = " -- ".join(f"({C.num(s)},{C.num(-p[2])})" for s, p in zip(sV, V))
    w(f"  % corridor: the path's altitude profile stroked {2 * rho:g} m wide (altitude scale), clipped at the ground")
    w("  \\begin{scope}")
    w(f"    \\clip ({dmin},0) rectangle ({dmax},{amax});")
    w(f"    \\draw[coredge, line width={C.num(2 * rho * ky + 0.03, 4)}cm] {side_path};")
    w(f"    \\draw[corfill, line width={C.num(2 * rho * ky - 0.01, 4)}cm] {side_path};")
    w("  \\end{scope}")
    w("  % takeoff box at the takeoff point")
    w(f"  \\fill[Afill] ({bn[0]},{-box['down'][1]}) rectangle ({bn[1]},{-box['down'][0]});")
    w(f"  \\draw[Aedge] ({bn[0]},{-box['down'][1]}) rectangle ({bn[1]},{-box['down'][0]});")
    w(f"  % ceiling {ceil_m:g} m")
    w(f"  \\draw[ceil] ({dmin},{ceil_m}) -- ({dmax},{ceil_m});")
    w(f"  \\node[wpl, anchor=south east] at ({dmax},{ceil_m}) {{ceiling}};")
    w(f"  % {n} trajectories (distance along the path, altitude)")
    for s, alt in side:
        w("  \\draw[run] plot coordinates {" + " ".join(f"({C.num(x)},{C.num(y)})" for x, y in zip(s, alt)) + "};")
    half = rho * ky / kx            # the corridor stroke's half-width in distance units
    for i, p in enumerate(W):
        si = sV[i + 1]
        w(f"  \\draw[wp] ({C.num(si)},{C.num(-p[2])}) circle (0.055cm);")
    for i, p in enumerate(W):
        si = sV[i + 1]
        if i == 0:
            w(f"  \\node[wpl, anchor=north west] at ({C.num(half + 0.1)},{C.num(-p[2] - 0.1)}) {{$w_{i}$}};")
        elif i == len(W) - 1:
            w(f"  \\node[wpl, anchor=west] at ({C.num(si + half + 0.1)},{C.num(-p[2])}) {{$w_{i}$}};")
        else:
            w(f"  \\node[wpl, anchor=north] at ({C.num(si)},{C.num(-p[2] - rho - 0.06)}) {{$w_{i}$}};")
    w("\\end{scope}")
    w(f"\\node[alab, anchor=north] at ({C.num((X0 + X1) / 2)},0.220) {{distance along the path}};")
    w(f"\\node[alab, rotate=90, anchor=south] at (0.420,{C.num(BOT_Y0 + BOT_H / 2)}) {{altitude}};")
    w("\\end{tikzpicture}%")
    dst = Path(args.out) / "montecarlo-paths.tex"
    dst.write_text("\n".join(out) + "\n")
    print(f"{dst}: {n} trajectories, positions equal for the two vehicles; passes {passed[0]}/{n} lean, "
          f"{passed[1]}/{len(ref)} ref; max altitude {max_alt:.4f} m; max distance to the path after the box "
          f"{max_cor * 100:.2f} cm; {dst.stat().st_size} bytes")


if __name__ == "__main__":
    main()
