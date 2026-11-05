#!/usr/bin/env python3
"""montecarlo-3d.tex: the 200 Monte Carlo trajectories of the course contract (sim/out/montecarlo) in
perspective, through the overview's camera (render_overview.py: yaw 17, pitch -34, distance 10.2 m,
the target and field of view of render_strobe.Camera), with an enlarged inset of the takeoff region
and the spread of the set against time computed for the header comment and the caption (not drawn).

The projection is render_strobe.Camera's (PyBullet's view and projection matrices applied in numpy);
every point is projected here and written as 2D TikZ coordinates in centimeters.

Spread: at each tick, the largest distance over the runs from the run's position to the nominal flown
path (sim/out/lean-course-1ms, the ground start at the origin, which lies in the box A), a geometric
measure. The runs reach w0 at different times (up to 0.32 s apart) and then fly the same path shifted
in time, so the distance between their positions at the same tick stays near 10 cm until the final
hover; the distance to a common path is what shrinks.

    sim/.venv/bin/python sim/figs/make_montecarlo_3d.py [--mc DIR] [--out DIR]
"""
from __future__ import annotations

import argparse
import csv
import gzip
import json
import math
from pathlib import Path

import numpy as np
from scipy.spatial import cKDTree

import common as C
import render_strobe as rs

MC = C.OUT / "montecarlo"
N_PTS = 150                    # points per trajectory in the main view
N_PTS_INSET = 120              # points per climb in the inset
WIDTH = 4.6                    # cm, the 3D scene; the inset fills the rest of the 8.2 cm column
INSET_W, GAP, INSET_H_MAX = 3.3, 0.3, 4.7   # cm
CAM = dict(dist=10.2, yaw=17.0, pitch=-34.0, aspect=1.5)   # render_overview.py's defaults
INSET_HW0, INSET_Z = 0.26, (0.0, 0.9)   # ENU m: the box and the climb to w0; the half-width grows to fit
STRIP_T = 6.0                  # s
HEAD_LEN = 0.03                # heading tick length in the inset, m


def read_run(path: Path) -> np.ndarray:
    with gzip.open(path, "rt") as f:
        rows = list(csv.reader(f))[1:]
    return np.array([[float(r[1]), float(r[2]), float(r[3])] for r in rows])


def ned_to_enu(p):
    p = np.asarray(p, float)
    return np.stack([p[..., 1], p[..., 0], -p[..., 2]], axis=-1)


def coords(pts, nd=3):
    return " ".join(f"({C.num(x, nd)},{C.num(y, nd)})" for x, y in pts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mc", default=str(MC))
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    mc = Path(args.mc)
    spec = json.loads((C.SIM / "spec" / "mission-course.json").read_text())
    rows = list(csv.DictReader(open(mc / "summary.csv")))
    lean = sorted((r for r in rows if r["vehicle"] == "copter_lean"), key=lambda r: int(r["index"]))
    n = len(lean)
    if any(int(r["differing_ticks"]) for r in lean):
        raise SystemExit("some paired runs differ; this figure draws one set for both vehicles")
    runs = []
    for r in lean:
        i = int(r["index"])
        a, b = read_run(mc / "runs" / f"lean-{i:03d}.csv.gz"), read_run(mc / "runs" / f"ref-{i:03d}.csv.gz")
        if not np.array_equal(a, b):
            raise SystemExit(f"sample {i}: the two vehicles' positions differ")
        runs.append(a)
    passed = sum(int(r["verdict"]) for r in rows)
    heads = np.array([float(r["heading_rad"]) for r in lean])
    hz = spec["tick_hz"]
    rho, ceil_m, r_m = spec["corridor_radius_m"], spec["ceiling_m"], spec["r_m"]
    W = ned_to_enu(spec["waypoints_ned_m"])
    V = ned_to_enu(spec["path_ned_m"])
    box = spec["box_ned_m"]
    blo = np.array([box["east"][0], box["north"][0], -box["down"][1]])
    bhi = np.array([box["east"][1], box["north"][1], -box["down"][0]])

    # ---------------- spread: distance of every position to the nominal flown path
    nom = C.load_flight(C.run_dir("lean"))
    nomp = np.stack([nom["x_n"], nom["y_e"], nom["z_d"]], axis=1)
    seg = np.linalg.norm(np.diff(nomp, axis=0), axis=1)
    dense = [nomp[:1]]
    for a, b, L in zip(nomp[:-1], nomp[1:], seg):                 # 0.1 mm spacing
        k = max(1, int(math.ceil(L / 1e-4)))
        dense.append(a + (b - a) * (np.arange(1, k + 1) / k)[:, None])
    tree = cKDTree(np.vstack(dense))
    m_strip = int(STRIP_T * hz) + 1
    G = np.stack([tree.query(x[:m_strip])[0] for x in runs])         # runs x ticks
    spread = G.max(axis=0)
    ts = np.arange(m_strip) / hz
    def first_below(thr):
        return float(ts[int(np.argmax(spread < thr))])
    def stays_below(thr):
        above = np.nonzero(spread >= thr)[0]
        return float(ts[above[-1] + 1]) if len(above) else 0.0
    t1cm, t1mm = first_below(0.01), first_below(0.001)
    s1cm, s1mm = stays_below(0.01), stays_below(0.001)
    starts = np.array([x[0] for x in runs])
    diam0 = max(np.linalg.norm(starts - p, axis=1).max() for p in starts)
    w0_t = [float(r["reach0_s"]) for r in lean]

    # ---------------- camera
    lo, hi = rs.floor_bounds(W)
    target = ((lo[0] + hi[0]) / 2, (lo[1] + hi[1]) / 2, W[:, 2].max() / 2)
    cam = rs.Camera(1500, int(round(1500 / CAM["aspect"])), target, CAM["dist"], CAM["yaw"], CAM["pitch"])
    view = np.array(cam.view).reshape(4, 4).T
    eye = -view[:3, :3].T @ view[:3, 3]
    floor = np.array(rs.floor_corners(W), float)
    ceil_front = floor.copy(); ceil_front[:, 2] = ceil_m
    # the near ceiling edge: the floor edge nearest the eye
    edges = [(0, 1), (1, 2), (2, 3), (3, 0)]
    near = min(edges, key=lambda e: np.linalg.norm((floor[e[0]] + floor[e[1]]) / 2 - eye))
    enu_runs = [ned_to_enu(x) for x in runs]
    px_all = np.vstack([cam.project(floor), cam.project(ceil_front[list(near)])]
                       + [cam.project(x[::40]) for x in enu_runs])
    x0p, y0p = px_all[:, 0].min(), px_all[:, 1].max()
    k = WIDTH * 0.985 / (px_all[:, 0].max() - x0p)
    pad = WIDTH * 0.0075
    def P(pts):
        """Main-view centimeters (x right, y up) of ENU points."""
        q = cam.project(pts)
        return np.stack([(q[:, 0] - x0p) * k + pad, (y0p - q[:, 1]) * k + pad], axis=1)
    main_h = (y0p - px_all[:, 1].min()) * k + 2 * pad
    # bottom row below the main view
    # inset: the takeoff region, widened until a INSET_W wide panel is at most INSET_H_MAX tall
    hw = INSET_HW0
    while True:
        reg = np.array([[x, y, z] for x in (-hw, hw) for y in (-hw, hw) for z in INSET_Z])
        rp = P(reg)
        r0, r1 = rp.min(axis=0), rp.max(axis=0)
        INSET_SCALE = INSET_W / (r1 - r0)[0]
        if (r1 - r0)[1] * INSET_SCALE <= INSET_H_MAX:
            break
        hw += 0.01
    INSET_REGION = ((-hw, hw), (-hw, hw), INSET_Z)
    iw, ih = (r1 - r0) * INSET_SCALE
    ix0 = WIDTH + GAP
    iy0 = main_h - ih                                                  # tops aligned
    def I(pts):
        return (P(pts) - r0) * INSET_SCALE + np.array([ix0, iy0])

    def corridor_pieces(Q, s_extra=1.0, step=0.25):
        """(points, width cm) pieces along the path, the width the cylinder's apparent diameter."""
        out = []
        for a, b in zip(V[:-1], V[1:]):
            L = np.linalg.norm(b - a); u = (b - a) / L
            m = max(1, int(math.ceil(L / step)))
            for j in range(m):
                p0, p1 = a + (b - a) * j / m, a + (b - a) * (j + 1) / m
                mid = (p0 + p1) / 2
                nrm = np.cross(u, mid - eye); nrm /= np.linalg.norm(nrm)
                w = np.linalg.norm(Q(np.array([mid + rho * nrm]))[0] - Q(np.array([mid - rho * nrm]))[0])
                out.append((Q(np.array([p0, p1])), w))
        return out

    out = []
    w = out.append
    w("% ==================================================================")
    w("%  Monte Carlo flights in perspective -- one sigconf text width (8.2 cm),")
    w("%  pdfLaTeX, plain TikZ (no pgfplots; coordinates are embedded)")
    w(f"%  Data:      cpp2lean {C.rel(mc / 'runs')}/<lean|ref>-<i>.csv.gz and summary.csv")
    w(f"%             (sim/montecarlo.py): {n} starts uniform in the takeoff box A with a")
    w("%             uniform heading, each")
    w("%             flown by copter_lean (the Lean translations of ArduPilot's classes)")
    w("%             and copter_ref (ArduPilot's classes compiled unmodified) on the 1 m/s")
    w("%             figure-eight course with the tuned gains; the two vehicles' positions")
    w(f"%             are equal on every tick (checked by the script), so one set of {n} is")
    w(f"%             drawn; the contract holds on {passed} of {len(rows)} runs.")
    w(f"%  Camera:    render_overview.py's (yaw {CAM['yaw']:g}, pitch {CAM['pitch']:g}, distance {CAM['dist']:g} m, field of")
    w(f"%             view {rs.CAM_FOV:g} deg, aspect {CAM['aspect']:g}), projected by the script; floor grid of")
    w(f"%             {rs.GRID:g} m, the ceiling's near edge at {ceil_m:g} m, the corridor as the planned path")
    w(f"%             (takeoff point, w0..w7) stroked at the apparent diameter of a {rho:g} m")
    w("%             cylinder (in 0.25 m pieces, so it narrows with depth), A in ochre,")
    w(f"%             the trajectories thinned to {N_PTS} points (largest-triangle-three-buckets).")
    w(f"%  Inset:     the takeoff region (east and north {INSET_REGION[0]} m, up {INSET_REGION[2]} m)")
    w(f"%             through the same camera, enlarged {INSET_SCALE:.1f} times; the climbs from tick 0 to")
    w(f"%             0.25 s after reaching w0 (w0 reached at {min(w0_t):.4f} to {max(w0_t):.4f} s), {N_PTS_INSET} points each, and")
    w(f"%             the starts as dots with a {HEAD_LEN * 100:g} cm tick toward the initial heading (uniform in")
    w("%             [-180, 180) deg, heading_rad of summary.csv).")
    w("%  Spread:    (not drawn) at each tick the largest distance over the runs")
    w("%             from the run's position to the nominal flown path (sim/out/lean-course-1ms,")
    w("%             the ground start at the origin, in A), log scale, 0 to 6 s. Initial")
    w(f"%             {spread[0] * 100:.2f} cm; first below 1 cm at {t1cm:.4f} s (below for good from {s1cm:.4f} s),")
    w(f"%             first below 1 mm at {t1mm:.4f} s (below from {s1mm:.4f} s, up to the final hover).")
    w(f"%             Largest distance between two starts {diam0 * 100:.2f} cm. The distance between")
    w("%             runs at the same tick does not shrink so: they reach w0 up to")
    w(f"%             {max(w0_t) - min(w0_t):.2f} s apart and then fly the same path shifted in time.")
    w("%  Generated by cpp2lean sim/figs/make_montecarlo_3d.py; no hand-edited coordinates.")
    w("% ==================================================================")
    w(C.PALETTE)
    w("""\\begin{tikzpicture}[
  x=1cm, y=1cm, line cap=round, line join=round,
  tick/.style={font=\\scriptsize, text=fwMute, inner sep=1pt},
  lab/.style={font=\\scriptsize, text=fwInk!85, inner sep=1pt},
  grid/.style={draw=fwHair!70, line width=0.25pt},
  ceil/.style={draw=fwBlue!45, line width=0.35pt, dash pattern=on 1.6pt off 1.2pt},
  coredge/.style={draw=fwBlue!40},
  corfill/.style={draw=fwBlue!8},
  run/.style={draw=fwBlue, line width=0.25pt, draw opacity=0.10},
  Afill/.style={fill=fwOchre, fill opacity=0.18},
  Aedge/.style={draw=fwOchre, line width=0.35pt},
  st/.style={fill=fwOchre, draw=none},
  hd/.style={draw=fwOchre!80!black, line width=0.3pt, draw opacity=0.75},
  wp/.style={draw=fwInk!70, fill=white, line width=0.35pt},
  frame/.style={draw=fwMute, line width=0.35pt},
  axis/.style={draw=fwHair, line width=0.4pt},
  mk/.style={draw=fwHair, line width=0.4pt},
  spr/.style={draw=fwBlue, line width=0.6pt},
  ref/.style={draw=fwMute, line width=0.3pt, dash pattern=on 1.2pt off 1pt},
]""")

    def scene(Q, pieces, run_pts, dot_r, wp_r, lw_scale, with_grid=True, clip=None, heads=None):
        if clip is not None:
            w("\\begin{scope}")
            w(f"  \\clip ({C.num(clip[0])},{C.num(clip[1])}) rectangle ({C.num(clip[2])},{C.num(clip[3])});")
        if with_grid:
            (gx0, gy0), (gx1, gy1) = lo, hi
            segs = [((v, gy0, 0), (v, gy1, 0)) for v in np.arange(gx0, gx1 + 1e-9, rs.GRID)]
            segs += [((gx0, v, 0), (gx1, v, 0)) for v in np.arange(gy0, gy1 + 1e-9, rs.GRID)]
            w("  \\draw[grid] " + " ".join(coords(Q(np.array(sg))).replace(") (", ") -- (") for sg in segs) + ";")
        w("  % corridor")
        for style, dw in (("coredge", 0.03), ("corfill", -0.012)):
            w("  " + " ".join(f"\\draw[{style}, line width={C.num(max(0.01, wd + dw), 4)}cm] "
                               f"{coords(p).replace(') (', ') -- (')};" for p, wd in pieces))
        bc = np.array([(x, y, z) for z in (blo[2], bhi[2]) for y in (blo[1], bhi[1]) for x in (blo[0], bhi[0])])
        bq = Q(bc)
        from scipy.spatial import ConvexHull
        h = ConvexHull(bq)
        w("  \\fill[Afill] " + " -- ".join(f"({C.num(x)},{C.num(y)})" for x, y in bq[h.vertices]) + " -- cycle;")
        be = [(0, 1), (2, 3), (4, 5), (6, 7), (0, 2), (1, 3), (4, 6), (5, 7), (0, 4), (1, 5), (2, 6), (3, 7)]
        w("  \\draw[Aedge] " + " ".join(f"({C.num(bq[i][0])},{C.num(bq[i][1])}) -- ({C.num(bq[j][0])},{C.num(bq[j][1])})"
                                         for i, j in be) + ";")
        w(f"  % {len(run_pts)} trajectories")
        for pts in run_pts:
            w(f"  \\draw[run, line width={C.num(0.25 * lw_scale, 3)}pt] plot coordinates {{{coords(pts)}}};")
        if heads is not None:
            # heading ticks: from each start along its initial nose direction (heading from north, clockwise)
            st0 = np.array([e[0] for e in enu_runs])
            tip = st0 + HEAD_LEN * np.stack([np.sin(heads), np.cos(heads), np.zeros(len(heads))], axis=1)
            a_, b_ = Q(st0), Q(tip)
            w("  \\draw[hd] " + " ".join(f"({C.num(p0[0])},{C.num(p0[1])}) -- ({C.num(p1[0])},{C.num(p1[1])})"
                                         for p0, p1 in zip(a_, b_)) + ";")
        if dot_r:
            w("  " + " ".join(f"\\fill[st] ({C.num(x)},{C.num(y)}) circle ({dot_r}pt);" for x, y in Q(np.array([e[0] for e in enu_runs]))))
        seen = set()
        for p in W:
            key = tuple(np.round(p, 6))
            if key in seen:
                continue
            seen.add(key)
            q = Q(p[None])[0]
            w(f"  \\draw[wp] ({C.num(q[0])},{C.num(q[1])}) circle ({wp_r}cm);")
        if clip is not None:
            w("\\end{scope}")

    # ---------------- main view
    w("% ---------------- main view")
    main_runs = []
    for x in enu_runs:
        q = P(x)
        main_runs.append(q[C.lttb(q, N_PTS)])
    scene(P, corridor_pieces(P), main_runs, 0, 0.045, 1.0)
    # region marker and leads to the inset
    w(f"\\draw[frame] ({C.num(r0[0])},{C.num(r0[1])}) rectangle ({C.num(r1[0])},{C.num(r1[1])});")
    w(f"\\draw[frame, draw opacity=0.6] ({C.num(r1[0])},{C.num(r1[1])}) -- ({C.num(ix0)},{C.num(iy0 + ih)});")
    w(f"\\draw[frame, draw opacity=0.6] ({C.num(r1[0])},{C.num(r0[1])}) -- ({C.num(ix0)},{C.num(iy0)});")

    # ---------------- inset
    w(f"% ---------------- inset: the takeoff region, {INSET_SCALE:g} times")
    w(f"\\fill[white] ({C.num(ix0)},{C.num(iy0)}) rectangle ({C.num(ix0 + iw)},{C.num(iy0 + ih)});")
    inset_runs = []
    for x, tw in zip(enu_runs, w0_t):
        m = int(round((tw + 0.25) * hz)) + 1
        q = I(x[:m])
        inset_runs.append(q[C.lttb(q, N_PTS_INSET)])
    scene(I, corridor_pieces(I, step=0.05), inset_runs, 0.45, 0.07, 1.6,
          clip=(ix0, iy0, ix0 + iw, iy0 + ih), heads=heads)
    w(f"\\draw[frame] ({C.num(ix0)},{C.num(iy0)}) rectangle ({C.num(ix0 + iw)},{C.num(iy0 + ih)});")
    a_lab = I(np.array([[blo[0], blo[1], 0.0]]))[0]
    w0q = I(W[:1])[0]
    w(f"\\node[lab, text=fwOchre!85!black, anchor=north east] at ({C.num(a_lab[0] - 0.05)},{C.num(a_lab[1] + 0.02)}) {{$A$}};")
    w(f"\\node[lab, anchor=east] at ({C.num(w0q[0] - 0.12)},{C.num(w0q[1])}) {{$w_0$}};")
    w(f"\\node[tick, anchor=north west] at ({C.num(ix0 + 0.03)},{C.num(iy0 + ih - 0.03)}) {{${INSET_SCALE:.1f}\\times$}};")
    w(f"\\node[lab, text=fwBlue!80, anchor=north west, align=left] at ({C.num(ix0 + 0.06)},{C.num(iy0 + ih - 0.42)}) "
      f"{{corridor\\\\[-1pt]{rho:g}\\,m}};")

    # ---------------- text under the scene (the free space left of the inset)
    top = max(float(r["max_alt_m"]) for r in lean)
    w(f"\\node[lab, anchor=south west, align=left] at (0,{C.num(iy0 + 0.02)}) {{{n} starts in $A$, any heading;\\\\[-1pt]"
      f"all in the corridor, highest {top:.2f}\\,m;\\\\[-1pt]Lean and C++ identical}};")
    w("\\end{tikzpicture}%")
    w("% Suggested caption: The 200 Monte Carlo flights in perspective, through the overview's camera. Every start")
    w("% lies in the takeoff box A, with a uniform heading (ticks in the inset); every trajectory stays in the")
    w(f"% {rho:g} m corridor and under the {ceil_m:g} m ceiling (highest point {top:.2f} m), and the Lean and C++ vehicles")
    w(f"% fly identical trajectories. Inset: the takeoff region enlarged {INSET_SCALE:.1f} times; the climbs converge")
    w(f"% into w0 within the corridor (farthest run from the nominal path below 1 cm from t = {s1cm:.2f} s).")
    dst = Path(args.out) / "montecarlo-3d.tex"
    dst.write_text("\n".join(out) + "\n")
    print(f"{dst}: {n} trajectories; spread initial {spread[0] * 100:.2f} cm, first < 1 cm at {t1cm:.4f} s "
          f"(stays from {s1cm:.4f} s), first < 1 mm at {t1mm:.4f} s (stays from {s1mm:.4f} s); start diameter "
          f"{diam0 * 100:.2f} cm; inset {INSET_SCALE:.2f}x, {iw:.2f} x {ih:.2f} cm; main {WIDTH} x {main_h:.2f} cm; "
          f"{dst.stat().st_size} bytes")


if __name__ == "__main__":
    main()
