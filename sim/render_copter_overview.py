#!/usr/bin/env python3
"""Overview figure: the stroboscopic flight of the Lean ArduCopter port with the contract's sets drawn
in its scene.

The script flies the 1 m/s figure-eight course with the compiled binary exactly as
render_copter_strobe.py does (`render_copter_strobe.fly_and_capture`, hence `run_copter.fly`: 400 Hz
control, 1200 Hz physics, the copter protocol), renders the instants with the same camera machinery
(PyBullet tiny renderer, supersampled, differenced against the empty scene) and composites them over
a hairline floor grid, with no text in the image. It then projects, through the same camera, the sets
of the contract and writes them as TikZ paths in centimeters, with the image's lower left corner at
the origin and its width equal to --width-cm:

  * A, the assumption: a 0.4 m x 0.4 m x 0.3 m box on the floor around the takeoff point
    (its silhouette and its twelve edges);
  * G, the guarantee: a ceiling at 2.0 m over the floor grid (the course volume, with its four
    vertical edges) and a corridor of radius 0.25 m around the planned path (takeoff to the first
    waypoint, then the waypoints in order). The corridor is the union, for every path sample, of a
    circle of radius 0.25 m in the plane normal to the path (and of a sphere at every vertex);
    its projection is rasterized and its outline traced, so the self-crossing of the figure eight
    and the holes inside the lobes come out exactly.

It then checks containment twice: in the world (the distance of every flown position, 400 Hz, from
the planned path, against the corridor radius) and in the image (vehicle pixels of every instant,
mesh drawn --scale times its size, outside the corridor's image). Neither check changes the radius.

Outputs (in --out, default out/copter-overview): strobe.png (the composite, --dpi, --width-cm wide),
sets.tex (the TikZ paths and named coordinates), overlay.png (the projected sets painted over the
composite, to check the alignment), flight.csv and motors.txt of the run.

    .venv/bin/python render_copter_overview.py --dpi 150 --supersample 1      # quick look
    .venv/bin/python render_copter_overview.py                                 # 600 dpi, 4x supersampling
"""
from __future__ import annotations

import argparse
import math
import shutil
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw
from scipy.spatial import ConvexHull

import render_copter_strobe as rs
import run_copter as rc

SIM_DIR = Path(__file__).resolve().parent
R_CORRIDOR = 0.25                              # corridor radius, m
CEIL = 2.0                                     # ceiling, m
A_LO, A_HI = np.array([-0.2, -0.2, 0.0]), np.array([0.2, 0.2, 0.3])   # assumption box (ENU, m)


# --------------------------------------------------------------------------------------------
# Geometry of the sets


def planned_path(wps_enu):
    """Takeoff point on the floor under the first waypoint, then the waypoints in order."""
    start = np.array([wps_enu[0, 0], wps_enu[0, 1], 0.0])
    return np.vstack([start, wps_enu])


def frame(u):
    """Two unit vectors orthogonal to u and to each other."""
    a = np.array([0.0, 0.0, 1.0]) if abs(u[2]) < 0.9 else np.array([1.0, 0.0, 0.0])
    e1 = np.cross(u, a); e1 /= np.linalg.norm(e1)
    return e1, np.cross(u, e1)


def corridor_pieces(path, r, step=0.04, n_circ=72):
    """Point sets whose convex hulls, projected and united, give the corridor's image."""
    th = np.linspace(0, 2 * np.pi, n_circ, endpoint=False)
    pieces = []
    for a, b in zip(path[:-1], path[1:]):
        L = np.linalg.norm(b - a)
        u = (b - a) / L
        e1, e2 = frame(u)
        ring = r * (np.cos(th)[:, None] * e1 + np.sin(th)[:, None] * e2)
        ss = np.linspace(0, 1, max(2, int(math.ceil(L / step)) + 1))
        rings = [a + s * (b - a) + ring for s in ss]
        for c0, c1 in zip(rings[:-1], rings[1:]):
            pieces.append(np.vstack([c0, c1]))
    # a sphere at every vertex closes the joints
    n = 400
    i = np.arange(n) + 0.5
    phi = np.arccos(1 - 2 * i / n); lam = np.pi * (1 + 5 ** 0.5) * i
    sph = r * np.stack([np.cos(lam) * np.sin(phi), np.sin(lam) * np.sin(phi), np.cos(phi)], axis=1)
    for v in path:
        pieces.append(v + sph)
    return pieces


def distance_to_path(pts, path):
    """Distance of every point (N x 3) from the polyline path."""
    d = np.full(len(pts), np.inf)
    for a, b in zip(path[:-1], path[1:]):
        u = b - a
        t = np.clip(((pts - a) @ u) / (u @ u), 0.0, 1.0)
        d = np.minimum(d, np.linalg.norm(pts - (a + t[:, None] * u), axis=1))
    return d


def box_corners(lo, hi):
    return np.array([(x, y, z) for z in (lo[2], hi[2]) for y in (lo[1], hi[1]) for x in (lo[0], hi[0])])


BOX_EDGES = [(0, 1), (2, 3), (4, 5), (6, 7), (0, 2), (1, 3), (4, 6), (5, 7), (0, 4), (1, 5), (2, 6), (3, 7)]


def hull2d(p):
    h = ConvexHull(p)
    return p[h.vertices]


def rdp(pts, eps):
    """Douglas-Peucker simplification of an open polyline."""
    if len(pts) < 3:
        return pts
    a, b = pts[0], pts[-1]
    ab = b - a
    n = np.hypot(*ab)
    if n == 0:
        d = np.hypot(*(pts - a).T)
    else:
        d = np.abs(ab[0] * (pts[:, 1] - a[1]) - ab[1] * (pts[:, 0] - a[0])) / n
    i = int(np.argmax(d))
    if d[i] > eps:
        return np.vstack([rdp(pts[: i + 1], eps)[:-1], rdp(pts[i:], eps)])
    return np.vstack([a, b])


def outline(mask: np.ndarray, eps_px: float):
    """Closed outlines (pixel coordinates x, y) of a binary mask, simplified."""
    import contourpy
    z = np.pad(mask.astype(float), 2)
    lines = contourpy.contour_generator(z=z).lines(0.5)
    out = []
    for ln in lines:
        ln = ln - 2.0
        if len(ln) < 8:
            continue
        if not np.allclose(ln[0], ln[-1]):
            ln = np.vstack([ln, ln[:1]])
        # split the closed loop in two halves so the simplification keeps both ends
        h = len(ln) // 2
        s = np.vstack([rdp(ln[: h + 1], eps_px)[:-1], rdp(ln[h:], eps_px)[:-1]])
        out.append(s)
    return out


# --------------------------------------------------------------------------------------------
# Composite


def context(draw, cam, path_enu, wps_enu, k, fade_drop=0.35):
    """Floor grid, waypoint drop lines and the flown path (muted), through the camera."""
    (x0, y0), (x1, y1) = rs.floor_bounds(wps_enu)
    for v in np.arange(x0, x1 + 1e-9, rs.GRID):
        w = rs.px(0.4 if abs(v - x0) < 1e-9 or abs(v - x1) < 1e-9 else 0.25, k)
        draw.line([tuple(p) for p in cam.project([(v, y0, 0), (v, y1, 0)])], fill=rs.HAIR, width=w)
    for v in np.arange(y0, y1 + 1e-9, rs.GRID):
        w = rs.px(0.4 if abs(v - y0) < 1e-9 or abs(v - y1) < 1e-9 else 0.25, k)
        draw.line([tuple(p) for p in cam.project([(x0, v, 0), (x1, v, 0)])], fill=rs.HAIR, width=w)
    mute = rs.toward_white(rs.MUTE, fade_drop)
    r = rs.DPI / 300.0
    for wp in wps_enu[1:-1]:
        rs.dashed(draw, cam.project([wp, (wp[0], wp[1], 0.0)]), mute, rs.px(0.3, k),
                  9 * rs.SS * k * 1.5 * r, 7 * rs.SS * k * 1.5 * r)
    draw.line([tuple(p) for p in cam.project(path_enu)], fill=rs.toward_white(rs.INK, 0.45),
              width=rs.px(0.35, k), joint="curve")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin", default=str(rc.DEFAULT_BIN))
    ap.add_argument("--params", action="append", default=None, metavar="FILE",
                    help="parameter files (default: copter-cf2x.txt, copter-course-speed.txt)")
    ap.add_argument("--ref", action="append", default=None, metavar="FILE",
                    help="motors.txt to compare the actuator stream with (repeatable)")
    ap.add_argument("--every", type=float, default=0.5)
    ap.add_argument("--scale", type=float, default=3.0)
    ap.add_argument("--dpi", type=int, default=600)
    ap.add_argument("--supersample", type=int, default=4)
    ap.add_argument("--width-cm", type=float, default=8.2)
    ap.add_argument("--aspect", type=float, default=1.5, help="render aspect w/h (wider than the strobe's "
                    "1.2 so that the ceiling fits; the vertical field of view is unchanged)")
    ap.add_argument("--duration", type=float, default=60.0)
    ap.add_argument("--pyb-hz", type=int, default=1200)
    ap.add_argument("--cam-dist", type=float, default=10.2)
    ap.add_argument("--cam-yaw", type=float, default=17.0)
    ap.add_argument("--cam-pitch", type=float, default=-34.0)
    ap.add_argument("--out", default=str(SIM_DIR / "out" / "copter-overview"))
    ap.add_argument("--copy-to", default=None, help="also copy strobe.png here under this file name")
    args = ap.parse_args()
    rs.DPI = args.dpi
    out = Path(args.out); out.mkdir(parents=True, exist_ok=True)

    params = args.params or [str(f) for f in rs.DEFAULT_PARAMS]
    run, poses, mission = rs.fly_and_capture(args.every, Path(args.bin), params, args.duration, args.pyb_hz)
    rc.write_outputs(out, run)
    print(f"run: {run.end_reason}; {len(run.rows)} ticks; {len(poses)} instants")
    rs.compare_motors(run, args.ref or rs.DEFAULT_REFS)

    width_px = int(round(args.width_cm / 2.54 * args.dpi))
    ss, W, H = rs.pick_supersample(width_px, args.aspect, args.supersample, 1.3)
    rs.SS = ss
    print(f"supersample {ss}: renders {W} x {H}")
    rows, path_enu, wps_enu = rs.path_and_waypoints(run, mission)
    lo, hi = rs.floor_bounds(wps_enu)
    target = ((lo[0] + hi[0]) / 2, (lo[1] + hi[1]) / 2, wps_enu[:, 2].max() / 2)
    cam = rs.Camera(W, H, target, args.cam_dist, args.cam_yaw, args.cam_pitch)

    # --- world check: flown positions against the corridor
    plan = planned_path(wps_enu)
    dist = distance_to_path(path_enu, plan)
    j = int(np.argmax(dist))
    print(f"flown path vs planned path: max distance {dist.max() * 100:.2f} cm at t = {rows[j, 0]:.4f} s "
          f"(ENU {path_enu[j, 0]:.3f} {path_enu[j, 1]:.3f} {path_enu[j, 2]:.3f}); corridor radius "
          f"{R_CORRIDOR * 100:.0f} cm; {int((dist > R_CORRIDOR).sum())} of {len(dist)} ticks outside")

    # --- sets, in render pixels
    floor3 = np.array(rs.floor_corners(wps_enu), float)
    ceil3 = floor3.copy(); ceil3[:, 2] = CEIL
    floor2, ceil2 = cam.project(floor3), cam.project(ceil3)
    pieces2 = [hull2d(cam.project(p)) for p in corridor_pieces(plan, R_CORRIDOR)]
    abox3 = box_corners(A_LO, A_HI)
    abox2 = cam.project(abox3)

    layers = rs.render_frames(poses, cam, args.scale)
    ticks = np.array([p for _, p, _ in poses])

    allp = np.vstack([floor2, ceil2, np.vstack(pieces2), abox2])
    boxes = np.array([l.box for l in layers])
    x0 = min(boxes[:, 0].min(), allp[:, 0].min()); x1 = max(boxes[:, 2].max(), allp[:, 0].max())
    y0 = min(boxes[:, 1].min(), allp[:, 1].min()); y1 = max(boxes[:, 3].max(), allp[:, 1].max())
    m = 0.006 * (x1 - x0)
    box = [int(x0 - m), int(y0 - m), int(math.ceil(x1 + m)), int(math.ceil(y1 + m))]
    if box[0] < 0 or box[1] < 0 or box[2] > cam.w or box[3] > cam.h:
        raise SystemExit(f"content box {box} leaves the {cam.w} x {cam.h} render")
    k = (box[2] - box[0]) / (width_px * ss)

    canvas = Image.new("RGB", (cam.w, cam.h), (255, 255, 255))
    context(ImageDraw.Draw(canvas), cam, path_enu, wps_enu, k)
    base = np.asarray(canvas, np.float32).copy()
    n = len(layers)
    for i, layer in enumerate(layers):
        rs.over(base, layer, 0.32 + 0.68 * (i / (n - 1)) ** 1.2)
    img = Image.fromarray(np.clip(base, 0, 255).astype(np.uint8)).crop(box)
    h_px = int(round(width_px * img.height / img.width))
    img = img.resize((width_px, h_px), Image.LANCZOS)
    img.save(out / "strobe.png", dpi=(args.dpi, args.dpi))
    bw = box[2] - box[0]
    cm_per = args.width_cm / bw
    height_cm = (box[3] - box[1]) * cm_per
    print(f"strobe.png: {width_px} x {h_px} px ({args.width_cm:.2f} x {height_cm:.3f} cm)")

    def cm(p):
        p = np.atleast_2d(p)
        return np.stack([(p[:, 0] - box[0]) * cm_per, (box[3] - p[:, 1]) * cm_per], axis=1)

    def path_tex(p, close=True):
        s = " -- ".join(f"({x:.3f},{y:.3f})" for x, y in cm(p))
        return s + (" -- cycle" if close else "")

    # --- corridor outline: rasterize the union of the hulls at four times the final resolution
    f = 4.0 * width_px / bw
    mw, mh = int(math.ceil(bw * f)), int(math.ceil((box[3] - box[1]) * f))
    mimg = Image.new("L", (mw, mh), 0)
    md = ImageDraw.Draw(mimg)
    for h in pieces2:
        md.polygon([((x - box[0]) * f, (y - box[1]) * f) for x, y in h], fill=255)
    mask = np.asarray(mimg) > 127
    loops = [np.stack([l[:, 0] / f + box[0], l[:, 1] / f + box[1]], axis=1) for l in outline(mask, 1.0)]
    print(f"corridor: {len(loops)} outline loops, {sum(len(l) for l in loops)} vertices")

    L = []
    L.append(f"% generated by sim/render_copter_overview.py; image {args.width_cm:.2f} x {height_cm:.3f} cm, "
             f"origin at its lower left")
    L.append(f"% image height {height_cm:.3f}")
    L.append("% ceilfill\n\\fill[Cfill] " + path_tex(ceil2) + ";")
    posts = " ".join(f"({a[0]:.3f},{a[1]:.3f}) -- ({b[0]:.3f},{b[1]:.3f})" for a, b in zip(cm(floor2), cm(ceil2)))
    L.append("% ceilposts\n\\draw[Cpost] " + posts + ";")
    L.append("% ceiledge\n\\draw[Cedge] " + path_tex(ceil2) + ";")
    L.append("% corridorfill\n\\fill[Tfill, even odd rule] " + " ".join(path_tex(l) for l in loops) + ";")
    L.append("% corridoredge\n\\draw[Tedge] " + " ".join(path_tex(l) for l in loops) + ";")
    L.append("% Afill\n\\fill[Afill] " + path_tex(hull2d(abox2)) + ";")
    ac = cm(abox2)
    L.append("% Aedge\n\\draw[Aedge] " + " ".join(
        f"({ac[i][0]:.3f},{ac[i][1]:.3f}) -- ({ac[j][0]:.3f},{ac[j][1]:.3f})" for i, j in BOX_EDGES) + ";")
    names = []
    for (t, _, _), p in zip(poses, cm(cam.project(ticks))):
        names.append(f"\\coordinate (v{int(round(t * 10)):03d}) at ({p[0]:.3f},{p[1]:.3f});")
    for i, p in enumerate(cm(cam.project(wps_enu))):
        names.append(f"\\coordinate (wp{i}) at ({p[0]:.3f},{p[1]:.3f});")
    for nm, p in zip(["ce0", "ce1", "ce2", "ce3"], cm(ceil2)):
        names.append(f"\\coordinate ({nm}) at ({p[0]:.3f},{p[1]:.3f});")
    for nm, p in zip(["fl0", "fl1", "fl2", "fl3"], cm(floor2)):
        names.append(f"\\coordinate ({nm}) at ({p[0]:.3f},{p[1]:.3f});")
    for i, p in enumerate(ac):
        names.append(f"\\coordinate (a{i}) at ({p[0]:.3f},{p[1]:.3f});")
    L.append("% coordinates")
    L.extend(names)
    (out / "sets.tex").write_text("\n".join(L) + "\n")

    # --- overlay check: the projected sets painted over the composite
    ov = img.convert("RGBA")
    lay = Image.new("RGBA", ov.size, (0, 0, 0, 0))
    d = ImageDraw.Draw(lay)
    s = width_px / bw

    def tp(p):
        return [((x - box[0]) * s, (y - box[1]) * s) for x, y in p]
    d.polygon(tp(ceil2), fill=(30, 63, 124, 20), outline=(30, 63, 124, 200))
    for l in loops:
        d.line(tp(l) + tp(l[:1]), fill=(192, 65, 43, 255), width=max(1, int(args.dpi / 300)))
    d.polygon(tp(hull2d(abox2)), fill=(196, 134, 15, 60), outline=(196, 134, 15, 255))
    for p in tp(cam.project(ticks)):
        d.ellipse([p[0] - 3, p[1] - 3, p[0] + 3, p[1] + 3], fill=(192, 65, 43, 255))
    Image.alpha_composite(ov, lay).convert("RGB").save(out / "overlay.png", dpi=(args.dpi, args.dpi))

    # --- containment check in pixels: vehicle pixels outside the corridor's image
    outside = 0; total = 0; worst = []
    for layer in layers:
        X0, Y0, X1, Y1 = layer.box
        ys, xs = np.nonzero(layer.alpha > 0.5)
        mx = ((xs + X0 - box[0]) * f).astype(int); my = ((ys + Y0 - box[1]) * f).astype(int)
        ok = (mx >= 0) & (my >= 0) & (mx < mw) & (my < mh)
        inside = np.zeros(len(xs), bool); inside[ok] = mask[my[ok], mx[ok]]
        o = int((~inside).sum())
        if o:
            worst.append((layer.t, o, len(xs)))
        outside += o; total += len(xs)
    print(f"vehicle pixels outside the corridor's image: {outside} of {total} "
          f"({100 * outside / max(1, total):.2f} %)")
    for t, o, nn in worst:
        print(f"  t = {t:5.2f} s: {o} of {nn} pixels outside")
    if args.copy_to:
        shutil.copy(out / "strobe.png", args.copy_to)
        print(f"copied to {args.copy_to}")


if __name__ == "__main__":
    main()
