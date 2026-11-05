#!/usr/bin/env python3
"""Overview figure: the stroboscopic flight of copter_lean with the contract's sets drawn in its scene.

Port of render_copter_overview.py of the delegate-port worktree (the earlier hand-written Lean port)
to this project. The script re-flies the 1 m/s figure-eight course with copter_lean exactly as
render_strobe.py does (`render_strobe.fly_and_capture`, hence sim/run_copter.py's `fly`: 400 Hz
control, 1200 Hz physics, the protocol of sim/PROTOCOL.md), checks the re-flown actuator and state
lines against the recorded flights (sim/out/lean-course-1ms, sim/out/ref-course-1ms), renders the
instants with the same camera machinery (PyBullet tiny renderer, supersampled, differenced against
the empty scene) and composites them over a hairline floor grid, with no text in the image. It then
projects, through the same camera, the sets of the contract and writes them as TikZ paths in
centimeters, with the image's lower left corner at the origin and its width equal to --width-cm:

  * A, the assumption: the takeoff box of sim/spec/mission-course.json (box_ned_m, 0.3 x 0.3 x
    0.3 m on the floor around the takeoff point), its silhouette and its twelve edges;
  * G, the guarantee: a ceiling (ceiling_m, 2.0 m) over the floor grid (the course volume, with its
    four vertical edges) and a corridor (corridor_radius_m, 0.25 m) around the planned path
    (path_ned_m: the takeoff point, then the waypoints in order). The corridor is the union, for
    every path sample, of a circle of that radius in the plane normal to the path (and of a sphere
    at every vertex);
    its projection is rasterized and its outline traced, so the self-crossing of the figure eight
    and the holes inside the lobes come out exactly.

It checks containment twice: in the world (the distance of every flown position, 400 Hz, from the
planned path, against the corridor radius) and in the image (vehicle pixels of every instant, mesh
drawn --scale times its size, outside the corridor's image). Neither check changes the radius.

Outputs: in --work (default sim/figs/out/overview): strobe.png, sets.tex, overlay.png (the projected
sets painted over the composite, to check the alignment), flight.csv, inputs.txt, motors.txt,
check.txt; in --out (default the staging figs folder): overview-D-strobe.png and overview-D.tex.

    sim/.venv/bin/python sim/figs/render_overview.py --dpi 150 --supersample 1 --out /tmp/x   # quick look
    sim/.venv/bin/python sim/figs/render_overview.py                                          # 600 dpi, 4x
"""
from __future__ import annotations

import argparse
import json
import math
import re
import shutil
from pathlib import Path

import numpy as np
from PIL import Image, ImageDraw
from scipy.spatial import ConvexHull

import common as C
import render_strobe as rs

# The sets come from the contract's spec, so the figure and the monitor cannot drift apart.
SPEC = json.loads((C.SIM / "spec" / "mission-course.json").read_text())
R_CORRIDOR = SPEC["corridor_radius_m"]          # corridor radius, m
CEIL = SPEC["ceiling_m"]                        # ceiling, m
_B = SPEC["box_ned_m"]                          # assumption box, NED -> ENU (east, north, up), m
A_LO = np.array([_B["east"][0], _B["north"][0], -_B["down"][1]])
A_HI = np.array([_B["east"][1], _B["north"][1], -_B["down"][0]])
PATH_ENU = np.array([[e, n, -d] for n, e, d in SPEC["path_ned_m"]])
# the code card quotes the integrator update of AC_PID::update_i in the translated code
PID_LEAN = C.ROOT / "ardupilot" / "out" / "AC_PID" / "AC_PID_lib.lean"


# --------------------------------------------------------------------------------------------
# Geometry of the sets


def planned_path(wps_enu):
    """The spec's path (path_ned_m): the takeoff point on the floor, then the waypoints in order;
    checked against the flown mission's waypoints."""
    if not np.allclose(PATH_ENU[1:], wps_enu, atol=1e-12):
        raise SystemExit("the spec's path does not pass through the mission's waypoints")
    return PATH_ENU.copy()


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


# --------------------------------------------------------------------------------------------
# The code card


def integrator_line():
    """The integrator update inside AC_PID's update_i in the translated code: (line number, text)."""
    lines = PID_LEAN.read_text().splitlines()
    start = next(i for i, ln in enumerate(lines) if ln.startswith("def update_i (p : Params) (s : State) (dt : Float32) (limit : Bool)"))
    for i in range(start, len(lines)):
        if "_integrator := s._integrator +" in lines[i]:
            return i + 1, lines[i].strip(), lines[start - 1].strip()
        if lines[i].strip() == "return s":
            break
    raise SystemExit("integrator update not found in update_i")


def lean_tex(code: str) -> str:
    """One line of Lean in the card's colors: keywords, operators, everything else as names."""
    toks = re.findall(r":=|[{}()+*]|[A-Za-z_][A-Za-z0-9_.]*|\s+|.", code)
    out = []
    for t in toks:
        if t in ("with", "let", "if", "then", "else", "do", "return"):
            out.append(f"\\textcolor{{LeanKeyword}}{{{t}}}")
        elif t in (":=", "+", "*"):
            out.append(f"\\textcolor{{LeanOperator}}{{{t}}}")
        elif t in ("{", "}"):
            out.append(f"\\textcolor{{LeanOperator}}{{\\{t}}}")
        elif t.isspace():
            out.append(" ")
        else:
            out.append(t.replace("_", "\\_"))
    return "".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin", default=str(C.BINARIES["lean"]))
    ap.add_argument("--every", type=float, default=0.5)
    ap.add_argument("--climb", type=float, default=0.05, help="as in render_strobe.py")
    ap.add_argument("--hover-tol", type=float, default=0.1, help="as in render_strobe.py")
    ap.add_argument("--scale", type=float, default=2.2, help="drawing scale of the vehicle mesh (default 2.2)")
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
    ap.add_argument("--work", default=str(C.FIGS / "out" / "overview"))
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    rs.DPI = args.dpi
    work, dst = Path(args.work), Path(args.out)
    work.mkdir(parents=True, exist_ok=True)

    run, all_poses, mission, cmd = rs.fly_and_capture(Path(args.bin), rs.DEFAULT_PARAMS, args.duration, args.pyb_hz)
    rc = rs.rc
    rc.write_outputs(work, run)
    check = [f"re-flight: {' '.join(cmd)}", f"end: {run.end_reason}; {len(run.rows)} ticks"]
    check += rs.compare_recorded(run)
    ndiff = sum(int(ln.split(" lines, ")[1].split()[0]) for ln in check[2:])
    rows, path_enu, wps_enu = rs.path_and_waypoints(run, mission)
    poses = rs.select_instants(all_poses, wps_enu, args.every, None if args.climb < 0 else args.climb,
                               args.hover_tol)
    check.append(f"{len(poses)} instants, t = " + " ".join(f"{t:g}" for t, _, _ in poses))
    print("\n".join(check), flush=True)
    if ndiff:
        (work / "check.txt").write_text("\n".join(check) + "\n")
        raise SystemExit("the re-flight differs from the recorded flights")

    width_px = int(round(args.width_cm / 2.54 * args.dpi))
    ss, W, H = rs.pick_supersample(width_px, args.aspect, args.supersample, 1.3)
    rs.SS = ss
    print(f"supersample {ss}: renders {W} x {H}", flush=True)
    lo, hi = rs.floor_bounds(wps_enu)
    target = ((lo[0] + hi[0]) / 2, (lo[1] + hi[1]) / 2, wps_enu[:, 2].max() / 2)
    cam = rs.Camera(W, H, target, args.cam_dist, args.cam_yaw, args.cam_pitch)

    # --- world check: flown positions against the corridor
    plan = planned_path(wps_enu)
    dist = distance_to_path(path_enu, plan)
    j = int(np.argmax(dist))
    world = (f"flown path vs planned path: max distance {dist.max() * 100:.2f} cm at t = {rows[j, 0]:.4f} s "
             f"(ENU {path_enu[j, 0]:.3f} {path_enu[j, 1]:.3f} {path_enu[j, 2]:.3f}); corridor radius "
             f"{R_CORRIDOR * 100:.0f} cm; {int((dist > R_CORRIDOR).sum())} of {len(dist)} ticks outside")
    check.append(world)
    print(world, flush=True)

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
    img.save(work / "strobe.png", dpi=(args.dpi, args.dpi))
    bw = box[2] - box[0]
    cm_per = args.width_cm / bw
    height_cm = (box[3] - box[1]) * cm_per
    check.append(f"strobe.png: {width_px} x {h_px} px ({args.width_cm:.2f} x {height_cm:.3f} cm), supersample {ss}")

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
    check.append(f"corridor: {len(loops)} outline loops, {sum(len(l) for l in loops)} vertices")

    sets = []
    sets.append("% ---------------- G: ceiling at 2.0 m over the floor, corridor of 0.25 m ----------------")
    sets.append("\\fill[Cfill] " + path_tex(ceil2) + ";")
    posts = " ".join(f"({a[0]:.3f},{a[1]:.3f}) -- ({b[0]:.3f},{b[1]:.3f})" for a, b in zip(cm(floor2), cm(ceil2)))
    sets.append("\\draw[Cpost] " + posts + ";")
    sets.append("\\draw[Cedge] " + path_tex(ceil2) + ";")
    sets.append("\\fill[Tfill, even odd rule] " + " ".join(path_tex(l) for l in loops) + ";")
    sets.append("\\draw[Tedge] " + " ".join(path_tex(l) for l in loops) + ";")
    sets.append("% ---------------- A: box around the takeoff point ----------------")
    sets.append("\\fill[Afill] " + path_tex(hull2d(abox2)) + ";")
    ac = cm(abox2)
    sets.append("\\draw[Aedge] " + " ".join(
        f"({ac[i][0]:.3f},{ac[i][1]:.3f}) -- ({ac[j][0]:.3f},{ac[j][1]:.3f})" for i, j in BOX_EDGES) + ";")
    names = []
    for (t, _, _), p in zip(poses, cm(cam.project(ticks))):
        names.append(f"\\coordinate (v{int(round(t * 10000)):06d}) at ({p[0]:.3f},{p[1]:.3f});")
    for i, p in enumerate(cm(cam.project(wps_enu))):
        names.append(f"\\coordinate (wp{i}) at ({p[0]:.3f},{p[1]:.3f});")
    for nm, p in zip(["ce0", "ce1", "ce2", "ce3"], cm(ceil2)):
        names.append(f"\\coordinate ({nm}) at ({p[0]:.3f},{p[1]:.3f});")
    for nm, p in zip(["fl0", "fl1", "fl2", "fl3"], cm(floor2)):
        names.append(f"\\coordinate ({nm}) at ({p[0]:.3f},{p[1]:.3f});")
    for i, p in enumerate(ac):
        names.append(f"\\coordinate (a{i}) at ({p[0]:.3f},{p[1]:.3f});")
    (work / "sets.tex").write_text("\n".join(names + sets) + "\n")

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
    Image.alpha_composite(ov, lay).convert("RGB").save(work / "overlay.png", dpi=(args.dpi, args.dpi))

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
    pix = (f"vehicle pixels outside the corridor's image: {outside} of {total} "
           f"({100 * outside / max(1, total):.2f} %)")
    check.append(pix)
    for t, o, nn in worst:
        check.append(f"  t = {t:5.2f} s: {o} of {nn} pixels outside")
    (work / "check.txt").write_text("\n".join(check) + "\n")
    shutil.copy(work / "strobe.png", dst / "overview-D-strobe.png")
    print("\n".join(check[-(2 + len(worst)):]), flush=True)

    # --- overview-D.tex
    line_no, code, doc = integrator_line()
    head, tail = code.split(" + ", 1)
    total_fmt = f"{total:,}".replace(",", " ")
    T = []
    w = T.append
    w("% ==================================================================")
    w("%  Overview -- the contract drawn in the flight's own scene")
    w("%  one sigconf text width (8.2 cm), pdfLaTeX")
    w("%  Preamble:  \\usepackage{tikz}  \\usetikzlibrary{arrows.meta,calc}")
    w("%             \\usepackage{graphicx}, overview-D-strobe.png on the graphics path")
    w(f"%  Image:     overview-D-strobe.png ({args.width_cm:.2f} x {height_cm:.3f} cm, {args.dpi} dpi, no text), the")
    w(f"%             stroboscopic composite (instants every {args.every:g} s from t = {poses[0][0]:g} s,")
    w(f"%             the first instant {args.climb * 100:g} cm above the start, to {poses[-2][0]:g} s, plus one")
    w(f"%             instant at the final hover, t = {poses[-1][0]:g} s: {len(poses)} in all; vehicle mesh")
    w(f"%             at {args.scale:g} times its size; {ss}x supersampled, PyBullet")
    w(f"%             ER_TINY_RENDERER, camera yaw {args.cam_yaw:g}, pitch {args.cam_pitch:g}, distance {args.cam_dist:g} m) of")
    w("%             the 1 m/s figure-eight course flown by copter_lean (the Lean")
    w("%             translations of ArduPilot's classes, cpp2lean")
    w("%             lean/.lake/build/bin/copter_lean) with the tuned gains (params")
    w("%             copter-cf2x.txt + copter-course-speed.txt + copter-cf2x-tuned.txt,")
    w("%             400 Hz control, 1200 Hz physics), re-flown through sim/run_copter.py")
    w("%             and made by cpp2lean sim/figs/render_overview.py, which also wrote")
    w("%             every coordinate and path below (sim/figs/out/overview/sets.tex).")
    w("%             The re-flown actuator and state lines equal the recorded ones,")
    for ln in check[2:6]:
        w("%               " + ln)
    dims = " x ".join(f"{h - l:g}" for l, h in zip(A_LO, A_HI))
    w(f"%             Over the image, through the same camera, the sets of the spec")
    w(f"%             sim/spec/mission-course.json: A, a {dims} m box around the")
    w(f"%             takeoff point (north and east {_B['north']}, down {_B['down']} m); G, a")
    w(f"%             ceiling at {CEIL:g} m over the floor and a corridor of radius {R_CORRIDOR:g} m around")
    w("%             the planned path (takeoff point, then the waypoints in order). Containment,")
    w(f"%             checked by the script at {args.dpi} dpi: every flown position (400 Hz)")
    w(f"%             lies within {dist.max() * 100:.2f} cm of the planned path (at t = {rows[j, 0]:.4f} s),")
    w(f"%             and {outside} of {total_fmt} vehicle pixels lie outside the corridor's image.")
    w(f"%  Code card: {C.rel(PID_LEAN)} line {line_no}, the")
    w("%             integrator update inside update_i (" + doc.replace("/-- ", "").replace(" -/", "").rstrip(".") + "),")
    w("%             verbatim, broken after the \"+\"; s._integrator, s._error,")
    w("%             p._ki, i_scale and dt are Float32.")
    w("%  Layout:    the labels, cards and binary sit at fixed offsets from the")
    w("%             projected coordinates (A from a3, G from wp3, M from a4) and from")
    w("%             each other; the generator writes them.")
    w("% ==================================================================")
    w(C.PALETTE.replace("{C4860F}%", "{C4860F}%   assumptions").replace("{1E3F7C}%", "{1E3F7C}%    guarantees"))
    w("% Lean syntax colors")
    w("\\definecolor{LeanKeyword}{HTML}{B5301E}%")
    w("\\definecolor{LeanDecl}{HTML}{5B2DB8}%")
    w("\\definecolor{LeanOperator}{HTML}{383A42}%")
    w("\\definecolor{LeanType}{HTML}{0E7490}%")
    w("\\definecolor{LeanName}{HTML}{1F2328}%")
    w("""\\begin{tikzpicture}[
  x=1cm, y=1cm, line cap=round, line join=round,
  >={Stealth[length=1.5mm, width=1.25mm]},
  tick/.style={font=\\scriptsize, text=fwMute, inner sep=1pt},
  fwcap/.style={font=\\footnotesize, text=fwInk, inner sep=0},
  verb/.style={font=\\scriptsize\\itshape, text=fwMute, inner sep=0.6pt},
  lbl/.style={font=\\footnotesize, inner sep=0.8pt},
  up/.style={draw=fwMute, line width=0.45pt, -{Stealth[length=1.3mm, width=1.05mm]}},
  lead/.style={draw=fwMute, line width=0.3pt},
  card/.style={draw=fwHair, line width=0.4pt, fill=white},
  Cfill/.style={fill=fwBlue, fill opacity=0.08},
  Cedge/.style={draw=fwBlue!70, line width=0.3pt},
  Cpost/.style={draw=fwBlue!45, line width=0.3pt},
  Tfill/.style={fill=fwBlue, fill opacity=0.10},
  Tedge/.style={draw=fwBlue, line width=0.4pt},
  Afill/.style={fill=fwOchre, fill opacity=0.18},
  Aedge/.style={draw=fwOchre, line width=0.3pt},
]
% ---------------- the flight (image origin at its lower left) ----------------
\\node[anchor=south west, inner sep=0] (img) at (0,0)""")
    w(f"  {{\\includegraphics[width={args.width_cm:g}cm]{{overview-D-strobe.png}}}};")
    T.extend(names)
    T.extend(sets)
    w("""% ---------------- labels in the scene ----------------
\\node[lbl, text=fwOchre!85!black, anchor=west] (Alab) at ($(a3)+(0.10,-0.17)$) {$A$};
\\node[lbl, text=fwBlue, anchor=north] (Glab) at ($(wp3)+(0.55,-0.30)$) {$G$};
\\node[lbl, text=fwInk, anchor=north east] (Mlab) at ($(a4)+(-0.32,0.02)$) {$M$};
\\draw[lead] (Mlab.north east) -- ($(wp0)+(-0.10,-0.06)$);
% ---------------- code, compile, binary ----------------
\\node[card, anchor=south west, inner sep=2pt, align=left, text=LeanName,
      font=\\tiny\\ttfamily, execute at begin node={\\baselineskip=6pt}]
  (code) at (0.04,0.22)""")
    w("  {" + lean_tex(head + " +") + "\\\\")
    w("   \\ \\ " + lean_tex(tail) + "};")
    w("""\\begin{scope}[shift={($(code.east)+(0.75,-0.15)$)}]
  \\draw[fill=white, draw=fwInk!70, line width=0.45pt] (0,0) rectangle (0.5,0.3);
  \\draw[fwInk!45, line width=0.4pt] (0.08,0.22) -- (0.34,0.22);
  \\draw[fwInk!45, line width=0.4pt] (0.08,0.15) -- (0.42,0.15);
  \\draw[fwInk!45, line width=0.4pt] (0.08,0.08) -- (0.27,0.08);
  \\coordinate (bin) at (0.25,0.3);
  \\coordinate (binW) at (0,0.15);
  \\coordinate (binE) at (0.5,0.15);
\\end{scope}
\\draw[up] (code.east |- binW) -- (binW);
\\node[verb, anchor=south] at ($(code.east |- binW)!0.5!(binW)+(0,0.03)$) {compile};
\\draw[up] (bin) -- ($(a1)+(-0.10,-0.10)$);
\\draw[lead] ($(code.north)+(0.55,0)$) -- (Mlab.south west);
\\node[verb, anchor=east] at ($($(code.north)+(0.55,0)$)!0.5!(Mlab.south west)+(-0.04,0.02)$) {lift};
% ---------------- formula card ----------------
\\node[card, anchor=west, inner sep=2.2pt, font=\\footnotesize] (spec) at ($(binE)+(0.30,0)$)
  {$(\\textcolor{fwOchre!88!black}{\\varphi},\\,\\textcolor{fwBlue}{\\psi})$};
\\draw[lead] ($(spec.north west)+(0.26,0)$) -- (Alab.south);
\\draw[lead] ($(spec.north east)+(-0.26,0)$) -- (Glab.south);
\\end{tikzpicture}%""")
    (dst / "overview-D.tex").write_text("\n".join(T) + "\n")
    print(f"code card: {C.rel(PID_LEAN)} line {line_no}: {code}")
    print(f"wrote {dst / 'overview-D-strobe.png'} and {dst / 'overview-D.tex'}")


if __name__ == "__main__":
    main()
