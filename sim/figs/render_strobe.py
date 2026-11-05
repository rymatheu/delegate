#!/usr/bin/env python3
"""Stroboscopic time lapse and filmstrip of the 1 m/s figure-eight course flown by copter_lean.

Port of render_copter_strobe.py of the delegate-port worktree (the earlier hand-written Lean port)
to this project: the camera, instants rule, compositing and image sizes are those of that script;
the flight goes through this project's driver, sim/run_copter.py.

The script flies the course headless exactly as `run_copter.py --backend bin --bin copter_lean`
does (sim/fly.sh, mission course-1ms): it calls `run_copter.fly`, so the lock-step loop of
sim/PROTOCOL.md, the 17-number input line, the actuator-to-RPM conversion, 400 Hz control and
1200 Hz physics, gravity 9.80665, the damping removal and the settling on the ground are those of the
recorded flights. The vehicle pose is taken from the simulator at every tick of the run's clock. The
re-flown actuator lines and state lines are compared with the recorded ones (sim/out/lean-course-1ms
and sim/out/ref-course-1ms, motors.txt and inputs.txt) line by line; the script stops if any differ.

Instants (`select_instants`): from the first tick at which the vehicle has climbed 5 cm above its
starting height, every 0.5 s until it arrives at the last waypoint (first within 0.1 m after its last
tick more than 0.5 m from it), plus the last captured tick (one instant at the final hover).

Rendering: PyBullet's software renderer (getCameraImage, ER_TINY_RENDERER, no GUI) in a render-only
client that holds the CF2X mesh and nothing else, from one fixed oblique camera (yaw 22, pitch -34,
distance 10.2 m, field of view 34 deg) aimed at the center of the course volume; vehicle pixels found
by differencing each frame against a render of the empty scene and composited in time order with
opacity rising toward the last instant, over a hairline floor grid (0.5 m), dashed drop lines at the
waypoints, the flown path and the waypoints, all drawn through the same camera. Mesh drawn --scale
times its size (3; 7 in the filmstrip). Everything rendered at --supersample times the output size and
shrunk with Lanczos. The images hold no text; the .tex wrappers carry the labels.

Outputs: in --work (default sim/figs/out/strobe): flight.csv, inputs.txt, motors.txt of the re-flight,
strobe.png, labels.txt, filmstrip.png, film-labels.txt, check.txt; in --out (default the staging figs
folder): flight-strobe.png, flight-strobe.tex, flight-filmstrip.png, flight-filmstrip.tex.

    sim/.venv/bin/python sim/figs/render_strobe.py                 # 600 dpi, 4x supersampling
    sim/.venv/bin/python sim/figs/render_strobe.py --dpi 150 --supersample 1 --out /tmp/x   # quick look
"""
from __future__ import annotations

import argparse
import math
import os
import shutil
import sys
from pathlib import Path
from types import SimpleNamespace

import numpy as np
from PIL import Image, ImageDraw

import common as C

sys.path.insert(0, str(C.SIM))
import run_copter as rc  # noqa: E402

DEFAULT_PARAMS = C.COURSE_PARAMS + [C.TUNED_PARAMS]
RECORDED = [C.run_dir("lean"), C.run_dir("ref")]
DPI = 600                                 # output resolution (--dpi)
SS = 4                                    # supersampling factor of every render and drawing (--supersample)

INK = (0x22, 0x25, 0x2A)
MUTE = (0x8A, 0x8F, 0x96)
HAIR = (0xC9, 0xCC, 0xD1)
OCHRE = (0xC4, 0x86, 0x0F)
BLUE = (0x1E, 0x3F, 0x7C)

CAM_FOV = 34.0                            # camera field of view, degrees (PyBullet ENU world)
GRID = 0.5                                # floor grid spacing, meters
FADE = 0.0                                # grid and drop lines blended toward white


def toward_white(c, f: float):
    return tuple(int(round(v + (255 - v) * f)) for v in c)


# --------------------------------------------------------------------------------------------
# Flight with pose capture


def fly_and_capture(bin_path: Path, params: list, duration: float, pyb_hz: int = 1200, hold: float = 3.0):
    """Fly the course with the bin backend through run_copter.fly; return the run, the poses at every
    tick on the run's clock (t, ENU position, quaternion xyzw), and the mission."""
    poses = []
    reset_env = rc.reset_env

    def reset_env_capturing(env):
        obs = reset_env(env)                        # reset, damping off, settling with motors off
        step = env.step
        tick = [0]

        def step_capturing(action):
            import pybullet as pb
            pos, quat = pb.getBasePositionAndOrientation(env.DRONE_IDS[0], physicsClientId=env.CLIENT)
            poses.append((tick[0] / rc.CTRL_HZ, np.array(pos), np.array(quat)))
            tick[0] += 1
            return step(action)

        env.step = step_capturing
        return obs

    files = [str(Path(f).resolve()) for f in params]
    ctrl_args = ["--exact"]
    for f in files:
        ctrl_args += ["--params", f]
    cmd, cwd = rc.backend_command("bin", bin_path, ctrl_args)
    mission = rc.effective_params(cmd, cwd, files, [])
    args = SimpleNamespace(gui=False, init_ned=None, init_euler=None, duration=duration, hold=hold,
                           tol=0.1, pass_tol=0.2, pyb_hz=pyb_hz, ground_timeout=3.0)
    rc.reset_env = reset_env_capturing
    try:
        run = rc.fly(args, cmd, cwd, mission)
    finally:
        rc.reset_env = reset_env
    return run, poses, mission, cmd


def compare_recorded(run, recorded=RECORDED) -> list[str]:
    """Line-by-line comparison of the re-flight's actuator and state lines with each recorded run."""
    lines = []
    for d in recorded:
        for name, mine in (("motors.txt", run.outputs), ("inputs.txt", run.inputs)):
            ref = (d / name).read_text().splitlines()
            diff = [i for i in range(max(len(ref), len(mine)))
                    if i >= len(ref) or i >= len(mine) or ref[i] != mine[i]]
            first = f" (first at line {diff[0] + 1})" if diff else ""
            lines.append(f"{name} vs {C.rel(d / name)}: {len(mine)} vs {len(ref)} lines, {len(diff)} differ{first}")
    return lines


def select_instants(poses, wps_enu, every_s: float, climb: float | None, hover_tol: float):
    """The strobe instants from poses captured at every tick.

    With `climb` None: every `every_s` seconds from t = 0. Otherwise: from the first tick at which the
    vehicle has climbed `climb` meters above its starting height, every `every_s` seconds after that
    until the vehicle arrives at the last waypoint, plus the last tick (one instant at the final
    hover). The vehicle arrives when it first comes within `hover_tol` meters of the last waypoint
    after its last tick more than 0.5 m from it (the first and last waypoints may coincide)."""
    step = int(round(every_s * rc.CTRL_HZ))
    if climb is None:
        return [ps for i, ps in enumerate(poses) if i % step == 0]
    z = np.array([p[2] for _, p, _ in poses])
    k0 = int(np.argmax(z - z[0] >= climb))
    d = np.array([np.linalg.norm(p - wps_enu[-1]) for _, p, _ in poses])
    on_course = np.nonzero(d > 0.5)[0]                    # last tick on the course, 0.5 m out
    j = int(on_course[-1]) + 1 if len(on_course) else 0
    arrived = np.nonzero(d[j:] <= hover_tol)[0]
    hover = j + int(arrived[0]) if len(arrived) else len(poses)
    picked = list(range(k0, hover, step))
    if not picked or picked[-1] != len(poses) - 1:
        picked.append(len(poses) - 1)
    return [poses[i] for i in picked]


def path_and_waypoints(run, mission):
    """Flown path and waypoints in PyBullet's ENU world."""
    rows = np.array([r[:4] for r in run.rows], float)        # t, n, e, d
    path_enu = np.stack([rows[:, 2], rows[:, 1], -rows[:, 3]], axis=1)
    wps_enu = np.array([(w[1], w[0], -w[2]) for w in mission["waypoints"]])
    return rows, path_enu, wps_enu


# --------------------------------------------------------------------------------------------
# Rendering


class Camera:
    def __init__(self, w: int, h: int, target, dist: float, yaw: float, pitch: float):
        import pybullet as pb
        self.w, self.h = w, h
        self.view = pb.computeViewMatrixFromYawPitchRoll(list(target), dist, yaw, pitch, 0, 2)
        self.proj = pb.computeProjectionMatrixFOV(CAM_FOV, w / h, 0.05, 30.0)
        self._m = np.array(self.proj).reshape(4, 4).T @ np.array(self.view).reshape(4, 4).T

    def project(self, pts):
        """Pixel coordinates (x right, y down) of world points (N x 3, ENU)."""
        pts = np.atleast_2d(np.asarray(pts, dtype=float))
        c = self._m @ np.hstack([pts, np.ones((len(pts), 1))]).T
        n = c[:3] / c[3]
        return np.stack([(n[0] + 1) / 2 * self.w, (1 - n[1]) / 2 * self.h], axis=1)


def render_rgb(pb, cam, client: int) -> np.ndarray:
    w, h, rgb, _, _ = pb.getCameraImage(cam.w, cam.h, cam.view, cam.proj, renderer=pb.ER_TINY_RENDERER,
                                        lightDirection=[-1.0, -2.0, 4.0], shadow=0, physicsClientId=client)
    if (w, h) != (cam.w, cam.h):
        raise RuntimeError(f"renderer returned {w} x {h} for {cam.w} x {cam.h}")
    return np.reshape(np.asarray(rgb, dtype=np.uint8), (h, w, 4))[:, :, :3].copy()


def renders_at(w: int, h: int) -> bool:
    """Whether the tiny renderer produces a w x h image."""
    import pybullet as pb
    client = pb.connect(pb.DIRECT)
    try:
        cam = SimpleNamespace(w=w, h=h, view=pb.computeViewMatrixFromYawPitchRoll([0, 0, 0], 5, 0, -30, 0, 2),
                              proj=pb.computeProjectionMatrixFOV(CAM_FOV, w / h, 0.05, 30.0))
        render_rgb(pb, cam, client)
        return True
    except Exception:
        return False
    finally:
        pb.disconnect(client)


class Layer:
    """The vehicle pixels of one frame: its bounding box origin, soft mask and colors."""

    def __init__(self, t, x0, y0, alpha, rgb):
        self.t, self.x0, self.y0, self.alpha, self.rgb = t, int(x0), int(y0), alpha, rgb

    @property
    def box(self):
        h, w = self.alpha.shape
        return self.x0, self.y0, self.x0 + w, self.y0 + h


def render_frames(poses, cam: Camera, scale: float):
    """Render the empty scene and one frame per pose; return the vehicle layers."""
    import gym_pybullet_drones
    import pybullet as pb
    client = pb.connect(pb.DIRECT)
    empty = render_rgb(pb, cam, client)
    urdf = os.path.join(os.path.dirname(gym_pybullet_drones.__file__), "assets", "cf2x.urdf")
    body = pb.loadURDF(urdf, [0, 0, 0], useFixedBase=True, globalScaling=scale, physicsClientId=client)
    for link in range(-1, pb.getNumJoints(body, physicsClientId=client)):
        pb.changeVisualShape(body, link, rgbaColor=[0.30, 0.32, 0.36, 1.0], physicsClientId=client)
    layers = []
    for t, pos, quat in poses:
        # The URDF base sits at the body origin; lift the scaled mesh so its landing gear stays on
        # the floor at t = 0 exactly as the true-size vehicle does.
        lift = np.array([0.0, 0.0, (scale - 1.0) * 0.0125 if pos[2] < 0.03 else 0.0])
        pb.resetBasePositionAndOrientation(body, (pos + lift).tolist(), quat.tolist(), physicsClientId=client)
        rgb = render_rgb(pb, cam, client)
        diff = np.abs(rgb.astype(np.int16) - empty.astype(np.int16)).max(axis=2)
        alpha = np.clip(diff / 24.0, 0.0, 1.0)      # soft edge from the difference image
        ys, xs = np.nonzero(alpha > 0)
        y0, y1, x0, x1 = ys.min(), ys.max() + 1, xs.min(), xs.max() + 1
        layers.append(Layer(t, x0, y0, alpha[y0:y1, x0:x1].astype(np.float32), rgb[y0:y1, x0:x1].copy()))
    pb.disconnect(client)
    return layers


# --------------------------------------------------------------------------------------------
# Composite


def px(pt: float, k: float) -> int:
    """Line width in supersampled pixels for pt points at the output resolution, before a shrink by k."""
    return max(1, int(round(pt / 72.0 * DPI * SS * k)))


def dashed(draw, xy, fill, width, on, off):
    xy = np.asarray(xy, float)
    for a, b in zip(xy[:-1], xy[1:]):
        L = float(np.hypot(*(b - a)))
        s = 0.0
        while s < L:
            e = min(L, s + on)
            draw.line([tuple(a + (b - a) * s / L), tuple(a + (b - a) * e / L)], fill=fill, width=width)
            s += on + off


def floor_bounds(wps_enu):
    """The waypoints' horizontal extent (ENU x, y), rounded out to the floor grid."""
    lo = np.floor(wps_enu[:, :2].min(axis=0) / GRID - 1e-9) * GRID
    hi = np.ceil(wps_enu[:, :2].max(axis=0) / GRID + 1e-9) * GRID
    return lo, hi


def floor_corners(wps_enu):
    (x0, y0), (x1, y1) = floor_bounds(wps_enu)
    return [(x0, y0, 0), (x1, y0, 0), (x1, y1, 0), (x0, y1, 0)]


def context(draw, cam: Camera, path_enu, wps_enu, k: float, until: int | None = None):
    """Floor grid, drop lines and the flown path, drawn through the camera."""
    (x0, y0), (x1, y1) = floor_bounds(wps_enu)
    hair, mute = toward_white(HAIR, FADE), toward_white(MUTE, FADE)
    for v in np.arange(x0, x1 + 1e-9, GRID):
        w = px(0.4 if abs(v - x0) < 1e-9 or abs(v - x1) < 1e-9 else 0.25, k)
        draw.line([tuple(p) for p in cam.project([(v, y0, 0), (v, y1, 0)])], fill=hair, width=w)
    for v in np.arange(y0, y1 + 1e-9, GRID):
        w = px(0.4 if abs(v - y0) < 1e-9 or abs(v - y1) < 1e-9 else 0.25, k)
        draw.line([tuple(p) for p in cam.project([(x0, v, 0), (x1, v, 0)])], fill=hair, width=w)
    for wp in wps_enu:
        r = DPI / 300.0                  # dash lengths were set at 300 dpi; keep them fixed in points
        dashed(draw, cam.project([wp, (wp[0], wp[1], 0.0)]), mute, px(0.3, k), 9 * SS * k * 1.5 * r,
               7 * SS * k * 1.5 * r)
    path = path_enu if until is None else path_enu[: until + 1]
    draw.line([tuple(p) for p in cam.project(path)], fill=BLUE, width=px(0.5, k), joint="curve")


def waypoint_marks(draw, cam: Camera, wps_enu, k: float, r_pt: float = 1.7):
    r = r_pt / 72 * DPI * SS * k
    for p in cam.project(wps_enu):
        draw.ellipse([p[0] - r, p[1] - r, p[0] + r, p[1] + r], outline=INK, fill=(255, 255, 255),
                     width=px(0.45, k))


def over(base: np.ndarray, layer: Layer, opacity: float) -> np.ndarray:
    """Alpha-composite one layer onto base (float H x W x 3) in place."""
    x0, y0, x1, y1 = layer.box
    a = (layer.alpha * opacity)[:, :, None]
    base[y0:y1, x0:x1] = base[y0:y1, x0:x1] * (1 - a) + layer.rgb * a
    return base


def composite(cam, layers, path_enu, wps_enu, width_px: int, out: Path, labels_out: Path, ticks):
    floor = cam.project(floor_corners(wps_enu))
    pts = np.vstack([cam.project(path_enu), floor])
    boxes = np.array([l.box for l in layers])
    x0 = min(boxes[:, 0].min(), pts[:, 0].min()); x1 = max(boxes[:, 2].max(), pts[:, 0].max())
    y0 = min(boxes[:, 1].min(), pts[:, 1].min()); y1 = max(boxes[:, 3].max(), pts[:, 1].max())
    m = 0.03 * (x1 - x0)
    box = [int(x0 - m), int(y0 - m), int(math.ceil(x1 + m)), int(math.ceil(y1 + m))]
    if box[0] < 0 or box[1] < 0 or box[2] > cam.w or box[3] > cam.h:
        raise SystemExit(f"content box {box} leaves the {cam.w} x {cam.h} render; adjust the camera")
    k = (box[2] - box[0]) / (width_px * SS)

    canvas = Image.new("RGB", (cam.w, cam.h), (255, 255, 255))
    context(ImageDraw.Draw(canvas), cam, path_enu, wps_enu, k)
    base = np.asarray(canvas, np.float32).copy()
    n = len(layers)
    for i, layer in enumerate(layers):
        over(base, layer, 0.22 + 0.78 * (i / (n - 1)) ** 1.2)
    img = Image.fromarray(np.clip(base, 0, 255).astype(np.uint8))
    waypoint_marks(ImageDraw.Draw(img), cam, wps_enu, k)
    img = img.crop(box)
    h_px = int(round(width_px * img.height / img.width))
    img = img.resize((width_px, h_px), Image.LANCZOS)
    img.save(out, dpi=(DPI, DPI))

    lines = ["# t_s  x_frac  y_frac  (vehicle center in the cropped image; y measured from the bottom)"]
    for layer, p in zip(layers, cam.project(ticks)):
        lines.append(f"{layer.t:.4f} {(p[0] - box[0]) / (box[2] - box[0]):.4f} "
                     f"{1 - (p[1] - box[1]) / (box[3] - box[1]):.4f}")
    for name, p in zip([f"wp{i}" for i in range(len(wps_enu))], cam.project(wps_enu)):
        lines.append(f"# {name} {(p[0] - box[0]) / (box[2] - box[0]):.4f} {1 - (p[1] - box[1]) / (box[3] - box[1]):.4f}")
    labels_out.write_text("\n".join(lines) + "\n")
    return box, img.size


def filmstrip(cam, layers, path_enu, wps_enu, times, rows_t, width_px: int, out: Path, labels_out: Path):
    """Six instants in a row, each the full view with the path flown so far and the vehicle; a blank
    strip under the tiles is left for the time labels, whose positions go to labels_out."""
    gap = int(round(0.06 / 2.54 * DPI))
    tile_w = (width_px - gap * (len(times) - 1)) // len(times)
    floor = cam.project(floor_corners(wps_enu))
    pts = np.vstack([cam.project(path_enu), floor])
    boxes = np.array([l.box for l in layers])
    x0 = min(boxes[:, 0].min(), pts[:, 0].min()); x1 = max(boxes[:, 2].max(), pts[:, 0].max())
    y0 = min(boxes[:, 1].min(), pts[:, 1].min()); y1 = max(boxes[:, 3].max(), pts[:, 1].max())
    m = 0.04 * (x1 - x0)
    cbox = [int(x0 - m), int(y0 - m), int(math.ceil(x1 + m)), int(math.ceil(y1 + m))]
    bw, bh = cbox[2] - cbox[0], cbox[3] - cbox[1]
    tile_h = int(round(tile_w * bh / bw))
    k = bw / (tile_w * SS)
    label_h = int(round(6.0 / 72 * DPI * 1.45))
    strip = Image.new("RGB", (width_px, tile_h + label_h), (255, 255, 255))
    by_t = {round(l.t, 4): l for l in layers}
    H = tile_h + label_h
    lines = ["# t_s  x_frac  y_frac  (tile center; middle of the label strip, y measured from the bottom)"]
    for j, t in enumerate(times):
        layer = by_t[round(t, 4)]
        until = int(np.searchsorted(rows_t, t + 1e-9))
        canvas = Image.new("RGB", (cam.w, cam.h), (255, 255, 255))
        context(ImageDraw.Draw(canvas), cam, path_enu, wps_enu, k, until=max(1, until))
        base = over(np.asarray(canvas, np.float32).copy(), layer, 1.0)
        img = Image.fromarray(np.clip(base, 0, 255).astype(np.uint8))
        waypoint_marks(ImageDraw.Draw(img), cam, wps_enu, k, r_pt=1.0)
        img = img.crop(cbox).resize((tile_w, tile_h), Image.LANCZOS)
        x = j * (tile_w + gap)
        strip.paste(img, (x, 0))
        ImageDraw.Draw(strip).rectangle([x, 0, x + tile_w - 1, tile_h - 1], outline=HAIR,
                                        width=max(1, int(round(DPI / 300))))
        lines.append(f"{t:.4f} {(x + tile_w / 2) / width_px:.4f} {1 - (tile_h + label_h / 2) / H:.4f}")
    strip.save(out, dpi=(DPI, DPI))
    labels_out.write_text("\n".join(lines) + "\n")


def pick_supersample(width_px: int, aspect: float, want: int, widen: float):
    """The largest supersampling factor <= want at which the tiny renderer produces the render."""
    for ss in range(max(1, want), 0, -1):
        W = int(width_px * ss * widen)
        if renders_at(W, int(round(W / aspect))):
            return ss, W, int(round(W / aspect))
        print(f"tiny renderer cannot produce {W} px wide; trying supersample {ss - 1}")
    raise SystemExit("tiny renderer failed at every supersampling factor")


# --------------------------------------------------------------------------------------------
# Labels for the .tex wrappers


def strobe_label_picks(instants_t, centers, wp_times, wp_frac, near_frac):
    """Which instants get a time label, and where: the first instant; for each inner waypoint the
    instant nearest its closest approach (summary.txt); the final hover, labeled together with the
    last instant on the course when their centers are within near_frac of the image width. Each label
    sits beside its vehicle on the side away from the centroid of the waypoints' images.
    Returns [(text, x_frac, y_frac, anchor)]."""
    t = np.asarray(instants_t)
    picks = [0]
    for tw in wp_times:
        picks.append(int(np.argmin(np.abs(t - tw))))
    picks.append(len(t) - 1)
    if np.hypot(*(np.array(centers[-2]) - np.array(centers[-1]))) < near_frac:
        picks.append(len(t) - 2)
    picks = sorted(set(picks))
    cx, cy = np.mean(wp_frac, axis=0)
    out = []
    i = 0
    while i < len(picks):
        j = picks[i]
        text = [j]
        if i + 1 < len(picks) and picks[i + 1] == len(t) - 1 and j == len(t) - 2:
            d = np.hypot(*(np.array(centers[j]) - np.array(centers[-1])))
            if d < near_frac:
                text.append(len(t) - 1)
                i += 1
        x, y = centers[j]
        ang = math.degrees(math.atan2(y - cy, x - cx))
        out.append((text, x, y, ang))
        i += 1
    return out


ANCHORS = [(-22.5, 22.5, "west"), (22.5, 67.5, "south west"), (67.5, 112.5, "south"),
           (112.5, 157.5, "south east"), (-67.5, -22.5, "north west"), (-112.5, -67.5, "north"),
           (-157.5, -112.5, "north east")]


def anchor_for(ang: float) -> str:
    for lo, hi, name in ANCHORS:
        if lo <= ang < hi:
            return name
    return "east"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin", default=str(C.BINARIES["lean"]), help="vehicle binary (default copter_lean)")
    ap.add_argument("--every", type=float, default=0.5, help="seconds between instants (default 0.5)")
    ap.add_argument("--climb", type=float, default=0.05, metavar="M")
    ap.add_argument("--hover-tol", type=float, default=0.1, metavar="M")
    ap.add_argument("--scale", type=float, default=3.0, help="drawing scale of the vehicle mesh (default 3)")
    ap.add_argument("--dpi", type=int, default=600)
    ap.add_argument("--supersample", type=int, default=4, metavar="N")
    ap.add_argument("--width-cm", type=float, default=8.2)
    ap.add_argument("--aspect", type=float, default=1.2, help="render aspect ratio w/h (default 1.2)")
    ap.add_argument("--film-scale", type=float, default=7.0)
    ap.add_argument("--film-times", type=float, nargs="+", default=[0.0, 3.5, 7.0, 10.5, 14.0, 18.5])
    ap.add_argument("--duration", type=float, default=60.0)
    ap.add_argument("--pyb-hz", type=int, default=1200)
    ap.add_argument("--cam-dist", type=float, default=10.2)
    ap.add_argument("--cam-yaw", type=float, default=22.0)
    ap.add_argument("--cam-pitch", type=float, default=-34.0)
    ap.add_argument("--label-offset", type=float, default=0.03,
                    help="label distance from the vehicle center, fraction of the image width")
    ap.add_argument("--work", default=str(C.FIGS / "out" / "strobe"))
    ap.add_argument("--out", default=str(C.STAGING / "figs"))
    args = ap.parse_args()
    global DPI, SS
    DPI = args.dpi
    work, dst = Path(args.work), Path(args.out)
    work.mkdir(parents=True, exist_ok=True)

    run, all_poses, mission, cmd = fly_and_capture(Path(args.bin), DEFAULT_PARAMS, args.duration, args.pyb_hz)
    rc.write_outputs(work, run)
    check = [f"re-flight: {' '.join(cmd)}", f"end: {run.end_reason}; {len(run.rows)} ticks"]
    check += compare_recorded(run)
    ndiff = sum(int(ln.split(" lines, ")[1].split()[0]) for ln in check[2:])
    rows, path_enu, wps_enu = path_and_waypoints(run, mission)
    poses = select_instants(all_poses, wps_enu, args.every, None if args.climb < 0 else args.climb,
                            args.hover_tol)
    check.append(f"{len(poses)} instants, t = " + " ".join(f"{t:g}" for t, _, _ in poses))
    print("\n".join(check), flush=True)
    if ndiff:
        (work / "check.txt").write_text("\n".join(check) + "\n")
        raise SystemExit("the re-flight differs from the recorded flights")

    width_px = int(round(args.width_cm / 2.54 * DPI))
    SS, W, H = pick_supersample(width_px, args.aspect, args.supersample, 1.25)
    print(f"supersample {SS}: renders {W} x {H} px", flush=True)
    lo, hi = floor_bounds(wps_enu)
    target = ((lo[0] + hi[0]) / 2, (lo[1] + hi[1]) / 2, wps_enu[:, 2].max() / 2)
    cam = Camera(W, H, target, args.cam_dist, args.cam_yaw, args.cam_pitch)
    layers = render_frames(poses, cam, args.scale)
    ticks = np.array([p for _, p, _ in poses])
    box, size = composite(cam, layers, path_enu, wps_enu, width_px, work / "strobe.png", work / "labels.txt", ticks)
    h_cm = size[1] / DPI * 2.54
    check.append(f"strobe.png: {size[0]} x {size[1]} px at {DPI} dpi ({size[0] / DPI * 2.54:.2f} x {h_cm:.2f} cm), "
                 f"supersample {SS}")
    film_poses = [ps for ps in all_poses if any(abs(ps[0] - t) < 1e-6 for t in args.film_times)]
    if len(film_poses) != len(args.film_times):
        raise SystemExit("a filmstrip time is not a captured tick")
    film_layers = render_frames(film_poses, cam, args.film_scale)
    filmstrip(cam, film_layers, path_enu, wps_enu, args.film_times, rows[:, 0], width_px,
              work / "filmstrip.png", work / "film-labels.txt")
    fimg = Image.open(work / "filmstrip.png")
    check.append(f"filmstrip.png: {fimg.size[0]} x {fimg.size[1]} px at {DPI} dpi")
    (work / "check.txt").write_text("\n".join(check) + "\n")
    shutil.copy(work / "strobe.png", dst / "flight-strobe.png")
    shutil.copy(work / "filmstrip.png", dst / "flight-filmstrip.png")

    # ---------------- flight-strobe.tex
    S = C.summary(C.run_dir("lean"))
    lab = [ln.split() for ln in (work / "labels.txt").read_text().splitlines() if not ln.startswith("#")]
    inst_t = [float(a[0]) for a in lab]
    centers = [(float(a[1]), float(a[2])) for a in lab]
    wp_frac = [(float(a[2]), float(a[3])) for a in
               (ln.split() for ln in (work / "labels.txt").read_text().splitlines() if ln.startswith("# wp"))]
    inner = [w["t_closest"] for w in S["waypoints"][1:-1]]
    picks = strobe_label_picks(inst_t, centers, inner, wp_frac, 0.1)
    aspect_h = size[1] / size[0]
    labels = []
    for idx, x, y, ang in picks:
        ts = [inst_t[j] for j in idx]
        txt = ", ".join(f"{v:.1f}" for v in ts) + "\\,s"
        if idx[0] == 0:
            txt = f"$t={ts[0]:.1f}$\\,s"
        dx = args.label_offset * math.cos(math.radians(ang))
        dy = args.label_offset * math.sin(math.radians(ang)) / aspect_h
        labels.append((txt, x + dx, y + dy, anchor_for(ang), ts))
    T = []
    w = T.append
    w("% ==================================================================")
    w("%  Time lapse of the flight -- one sigconf text width, pdfLaTeX")
    w("%  Preamble:  \\usepackage{tikz}  (graphicx comes with acmart);")
    w("%             flight-strobe.png on the graphics path")
    w(f"%  Image:     flight-strobe.png ({size[0] / DPI * 2.54:.2f} x {h_cm:.2f} cm, {DPI} dpi), made by")
    w("%             cpp2lean sim/figs/render_strobe.py: copter_lean (the Lean")
    w("%             translations of ArduPilot's classes, lean/.lake/build/bin/copter_lean)")
    w("%             re-flying the figure-eight course of sim/params/copter-cf2x.txt at")
    w("%             1 m/s (copter-course-speed.txt) with the tuned gains")
    w("%             (copter-cf2x-tuned.txt) headless through sim/run_copter.py's fly")
    w(f"%             (400 Hz control, 1200 Hz physics, {len(run.rows)} ticks); the vehicle pose")
    w(f"%             taken every {args.every:g} s from t = {poses[0][0]:g} s (the first instant")
    w(f"%             {args.climb * 100:g} cm above the start) to {poses[-2][0]:g} s, plus one instant at the")
    w(f"%             final hover (t = {poses[-1][0]:g} s), {len(poses)} in all, and rendered by PyBullet")
    w(f"%             (getCameraImage, ER_TINY_RENDERER, {SS}x supersampled) from one fixed")
    w(f"%             oblique camera (yaw {args.cam_yaw:g}, pitch {args.cam_pitch:g}, distance {args.cam_dist:g} m);")
    w("%             vehicle pixels found by differencing against the empty scene and")
    w("%             composited with opacity rising toward the last instant. The")
    w(f"%             vehicle mesh is drawn at {args.scale:g} times its size. The re-flown actuator")
    w("%             and state lines equal those of the recorded flights")
    for ln in check[2:6]:
        w("%               " + ln)
    w("%             No text in the image; labels sit beside the projected vehicle")
    w("%             centers written by the script to sim/figs/out/strobe/labels.txt,")
    w("%             at the first instant, the instant nearest each inner waypoint's")
    w("%             closest approach (summary.txt), and the final hover (with the")
    w("%             last course instant when the two are within a tenth of the image")
    w("%             width), each on the side away from the waypoints' centroid.")
    w("%             Generated by the script; no hand-edited coordinates.")
    w("% ==================================================================")
    w("\\definecolor{fwInk}{HTML}{22252A}%")
    w("\\definecolor{fwMute}{HTML}{8A8F96}%")
    w("\\begin{tikzpicture}[tl/.style={font=\\scriptsize, text=fwMute, inner sep=0.5pt}]")
    w("\\node[anchor=south west, inner sep=0] (img) at (0,0)")
    w("  {\\includegraphics[width=\\linewidth]{flight-strobe.png}};")
    w("\\begin{scope}[x={(img.south east)}, y={(img.north west)}]")
    for txt, x, y, anc, ts in labels:
        w(f"  \\node[tl, anchor={anc}] at ({x:.3f},{y:.3f}) {{{txt}}};")
    w("\\end{scope}")
    w("\\end{tikzpicture}%")
    (dst / "flight-strobe.tex").write_text("\n".join(T) + "\n")

    # ---------------- flight-filmstrip.tex
    fl = [ln.split() for ln in (work / "film-labels.txt").read_text().splitlines() if not ln.startswith("#")]
    T = []
    w = T.append
    w("% ==================================================================")
    w("%  Filmstrip of the flight -- one sigconf text width, pdfLaTeX")
    w("%  Preamble:  \\usepackage{tikz}  (graphicx comes with acmart);")
    w("%             flight-filmstrip.png on the graphics path")
    w(f"%  Image:     flight-filmstrip.png ({fimg.size[0] / DPI * 2.54:.2f} cm wide, {DPI} dpi), made by")
    w("%             cpp2lean sim/figs/render_strobe.py from the same re-flight and")
    w("%             camera as flight-strobe.png (copter_lean with the tuned gains,")
    w("%             1 m/s figure-eight course, 400 Hz control, 1200 Hz physics; its")
    w("%             actuator lines equal the recorded ones, 0 differ): six")
    w(f"%             instants, each tile the full view with the path flown so far and the")
    w(f"%             vehicle drawn at {args.film_scale:g} times its size, {SS}x supersampled. The image")
    w("%             holds no text; a blank strip under the tiles carries the time")
    w("%             labels, placed at the tile centers written by the script to")
    w("%             sim/figs/out/strobe/film-labels.txt.")
    w("% ==================================================================")
    w("\\definecolor{fwInk}{HTML}{22252A}%")
    w("\\definecolor{fwMute}{HTML}{8A8F96}%")
    w("\\begin{tikzpicture}[fl/.style={font=\\footnotesize, text=fwMute, inner sep=0pt, anchor=mid}]")
    w("\\node[anchor=south west, inner sep=0] (img) at (0,0)")
    w("  {\\includegraphics[width=\\linewidth]{flight-filmstrip.png}};")
    w("\\begin{scope}[x={(img.south east)}, y={(img.north west)}]")
    for j, (ts, xf, yf) in enumerate(fl):
        tv = float(ts)
        txt = f"{tv:g}\\,s" if j else f"$t={tv:g}$\\,s"
        w(f"  \\node[fl] at ({float(xf):.4f},{float(yf):.4f}) {{{txt}}};")
    w("\\end{scope}")
    w("\\end{tikzpicture}%")
    (dst / "flight-filmstrip.tex").write_text("\n".join(T) + "\n")
    print("\n".join(check[-2:]))
    print(f"wrote {dst / 'flight-strobe.png'}, flight-strobe.tex, flight-filmstrip.png, flight-filmstrip.tex")


if __name__ == "__main__":
    main()
