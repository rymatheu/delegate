#!/usr/bin/env python3
"""Stroboscopic time lapse of the CF2X course flown by the Lean port of ArduCopter (`copter`, C route).

The script flies the course headless exactly as `run_copter.py --backend bin` does: it calls
`run_copter.fly`, so the lock-step loop, the 17-number input line (NED position and velocity, the
earth-frame specific force of `run_copter.SpecificForce`, the body-to-NED quaternion of
`run_copter.quat_ned_frd`, the body rates, dt), the four actuators and their conversion to RPM
(`run_copter.actuators_to_rpm`), the 400 Hz control and 1200 Hz physics rates, gravity 9.80665, the
damping removal and the settling on the ground are those of the recorded flights. The vehicle pose is
taken from the simulator every `--every` seconds of the run's clock (which starts after the settling).
The actuator stream of this run is compared line by line with each `--ref` file and the number of
differing lines is printed.

The camera and compositing are those of `render_strobe.py` (the earlier stack's script), carried over
unchanged: the poses are rendered with PyBullet's software renderer (`getCameraImage`,
ER_TINY_RENDERER, no GUI) in a render-only client that holds the CF2X mesh and nothing else, from one
fixed oblique camera aimed at the center of the course volume; the vehicle pixels are found by
differencing each frame against a render of the empty scene and composited in time order, with
opacity rising toward the last instant, over a hairline floor grid (0.5 m), dashed drop lines at the
waypoints, the flown path and the waypoints, all drawn through the same camera. The mesh is drawn
`--scale` times its size (default 3). Everything is rendered at `--supersample` times the output size
and shrunk with Lanczos. The images hold no text: label positions go to text files for TikZ.

Outputs (in --out, default out/copter-strobe): flight.csv, inputs.txt and motors.txt of the run,
strobe.png (composite, --dpi, --width-cm wide), labels.txt (time and normalized image position of
each instant), filmstrip.png (six instants in a row, vehicle drawn --film-scale times its size) and
film-labels.txt (normalized position of each tile's label).

    .venv/bin/python render_copter_strobe.py          # the 1 m/s course, 600 dpi, 4x supersampling
    .venv/bin/python render_copter_strobe.py --dpi 150 --supersample 1 --no-filmstrip   # quick look
"""
from __future__ import annotations

import argparse
import math
import os
import shutil
from pathlib import Path
from types import SimpleNamespace

import numpy as np
from PIL import Image, ImageDraw

import run_copter as rc

SIM_DIR = Path(__file__).resolve().parent
DEFAULT_PARAMS = [SIM_DIR / "params" / "copter-cf2x.txt", SIM_DIR / "params" / "copter-course-speed.txt"]
DEFAULT_REFS = [SIM_DIR / "out" / "copter-course-1ms-det" / "copter-bin" / "motors.txt",
                SIM_DIR / "out" / "copter-course-1ms" / "copter-bin" / "motors.txt"]
DPI = 600                                 # output resolution (--dpi)
SS = 4                                    # supersampling factor of every render and drawing (--supersample)

INK = (0x22, 0x25, 0x2A)
MUTE = (0x8A, 0x8F, 0x96)
HAIR = (0xC9, 0xCC, 0xD1)
OCHRE = (0xC4, 0x86, 0x0F)
BLUE = (0x1E, 0x3F, 0x7C)

CAM_FOV = 34.0                            # camera field of view, degrees (PyBullet ENU world)
GRID = 0.5                                # floor grid spacing, meters
FADE = 0.0                                # --context-fade: grid and drop lines blended toward white


def toward_white(c, f: float):
    return tuple(int(round(v + (255 - v) * f)) for v in c)


# --------------------------------------------------------------------------------------------
# Flight with pose capture


def fly_and_capture(every_s: float, bin_path: Path, params: list[str], duration: float,
                    pyb_hz: int = 1200, hold: float = 3.0):
    """Fly the course with the bin backend through run_copter.fly; return the run, the poses at
    multiples of every_s on the run's clock, and the mission."""
    every = int(round(every_s * rc.CTRL_HZ))
    poses = []                                      # (t, ENU position, quaternion xyzw)
    reset_env = rc.reset_env

    def reset_env_capturing(env):
        obs = reset_env(env)                        # reset, damping off, settling with motors off
        step = env.step
        tick = [0]

        def step_capturing(action):
            if tick[0] % every == 0:
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
    return run, poses, mission


def compare_motors(run, refs):
    for ref in refs:
        ref = Path(ref)
        if not ref.exists():
            print(f"motor lines vs {ref}: reference missing")
            continue
        a, b = ref.read_text().splitlines(), run.outputs
        diff = [i for i in range(max(len(a), len(b))) if i >= len(a) or i >= len(b) or a[i] != b[i]]
        first = f" (first at line {diff[0] + 1})" if diff else ""
        print(f"motor lines vs {ref.relative_to(SIM_DIR) if ref.is_relative_to(SIM_DIR) else ref}: "
              f"{len(b)} vs {len(a)} lines, {len(diff)} differ{first}")


def path_and_waypoints(run, mission):
    """Flown path and waypoints in PyBullet's ENU world."""
    rows = np.array([r[:4] for r in run.rows], float)        # t, n, e, d
    path_enu = np.stack([rows[:, 2], rows[:, 1], -rows[:, 3]], axis=1)
    wps_enu = np.array([(w[1], w[0], -w[2]) for w in mission["waypoints"]])
    return rows, path_enu, wps_enu


# --------------------------------------------------------------------------------------------
# Rendering (camera and frames as in render_strobe.py)


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
# Composite (as in render_strobe.py)


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
        lines.append(f"{layer.t:5.2f} {(p[0] - box[0]) / (box[2] - box[0]):.4f} "
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
    by_t = {round(l.t, 2): l for l in layers}
    H = tile_h + label_h
    lines = ["# t_s  x_frac  y_frac  (tile center; middle of the label strip, y measured from the bottom)"]
    for j, t in enumerate(times):
        layer = by_t[round(t, 2)]
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
        lines.append(f"{t:5.2f} {(x + tile_w / 2) / width_px:.4f} {1 - (tile_h + label_h / 2) / H:.4f}")
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


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bin", default=str(rc.DEFAULT_BIN), help="path of the C-route binary")
    ap.add_argument("--params", action="append", default=None, metavar="FILE",
                    help="parameter files passed to the controller (default: copter-cf2x.txt, "
                         "copter-course-speed.txt)")
    ap.add_argument("--ref", action="append", default=None, metavar="FILE",
                    help="motors.txt to compare the actuator stream with (repeatable; default: "
                         "out/copter-course-1ms-det/copter-bin and out/copter-course-1ms/copter-bin)")
    ap.add_argument("--every", type=float, default=0.5, help="seconds between instants (default 0.5)")
    ap.add_argument("--scale", type=float, default=3.0, help="drawing scale of the vehicle mesh (default 3)")
    ap.add_argument("--dpi", type=int, default=600, help="output resolution (default 600)")
    ap.add_argument("--supersample", type=int, default=4, metavar="N",
                    help="render and composite at N times the output size (default 4)")
    ap.add_argument("--width-cm", type=float, default=8.2, help="width of the composite (default 8.2 cm)")
    ap.add_argument("--aspect", type=float, default=1.2, help="render aspect ratio w/h (default 1.2)")
    ap.add_argument("--film-scale", type=float, default=7.0, help="vehicle scale in the filmstrip (default 7)")
    ap.add_argument("--film-times", type=float, nargs="+", default=[0.0, 3.5, 7.0, 11.0, 14.5, 21.0])
    ap.add_argument("--filmstrip", action=argparse.BooleanOptionalAction, default=True)
    ap.add_argument("--duration", type=float, default=60.0, help="simulated seconds at most (default 60)")
    ap.add_argument("--pyb-hz", type=int, default=1200, help="physics rate (default 1200)")
    ap.add_argument("--cam-dist", type=float, default=10.2)
    ap.add_argument("--cam-yaw", type=float, default=22.0)
    ap.add_argument("--cam-pitch", type=float, default=-34.0)
    ap.add_argument("--out", default=str(SIM_DIR / "out" / "copter-strobe"))
    ap.add_argument("--copy-to", default=None, help="also copy strobe.png and filmstrip.png here as "
                    "flight-strobe.png and flight-filmstrip.png")
    args = ap.parse_args()
    global DPI, SS
    DPI = args.dpi
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)

    params = args.params or [str(f) for f in DEFAULT_PARAMS]
    run, poses, mission = fly_and_capture(args.every, Path(args.bin), params, args.duration, args.pyb_hz)
    rc.write_outputs(out, run)
    print(f"run: {run.end_reason}; {len(run.rows)} ticks; {len(poses)} instants captured")
    compare_motors(run, args.ref or DEFAULT_REFS)

    width_px = int(round(args.width_cm / 2.54 * DPI))
    SS, W, H = pick_supersample(width_px, args.aspect, args.supersample, 1.25)
    print(f"supersample {SS}: renders {W} x {H} px")
    rows, path_enu, wps_enu = path_and_waypoints(run, mission)
    lo, hi = floor_bounds(wps_enu)
    target = ((lo[0] + hi[0]) / 2, (lo[1] + hi[1]) / 2, wps_enu[:, 2].max() / 2)
    cam = Camera(W, H, target, args.cam_dist, args.cam_yaw, args.cam_pitch)
    layers = render_frames(poses, cam, args.scale)
    ticks = np.array([p for _, p, _ in poses])
    box, size = composite(cam, layers, path_enu, wps_enu, width_px, out / "strobe.png", out / "labels.txt", ticks)
    print(f"strobe.png: {size[0]} x {size[1]} px at {DPI} dpi "
          f"({size[0] / DPI * 2.54:.2f} x {size[1] / DPI * 2.54:.2f} cm)")
    if args.filmstrip:
        film_poses = [ps for ps in poses if any(abs(ps[0] - t) < 1e-6 for t in args.film_times)]
        film_layers = render_frames(film_poses, cam, args.film_scale)
        filmstrip(cam, film_layers, path_enu, wps_enu, args.film_times, rows[:, 0], width_px,
                  out / "filmstrip.png", out / "film-labels.txt")
        print("filmstrip.png and film-labels.txt written")
    if args.copy_to:
        dst = Path(args.copy_to)
        shutil.copy(out / "strobe.png", dst / "flight-strobe.png")
        if args.filmstrip:
            shutil.copy(out / "filmstrip.png", dst / "flight-filmstrip.png")
        print(f"copied to {dst}")


if __name__ == "__main__":
    main()
