#!/usr/bin/env python3
"""Render a gorge flight of sim/gorge_lockstep.py with leanfc's gorge cameras: an animation (chase view of the CF2X, under
it the onboard forward RGB and forward thermal cameras; the layout of leanfc's gallery, sim/world/render_formation.py, for
one vehicle) as H.264 mp4, and stills (overview with the flown track, a chase frame, an onboard RGB frame, a thermal frame).

    build/reference/venv/bin/python sim/render_gorge.py --run sim/out/gorge-port/flight --out sim/out/gorge-port
        [--every 0.05] [--span T0 T1] [--name gorge-port]

Adapter code (cpp2lean); the renderers are leanfc's, imported from LEANFC_ROOT (default /Users/ryan/Research/leanfc),
nothing copied: the world (gorge.py: Gorge.load "visual" and "thermal"), the scene renderer (render_world.Scene.shoot:
PyBullet TinyRenderer, fires of fire.py at the still quality, haze), the cameras (sensors.py: RGBCamera 320 x 240, 90 deg,
with its AutoExposure; the thermal camera ThermalSpec 640 x 512, 54 deg, split as render_formation.SplitThermal into its
stateless optics and its stateful detector; the display AGC), the fonts (render_world.font: DejaVu Sans from Matplotlib) and
the H.264 encoder script (render_formation.MP4_ENCODER: libx264, yuv420p, CRF 18, through PyAV) run with the environment
build/gorge-video (av 19.0.2, numpy 2.5.4, as leanfc's requirements-video.txt).

What is the port's: the poses (track.csv of the flight, 100 Hz: ENU position and PyBullet quaternion of the simulated
vehicle, and its four actuators), the times (one frame every EVERY seconds of simulated time from 1 s before arming to
1 s after the disarm, played at real speed). The vehicle (flight.json "vehicle", VEHICLES): the X500 as leanfc renders it
(render_flight.model_path("x500"): PX4's X500 meshes without propellers, with render_flight.draw_props' propeller motion
blur from the actuators, ArduPilot's motor slots 0..3 being render_flight.HUBS' rotors 0..3; the cameras on sensors.FORWARD,
0.20 m ahead of the centre, 30 deg down; the chase camera of render_formation.Setup.chase), or the CF2X
(gym-pybullet-drones' cf2x.urdf, MIT, at true size, no blur; the same cameras 0.03 m ahead and 0.01 m below its centre,
30 deg down; a chase camera 1.25 m behind).
The onboard views are rendered with the vehicle moved out of the world, as in render_formation.py.

Two worker processes (one PyBullet client each, about 4 GB): one renders the chase canvas and the RGB camera's raw frame,
the other the thermal camera's optical signal; the main process applies, in frame order, what carries state from frame
to frame (RGB exposure, thermal detector, AGC), assembles and encodes. The overview is rendered after the workers exit.

Writes in OUT: NAME.mp4, NAME-chase.png, NAME-rgb.png, NAME-thermal.png, NAME-overview.png, NAME-frames/ (every 20th frame
as PNG, for checking) and NAME-render.json.
"""
import argparse
import json
import math
import multiprocessing as mp
import os
import shutil
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

SIM_DIR = Path(__file__).resolve().parent
ROOT = SIM_DIR.parent
LEANFC_ROOT = Path(os.environ.get("LEANFC_ROOT", "/Users/ryan/Research/leanfc"))
VIDEO_PY = Path(os.environ.get("GORGE_VIDEO_PY", ROOT / "build" / "gorge-video" / "bin" / "python"))
sys.dont_write_bytecode = True
sys.path.insert(0, str(SIM_DIR))
for _d in (LEANFC_ROOT / "sim" / "world", LEANFC_ROOT / "sim"):
    if str(_d) not in sys.path:
        sys.path.append(str(_d))

import pybullet as p  # noqa: E402
from PIL import Image, ImageDraw  # noqa: E402

import lockstep_gcs  # noqa: E402
import gorge as G  # noqa: E402
import sensors as S  # noqa: E402
import render_world as RW  # noqa: E402
import render_formation as RFM  # noqa: E402

# per vehicle: camera mount, chase camera (m behind, above, aim ahead, aim below, vertical FOV), label height, propeller blur.
# x500: leanfc's own (sensors.FORWARD; render_formation.Setup.chase's camera; render_flight's X500 meshes and propeller
# blur); cf2x: the package's CF2X at true size, the same cameras 0.03 m ahead of its centre, a closer chase camera.
VEHICLES = dict(
    x500=dict(mount=S.FORWARD, chase=(5.0, 1.9, 5.0, 1.0, 56.0), tag=0.45, props=True, name="X500"),
    cf2x=dict(mount=S.Mount(pos=(0.03, 0.0, -0.01), pitch_deg=30.0), chase=(1.25, 0.42, 4.0, 0.55, 56.0), tag=0.10, props=False,
              name="CF2X"))
MODE_NAMES = {v: k for k, v in lockstep_gcs.MODES.items()}
W, H = 720, 400                      # chase view
PW, PH = W // 2, W * 3 // 8          # two panels under it, 4:3
TITLE_H = 22
THERMAL_SEED = 0


def quat_R(q):
    """Rotation matrix (body FLU -> world ENU) of a PyBullet quaternion (x, y, z, w)."""
    x, y, z, w = q
    return np.array([[1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)],
                     [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)],
                     [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)]])


class Track:
    """The flight's 100 Hz record (track.csv), its flight.json and mission.json."""

    def __init__(self, run, every=0.05, span=None):
        run = Path(run)
        self.d = np.genfromtxt(run / "track.csv", delimiter=",", names=True)
        self.flight = json.loads((run / "flight.json").read_text())
        self.mission = json.loads((run / "mission.json").read_text())
        self.t = self.d["t"]
        self.pos = np.column_stack([self.d["x"], self.d["y"], self.d["z"]])
        self.quat = np.column_stack([self.d["qx"], self.d["qy"], self.d["qz"], self.d["qw"]])
        self.speed = np.sqrt(self.d["vn"] ** 2 + self.d["ve"] ** 2 + self.d["vz_up"] ** 2)
        self.vehicle = self.flight.get("vehicle", "cf2x")
        self.v = VEHICLES[self.vehicle]
        self.prop_angle, self.prop_speed = RW.RF.prop_state(self.d, hz=1.0 / (self.t[1] - self.t[0]))   # 100 Hz rows
        rec = self.flight["record"]
        t0, t1 = rec["t_arm"] - 1.0, rec["t_disarm"] + 1.0
        n = int(math.floor((t1 - t0) / every + 1e-9)) + 1
        ts = t0 + every * np.arange(n)
        self.times = ts if span is None else ts[(ts >= span[0] - 1e-9) & (ts < span[1] - 1e-9)]

    def k_at(self, t):
        return int(np.argmin(np.abs(self.t - t)))

    def pose(self, k):
        return self.pos[k], quat_R(self.quat[k])


class View:
    """A PyBullet client with the gorge's visual world and the CF2X; `shoot` is render_world.Scene.shoot."""
    shoot = RW.Scene.shoot

    def __init__(self, g, vehicle="cf2x"):
        self.g = g
        self.c = p.connect(p.DIRECT)
        self.bodies = g.load(self.c, "visual")
        self.fires = S.FI.Fires(g, "still")
        self.body = None
        self.urdf = RW.RF.model_path(vehicle)      # x500: leanfc's PX4 X500 meshes without propellers; cf2x: the package's

    def place(self, pos, R):
        q = RW.RF.quat_xyzw(R)
        if self.body is None:
            self.body = p.loadURDF(self.urdf, list(pos), q, useFixedBase=True, physicsClientId=self.c)
        else:
            p.resetBasePositionAndOrientation(self.body, list(pos), q, physicsClientId=self.c)

    def hide(self):
        if self.body is not None:
            p.resetBasePositionAndOrientation(self.body, [0, 0, -500], [0, 0, 0, 1], physicsClientId=self.c)

    def chase(self, tr, t):
        """The canvas of a frame without the two panel images: chase view, labels, status line, panel titles."""
        k = tr.k_at(t)
        pos, R = tr.pose(k)
        self.place(pos, R)
        BACK, UP, AHEAD, DOWN, FOV = tr.v["chase"]
        ax = self.g.axis_dir(pos[1])
        eye = pos - BACK * ax + [0, 0, UP]
        tgt = pos + AHEAD * ax - [0, 0, DOWN]
        props = [(pos, R, tr.prop_angle[k], tr.prop_speed[k])] if tr.v["props"] else []
        img, px = self.shoot(W, H, eye, tgt, (0, 0, 1), FOV, 0.03, 200, props, 1.0, t=t)
        self.hide()
        canvas = Image.new("RGB", (W, H + TITLE_H + PH), RFM.BG)
        canvas.paste(img, (0, 0))
        dr = ImageDraw.Draw(canvas, "RGBA")
        a, ok = px(pos + [0, 0, tr.v["tag"]])
        if ok[0]:
            dr.text((a[0][0], a[0][1] - 4), tr.v["name"], font=RW.font(13, True), fill=(255, 255, 255), anchor="ms",
                    stroke_width=2, stroke_fill=(0, 0, 0))
        d = tr.d
        mode = MODE_NAMES.get(int(d["mode"][k]), str(int(d["mode"][k])))
        if not d["armed"][k]:
            mode += ", disarmed"
        item = int(d["item"][k])
        dr.rectangle([0, 0, W, 24], fill=(0, 0, 0, 150))
        dr.text((8, 5), f"ArduCopter in Lean (cpp2lean)   t {t:6.2f} s   N {pos[1]:5.1f} m   {tr.speed[k]:4.2f} m/s   "
                f"{mode}" + (f"   item {item}" if item >= 0 else ""), font=RW.font(13, True), fill=(255, 255, 255))
        dr.text((W - 8, H - 8), f"clearance {max(0.0, d['clearance'][k]):4.2f} m", font=RW.font(12, True), fill=(255, 255, 255),
                anchor="rs", stroke_width=2, stroke_fill=(0, 0, 0))
        for j, ttl in enumerate(("forward RGB (320 x 240, 90 deg)", "forward thermal (640 x 512, 54 deg)")):
            dr.text((j * PW + 4, H + 4), ttl, font=RW.font(12, True), fill=(235, 235, 235))
        return canvas, float(pos[1])


def finish(canvas, rgb, disp):
    canvas.paste(Image.fromarray(rgb).resize((PW, PH), Image.BILINEAR), (0, H + TITLE_H))
    canvas.paste(Image.fromarray(disp).resize((PW, PH), Image.BILINEAR), (PW, H + TITLE_H))
    return canvas


class Mp4:
    """render_formation.MP4_ENCODER (libx264 through PyAV) in VIDEO_PY, raw RGB frames on its standard input."""

    def __init__(self, path, size, fps):
        self.w, self.h = size[0] + size[0] % 2, size[1] + size[1] % 2
        r = Fraction(fps).limit_denominator(1000)
        self.proc = subprocess.Popen([str(VIDEO_PY), "-c", RFM.MP4_ENCODER, str(self.w), str(self.h), str(r.numerator),
                                      str(r.denominator), str(path)], stdin=subprocess.PIPE)

    def add(self, img):
        if img.size != (self.w, self.h):
            pad = Image.new("RGB", (self.w, self.h), RFM.BG)
            pad.paste(img, (0, 0))
            img = pad
        self.proc.stdin.write(img.tobytes())

    def close(self):
        self.proc.stdin.close()
        if self.proc.wait() != 0:
            raise RuntimeError("mp4 encoder failed")


def _save_atomic(path, arrays):
    tmp = path.with_name(path.name + ".part")
    with open(tmp, "wb") as fh:
        np.savez(fh, **arrays)
    os.replace(tmp, path)


def _worker(kind, run, every, span, raw, jobs, ready):
    """kind "vis": the chase canvas and the RGB camera's frame before exposure; kind "th": the thermal camera's optical
    signal. One PyBullet client per process."""
    tr = Track(run, every, span)
    g = G.Gorge(tr.flight["gorge_seed"])
    if kind == "vis":
        v = View(g, tr.vehicle)
        keep = RFM.KeepRaw()
        cam = S.RGBCamera(v.c, v.bodies, tr.v["mount"], gorge=g, fire_quality=RFM.FIRE_QUALITY, exposure=keep)
    else:
        th = p.connect(p.DIRECT)
        bt = g.load(th, "thermal")
        cam = RFM.SplitThermal(th, bt, tr.v["mount"], seed=THERMAL_SEED, gorge=g, fire_quality=RFM.FIRE_QUALITY)
    ready.put(kind)
    while True:
        job = jobs.get()
        if job is None:
            return
        for i in job:
            t = tr.times[i]
            pos, R = tr.pose(tr.k_at(t))
            if kind == "vis":
                canvas, north = v.chase(tr, t)
                cam.capture(R, pos, t)
                _save_atomic(raw / f"vis_{i:05d}.npz", dict(canvas=np.asarray(canvas), north=north, rgb=keep.img))
            else:
                _save_atomic(raw / f"th_{i:05d}.npz", dict(lo=cam.optics(R, pos, t)))


def caption(img, text, size=16):
    """The image with a caption bar above it."""
    f = RW.font(size, True)
    out = Image.new("RGB", (img.width, img.height + size + 14), RFM.BG)
    out.paste(img, (0, size + 14))
    ImageDraw.Draw(out).text((8, 6), text, font=f, fill=(255, 255, 255))
    return out


def overview(g, tr, path):
    """Top-down view of the gorge with the flown track (liftoff to touchdown), the plan's waypoints, the land item and
    the point of least clearance (render_world.overview's camera)."""
    v = View(g, tr.vehicle)
    Wo, Ho = 2400, 960
    y0, y1 = -3.0, 76.0
    xm = float(np.mean(g.xc_fn(np.linspace(0, 72, 100))))
    ym = (y0 + y1) / 2
    alt = 400.0
    across = (y1 - y0) * Ho / Wo
    fov_v = 2 * math.degrees(math.atan(across / 2 / alt))
    img, px = v.shoot(Wo, Ho, (xm, ym, alt), (xm, ym, 0), (-1, 0, 0), fov_v, 300, 430, (), 1.0, bg=(46, 50, 56))
    dr = ImageDraw.Draw(img, "RGBA")
    met = tr.flight["metrics"]
    fly = (tr.t >= met["liftoff_t"]) & (tr.t <= (met.get("touchdown_t") or tr.t[-1]))
    q, _ = px(tr.pos[fly][::5])
    dr.line([tuple(a) for a in q], fill=(230, 50, 40, 235), width=4)
    path_ = g.path
    q, _ = px(path_)
    for j, a in enumerate(q):
        dr.ellipse([a[0] - 7, a[1] - 7, a[0] + 7, a[1] + 7], fill=(40, 110, 230, 235), outline=(255, 255, 255, 230))
        dr.text((a[0], a[1] - 12), "T" if j == 0 else str(j), font=RW.font(20, True), fill=(255, 255, 255), anchor="ms",
                stroke_width=2, stroke_fill=(0, 0, 0))
    a = q[-1]
    dr.ellipse([a[0] - 16, a[1] - 16, a[0] + 16, a[1] + 16], outline=(255, 255, 255, 240), width=3)
    c = met["clearance_min_at"]
    b, _ = px(np.array([[c["east"], c["north"], c["up"]]]))
    b = b[0]
    dr.ellipse([b[0] - 12, b[1] - 12, b[0] + 12, b[1] + 12], outline=(255, 226, 70, 255), width=4)
    RW.label(dr, (b[0] + 20, b[1] + 60), f"least clearance {met['clearance_min_in_air_m']:.2f} m", 24, fill=(255, 236, 140))
    a, _ = px(np.array([[xm - 13.5, y0 + 2, 0], [xm - 13.5, y0 + 12, 0]]))
    dr.line([tuple(a[0]), tuple(a[1])], fill=(255, 255, 255, 255), width=6)
    dr.text((a[0][0], a[0][1] - 34), "10 m", font=RW.font(24, True), fill=(255, 255, 255))
    dr.line([(Wo - 140, 70), (Wo - 50, 70)], fill=(255, 255, 255), width=5)
    dr.polygon([(Wo - 50, 58), (Wo - 26, 70), (Wo - 50, 82)], fill=(255, 255, 255))
    dr.text((Wo - 128, 82), "north", font=RW.font(24, True), fill=(255, 255, 255))
    dr.rectangle([0, 0, Wo, 30], fill=(0, 0, 0, 120))
    dr.text((12, 3), f"Gorge seed {g.seed} from above: ArduCopter in Lean (cpp2lean) flying the {tr.v['name']} on the gorge mission. "
            f"Red: flown track, liftoff to touchdown; blue: the plan's takeoff (T) and spline waypoints 1-10; white ring: land",
            font=RW.font(20), fill=(255, 255, 255))
    img.save(path)
    p.disconnect(v.c)


def render(run, out, name, every=0.05, span=None):
    run, out = Path(run), Path(out)
    out.mkdir(parents=True, exist_ok=True)
    tr = Track(run, every, span)
    ts = tr.times
    g = G.Gorge(tr.flight["gorge_seed"])
    fdir = out / f"{name}-frames"
    shutil.rmtree(fdir, ignore_errors=True)
    fdir.mkdir()
    raw = fdir / ".raw"
    raw.mkdir()
    ctx = mp.get_context("spawn")
    chunks = [list(range(a, min(a + 4, len(ts)))) for a in range(0, len(ts), 4)]
    queues = {k: ctx.Queue() for k in ("vis", "th")}
    for q in queues.values():
        for c in chunks:
            q.put(c)
        q.put(None)
    ready = ctx.Queue()
    procs = []
    t0 = time.time()
    for k in ("vis", "th"):            # one at a time: loading the world takes several GB for a moment
        pr = ctx.Process(target=_worker, args=(k, str(run), every, span, raw, queues[k], ready), daemon=True)
        pr.start()
        procs.append(pr)
        ready.get(timeout=900)
    print(f"2 workers ready after {time.time() - t0:.0f} s; {len(ts)} frames from {ts[0]:.2f} to {ts[-1]:.2f} s", flush=True)
    therm = RFM.SplitThermal(None, {}, tr.v["mount"], seed=THERMAL_SEED, gorge=g, fire_quality=RFM.FIRE_QUALITY)
    ae, agc = S.AutoExposure(), S.AGC()
    mp4 = None
    best = None                         # the thermal frame with the hottest pixels (a fire in view)
    rgb_still = chase_still = None
    blank = []
    for i, t in enumerate(ts):
        fv, ft = raw / f"vis_{i:05d}.npz", raw / f"th_{i:05d}.npz"
        while not (fv.exists() and ft.exists()):
            dead = [pr for pr in procs if pr.exitcode not in (None, 0)]
            if dead:
                raise RuntimeError(f"a worker failed (exit {dead[0].exitcode})")
            time.sleep(0.05)
        a, b = np.load(fv), np.load(ft)
        canvas = Image.fromarray(a["canvas"])
        north = float(a["north"])
        rgb = RFM.expose(ae, a["rgb"])
        temp = therm.detector(b["lo"])
        disp = agc(temp)
        finish(canvas, rgb, disp)
        if rgb.std() < 2 or disp.std() < 2:
            blank.append(i)
        if mp4 is None:
            mp4 = Mp4(out / f"{name}.mp4", canvas.size, 1 / every)
        mp4.add(canvas)
        if i % 20 == 0:
            canvas.save(fdir / f"frame_{i:04d}.png")
        hot = float(np.quantile(temp, 0.9995))
        if best is None or hot > best[0]:
            best = (hot, t, disp, north)
        if chase_still is None and north >= 36.0:
            chase_still = (t, canvas.copy())
        if rgb_still is None and north >= 40.0:
            rgb_still = (t, rgb, north)
        fv.unlink()
        ft.unlink()
        if i % 100 == 0:
            print(f"frame {i}/{len(ts)}  {time.time() - t0:.0f} s", flush=True)
    mp4.close()
    for pr in procs:
        pr.join()
    shutil.rmtree(raw, ignore_errors=True)
    stills = {}
    if chase_still is not None:
        chase_still[1].save(out / f"{name}-chase.png")
        stills["chase"] = dict(t=chase_still[0])
    if rgb_still is not None:
        im = Image.fromarray(rgb_still[1]).resize((640, 480), Image.NEAREST)
        caption(im, f"Onboard forward RGB, 320 x 240 (shown 2x), t {rgb_still[0]:.2f} s, N {rgb_still[2]:.1f} m").save(out / f"{name}-rgb.png")
        stills["rgb"] = dict(t=rgb_still[0])
    if best is not None:
        caption(Image.fromarray(best[2]), f"Onboard forward thermal 640 x 512, automatic gain, t {best[1]:.2f} s, N {best[3]:.1f} m",
                14).save(out / f"{name}-thermal.png")
        stills["thermal"] = dict(t=best[1], hot_c=best[0])
    wall = time.time() - t0
    if span is None:
        overview(g, tr, out / f"{name}-overview.png")
    info = dict(run=str(run), frames=len(ts), every_s=every, fps=1 / every, t0=float(ts[0]), t1=float(ts[-1]), size=list(canvas.size),
                render_wall_s=round(wall, 1), mp4_mb=round((out / f"{name}.mp4").stat().st_size / 1e6, 2), stills=stills,
                blank_panel_frames=blank, vehicle=tr.vehicle, mount=dict(pos=tr.v["mount"].pos, pitch_deg=tr.v["mount"].pitch_deg), leanfc=str(LEANFC_ROOT))
    (out / f"{name}-render.json").write_text(json.dumps(info, indent=1) + "\n")
    print(json.dumps(info), flush=True)
    return info


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--name", default="gorge-port")
    ap.add_argument("--every", type=float, default=0.05, help="seconds of flight per frame (default 0.05: 20 fps at real speed)")
    ap.add_argument("--span", type=float, nargs=2, default=None, metavar=("T0", "T1"), help="only frames in [T0, T1) s")
    a = ap.parse_args()
    if not VIDEO_PY.exists():
        sys.exit(f"render_gorge: {VIDEO_PY} not found (see sim/README.md, Gorge flight)")
    render(a.run, a.out, a.name, a.every, a.span)


if __name__ == "__main__":
    main()
