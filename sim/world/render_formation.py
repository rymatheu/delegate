"""Evidence of a formation flight (formation.py): an animation of both X500s in the gorge seen from outside
(chase camera behind the pair), with the onboard views below it, and the frames it is made from.

    python render_formation.py --run out/formation/staggered-field-s0 [--name formation-staggered]
                               [--every 0.3] [--out out] [--workers 1] [--no-mp4]

Writes OUT/NAME.gif, OUT/NAME.webp and OUT/NAME.mp4 (the same frames; the GIF with a palette of its own
per frame, the WebP lossy, the MP4 H.264 through PyAV in sim/world/.venv-video when that exists; one frame
every EVERY seconds of flight, played at real speed), OUT/NAME-frames/frame_NNN.png (as many digits as
the frame count needs) and OUT/NAME-still.png (one frame at full size, in the first narrows). When the
GIF is larger than 100 MB, also OUT/NAME-small.gif: the same frames at reduced width and palette, under
50 MB. The frames are streamed to the encoders, never all held in memory.

Panels under the chase view, rendered after the flight from each vehicle's recorded true pose with
sensors.py's cameras (forward mount, 30 deg down), with the fires at the still quality of fire.py:
vehicle 1's forward RGB and thermal, vehicle 2's RGB and thermal. RGB: 320 x 240, 90 deg HFOV, with its
automatic exposure. Thermal: sensors.ThermalSpec, the 640 x 512 core with a 54 deg HFOV (non-uniformity,
temporal noise, gain switching, 14-bit output), shown through sensors.AGC (automatic gain on the band
radiance, ironbow-like palette PALETTE, smoothed over frames). In the staggered plan vehicle 2 flies nose
against the direction of travel, so its camera looks behind the formation.

--workers N (N > 1) shards the rendering over N processes, each with one PyBullet client: half of them
render the chase view and the RGB panels' raw scene (before exposure), the others the thermal panels'
optical signal (before the detector); the main process assembles the frames in order and applies
everything that carries state from frame to frame serially, as a single process does: the RGB automatic
exposure, the thermal detector (gain state with hysteresis, the temporal noise from the camera's random
generator) and the display AGC. The fire animation and the propeller blur depend on the time only. The
frames come out identical to --workers 1.

Rendering only (PyBullet TinyRenderer), with render_world.py's look: the gorge's visual meshes at full
detail (Gorge.load lod 0), the PX4 X500 meshes (sim/assets/x500_render_noprops.urdf) and render_flight.py's
propeller motion blur, DejaVu Sans from Matplotlib's data directory. The onboard views do not contain the
other vehicle (they are rendered with both vehicles moved out of the world); the run's report says how
often the other vehicle's centre is inside each RGB camera's field of view (`in_view`), which is the time
the onboard images are missing it.
"""
import argparse
import io
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
import pybullet as p
from PIL import Image, ImageDraw

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent))
import render_flight as RF  # noqa: E402

import gorge as G  # noqa: E402
import sensors as S  # noqa: E402
from render_world import Scene, font  # noqa: E402

VIDEO_PY = HERE / ".venv-video" / "bin" / "python"
FIRE_QUALITY = "still"
BG = (24, 24, 28)


class Pair(Scene):
    """render_world.Scene for two recorded vehicles (vN.csv of a formation run); client=False loads the
    flight data only."""

    def __init__(self, g, run, client=True):
        self.g = g
        if client:
            self.c = p.connect(p.DIRECT)
            self.bodies = g.load(self.c, "visual")
            self.fires = S.FI.Fires(g, "still")
        self.runs = []
        for v in (1, 2):
            d, meta, wps, pos, sp, quat = RF.load(str(run / f"v{v}.csv"))
            ang, spd = RF.prop_state(d)
            self.runs.append(dict(d=d, meta=meta, pos=pos, quat=quat, angle=ang, speed=spd, t=d["t"], body=None))

    def at(self, v, t):
        r = self.runs[v]
        k = int(np.argmin(np.abs(r["t"] - t)))
        return k if abs(r["t"][k] - t) < 0.01 else None

    def pose(self, v, k):
        r = self.runs[v]
        return r["pos"][k], RF.body_rotation(r["quat"][k]), r["angle"][k], r["speed"][k]

    def place(self, v, k):
        r = self.runs[v]
        veh = self.pose(v, k)
        R = veh[1]
        if r["body"] is None:
            r["body"] = p.loadURDF(RF.model_path("x500"), r["pos"][k].tolist(), RF.quat_xyzw(R), useFixedBase=True,
                                   physicsClientId=self.c)
        else:
            p.resetBasePositionAndOrientation(r["body"], r["pos"][k].tolist(), RF.quat_xyzw(R), physicsClientId=self.c)
        return veh

    def hide(self, v):
        r = self.runs[v]
        if r["body"] is not None:
            p.resetBasePositionAndOrientation(r["body"], [0, 0, -500], [0, 0, 0, 1], physicsClientId=self.c)


class SplitThermal(S.ThermalCamera):
    """sensors.ThermalCamera.capture in two halves, for sharded rendering: `optics` (render, radiometry,
    fires, optics; no state) and `detector` (gain state, non-uniformity, temporal noise, saturation,
    quantization; carries state, so it runs serially). optics then detector gives capture's temp_c
    exactly (the statements are capture's, in its order); keep them in step with sensors.py."""

    def optics(self, R_wb, p_wb, t=0.0):
        s, ss = self.s, self.s.ss
        W, H = s.width * ss, s.height * ss
        eye, fwd, up, right = S.camera_pose(R_wb, p_wb, self.mount)
        view, proj = S.matrices(eye, fwd, up, s.hfov_deg, W, H, self.near, self.far, self.c)
        self.cull(eye, fwd, up, right, s.hfov_deg, W, H, self.far)
        rgb, dep, seg = S.tiny(self.c, W, H, view, proj, seg=self.want_fill)
        kz = S.range_factor(W, H, s.hfov_deg)
        sky = dep >= 0.99999
        z = np.where(sky, np.inf, S.linear_depth(dep, self.near, self.far)).astype(np.float32)
        rng_m = np.where(sky, np.inf, z * kz)
        rgbf = rgb.astype(np.float32)
        t_k = np.float32(G.T_ENC_MIN) + (rgbf[..., 0] * 256 + rgbf[..., 1]) * np.float32(G.T_ENC_SPAN / 65535)
        emis = rgbf[..., 2] / 255
        tau = np.exp(-S.ALPHA_PER_M * np.where(sky, 0, rng_m)).astype(np.float32)
        L = tau * (emis * S.band_radiance(t_k) + (1 - emis) * self.L_air) + (1 - tau) * self.L_air
        if sky.any():
            ii, jj = np.nonzero(sky)
            tx = math.tan(math.radians(s.hfov_deg) / 2)
            ty = tx * H / W
            d = (((jj + 0.5) / W * 2 - 1) * tx)[:, None] * right + ((1 - (ii + 0.5) / H * 2) * ty)[:, None] * up + fwd
            L[sky] = S.band_radiance(S.T_SKY(np.arcsin(np.clip(d[:, 2] / np.linalg.norm(d, axis=1), -1, 1))))
        if self.fires is not None:
            L, zf, fire_rho = self.fires.render_thermal(L, z, S.FI.Camera(eye, fwd, up, right, s.hfov_deg, W, H, self.near), t,
                                                        S.band_radiance, G.T_AIR_C + 273.15, per_fire=self.want_fill)
        blk = (lambda a: a.reshape(s.height, ss, s.width, ss).mean(axis=(1, 3))) if ss > 1 else (lambda a: a)
        Lp = blk(L)
        core = S.gaussian_filter(Lp, s.psf_sigma_px, mode="nearest")
        frac = sum(b for b, _ in s.halo)
        small = Lp.reshape(s.height // 4, 4, s.width // 4, 4).mean(axis=(1, 3))
        halo = sum(b * S.gaussian_filter(small, sg / 4, mode="nearest") for b, sg in s.halo)
        return (1 - frac) * core + S.zoom(halo, 4, order=1)

    def detector(self, Lo):
        s = self.s
        L_hi = S.band_radiance(s.t_max_c + 273.15)
        hot = float((Lo > 0.9 * L_hi).mean())
        if self.gain_high and hot > 0.002:
            self.gain_high = False
        elif not self.gain_high and float((Lo > S.band_radiance(s.t_max_c - 20 + 273.15)).mean()) < 0.0005:
            self.gain_high = True
        L_max = L_hi if self.gain_high else S.band_radiance(s.t_max_low_c + 273.15)
        netd = s.netd_k if self.gain_high else s.netd_low_k
        sig = Lo * self.fpn_gain + self.fpn_off * (1.0 if self.gain_high else 2.0)
        sig = sig + self.dL * (netd * self.rng.normal(size=sig.shape) + s.row_noise_k * self.rng.normal(size=(s.height, 1)))
        sig = np.clip(sig, self.L_min, L_max)
        q = (L_max - self.L_min) / (2 ** s.adc_bits - 1)
        counts = np.round((sig - self.L_min) / q)
        Lq = self.L_min + counts * q
        temp_c = S.band_temperature(Lq) - 273.15
        return temp_c.astype(np.float32)


class KeepRaw:
    """An RGBCamera exposure that keeps the frame before exposure (render_rgb calls it with the float
    image) and applies none; `expose` then does what render_rgb does with an AutoExposure."""

    def __call__(self, img):
        self.img = img.copy()
        return 1.0


def expose(ae, img):
    gain = ae(img)
    if gain != 1.0:
        img = img * np.float32(gain)
    return S.tone(img).astype(np.uint8)


def in_fov(R, pos, other, hfov, w, h, mount=S.FORWARD):
    eye, fwd, up, right = S.camera_pose(R, pos, mount)
    d = other - eye
    z = d @ fwd
    if z <= 0:
        return False
    tx = math.tan(math.radians(hfov) / 2)
    return abs(d @ right / z) <= tx and abs(d @ up / z) <= tx * h / w


# --- one frame ---------------------------------------------------------------------------------------------

class Setup:
    """Everything a frame needs besides the renderers: run, plan, times, layout."""

    def __init__(self, run, every, W=720, H=400, span=None):
        self.run, self.every, self.W, self.H, self.span = Path(run), every, W, H, span
        self.fm = json.loads((self.run / "formation.json").read_text())
        self.g = G.Gorge(self.fm["gorge_seed"])
        self.g.write_assets()
        self.PW, self.PH = W // 4, W * 3 // 16          # four panels under the chase view, 4:3
        self.f = np.genfromtxt(self.run / "formation.csv", delimiter=",", names=True)
        self.rev = self.fm["reverse"]

    def times(self, sc):
        t_end = min(sc.runs[0]["t"][-1], sc.runs[1]["t"][-1])
        ts = np.arange(0.0, t_end, self.every)
        return ts if self.span is None else ts[(ts >= self.span[0] - 1e-9) & (ts < self.span[1] - 1e-9)]

    def poses(self, sc, t):
        ks = [sc.at(v, t) for v in (0, 1)]
        return [None if k is None else sc.pose(v, k) for v, k in enumerate(ks)], ks

    def chase(self, sc, t):
        """The canvas of a frame without the four panel images: chase view (the vehicles placed in sc's
        client), labels, status line, panel titles. Leaves both vehicles out of the world."""
        W, H, PW, PH, g, fm = self.W, self.H, self.PW, self.PH, self.g, self.fm
        _, ks = self.poses(sc, t)
        vehicles, poses = [], []
        for v in (0, 1):
            if ks[v] is None:
                sc.hide(v)
                poses.append(None)
                continue
            veh = sc.place(v, ks[v])
            vehicles.append(veh)
            poses.append((veh[0], veh[1]))
        live = [q for q in poses if q is not None]
        mid = np.mean([q[0] for q in live], axis=0)
        ax = g.axis_dir(mid[1])
        eye = mid - 5.0 * ax + [0, 0, 1.9]
        tgt = mid + 5.0 * ax - [0, 0, 1.0]
        img, px = sc.shoot(W, H, eye, tgt, (0, 0, 1), 56, 0.05, 200, vehicles, 1.0, t=t)
        sc.hide(0)
        sc.hide(1)
        canvas = Image.new("RGB", (W, H + PH + 22), BG)
        canvas.paste(img, (0, 0))
        dr = ImageDraw.Draw(canvas, "RGBA")
        for v, q in enumerate(poses):
            if q is None:
                continue
            a, ok = px(q[0] + [0, 0, 0.45])
            if ok[0]:
                tag = f"V{v + 1}" + (" (rear, flying backward)" if self.rev[v] else "")
                dr.text((a[0][0], a[0][1] - 4), tag, font=font(13, True), fill=(255, 255, 255), anchor="ms",
                        stroke_width=2, stroke_fill=(0, 0, 0))
        side = "rear-view" if self.rev[1] else "forward"
        titles = ["V1 forward RGB", "V1 forward thermal", f"V2 {side} RGB", f"V2 {side} thermal"]
        for j, ttl in enumerate(titles):
            dr.text((j * PW + 4, H + 4), ttl, font=font(12, True), fill=(235, 235, 235))
        k = int(np.argmin(np.abs(self.f["t"] - (t + 1 / 400))))
        north = float(mid[1])
        dr.rectangle([0, 0, W, 24], fill=(0, 0, 0, 150))
        dr.text((8, 5), f"{fm['plan']}   t {t:5.2f} s   N {north:5.1f} m   separation {self.f['dist'][k]:4.2f} m (nominal "
                f"{fm['nominal_distance']:.2f})", font=font(13, True), fill=(255, 255, 255))
        return canvas, north

    def finish(self, canvas, rgbs, temps, agcs):
        """Paste the panels: rgbs[v] (uint8 image or None when vehicle v is absent), temps[v] (thermal
        apparent temperature) through agcs[v]."""
        PW, PH = self.PW, self.PH
        for v in (0, 1):
            if rgbs[v] is None:
                pn = [Image.new("RGB", (PW, PH), (0, 0, 0))] * 2
            else:
                pn = [Image.fromarray(rgbs[v]).resize((PW, PH), Image.BILINEAR),
                      Image.fromarray(agcs[v](temps[v])).resize((PW, PH), Image.BILINEAR)]
            for j, im in enumerate(pn):
                canvas.paste(im, ((2 * v + j) * PW, self.H + 22))
        return canvas

    def inview(self, sc, t, acc):
        poses, _ = self.poses(sc, t)
        for v in (0, 1):
            if poses[v] is not None and poses[1 - v] is not None:
                acc[f"v{v + 1} sees v{2 - v}"] += int(in_fov(poses[v][1], poses[v][0], poses[1 - v][0], 90.0, 320, 240))
        acc["n"] += 1


# --- streaming outputs -------------------------------------------------------------------------------------

class GifStream:
    """An animated GIF written frame by frame (each frame its own adaptive palette as a local color table,
    loop forever): each frame is encoded by Pillow as a one-frame GIF whose global table becomes the
    frame's local one."""

    def __init__(self, path, size, ms, colors):
        self.fp, self.ms, self.colors = open(path, "wb"), ms, colors
        w, h = size
        self.fp.write(b"GIF89a" + w.to_bytes(2, "little") + h.to_bytes(2, "little") + bytes([0, 0, 0]))
        self.fp.write(b"\x21\xff\x0bNETSCAPE2.0\x03\x01\x00\x00\x00")

    def add(self, img):
        b = io.BytesIO()
        img.convert("P", palette=Image.ADAPTIVE, colors=self.colors).save(b, "GIF", duration=self.ms)
        d = b.getvalue()
        flags = d[10]
        gct = d[13:13 + 3 * 2 ** ((flags & 7) + 1)] if flags & 0x80 else b""
        i, out = 13 + len(gct), []
        while d[i] != 0x3B:
            if d[i] == 0x21:                         # extension: keep the graphic control one
                j = i + 2
                while d[j]:
                    j += d[j] + 1
                if d[i + 1] == 0xF9:
                    out.append(d[i:j + 1])
                i = j + 1
            elif d[i] == 0x2C:                       # image: descriptor with the local table, then the data
                desc = bytearray(d[i:i + 10])
                if gct:
                    desc[9] = (desc[9] & 0x78) | 0x80 | (flags & 7)
                j = i + 11
                while d[j]:
                    j += d[j] + 1
                out += [bytes(desc), gct, d[i + 10:j + 1]]
                i = j + 1
            else:
                raise ValueError("unexpected GIF block")
        self.fp.write(b"".join(out))

    def close(self):
        self.fp.write(b";")
        self.fp.close()


MP4_ENCODER = r"""
import sys
from fractions import Fraction
import av, numpy as np
W, H, num, den, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
c = av.open(out, "w", options={"movflags": "faststart"})
s = c.add_stream("libx264", rate=Fraction(num, den))
s.width, s.height, s.pix_fmt = W, H, "yuv420p"
s.options = {"crf": "18", "preset": "medium"}
n, f = W * H * 3, sys.stdin.buffer
while True:
    b = f.read(n)
    if len(b) < n:
        break
    for pk in s.encode(av.VideoFrame.from_ndarray(np.frombuffer(b, np.uint8).reshape(H, W, 3), format="rgb24")):
        c.mux(pk)
for pk in s.encode():
    c.mux(pk)
c.close()
"""


class Mp4Stream:
    """H.264 (libx264, yuv420p, CRF 18) through PyAV in .venv-video: raw RGB frames piped to it; the height
    padded to even with the background color."""

    def __init__(self, path, size, every):
        self.w, self.h = size[0] + size[0] % 2, size[1] + size[1] % 2
        r = Fraction(1 / every).limit_denominator(1000)
        self.proc = subprocess.Popen([str(VIDEO_PY), "-c", MP4_ENCODER, str(self.w), str(self.h), str(r.numerator),
                                      str(r.denominator), str(path)], stdin=subprocess.PIPE)

    def add(self, img):
        if img.size != (self.w, self.h):
            pad = Image.new("RGB", (self.w, self.h), BG)
            pad.paste(img, (0, 0))
            img = pad
        self.proc.stdin.write(img.tobytes())

    def close(self):
        self.proc.stdin.close()
        if self.proc.wait() != 0:
            raise RuntimeError("mp4 encoder failed")


class _Frames:
    """Frame PNGs as one multi-frame image for Pillow's WebP writer, opened one at a time."""

    def __init__(self, paths):
        self.paths, self.n_frames, self.cur = paths, len(paths), None

    def seek(self, i):
        self.cur = Image.open(self.paths[i]).convert("RGB")

    def __getattr__(self, a):
        return getattr(self.cur, a)


class Outputs:
    def __init__(self, out, name, every, n, mp4=True):
        self.out, self.name, self.every = Path(out), name, every
        self.ms = int(round(1000 * every))
        self.dir = self.out / f"{name}-frames"
        self.dir.mkdir(parents=True, exist_ok=True)
        for old in self.dir.glob("frame_*.png"):
            old.unlink()
        self.digits = max(3, len(str(n - 1)))
        self.gif = None
        self.mp4 = mp4 and VIDEO_PY.exists()
        self.v = None
        self.paths = []
        self.still_t = None

    def add(self, i, t, canvas, north):
        path = self.dir / f"frame_{i:0{self.digits}d}.png"
        canvas.save(path)
        self.paths.append(path)
        if self.still_t is None and north >= 22.0:
            self.still_t = t
            canvas.save(self.out / f"{self.name}-still.png")
        if self.gif is None:
            self.gif = GifStream(self.out / f"{self.name}.gif", canvas.size, self.ms, 160)
            self.v = Mp4Stream(self.out / f"{self.name}.mp4", canvas.size, self.every) if self.mp4 else None
        self.gif.add(canvas)
        if self.v is not None:
            self.v.add(canvas)

    def close(self):
        self.gif.close()
        if self.v is not None:
            self.v.close()
        first = Image.open(self.paths[0]).convert("RGB")
        first.save(self.out / f"{self.name}.webp", save_all=True, append_images=[_Frames(self.paths[1:])], duration=self.ms,
                   loop=0, quality=72, method=4)
        sizes = {ext: round((self.out / f"{self.name}.{ext}").stat().st_size / 1e6, 1) for ext in ("gif", "webp", "mp4")
                 if (self.out / f"{self.name}.{ext}").exists()}
        if sizes["gif"] > 100:
            sizes["small_gif"] = self.small()
        return sizes

    def small(self, width=480, colors=96, limit_mb=50.0):
        """NAME-small.gif: the same frames at `width` and `colors`, reduced further until under limit_mb."""
        path = self.out / f"{self.name}-small.gif"
        while True:
            w0, h0 = Image.open(self.paths[0]).size
            size = (width, round(h0 * width / w0))
            gs = GifStream(path, size, self.ms, colors)
            for q in self.paths:
                gs.add(Image.open(q).convert("RGB").resize(size, Image.LANCZOS))
            gs.close()
            mb = path.stat().st_size / 1e6
            print(f"small GIF {size[0]} x {size[1]}, {colors} colors: {mb:.1f} MB", flush=True)
            if mb < limit_mb:
                return dict(mb=round(mb, 1), width=size[0], height=size[1], colors=colors)
            width, colors = int(width * 0.85) // 2 * 2, max(48, int(colors * 0.8))


# --- serial and sharded rendering ---------------------------------------------------------------------------

def render(run, out, name, every=0.3, W=720, H=400, workers=1, mp4=True, span=None):
    if workers > 1:
        return render_sharded(run, out, name, every, W, H, workers, mp4, span)
    st = Setup(run, every, W, H, span)
    g, fm = st.g, st.fm
    sc = Pair(g, Path(run))
    th = p.connect(p.DIRECT)
    bt = g.load(th, "thermal")
    rgb = [S.RGBCamera(sc.c, sc.bodies, S.FORWARD, gorge=g, fire_quality=FIRE_QUALITY) for _ in range(2)]
    therm = [S.ThermalCamera(th, bt, S.FORWARD, seed=fm["seed"] + 100 * v, gorge=g, fire_quality=FIRE_QUALITY) for v in range(2)]
    agcs = [S.AGC() for _ in range(2)]
    ts = st.times(sc)
    o = Outputs(out, name, every, len(ts), mp4)
    acc = {"v1 sees v2": 0, "v2 sees v1": 0, "n": 0}
    t0 = time.time()
    for i, t in enumerate(ts):
        canvas, north = st.chase(sc, t)
        poses, _ = st.poses(sc, t)
        rgbs, temps = [None, None], [None, None]
        for v in (0, 1):
            if poses[v] is not None:
                pos, R = poses[v][0], poses[v][1]
                rgbs[v] = rgb[v].capture(R, pos, t)["rgb"]
                temps[v] = therm[v].capture(R, pos, t)["temp_c"]
        st.finish(canvas, rgbs, temps, agcs)
        st.inview(sc, t, acc)
        o.add(i, t, canvas, north)
    return report(o, st, acc, len(ts), workers, time.time() - t0)


def report(o, st, acc, n, workers, wall):
    sizes = o.close()
    info = dict(run=str(st.run), frames=n, every_s=st.every, frame_ms=o.ms, workers=workers, render_wall_s=round(wall, 1),
                mb=sizes, gif_mb=sizes["gif"], still_t=o.still_t,
                other_vehicle_in_rgb_fov_fraction={k: v / max(acc["n"], 1) for k, v in acc.items() if k != "n"})
    (o.dir / "render.json").write_text(json.dumps(info, indent=1) + "\n")
    print(json.dumps(info), flush=True)
    return info


def _save_atomic(path, write):
    tmp = path.with_name(path.name + ".part")
    with open(tmp, "wb") as fh:
        write(fh)
    os.replace(tmp, path)


def _worker(kind, run, every, W, H, span, raw, jobs, ready):
    """kind "vis": chase canvas (PNG) and both RGB panels before exposure; kind "th": both thermal panels'
    optical signal. One PyBullet client per process."""
    st = Setup(run, every, W, H, span)
    g, fm = st.g, st.fm
    if kind == "vis":
        sc = Pair(g, st.run)
        keep = [KeepRaw(), KeepRaw()]
        cams = [S.RGBCamera(sc.c, sc.bodies, S.FORWARD, gorge=g, fire_quality=FIRE_QUALITY, exposure=keep[v]) for v in range(2)]
    else:
        sc = Pair(g, st.run, client=False)
        th = p.connect(p.DIRECT)
        bt = g.load(th, "thermal")
        cams = [SplitThermal(th, bt, S.FORWARD, seed=fm["seed"] + 100 * v, gorge=g, fire_quality=FIRE_QUALITY) for v in range(2)]
    ts = st.times(sc)
    ready.put(kind)
    while True:
        job = jobs.get()
        if job is None:
            return
        for i in job:
            t = ts[i]
            poses, _ = st.poses(sc, t)
            if kind == "vis":
                canvas, north = st.chase(sc, t)
                arr = [None, None]
                for v in (0, 1):
                    if poses[v] is not None:
                        cams[v].capture(poses[v][1], poses[v][0], t)
                        arr[v] = keep[v].img
                _save_atomic(raw / f"vis_{i:05d}.npz", lambda fh: np.savez(fh, canvas=np.asarray(canvas), north=north,
                                                                            **{f"rgb{v}": a for v, a in enumerate(arr) if a is not None}))
            else:
                arr = {f"lo{v}": cams[v].optics(poses[v][1], poses[v][0], t) for v in (0, 1) if poses[v] is not None}
                _save_atomic(raw / f"th_{i:05d}.npz", lambda fh: np.savez(fh, **arr))


def render_sharded(run, out, name, every, W, H, workers, mp4, span=None, chunk=4):
    st = Setup(run, every, W, H, span)
    fm = st.fm
    sc = Pair(st.g, st.run, client=False)
    ts = st.times(sc)
    o = Outputs(out, name, every, len(ts), mp4)
    raw = o.dir / ".raw"
    shutil.rmtree(raw, ignore_errors=True)
    raw.mkdir()
    ctx = mp.get_context("spawn")
    n_vis = workers // 2                # the thermal half is the slower one
    kinds = ["vis"] * n_vis + ["th"] * (workers - n_vis)
    queues = {k: ctx.Queue() for k in ("vis", "th")}
    chunks = [list(range(a, min(a + chunk, len(ts)))) for a in range(0, len(ts), chunk)]
    for k, q in queues.items():
        for c in chunks:
            q.put(c)
        for _ in range(kinds.count(k)):
            q.put(None)
    ready = ctx.Queue()
    procs = []
    t0 = time.time()
    for k in kinds:                     # one at a time: loading the world takes several GB for a moment
        pr = ctx.Process(target=_worker, args=(k, str(run), every, W, H, span, raw, queues[k], ready), daemon=True)
        pr.start()
        procs.append(pr)
        ready.get(timeout=600)
    print(f"{workers} workers ({kinds.count('vis')} chase and RGB, {kinds.count('th')} thermal) ready after "
          f"{time.time() - t0:.0f} s", flush=True)
    therm = [SplitThermal(None, {}, S.FORWARD, seed=fm["seed"] + 100 * v, gorge=st.g, fire_quality=FIRE_QUALITY) for v in range(2)]
    aes = [S.AutoExposure() for _ in range(2)]
    agcs = [S.AGC() for _ in range(2)]
    acc = {"v1 sees v2": 0, "v2 sees v1": 0, "n": 0}
    for i, t in enumerate(ts):
        fv, ft = raw / f"vis_{i:05d}.npz", raw / f"th_{i:05d}.npz"
        while not (fv.exists() and ft.exists()):
            dead = [pr for pr in procs if pr.exitcode not in (None, 0)]
            if dead:
                raise RuntimeError(f"a worker failed (exit {dead[0].exitcode})")
            time.sleep(0.05)
        a, b = np.load(fv), np.load(ft)
        canvas = Image.fromarray(a["canvas"])
        rgbs = [expose(aes[v], a[f"rgb{v}"]) if f"rgb{v}" in a else None for v in (0, 1)]
        temps = [therm[v].detector(b[f"lo{v}"]) if f"lo{v}" in b else None for v in (0, 1)]
        st.finish(canvas, rgbs, temps, agcs)
        st.inview(sc, t, acc)
        o.add(i, t, canvas, float(a["north"]))
        fv.unlink()
        ft.unlink()
        if i % 50 == 0:
            print(f"frame {i}/{len(ts)}  {time.time() - t0:.0f} s", flush=True)
    for pr in procs:
        pr.join()
    shutil.rmtree(raw, ignore_errors=True)
    return report(o, st, acc, len(ts), workers, time.time() - t0)


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--name", default=None)
    ap.add_argument("--every", type=float, default=0.3)
    ap.add_argument("--out", default=str(HERE / "out"))
    ap.add_argument("--workers", type=int, default=1, help="rendering processes (more than 1: sharded, same frames)")
    ap.add_argument("--no-mp4", action="store_true")
    ap.add_argument("--span", type=float, nargs=2, default=None, metavar=("T0", "T1"),
                    help="render only the frames in [T0, T1) s (for checks)")
    a = ap.parse_args()
    run = Path(a.run)
    name = a.name or "formation-" + json.loads((run / "formation.json").read_text())["plan"]
    render(run, a.out, name, a.every, workers=a.workers, mp4=not a.no_mp4, span=a.span)


if __name__ == "__main__":
    main()
