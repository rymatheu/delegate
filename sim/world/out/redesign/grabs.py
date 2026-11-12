"""Screen grabs of the redesigned gorge world, fires and thermal camera (out/redesign/grabs/).

    python out/redesign/grabs.py [--only NAME ...] [--ss 2]

Scene views are rendered at ss x the output size and averaged down (anti-aliasing); thermal images
are the camera's own output (640 x 512) shown 2x. Captions use DejaVu Sans from Matplotlib.
"""
import argparse
import math
import sys
from pathlib import Path

import matplotlib
import numpy as np
import pybullet as p
from PIL import Image, ImageDraw, ImageFont

HERE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(HERE))
import fire as FI  # noqa: E402
import gorge as G  # noqa: E402
import sensors as S  # noqa: E402

OUT = HERE / "out" / "redesign" / "grabs"
FONT = Path(matplotlib.get_data_path()) / "fonts/ttf/DejaVuSans.ttf"
OLD = HERE.parents[1] / "gallery"          # the earlier renders (read only)


def font(n):
    return ImageFont.truetype(str(FONT), n)


def caption(img, text, size=None):
    """A one-line caption in a dark band under the image."""
    size = size or max(14, img.width // 90)
    while size > 10 and ImageDraw.Draw(img).textlength(text, font=font(size)) > img.width - 20:
        size -= 1
    band = int(size * 1.7)
    out = Image.new("RGB", (img.width, img.height + band), (22, 22, 24))
    out.paste(img, (0, 0))
    ImageDraw.Draw(out).text((10, img.height + band // 2), text, font=font(size), fill=(230, 230, 230), anchor="lm")
    return out


class World:
    def __init__(self):
        self.g = G.Gorge(7)
        self.vis = p.connect(p.DIRECT)
        self.th = p.connect(p.DIRECT)
        self.bv = self.g.load(self.vis, "visual")
        self.bt = self.g.load(self.th, "thermal")
        self.fires = FI.Fires(self.g, "still")
        self.fires_live = FI.Fires(self.g, "live")
        self.vis_live, self.th_live = p.connect(p.DIRECT), p.connect(p.DIRECT)        # the live level of detail
        self.bv_live = self.g.load(self.vis_live, "visual", lod=2)
        self.bt_live = self.g.load(self.th_live, "thermal", lod=2)

    def live_rgb_cam(self, W=640, H=480, hfov=90.0):
        """The onboard RGB camera exactly as camera_render.py runs it (live world, live fires, culling,
        automatic exposure)."""
        return S.RGBCamera(self.vis_live, self.bv_live, S.FORWARD, W, H, hfov, gorge=self.g)

    def live_th_cam(self, seed=0):
        """The onboard thermal camera as camera_render.py runs it: the core's chain rendered at 320 x 256."""
        core = S.ThermalSpec()
        spec = S.ThermalSpec(width=core.width // 2, height=core.height // 2, pitch_um=core.pitch_um * 2)
        return S.ThermalCamera(self.th_live, self.bt_live, S.FORWARD, spec, seed=seed, gorge=self.g)

    @staticmethod
    def at(cam, eye, target, t):
        """Capture with camera `cam` from eye toward target (the mount set aside)."""
        eye, fwd, up, right = S.look_at(eye, target)
        R = np.column_stack([fwd, -right, up])
        m = cam.mount
        cam.mount = S.Mount(pos=(0, 0, 0), pitch_deg=0.0)
        fr = cam.capture(R, eye, t)
        cam.mount = m
        return fr

    def view(self, eye, target, W, H, hfov=60.0, t=0.0, ss=2, fires=True, live=False):
        eye, fwd, up, right = S.look_at(eye, target)
        fr = (self.fires_live if live else self.fires) if fires else None
        rgb, z, _ = S.render_rgb(self.vis, eye, fwd, up, right, hfov, W * ss, H * ss, 0.05, 600.0, t, fr)
        im = Image.fromarray(rgb)
        return im.resize((W, H), Image.LANCZOS) if ss > 1 else im

    def thermal(self, eye, target, t=0.0, ss=2, seed=0, spec=None, cam=None, live=False):
        spec = spec or S.ThermalSpec(ss=ss)
        cam = cam or S.ThermalCamera(self.th, self.bt, S.FORWARD, spec, seed=seed, gorge=self.g, fire_quality="live" if live else "still")
        eye, fwd, up, right = S.look_at(eye, target)
        R = np.column_stack([fwd, -right, up])           # body FLU with x along fwd
        m = cam.mount
        cam.mount = S.Mount(pos=(0, 0, 0), pitch_deg=0.0)
        fr = cam.capture(R, eye, t)
        cam.mount = m
        return fr, cam


def up_thermal(fr):
    """A live thermal frame (320 x 256) resized to the stream's 640 x 512, as camera_render.py does."""
    from scipy.ndimage import zoom
    fr = dict(fr)
    fr["temp_c"] = zoom(fr["temp_c"], 2, order=1)
    return fr


def heading_R(d):
    d = np.array([d[0], d[1], 0.0]); d /= np.linalg.norm(d)
    return np.column_stack([d, [-d[1], d[0], 0.0], [0, 0, 1.0]])


def thermal_panel(fr, mode="agc", lo=20.0, hi=300.0, agc=None, scale=2, bar=True, unit="C"):
    t = fr["temp_c"]
    rgb = (agc or S.AGC())(t) if mode == "agc" else S.fixed_scale(t, lo, hi)
    im = Image.fromarray(rgb).resize((t.shape[1] * scale, t.shape[0] * scale), Image.BICUBIC)
    if bar:
        dr = ImageDraw.Draw(im)
        H = im.height
        bh, bw = int(H * 0.55), 22
        x0, y0 = im.width - bw - 18, (H - bh) // 2
        if mode == "agc":
            tmin, tmax = float(np.quantile(t, 0.002)), float(t.max())
        else:
            tmin, tmax = lo, hi
        im.paste(Image.fromarray(S.colorbar(bh, bw)), (x0, y0))
        dr.rectangle([x0 - 1, y0 - 1, x0 + bw, y0 + bh], outline=(230, 230, 230))
        f = font(max(14, H // 36))
        for txt, yy, anc in ((f"{tmax:.0f} {unit}", y0 - 6, "rb"), (f"{tmin:.0f} {unit}", y0 + bh + 6, "rt")):
            l, tp, r, b = dr.textbbox((x0 + bw, yy), txt, font=f, anchor=anc)
            dr.rectangle([l - 5, tp - 3, r + 5, b + 3], fill=(0, 0, 0))
            dr.text((x0 + bw, yy), txt, font=f, fill=(255, 255, 255), anchor=anc)
    return im


def grid(ims, cols, pad=6, bg=(22, 22, 24)):
    w, h = ims[0].width, ims[0].height
    rows = int(math.ceil(len(ims) / cols))
    out = Image.new("RGB", (cols * w + (cols + 1) * pad, rows * h + (rows + 1) * pad), bg)
    for k, im in enumerate(ims):
        out.paste(im, (pad + (k % cols) * (w + pad), pad + (k // cols) * (h + pad)))
    return out


def label(im, text, size=18):
    dr = ImageDraw.Draw(im)
    f = font(size)
    l, t, r, b = dr.textbbox((10, 8), text, font=f)
    dr.rectangle([l - 5, t - 4, r + 5, b + 4], fill=(0, 0, 0))
    dr.text((10, 8), text, font=f, fill=(255, 255, 255))
    return im


# --- the views -------------------------------------------------------------------------------------------

KIND = {"shrub": "a burning shrub with a litter fire around it", "tree": "a surface fire at the base of a small pine",
        "litter": "a litter fire", "grass": "a grass fire", "log": "a burning log in a litter fire"}


def fire_view(w, k, dist, height, side=-0.4, back=True):
    """Eye and target for looking at fire k from `dist` m (from the approach side, a little to the side)."""
    f = w.g.firebrands[k]
    ax = w.g.axis_dir(f.center[1])
    perp = np.array([ax[1], -ax[0], 0.0])
    eye = f.center - ax * dist * math.cos(side) + perp * dist * math.sin(side)
    eye[2] = w.g.ground_z(eye[None, :2])[0] + height
    tgt = f.center + [0, 0, 0.35]
    return eye, tgt


def open_fires(w):
    return [k for k, f in enumerate(w.g.firebrands) if not f.hidden]


def run(names, ss):
    w = World()
    g = w.g
    OUT.mkdir(parents=True, exist_ok=True)
    Wd, Hd = 1600, 900
    yc = lambda y: np.array([g.xc_fn(y), y, g.floor_c(y)])
    if "gorge-oblique-1" in names:
        e = yc(-8.0) + [-4.0, 0, 17.0]
        im = w.view(e, yc(24.0) + [0, 0, 1.0], Wd, Hd, 62, ss=ss)
        caption(im, "Into the gorge from the south, 17 m above the wash (seed 7): basalt colonnade and entablature, talus with shrubs, dry wash [still quality: 2x supersampled, flames at full resolution]").save(OUT / "gorge-oblique-1.png")
    if "gorge-oblique-2" in names:
        y = 34.0
        e = np.array([g.at_lateral(y, -2.5), y, g.floor_c(y) + 13.0])
        tgt = np.array([g.at_lateral(y + 14, 6.0), y + 14, g.floor_c(y + 14) + 7.0])
        im = w.view(e, tgt, Wd, Hd, 70, ss=ss)
        caption(im, "Inside the gorge 13 m above the wash, toward the sunlit east wall: colonnade, entablature, talus apron with shrubs, the dry wash [still quality: 2x supersampled, flames at full resolution]").save(OUT / "gorge-oblique-2.png")
    if "gorge-floor" in names:
        cands = [b for b in g.boulders if 6 < b.center[1] < 66 and b.cluster < 0 and b.size > 1.6 and not b.wall]
        b = cands[int(np.argmax([g.sunlit(b.center[None] + [0, 0, 0.3], np.array([[0, 0, 1.0]]))[0] * b.size for b in cands]))]
        d = np.array([math.cos(math.radians(40)), math.sin(math.radians(40)), 0.0])       # looking north-east, the sun behind
        e = b.center - d * 4.2
        e[2] = g.ground_z(e[None, :2])[0] + 1.0
        tgt = b.center + d * 3 + [0, 0, 0.4]
        im = w.view(e, tgt, Wd, Hd, 70, ss=ss)
        caption(im, "On the wash among boulders, 1 m above the ground: partly buried boulders with chips, cobbles and grass at their foot [still quality: 2x supersampled, flames at full resolution]").save(OUT / "gorge-floor.png")
    if "gorge-top" in names:
        Wt, Ht = 2400, 900
        y0, y1 = -10.0, 86.0
        ym = (y0 + y1) / 2
        hgt = 600.0
        e = np.array([g.xc_fn(ym), ym, hgt])
        fov = 2 * math.degrees(math.atan((y1 - y0) / 2 / hgt))
        eye, fwd, up, right = e, np.array([0, 0, -1.0]), np.array([-1.0, 0, 0]), None
        right = np.cross(fwd, up)
        rgb, z, _ = S.render_rgb(w.vis, eye, fwd, up, right, fov, Wt * ss, Ht * ss, 500.0, 700.0, 0.0, w.fires, haze=False)
        im = Image.fromarray(rgb).resize((Wt, Ht), Image.LANCZOS)
        caption(im, "From above, north to the right, 96 m of the gorge (flight from N 0 to 72 m); smoke drifts up-gorge from the eight fires [still quality: 2x supersampled, flames at full resolution]").save(OUT / "gorge-top.png")
    if "onboard-rgb" in names or "thermal-onboard" in names:
        pts = g.path_points(0.25)
        ks = [k for k, f in enumerate(g.firebrands)]
        ys = [4.0, 16.0, g.firebrands[open_fires(w)[0]].center[1] - 7.0, 38.0, g.firebrands[open_fires(w)[1]].center[1] - 9.0, 63.0]
        rgbs, ths, caps = [], [], []
        camR = w.live_rgb_cam()
        camT = w.live_th_cam()
        agc = S.AGC()
        for i, y in enumerate(ys):
            q = pts[np.argmin(np.abs(pts[:, 1] - y))]
            d = g.axis_dir(y)
            R = heading_R(d)
            t = 2.0 + 0.7 * i
            rgbs.append(label(Image.fromarray(camR.capture(R, q, t)["rgb"]), f"N {y:.0f} m"))
            agc.lut = None
            for _ in range(2):
                fr = up_thermal(camT.capture(R, q, t))
            ths.append(label(thermal_panel(fr, "agc", agc=agc, scale=1, bar=True), f"N {y:.0f} m, {fr['gain']} gain"))
        if "onboard-rgb" in names:
            caption(grid(rgbs, 3), "Onboard forward RGB, 640 x 480, 90 deg, 30 deg down, along the route at 3.5 m [live quality: the onboard camera's own 1x output, flames at half, smoke at a quarter resolution]").save(OUT / "onboard-rgb.png")
        if "thermal-onboard" in names:
            caption(grid(ths, 3), "Onboard forward thermal, 640 x 512, 54 deg, automatic gain, same poses, fires in view and not [live quality: the onboard camera's own 1x output, flames at half, smoke at a quarter resolution]").save(OUT / "thermal-onboard.png")
    if any(n.startswith("fire-rgb") or n.startswith("thermal-fire") for n in names):
        ko = open_fires(w)
        if "fire-rgb-1" in names:
            e, tg = fire_view(w, ko[0], 3.2, 1.3)
            caption(w.view(e, tg, Wd, Hd, 60, t=3.0, ss=ss), f"Fire {ko[0]} (in the open), {KIND[g.firebrands[ko[0]].kind]}, 3.2 m away [still quality: 2x supersampled, flames at full resolution]").save(OUT / "fire-rgb-1.png")
        if "fire-rgb-2" in names:
            e, tg = fire_view(w, ko[1], 9.0, 2.6, side=0.25)
            cr = w.live_rgb_cam()
            for tt in (4.8, 4.9, 5.0):                      # let the automatic exposure settle
                im = Image.fromarray(w.at(cr, e, tg, tt)["rgb"])
            im = im.resize((1280, 960), Image.BICUBIC)
            caption(im, f"Fire {ko[1]} (in the open), {KIND[g.firebrands[ko[1]].kind]}, 9 m away, 640 x 480 90 deg shown 2x [live quality: the onboard camera's own 1x output, flames at half, smoke at a quarter resolution]").save(OUT / "fire-rgb-2.png")
        if "fire-rgb-sequence" in names:
            e, tg = fire_view(w, ko[0], 2.6, 1.0)
            ims = [label(w.view(e, tg, 800, 450, 55, t=4.0 + dt, ss=ss), f"t = {4.0 + dt:.2f} s") for dt in (0.0, 0.15, 0.3, 0.45)]
            caption(grid(ims, 2), "The same fire at four instants 0.15 s apart: flame tongues flicker, tips break off [still quality: 2x supersampled, flames at full resolution]").save(OUT / "fire-rgb-sequence.png")
        if "thermal-fire-1" in names:
            e, tg = fire_view(w, ko[0], 3.2, 1.3)
            fr, _ = w.thermal(e, tg, 3.0, ss)
            caption(thermal_panel(fr, "fixed", 30.0, 300.0), f"Thermal 3.2 m from fire {ko[0]}, fixed scale 30-300 C ({fr['gain']} gain) [still quality: 2x supersampled, flames at full resolution]").save(OUT / "thermal-fire-1.png")
        if "thermal-fire-2" in names:
            e, tg = fire_view(w, ko[1], 9.0, 2.6, side=0.25)
            ct = w.live_th_cam()
            agc2 = S.AGC()
            agc2(up_thermal(w.at(ct, e, tg, 5.0))["temp_c"])
            fr = up_thermal(w.at(ct, e, tg, 5.1))
            caption(thermal_panel(fr, "agc", agc=agc2), f"Thermal 9 m from fire {ko[1]}, automatic gain ({fr['gain']} gain) [live quality: the onboard camera's own 1x output, flames at half, smoke at a quarter resolution]").save(OUT / "thermal-fire-2.png")
    if "thermal-aerial" in names:
        y = 34.0
        e = np.array([g.xc_fn(y) + 3, y - 14, g.floor_c(y) + 26])
        fr, cam = w.thermal(e, np.array([g.xc_fn(y + 12), y + 12, g.floor_c(y + 12)]), 2.0, ss)
        fr, _ = w.thermal(e, np.array([g.xc_fn(y + 12), y + 12, g.floor_c(y + 12)]), 2.0, ss, cam=cam)
        caption(thermal_panel(fr, "agc"), f"Thermal from 26 m above the wash looking up-gorge, automatic gain ({fr['gain']} gain) [still quality: 2x supersampled, flames at full resolution]").save(OUT / "thermal-aerial.png")

    if "fire.gif" in names:
        k = open_fires(w)[1]
        e, tg = fire_view(w, k, 4.0, 1.4)
        cam = None
        agc = S.AGC()
        frames = []
        for i in range(30):
            t = 6.0 + 0.1 * i
            if cam is None:
                cam, crg = w.live_th_cam(), w.live_rgb_cam(640, 512, 54.2)
            rgb = Image.fromarray(w.at(crg, e, tg, t)["rgb"])
            fr = up_thermal(w.at(cam, e, tg, t))
            th = thermal_panel(fr, "agc", agc=agc, scale=1, bar=False)
            im = grid([label(rgb, f"RGB, live quality, t = {t:.1f} s", 16), label(th, "thermal, live quality, automatic gain", 16)], 2, pad=4)
            frames.append(im.convert("P", palette=Image.ADAPTIVE, colors=255))
        frames[0].save(OUT / "fire.gif", save_all=True, append_images=frames[1:], duration=100, loop=0, optimize=True)
    if "live-vs-still" in names:
        pts = g.path_points(0.25)
        y = g.firebrands[open_fires(w)[0]].center[1] - 7.0
        q = pts[np.argmin(np.abs(pts[:, 1] - y))]
        R = heading_R(g.axis_dir(y))
        eye, fwd, up, right = S.camera_pose(R, q, S.FORWARD)
        tgt = eye + fwd
        t = 3.0
        still = w.view(eye, tgt, 640, 480, 90.0, t=t, ss=2)
        cr = w.live_rgb_cam()
        for tt in (t - 0.2, t - 0.1, t):
            live = Image.fromarray(cr.capture(R, q, tt)["rgb"])
        fs, _ = w.thermal(eye, tgt, t, 2)
        fs = dict(fs)
        ct = w.live_th_cam()
        fl = up_thermal(ct.capture(R, q, t))
        a1, a2 = S.AGC(), S.AGC()
        ims = [label(still, "still path: full world, 2x supersampled, flames at full resolution", 15),
               label(live, "live path (the onboard camera): live world, 1x, flames at half resolution", 15),
               label(thermal_panel(fs, "agc", agc=a1, scale=1), "still: 640 x 512, full world, 2x2 samples", 15).resize((640, 512)),
               label(thermal_panel(fl, "agc", agc=a2, scale=1), "live: rendered at 320 x 256, live world, resized", 15).resize((640, 512))]
        top = grid(ims[:2], 2, pad=6)
        bot = grid(ims[2:], 2, pad=6)
        out = Image.new("RGB", (top.width, top.height + bot.height), (22, 22, 24))
        out.paste(top, (0, 0)); out.paste(bot, (0, top.height))
        caption(out, f"The same onboard pose (N {y:.0f} m, forward camera) through the still path (left) and the live path of the onboard cameras (right)").save(OUT / "live-vs-still.png")
    if "before-after" in names:
        pairs = [("oblique.png", HERE / "out" / "oblique.png", "gorge, from the south"),
                 ("onboard-rgb.png", HERE / "out" / "onboard-rgb.png", "onboard RGB contact sheet"),
                 ("onboard-thermal.png", HERE / "out" / "onboard-thermal.png", "onboard RGB and thermal contact sheet")]
        rows = []
        Wc = 1200
        for old, new, what in pairs:
            a, b = Image.open(OLD / old).convert("RGB"), Image.open(new).convert("RGB")
            h = int(min(a.height * Wc / a.width, b.height * Wc / b.width))
            a = a.resize((Wc, int(a.height * Wc / a.width))); b = b.resize((Wc, int(b.height * Wc / b.width)))
            H = max(a.height, b.height)
            row = Image.new("RGB", (2 * Wc + 30, H + 40), (22, 22, 24))
            row.paste(a, (10, 34)); row.paste(b, (Wc + 20, 34))
            dr = ImageDraw.Draw(row)
            dr.text((12, 8), f"before: {what} (gallery/{old})", font=font(20), fill=(230, 230, 230))
            dr.text((Wc + 22, 8), f"after: {what} (render_world.py on the new world, the same flight script)", font=font(20), fill=(230, 230, 230))
            rows.append(row)
        out = Image.new("RGB", (rows[0].width, sum(r.height for r in rows)), (22, 22, 24))
        y = 0
        for r in rows:
            out.paste(r, (0, y)); y += r.height
        out.save(OUT / "before-after.png")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", nargs="*", default=None)
    ap.add_argument("--ss", type=int, default=2)
    a = ap.parse_args()
    allnames = ["gorge-oblique-1", "gorge-oblique-2", "gorge-floor", "gorge-top", "onboard-rgb", "fire-rgb-1", "fire-rgb-2",
                "fire-rgb-sequence", "thermal-fire-1", "thermal-fire-2", "thermal-onboard", "thermal-aerial", "fire.gif"]
    run(set(a.only or allnames), a.ss)
