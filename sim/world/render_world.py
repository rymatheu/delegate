"""Evidence images of a gorge flight: overview.png (top down), oblique.png (perspective),
onboard-rgb.png and onboard-thermal.png (contact sheets) and flight.gif (chase camera with the
thermal image inset), from a run directory written by fly_gorge.py.

Rendering only, in PyBullet's TinyRenderer with the gorge's visual meshes; the vehicle is drawn with
the PX4 X500 meshes (sim/assets/x500_render_noprops.urdf) and render_flight.py's propeller motion
blur (`draw_props`). The scene is sensors.render_rgb with the fires of fire.py (flames, smoke, light). Text uses
DejaVu Sans from Matplotlib's own data directory.

Run: python render_world.py [--run out/main] [--only overview|oblique|sheets|gif]
"""
import argparse
import contextlib
import json
import math
import sys
from pathlib import Path

import matplotlib
import numpy as np
import pybullet as p
from PIL import Image, ImageDraw, ImageFont

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE.parent))
import render_flight as RF  # noqa: E402

import fire as FI  # noqa: E402
import gorge as G  # noqa: E402
import sensors as S  # noqa: E402

OUT = HERE / "out"
FONT = Path(matplotlib.get_data_path()) / "fonts/ttf/DejaVuSans.ttf"
FONT_B = Path(matplotlib.get_data_path()) / "fonts/ttf/DejaVuSans-Bold.ttf"


def font(size, bold=False):
    return ImageFont.truetype(str(FONT_B if bold else FONT), size)


@contextlib.contextmanager
def prop_scale(s):
    """Draw the propeller blur for a vehicle drawn s times its size."""
    saved = RF.HUBS, RF.PROP_RADIUS, RF.chord
    chord0 = RF.chord
    RF.HUBS, RF.PROP_RADIUS, RF.chord = saved[0] * s, saved[1] * s, (lambda x: s * chord0(x))
    try:
        yield
    finally:
        RF.HUBS, RF.PROP_RADIUS, RF.chord = saved


class Scene:
    def __init__(self, g, run):
        self.g = g
        self.c = p.connect(p.DIRECT)
        self.bodies = g.load(self.c, "visual")
        self.fires = FI.Fires(g, "still")
        self.d, self.meta, self.wps, self.pos, self.sp, self.quat = RF.load(str(run / "flight.csv"))
        self.t = self.d["t"]
        self.angle, self.speed = RF.prop_state(self.d)
        self.vehicles = []

    def k_at(self, t):
        return int(np.argmin(np.abs(self.t - t)))

    def k_at_north(self, y):
        return int(np.argmin(np.abs(self.pos[:, 1] - y)))

    def place_vehicle(self, k, scale=1.0, body=None):
        R = RF.body_rotation(self.quat[k])
        if body is None:
            body = p.loadURDF(RF.model_path("x500"), self.pos[k].tolist(), RF.quat_xyzw(R), useFixedBase=True,
                              globalScaling=scale, physicsClientId=self.c)
        else:
            p.resetBasePositionAndOrientation(body, self.pos[k].tolist(), RF.quat_xyzw(R), physicsClientId=self.c)
        return body, (self.pos[k], R, self.angle[k], self.speed[k])

    def shoot(self, W, H, eye, target, up, fov_v, near, far, vehicles=(), scale=1.0, bg=None, bloom=None, t=0.0):
        eye = np.asarray(eye, float)
        fwd = np.asarray(target, float) - eye
        fwd /= np.linalg.norm(fwd)
        right = np.cross(fwd, up); right /= np.linalg.norm(right)
        upv = np.cross(right, fwd)
        hf = 2 * math.degrees(math.atan(math.tan(math.radians(fov_v) / 2) * W / H))
        rgb, z, _ = S.render_rgb(self.c, eye, fwd, upv, right, hf, W, H, near, far, t, self.fires, haze=bg is None)
        img = rgb.astype(float)
        if bg is not None:
            img[~np.isfinite(z)] = bg
        view = p.computeViewMatrix(list(eye), list(target), list(up), physicsClientId=self.c)
        proj = p.computeProjectionMatrixFOV(fov_v, W / H, near, far, physicsClientId=self.c)
        cam = np.asarray(eye, float)
        with prop_scale(scale):
            for v in sorted(vehicles, key=lambda v: -np.linalg.norm(v[0] - cam)):
                RF.draw_props(img, view, proj, *v)
        V, P = np.array(view).reshape(4, 4).T, np.array(proj).reshape(4, 4).T

        def px(pts):
            pts = np.atleast_2d(pts)
            c = (P @ V @ np.column_stack([pts, np.ones(len(pts))]).T).T
            ok = c[:, 3] > 0.05
            ndc = c[:, :3] / np.where(ok, c[:, 3], 1)[:, None]
            return np.column_stack([(ndc[:, 0] + 1) / 2 * W, (1 - ndc[:, 1]) / 2 * H]), ok
        return Image.fromarray(img.astype(np.uint8)), px

    def footprint(self, k, mount=S.FORWARD, spec=S.Lepton(), reach=40.0, n=24):
        """World polygon of the thermal camera's view on the terrain at tick k: ray tests along the
        frustum's four edges (up to `reach` m) against the gorge's collision geometry."""
        R = RF.body_rotation(self.quat[k])
        eye, fwd, up, right = S.camera_pose(R, self.pos[k], mount)
        tx = math.tan(math.radians(spec.hfov_deg) / 2)
        ty = tx * spec.height / spec.width
        s = np.linspace(-1, 1, n)
        edge = np.concatenate([np.column_stack([s, -np.ones(n)]), np.column_stack([np.ones(n), s]),
                               np.column_stack([s[::-1], np.ones(n)]), np.column_stack([-np.ones(n), s[::-1]])])
        d = edge[:, :1] * tx * right + edge[:, 1:] * ty * up + fwd
        d /= np.linalg.norm(d, axis=1, keepdims=True)
        a = np.repeat(eye[None], len(d), 0)
        frac, _ = self.g.rays(a, a + reach * d)
        return eye, a + (frac * reach)[:, None] * d


def label(dr, xy, text, size=26, fill=(255, 255, 255), box=(0, 0, 0, 150), anchor="la"):
    f = font(size, bold=True)
    l, t, r, b = dr.textbbox(xy, text, font=f, anchor=anchor)
    dr.rounded_rectangle([l - 8, t - 6, r + 8, b + 6], 6, fill=box)
    dr.text(xy, text, font=f, fill=fill, anchor=anchor)
    return (l - 8, t - 6, r + 8, b + 6)


# --- overview ------------------------------------------------------------------------------------------


def overview(sc, out):
    g = sc.g
    W, H = 2400, 960
    y0, y1 = -3.0, 76.0
    xm = float(np.mean(g.xc_fn(np.linspace(0, 72, 100))))
    ym = (y0 + y1) / 2
    alt = 400.0
    across = (y1 - y0) * H / W
    fov_v = 2 * math.degrees(math.atan(across / 2 / alt))
    SCALE = 4.0
    ks = [sc.k_at_north(y) for y in (14.0, 39.5, 62.0)]
    placed = [sc.place_vehicle(k, SCALE) for k in ks]
    img, px = sc.shoot(W, H, (xm, ym, alt), (xm, ym, 0), (-1, 0, 0), fov_v, 300, 430,
                       [v for _, v in placed], SCALE, bg=(46, 50, 56), bloom=(2.0, 5.0))
    for b, _ in placed:
        p.removeBody(b, physicsClientId=sc.c)
    dr = ImageDraw.Draw(img, "RGBA")
    # sensor field of view wedges
    for k in ks:
        eye, poly = sc.footprint(k)
        q, ok = px(np.vstack([eye, poly]))
        dr.polygon([tuple(a) for a in q[1:]], fill=(255, 226, 70, 60), outline=(255, 226, 70, 220))
        for a in (q[1], q[24], q[48], q[72]):
            dr.line([tuple(q[0]), tuple(a)], fill=(255, 226, 70, 150), width=2)
    # flown path and waypoints
    q, _ = px(sc.pos[::20])
    dr.line([tuple(a) for a in q], fill=(230, 50, 40, 230), width=4)
    q, _ = px(np.vstack([sc.pos[:1], [[w[1], w[0], -w[2]] for w in sc.wps]]))
    for a in q:
        dr.ellipse([a[0] - 6, a[1] - 6, a[0] + 6, a[1] + 6], fill=(40, 110, 230, 230), outline=(255, 255, 255, 220))
    # firebrand markers (outer ring) and labels
    fq, _ = px(np.array([f.center for f in g.firebrands]))
    for f, a in zip(g.firebrands, fq):
        r = 18
        dr.ellipse([a[0] - r, a[1] - r, a[0] + r, a[1] + r], outline=(255, 120, 30, 230), width=3)
    hid = [i for i, f in enumerate(g.firebrands) if f.hidden]
    box = label(dr, (W * 0.40, 40), "Firebrands behind boulders", 34, fill=(255, 196, 120))
    for i in hid:
        a = fq[i]
        dr.line([((box[0] + box[2]) / 2, box[3]), (a[0], a[1] - 18)], fill=(255, 170, 90, 210), width=3)
    opn = [i for i, f in enumerate(g.firebrands) if not f.hidden]
    box = label(dr, (W * 0.47, H - 120), "Firebrands in the open", 26, fill=(255, 196, 120))
    for i in opn:
        a = fq[i]
        dr.line([((box[0] + box[2]) / 2, box[1]), (a[0], a[1] + 18)], fill=(255, 170, 90, 180), width=2)
    eye, poly = sc.footprint(ks[0])
    q, _ = px(poly)
    tip = q[60]
    box = label(dr, (tip[0] + 120, H - 190), "Sensor field of view", 30, fill=(255, 236, 140))
    dr.line([(box[0], (box[1] + box[3]) / 2), tuple(tip)], fill=(255, 226, 70, 230), width=3)
    # scale bar, north arrow, caption
    a, _ = px(np.array([[xm - 13.5, y0 + 2, 0], [xm - 13.5, y0 + 12, 0]]))
    dr.line([tuple(a[0]), tuple(a[1])], fill=(255, 255, 255, 255), width=6)
    dr.text((a[0][0], a[0][1] - 34), "10 m", font=font(24, True), fill=(255, 255, 255))
    dr.line([(W - 140, 70), (W - 50, 70)], fill=(255, 255, 255), width=5)
    dr.polygon([(W - 50, 58), (W - 26, 70), (W - 50, 82)], fill=(255, 255, 255))
    dr.text((W - 128, 82), "north", font=font(24, True), fill=(255, 255, 255))
    dr.rectangle([0, 0, W, 30], fill=(0, 0, 0, 120))
    dr.text((12, 3), f"Gorge seed {g.seed} from above: X500 with the frozen leanfc controller at three instants (drawn {SCALE:g}x size), "
            f"red: flown path, blue: waypoints, yellow: thermal camera footprint (54 deg x 45 deg, 30 deg down), orange rings: firebrands",
            font=font(20), fill=(255, 255, 255))
    img.save(out / "overview.png")
    print("wrote", out / "overview.png", img.size)


# --- oblique --------------------------------------------------------------------------------------------


def oblique(sc, out):
    g = sc.g
    W, H = 1800, 1100
    ks = [sc.k_at_north(y) for y in (9.0, 15.0)]
    placed = [sc.place_vehicle(k, 1.0) for k in ks]
    eye = np.array([g.xc_fn(-4.0) - 5.0, -4.0, g.floor_c(-4.0) + 13.0])
    tgt = np.array([g.xc_fn(26.0), 26.0, g.floor_c(26.0) + 1.0])
    img, px = sc.shoot(W, H, eye, tgt, (0, 0, 1), 46, 0.1, 300, [v for _, v in placed], 1.0)
    for b, _ in placed:
        p.removeBody(b, physicsClientId=sc.c)
    dr = ImageDraw.Draw(img, "RGBA")
    pts = sc.pos[::10]
    frac, _ = g.rays(np.repeat(eye[None], len(pts), 0), pts)          # draw only the path in sight
    q, ok = px(pts)
    vis = ok & (frac >= 0.999)
    for i in range(len(pts) - 1):
        if vis[i] and vis[i + 1]:
            dr.line([tuple(q[i]), tuple(q[i + 1])], fill=(230, 50, 40, 200), width=3)
    a, _ = px(sc.pos[ks[1]] + [0, 0, 0.45])
    label(dr, (a[0][0], a[0][1] - 20), "X500 (0.5 m), 3.5 m above the floor", 24, anchor="ms")
    yn = g.narrows[0]
    a, _ = px(np.array([[g.xc_fn(yn), yn, g.floor_c(yn) + 7.0]]))
    label(dr, tuple(a[0]), f"narrows: floor {g.width_at(yn):.1f} m wide", 24, anchor="mm")
    dr.rectangle([0, 0, W, 34], fill=(0, 0, 0, 120))
    m = (g.y >= 0) & (g.y <= G.Y_END)
    dr.text((12, 5), f"Into the gorge from the south (seed {g.seed}): walls {min(g.height[-1][m].min(), g.height[1][m].min()):.0f}-"
            f"{max(g.height[-1][m].max(), g.height[1][m].max()):.0f} m high, floor {g.width[m].min():.1f}-{g.width[m].max():.1f} m wide; "
            f"vehicle at two instants at true size, red: flown path (where in sight)",
            font=font(22), fill=(255, 255, 255))
    img.save(out / "oblique.png")
    print("wrote", out / "oblique.png", img.size)


# --- contact sheets ------------------------------------------------------------------------------------


def project_cam(R, pos, X, spec_w, spec_h, hfov, mount=S.FORWARD):
    eye, fwd, up, right = S.camera_pose(R, pos, mount)
    d = np.asarray(X) - eye
    z = d @ fwd
    tx = math.tan(math.radians(hfov) / 2)
    ty = tx * spec_h / spec_w
    u = ((d @ right) / z / tx + 1) / 2 * spec_w
    v = (1 - (d @ up) / z / ty) / 2 * spec_h
    return u, v, z, float(np.linalg.norm(d))


def pick_instants(sc, run):
    """Five instants: an open firebrand at long range, then for two hidden firebrands a frame in
    which the fire is inside the thermal image but occluded (no sample of it rendered) and the
    frame of its first detection."""
    det = json.loads((run / "detections.json").read_text())
    tt = np.array(det["t"])
    fill = {int(k): np.array([q[1] for q in v]) for k, v in det["fill"].items()}
    g = sc.g
    spec = S.Lepton()
    first = {}
    for d in det["detections"]:
        if d["match"] >= 0 and d["match"] not in first:
            first[d["match"]] = d["t"]
    opn = [k for k, f in enumerate(g.firebrands) if not f.hidden and k in first]
    hid = [k for k, f in enumerate(g.firebrands) if f.hidden and k in first]
    out = [(first[opn[0]], opn[0], "visible")]
    for k in hid:
        f = g.firebrands[k]
        cand, rr = [], []
        for i, t in enumerate(tt):
            if t >= first[k] - 0.5 or fill[k][i] > 0:
                continue
            kk = sc.k_at(t)
            u, v, z, r = project_cam(RF.body_rotation(sc.quat[kk]), sc.pos[kk], f.center, spec.width, spec.height, spec.hfov_deg)
            if z > 0 and 5 < u < spec.width - 5 and 5 < v < spec.height - 5 and r < 16:
                cand.append(t); rr.append(r)
        if cand:
            out += [(cand[int(np.argmin(np.abs(np.array(rr) - 10.0)))], k, "occluded"), (first[k], k, "visible")]
        if len(out) >= 5:
            break
    return out[:5]


def sheets(sc, run, out):
    g = sc.g
    spec = S.Lepton()
    cams = {n: np.load(run / f"cams_{n}.npz") for n in ("rgb_fwd", "rgb_down", "thermal")}
    picks = pick_instants(sc, run)
    cw, ch = 320, 240
    rows_rgb, rows_th, caps = [[], []], [[], [], []], []
    for t, k, state in picks:
        idx = {n: int(np.argmin(np.abs(c["t"] - t))) for n, c in cams.items()}
        kk = sc.k_at(t)
        R = RF.body_rotation(sc.quat[kk])
        f = g.firebrands[k]
        temp = cams["thermal"]["img"][idx["thermal"]].astype(np.float32)
        tiles = dict(fwd=Image.fromarray(cams["rgb_fwd"]["img"][idx["rgb_fwd"]]), down=Image.fromarray(cams["rgb_down"]["img"][idx["rgb_down"]]),
                     fixed=Image.fromarray(S.fixed_scale(temp, 20, 100)).resize((cw, ch), Image.NEAREST),
                     agc=Image.fromarray(S.agc(temp)).resize((cw, ch), Image.NEAREST))
        u, v, z, r = project_cam(R, sc.pos[kk], f.center, cw, ch, 90.0)
        ut, vt, _, _ = project_cam(R, sc.pos[kk], f.center, cw, ch, spec.hfov_deg)
        col = (80, 255, 120) if state == "visible" else (255, 255, 255)
        for name, (uu, vv) in (("fwd", (u, v)), ("fixed", (ut, vt)), ("agc", (ut, vt))):
            dr = ImageDraw.Draw(tiles[name], "RGBA")
            rr = 11
            if state == "visible":
                dr.ellipse([uu - rr, vv - rr, uu + rr, vv + rr], outline=col, width=2)
            else:
                for a0 in range(0, 360, 40):
                    dr.arc([uu - rr, vv - rr, uu + rr, vv + rr], a0, a0 + 20, fill=col, width=2)
        cap = (f"t {t:.2f} s, fire {k} at {r:.1f} m: {state}\n"
               f"({'hidden behind boulder ' + str(f.boulder) if f.hidden else 'in the open'})")
        caps.append(cap)
        rows_rgb[0].append(tiles["fwd"]); rows_rgb[1].append(tiles["down"])
        rows_th[0].append(tiles["fwd"]); rows_th[1].append(tiles["fixed"]); rows_th[2].append(tiles["agc"])
    def sheet(rows, names, title, path, bar=False):
        n = len(rows[0])
        lw, gap, top = 172, 6, 80
        Wd = lw + n * (cw + gap) + (120 if bar else 0)
        Hd = top + len(rows) * (ch + gap)
        im = Image.new("RGB", (Wd, Hd), (24, 26, 30))
        dr = ImageDraw.Draw(im)
        dr.text((10, 10), title, font=font(18, True), fill=(255, 255, 255))
        for j, cap in enumerate(caps):
            dr.multiline_text((lw + j * (cw + gap), 38), cap, font=font(14), fill=(255, 255, 255))
        for i, (row, nm) in enumerate(zip(rows, names)):
            y = top + i * (ch + gap)
            dr.multiline_text((10, y + ch / 2 - 30), nm, font=font(15), fill=(220, 220, 220))
            for j, tile in enumerate(row):
                im.paste(tile, (lw + j * (cw + gap), y))
        if bar:
            x0 = lw + n * (cw + gap) + 8
            y0 = top + (ch + gap)
            grad = S.false_color(np.linspace(1, 0, ch)[:, None].repeat(22, 1))
            im.paste(Image.fromarray(grad), (x0, y0))
            for tc in (20, 40, 60, 80, 100):
                yy = y0 + (1 - (tc - 20) / 80) * (ch - 1)
                dr.text((x0 + 26, yy - 8), f"{tc} C", font=font(13), fill=(220, 220, 220))
            dr.text((x0 - 4, y0 + ch + 8), "AGC: histogram\nequalized", font=font(12), fill=(200, 200, 200))
        im.save(path)
        print("wrote", path, im.size)
    sheet(rows_rgb, ["forward RGB\n320 x 240, 90 deg\n30 deg down", "downward RGB\n320 x 240, 90 deg"],
          "Onboard RGB, gorge flight (green ring: firebrand in view; dashed white ring: firebrand position, occluded)",
          out / "onboard-rgb.png")
    sheet(rows_th, ["forward RGB", "thermal 640 x 512\n54 deg, 8.7 Hz\n20-100 C fixed", "thermal\nautomatic gain"],
          "Onboard RGB above thermal (640 x 512 core, shown binned 2 x 2; apparent temperature, flames saturate)",
          out / "onboard-thermal.png", bar=True)
    return picks


# --- gif --------------------------------------------------------------------------------------------------


def gif(sc, run, out, every=0.3, W=544, H=340, colors=128, name="flight"):
    g = sc.g
    th = np.load(run / "cams_thermal.npz")
    det = json.loads((run / "detections.json").read_text())
    body = None
    frames = []
    found = set()
    for t in np.arange(0.0, sc.t[-1], every):
        k = sc.k_at(t)
        body, v = sc.place_vehicle(k, 1.0, body)
        y = sc.pos[k][1]
        ax = g.axis_dir(y)
        eye = sc.pos[k] - 4.5 * ax + [0, 0, 1.6]
        tgt = sc.pos[k] + 6.0 * ax - [0, 0, 1.2]
        img, _ = sc.shoot(W, H, eye, tgt, (0, 0, 1), 50, 0.05, 200, [v], 1.0)
        i = int(np.searchsorted(th["t"], t, side="right")) - 1
        temp = th["img"][max(i, 0)].astype(np.float32)
        inset = Image.fromarray(S.fixed_scale(temp, 20, 100)).resize((200, 150), Image.NEAREST)
        img.paste(inset, (W - 206, 36))
        dr = ImageDraw.Draw(img, "RGBA")
        dr.rectangle([W - 207, 35, W - 5, 187], outline=(255, 255, 255), width=1)
        dr.text((W - 204, 188), "thermal, 20-100 C", font=font(12, True), fill=(255, 255, 255))
        for d in det["detections"]:
            if d["t"] <= t and d["match"] >= 0:
                found.add(d["match"])
        vel = np.linalg.norm([sc.d["v_n"][k], sc.d["v_e"][k], sc.d["v_d"][k]])
        dr.rectangle([0, 0, W, 28], fill=(0, 0, 0, 140))
        dr.text((8, 6), f"t {t:5.2f} s   N {y:5.1f} m   speed {vel:4.2f} m/s   firebrands detected {len(found)}/{len(g.firebrands)}",
                font=font(13, True), fill=(255, 255, 255))
        frames.append(img.convert("P", palette=Image.ADAPTIVE, colors=colors))
    ms = int(round(1000 * every))
    frames[0].save(out / f"{name}.gif", save_all=True, append_images=frames[1:], duration=ms, loop=0)
    print("wrote", out / f"{name}.gif", len(frames), "frames", f"{(out / f'{name}.gif').stat().st_size / 1e6:.1f} MB")
    # the same frames as an animated WebP: a fraction of the GIF's size at the same frame rate
    frames[0].convert("RGB").save(out / f"{name}.webp", save_all=True, append_images=(f.convert("RGB") for f in frames[1:]),
                                  duration=ms, loop=0, quality=72, method=4)
    print("wrote", out / f"{name}.webp", f"{(out / f'{name}.webp').stat().st_size / 1e6:.1f} MB")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--run", default=str(OUT / "main"))
    ap.add_argument("--only", choices=("overview", "oblique", "sheets", "gif"), default=None)
    ap.add_argument("--fps", type=float, default=1 / 0.3, help="frame rate of the animation (the thermal inset updates at the sensor's 8.7 Hz)")
    ap.add_argument("--name", default="flight", help="base name of the animation files")
    a = ap.parse_args()
    run = Path(a.run)
    meta = json.loads((run / "flight.json").read_text())
    g = G.Gorge(meta["gorge_seed"])
    g.write_assets()
    sc = Scene(g, run)
    for name, fn in (("overview", lambda: overview(sc, OUT)), ("oblique", lambda: oblique(sc, OUT)),
                     ("sheets", lambda: sheets(sc, run, OUT)), ("gif", lambda: gif(sc, run, OUT, every=1 / a.fps, name=a.name))):
        if a.only in (None, name):
            fn()


if __name__ == "__main__":
    main()
