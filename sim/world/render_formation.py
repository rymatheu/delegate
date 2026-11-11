"""Evidence of a formation flight (formation.py): an animation of both X500s in the gorge seen from outside
(chase camera behind the pair), with the onboard views below it, and the frames it is made from.

    python render_formation.py --run out/formation/study/staggered-field-s0-off [--name formation-staggered]
                               [--every 0.3] [--out out]

Writes OUT/NAME.gif, OUT/NAME.webp (the same frames), OUT/NAME-frames/frame_NNN.png and OUT/NAME-still.png
(one frame at full size, in the first narrows). Panels under the chase view, rendered after the flight
from each vehicle's recorded true pose with sensors.py's cameras (forward mount, 30 deg down; the RGB
camera at 320 x 240, 90 deg; the thermal camera at its native 160 x 120, 57 deg, shown on the fixed
20 to 100 C scale): vehicle 1's forward RGB and thermal, vehicle 2's RGB and thermal. In the staggered
plan vehicle 2 flies nose against the direction of travel, so its camera looks behind the formation.

Rendering only (PyBullet TinyRenderer), with render_world.py's look: the gorge's visual meshes, the PX4 X500
meshes (sim/assets/x500_render_noprops.urdf) and render_flight.py's propeller motion blur, DejaVu Sans
from Matplotlib's data directory. The onboard views do not contain the other vehicle (sensors.py renders
the world only); the run's report says how often the other vehicle's centre is inside each camera's
field of view (`in_view`), which is the time the onboard images are missing it.
"""
import argparse
import json
import math
import sys
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


class Pair(Scene):
    """render_world.Scene for two recorded vehicles (vN.csv of a formation run)."""

    def __init__(self, g, run):
        self.g = g
        self.c = p.connect(p.DIRECT)
        self.bodies = g.load(self.c, "visual")
        self.ember_colors = {b: G.ember_rgb(g.firebrands[k].temp_c) for b, (cls, k) in self.bodies.items() if cls == "ember"}
        self.runs = []
        for v in (1, 2):
            d, meta, wps, pos, sp, quat = RF.load(str(run / f"v{v}.csv"))
            ang, spd = RF.prop_state(d)
            self.runs.append(dict(d=d, meta=meta, pos=pos, quat=quat, angle=ang, speed=spd, t=d["t"], body=None))

    def at(self, v, t):
        r = self.runs[v]
        k = int(np.argmin(np.abs(r["t"] - t)))
        return k if abs(r["t"][k] - t) < 0.01 else None

    def place(self, v, k):
        r = self.runs[v]
        R = RF.body_rotation(r["quat"][k])
        if r["body"] is None:
            r["body"] = p.loadURDF(RF.model_path("x500"), r["pos"][k].tolist(), RF.quat_xyzw(R), useFixedBase=True,
                                   physicsClientId=self.c)
        else:
            p.resetBasePositionAndOrientation(r["body"], r["pos"][k].tolist(), RF.quat_xyzw(R), physicsClientId=self.c)
        return r["pos"][k], R, r["angle"][k], r["speed"][k]

    def hide(self, v):
        r = self.runs[v]
        if r["body"] is not None:
            p.resetBasePositionAndOrientation(r["body"], [0, 0, -500], [0, 0, 0, 1], physicsClientId=self.c)


def in_fov(R, pos, other, hfov, w, h, mount=S.FORWARD):
    eye, fwd, up, right = S.camera_pose(R, pos, mount)
    d = other - eye
    z = d @ fwd
    if z <= 0:
        return False
    tx = math.tan(math.radians(hfov) / 2)
    return abs(d @ right / z) <= tx and abs(d @ up / z) <= tx * h / w


def render(run, out, name, every=0.3, W=720, H=400):
    run, out = Path(run), Path(out)
    fm = json.loads((run / "formation.json").read_text())
    g = G.Gorge(fm["gorge_seed"])
    g.write_assets()
    sc = Pair(g, run)
    vis, th = p.connect(p.DIRECT), p.connect(p.DIRECT)
    bv, bt = g.load(vis, "visual"), g.load(th, "thermal")
    PW, PH = W // 4, W * 3 // 16                      # four panels under the chase view, 4:3
    rgb = [S.RGBCamera(vis, bv, S.FORWARD, gorge=g) for _ in range(2)]
    therm = [S.ThermalCamera(th, bt, S.FORWARD, seed=fm["seed"] + 100 * v) for v in range(2)]
    f = np.genfromtxt(run / "formation.csv", delimiter=",", names=True)
    rev = fm["reverse"]
    frames_dir = out / f"{name}-frames"
    frames_dir.mkdir(parents=True, exist_ok=True)
    for old in frames_dir.glob("frame_*.png"):
        old.unlink()
    t_end = min(sc.runs[0]["t"][-1], sc.runs[1]["t"][-1])
    frames, inview = [], {"v1 sees v2": 0, "v2 sees v1": 0, "n": 0}
    still_t = None
    for i, t in enumerate(np.arange(0.0, t_end, every)):
        ks = [sc.at(v, t) for v in (0, 1)]
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
        img, px = sc.shoot(W, H, eye, tgt, (0, 0, 1), 56, 0.05, 200, vehicles, 1.0)
        canvas = Image.new("RGB", (W, H + PH + 22), (24, 24, 28))
        canvas.paste(img, (0, 0))
        dr = ImageDraw.Draw(canvas, "RGBA")
        for v, q in enumerate(poses):
            if q is None:
                continue
            a, ok = px(q[0] + [0, 0, 0.45])
            if ok[0]:
                tag = f"V{v + 1}" + (" (rear, flying backward)" if rev[v] else "")
                dr.text((a[0][0], a[0][1] - 4), tag, font=font(13, True), fill=(255, 255, 255), anchor="ms",
                        stroke_width=2, stroke_fill=(0, 0, 0))
        panels = []
        for v in (0, 1):
            if poses[v] is None:
                panels += [Image.new("RGB", (PW, PH), (0, 0, 0))] * 2
                continue
            R, pos = poses[v][1], poses[v][0]
            fr = rgb[v].capture(R, pos)
            panels.append(Image.fromarray(fr["rgb"]).resize((PW, PH), Image.BILINEAR))
            ft = therm[v].capture(R, pos)
            panels.append(Image.fromarray(S.fixed_scale(ft["temp_c"], 20, 100)).resize((PW, PH), Image.NEAREST))
            other = poses[1 - v]
            if other is not None:
                inview[f"v{v + 1} sees v{2 - v}"] += int(in_fov(R, pos, other[0], 90.0, 320, 240))
        inview["n"] += 1
        titles = ["V1 forward RGB", "V1 forward thermal",
                  "V2 " + ("rear-view" if rev[1] else "forward") + " RGB", "V2 " + ("rear-view" if rev[1] else "forward") + " thermal"]
        for j, (pn, ttl) in enumerate(zip(panels, titles)):
            canvas.paste(pn, (j * PW, H + 22))
            dr.text((j * PW + 4, H + 4), ttl, font=font(12, True), fill=(235, 235, 235))
        k = int(np.argmin(np.abs(f["t"] - (t + 1 / 400))))
        north = float(mid[1])
        dr.rectangle([0, 0, W, 24], fill=(0, 0, 0, 150))
        dr.text((8, 5), f"{fm['plan']}   t {t:5.2f} s   N {north:5.1f} m   separation {f['dist'][k]:4.2f} m (nominal "
                f"{fm['nominal_distance']:.2f})", font=font(13, True), fill=(255, 255, 255))
        canvas.save(frames_dir / f"frame_{i:03d}.png")
        if still_t is None and north >= 22.0:
            still_t = t
            canvas.save(out / f"{name}-still.png")
        frames.append(canvas.convert("P", palette=Image.ADAPTIVE, colors=160))
    ms = int(round(1000 * every))
    frames[0].save(out / f"{name}.gif", save_all=True, append_images=frames[1:], duration=ms, loop=0)
    imgs = [Image.open(q).convert("RGB") for q in sorted(frames_dir.glob("frame_*.png"))]
    imgs[0].save(out / f"{name}.webp", save_all=True, append_images=imgs[1:], duration=ms, loop=0, quality=72, method=4)
    info = dict(run=str(run), frames=len(frames), every_s=every, gif_mb=round((out / f"{name}.gif").stat().st_size / 1e6, 1),
                still_t=still_t, other_vehicle_in_rgb_fov_fraction={k: v / max(inview["n"], 1) for k, v in inview.items() if k != "n"})
    (frames_dir / "render.json").write_text(json.dumps(info, indent=1) + "\n")
    print(json.dumps(info))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--run", required=True)
    ap.add_argument("--name", default=None)
    ap.add_argument("--every", type=float, default=0.3)
    ap.add_argument("--out", default=str(HERE / "out"))
    a = ap.parse_args()
    run = Path(a.run)
    name = a.name or "formation-" + json.loads((run / "formation.json").read_text())["plan"]
    render(run, a.out, name, a.every)


if __name__ == "__main__":
    main()
