"""Animate a recorded leanfc flight in PyBullet's renderer (camera following the vehicle at a
fixed distance and direction, one frame every STEP ticks), from the CSV written by run_leanfc.py.
Rendering only; see render_flight.py, which also draws the propellers' motion blur.
Usage: render_gif.py run.csv out.gif [--until SECONDS] [--step TICKS] [--dist M] [--title TEXT]
       render_gif.py run.csv out.png --still SECONDS [--dist M] [--scale K]   (one frame, K× size)
"""
import sys

import numpy as np
import pybullet as p
from PIL import Image, ImageDraw, ImageFont

from render_flight import body_rotation, quat_xyzw, model_path, prop_state, render, load, scene, font as dejavu

csv, out = sys.argv[1], sys.argv[2]
arg = lambda k, dflt: type(dflt)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else dflt
until, step, title, dist = arg("--until", 14.0), arg("--step", 16), arg("--title", ""), arg("--dist", 2.4)
still, scale = arg("--still", -1.0), arg("--scale", 1)
W, H = 960 * scale, 600 * scale
d, meta, wps, pos, sp, quat = load(csv)
t = d["t"]
angle, speed = prop_state(d)
is_x500 = meta.get("vehicle", "x500") != "cf2x"
scene(wps, radius=0.07)
body = p.loadURDF(model_path(meta.get("vehicle", "x500")), pos[0].tolist(), useFixedBase=True)
proj = p.computeProjectionMatrixFOV(42, W / H, 0.1, 100)
Pm = np.array(proj).reshape(4, 4).T
font = dejavu(18 * scale)
last = int(np.searchsorted(t, until))


def frame(k):
    R = body_rotation(quat[k])
    p.resetBasePositionAndOrientation(body, pos[k].tolist(), quat_xyzw(R))
    view = p.computeViewMatrixFromYawPitchRoll(pos[k].tolist(), dist, 32.0, -22.0, 0, 2)
    V = np.array(view).reshape(4, 4).T
    def px(pts):
        c = (Pm @ V @ np.column_stack([pts, np.ones(len(pts))]).T).T
        front = c[:, 3] > 0.05                      # drop points behind the camera
        ndc = c[front, :3] / c[front, 3:4]
        return [tuple(a) for a in np.column_stack([(ndc[:, 0] + 1) / 2 * W, (1 - ndc[:, 1]) / 2 * H])]
    img = render(W, H, view, proj, [(pos[k], R, angle[k], speed[k])] if is_x500 else [])
    dr = ImageDraw.Draw(img, "RGBA")
    lo = max(0, k - 1200)                           # the last 3 s of path, and the target ahead
    for pts, col, wd in ((sp[k:min(last, k + 800):8], (20, 80, 200, 170), 2 * scale), (pos[lo:k + 1:4], (210, 60, 30, 230), 3 * scale)):
        q = px(pts)
        if len(q) >= 2:
            dr.line(q, fill=col, width=wd)
    tilt = np.degrees(np.arccos(np.clip(R[2, 2], -1, 1)))
    v = np.linalg.norm([d["v_n"][k], d["v_e"][k], d["v_d"][k]])
    dr.rectangle([0, 0, W, 34 * scale], fill=(255, 255, 255, 215))
    dr.text((10 * scale, 6 * scale), f"{title}   t = {t[k]:5.2f} s   speed {v:4.2f} m/s   tilt {tilt:4.1f}°   leg {int(d['leg'][k]) + 1}   motors "
            + " ".join(f"{d[c][k]:.2f}" for c in ("m1", "m2", "m3", "m4")), fill=(0, 0, 0, 255), font=font)
    return img


if still >= 0:
    frame(int(np.argmin(np.abs(t - still)))).save(out)
    print("wrote", out)
else:
    frames = [frame(k).convert("P", palette=Image.ADAPTIVE, colors=200) for k in range(0, last, step)]
    frames[0].save(out, save_all=True, append_images=frames[1:], duration=int(1000 * step / 400), loop=0, optimize=False)
    print("wrote", out, len(frames), "frames")
