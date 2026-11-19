"""The gorge renderers' scene camera and text: `Scene.shoot` (one image of a PyBullet client holding the gorge's visual
world: sensors.render_rgb with the fires of fire.py, haze or a flat background, then render_flight's propeller motion blur
for each vehicle given, far to near), `font` (DejaVu Sans from Matplotlib's own data directory, no system fonts) and
`label` (text in a rounded box).
"""
import contextlib
import math
from pathlib import Path

import matplotlib
import numpy as np
import pybullet as p
from PIL import Image, ImageFont

import render_flight as RF
import sensors as S

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
    """A view of the gorge's visual world. Subclasses set self.c (the PyBullet client holding Gorge.load(c, "visual"))
    and self.fires (fire.Fires(g, quality)) before calling `shoot`."""

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


def label(dr, xy, text, size=26, fill=(255, 255, 255), box=(0, 0, 0, 150), anchor="la"):
    f = font(size, bold=True)
    l, t, r, b = dr.textbbox(xy, text, font=f, anchor=anchor)
    dr.rounded_rectangle([l - 8, t - 6, r + 8, b + 6], 6, fill=box)
    dr.text(xy, text, font=f, fill=fill, anchor=anchor)
    return (l - 8, t - 6, r + 8, b + 6)
