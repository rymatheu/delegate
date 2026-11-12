"""Render worker of the simulated camera payload (camera_component.py starts one or more per stream).

    python camera_render.py --kind rgb|thermal [--width W --height H] [--hfov DEG] [--seed N] [--gorge-seed 7]
                            [--lod 0|1|2]

Runs in the simulator's Python (PyBullet). Loads the gorge's visual world ("rgb") or thermal twin
("thermal") into its own PyBullet client and renders with sensors.py's cameras on the FORWARD mount
(0.20 m ahead of the base, 30 deg below the nose), exactly as fly_gorge.py's cameras do:
- rgb: sensors.RGBCamera (TinyRenderer with the baked lighting, sky, the fires' flames, smoke and
  light at the frame's simulated time, haze, tone curve);
- thermal: sensors.ThermalCamera (640 x 512 class core, 54 deg, radiometric chain with the flames,
  halo, non-uniformity, noise, gain states; sensors.py's docstring), shown with sensors.AGC (plateau
  histogram equalization smoothed over this worker's frames) through sensors.PALETTE (control points
  in code). --width/--height other than the core's bin the core's image (e.g. 320 x 256: 2 x 2).
--lod (level of detail): 2, the default, is the live level of detail: the decimated live world
(Gorge.load(..., lod=2): low-poly plants, decimated boulders, fewer rocks, no grass, in chunks that are
frustum-culled per frame), the fires' live quality (fire.py), and the thermal image rendered at half
the core's resolution (320 x 256, the same radiometric chain) and resized to the stream bilinearly.
1: the full world without grass, thermal at half resolution; 0: the full world at full resolution (the
still-quality world of the grabs).

Protocol on stdin/stdout (binary, little-endian): after loading it writes b"RDY\\n"; then for each request
REQ = <I3d4dd> (frame index, ENU position of the base, PyBullet quaternion x, y, z, w, simulated time s)
it answers <Id> (frame index, render time in ms) followed by H * W * 3 bytes of RGB (row 0 at the top).
"""
import argparse
import struct
import sys
import time
from pathlib import Path

import numpy as np
import pybullet as p
from PIL import Image

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import gorge as G  # noqa: E402
import sensors as S  # noqa: E402

REQ = struct.Struct("<I3d4dd")
REP = struct.Struct("<Id")


def bin_to(img, w, h):
    """Average an image (H x W x 3) down to w x h (integer factors) or repeat it up."""
    H, W = img.shape[:2]
    if (W, H) == (w, h):
        return img
    if W % w == 0 and H % h == 0:
        return img.reshape(h, H // h, w, W // w, 3).mean(axis=(1, 3)).astype(np.uint8)
    return np.asarray(Image.fromarray(img).resize((w, h), Image.BILINEAR))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--kind", choices=("rgb", "thermal"), required=True)
    ap.add_argument("--width", type=int, default=None)
    ap.add_argument("--height", type=int, default=None)
    ap.add_argument("--hfov", type=float, default=90.0)
    ap.add_argument("--seed", type=int, default=0, help="thermal noise and non-uniformity seed")
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--lod", type=int, default=2, help="2: the live level of detail (default); 1: no grass, thermal at half "
                    "resolution; 0: the full world")
    a = ap.parse_args()
    g = G.Gorge(a.gorge_seed)
    c = p.connect(p.DIRECT)
    if a.kind == "rgb":
        w, h = a.width or 320, a.height or 240
        cam = S.RGBCamera(c, g.load(c, "visual", lod=a.lod), S.FORWARD, width=w, height=h, hfov_deg=a.hfov, gorge=g)
        render = lambda R_wb, pos, t: cam.capture(R_wb, pos, t)["rgb"]
    else:
        core = S.ThermalSpec()
        spec = S.ThermalSpec(width=core.width // 2, height=core.height // 2, pitch_um=core.pitch_um * 2) if a.lod else core
        w, h = a.width or core.width, a.height or core.height
        cam = S.ThermalCamera(c, g.load(c, "thermal", lod=a.lod), S.FORWARD, spec, seed=a.seed, gorge=g)
        agc = S.AGC()
        render = lambda R_wb, pos, t: bin_to(agc(cam.capture(R_wb, pos, t)["temp_c"]), w, h)
    inp, out = sys.stdin.buffer, sys.stdout.buffer
    out.write(b"RDY\n")
    out.flush()
    while True:
        req = inp.read(REQ.size)
        if len(req) < REQ.size:
            return
        idx, x, y, z, qx, qy, qz, qw, t = REQ.unpack(req)
        t0 = time.perf_counter()
        R_wb = np.array(p.getMatrixFromQuaternion((qx, qy, qz, qw))).reshape(3, 3)
        img = np.ascontiguousarray(render(R_wb, np.array([x, y, z]), t), dtype=np.uint8)
        out.write(REP.pack(idx, (time.perf_counter() - t0) * 1000) + img.tobytes())
        out.flush()


if __name__ == "__main__":
    main()
