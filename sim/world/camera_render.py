"""Render process of the simulated camera payload (camera_component.py starts one per stream kind).

    .venv/bin/python sim/world/camera_render.py --kind rgb|thermal [--width W --height H] [--hfov DEG] [--seed N]
                                                [--gorge-seed 7] [--lod 0|1|2] [--fds R:W[:SEED][,R:W[:SEED]...]]

Runs in the simulator's Python (PyBullet). Loads the gorge's visual world ("rgb") or thermal twin ("thermal") into its
own PyBullet client and renders with sensors.py's cameras on the FORWARD mount (0.20 m ahead of the base, 30 deg below
the nose), the onboard cameras of the renderers:
- rgb: sensors.RGBCamera (TinyRenderer with the baked lighting, sky, the fires' flames, smoke and light at the frame's
  simulated time, haze, tone curve);
- thermal: sensors.ThermalCamera (640 x 512 class core, 54 deg, radiometric chain with the flames, halo,
  non-uniformity, noise, gain states; sensors.py's docstring), shown with sensors.AGC (plateau histogram equalization
  smoothed over this worker's frames) through sensors.PALETTE. --width/--height other than the core's bin the core's
  image (e.g. 320 x 256: 2 x 2).
--lod (level of detail): 2, the default, is the live level of detail: the decimated live world (Gorge.load(..., lod=2):
low-poly plants, decimated boulders, fewer rocks, no grass, in chunks that are frustum-culled per frame), the fires'
live quality (fire.py), and the thermal image rendered at half the core's resolution (320 x 256, the same radiometric
chain) and resized to the stream bilinearly. 1: the full world without grass, thermal at half resolution; 0: the full
world at full resolution.

Workers: with --fds, the world is loaded once and the process forks one worker per further pipe pair, so the workers
share the loaded world's memory (about 2 GB per kind) copy-on-write; each worker serves its own pair (R: requests
in, W: replies out) and ends when its request pipe closes. A pair may name its own thermal seed (R:W:SEED, for the
cameras of several vehicles: each its own non-uniformity and noise). Without --fds the one worker uses stdin and
stdout.

Protocol (binary, little-endian): after loading, each worker writes b"RDY\\n"; then for each request REQ = <I3d4dd>
(frame index, ENU position of the base, PyBullet quaternion x, y, z, w, simulated time s) it answers <Id> (frame index,
render time in ms) followed by H * W * 3 bytes of RGB (row 0 at the top).
"""
import argparse
import os
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
    """Average an image (H x W x 3) down to w x h (integer factors) or resize it bilinearly."""
    H, W = img.shape[:2]
    if (W, H) == (w, h):
        return img
    if W % w == 0 and H % h == 0:
        return img.reshape(h, H // h, w, W // w, 3).mean(axis=(1, 3)).astype(np.uint8)
    return np.asarray(Image.fromarray(img).resize((w, h), Image.BILINEAR))


def read_exact(fd, n):
    buf = bytearray()
    while len(buf) < n:
        chunk = os.read(fd, n - len(buf))
        if not chunk:
            return bytes(buf)
        buf += chunk
    return bytes(buf)


def write_all(fd, data):
    view = memoryview(data)
    while view:
        view = view[os.write(fd, view):]


def serve(render, rfd, wfd):
    write_all(wfd, b"RDY\n")
    while True:
        req = read_exact(rfd, REQ.size)
        if len(req) < REQ.size:
            return
        idx, x, y, z, qx, qy, qz, qw, t = REQ.unpack(req)
        t0 = time.perf_counter()
        R_wb = np.array(p.getMatrixFromQuaternion((qx, qy, qz, qw))).reshape(3, 3)
        img = np.ascontiguousarray(render(R_wb, np.array([x, y, z]), t), dtype=np.uint8)
        try:
            write_all(wfd, REP.pack(idx, (time.perf_counter() - t0) * 1000) + img.tobytes())
        except (BrokenPipeError, OSError):
            return


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
    ap.add_argument("--fds", default=None, help="R:W pipe pairs, one per worker (default: stdin and stdout, one worker)")
    a = ap.parse_args()
    specs = [[int(v) for v in s.split(":")] for s in a.fds.split(",")] if a.fds else [[0, 1]]
    pairs = [tuple(sp[:2]) for sp in specs]
    seeds = [sp[2] if len(sp) > 2 else a.seed for sp in specs]
    g = G.Gorge(a.gorge_seed)
    c = p.connect(p.DIRECT)
    cam = None
    if a.kind == "rgb":
        w, h = a.width or 320, a.height or 240
        cam = S.RGBCamera(c, g.load(c, "visual", lod=a.lod), S.FORWARD, width=w, height=h, hfov_deg=a.hfov, gorge=g)
        render = lambda R_wb, pos, t: cam.capture(R_wb, pos, t)["rgb"]
    else:
        core = S.ThermalSpec()
        spec = S.ThermalSpec(width=core.width // 2, height=core.height // 2, pitch_um=core.pitch_um * 2) if a.lod else core
        w, h = a.width or core.width, a.height or core.height
        bodies = g.load(c, "thermal", lod=a.lod)
        cam = S.ThermalCamera(c, bodies, S.FORWARD, spec, seed=seeds[0], gorge=g)
        agc = S.AGC()
        render = lambda R_wb, pos, t: bin_to(agc(cam.capture(R_wb, pos, t)["temp_c"]), w, h)
    mine, index = pairs[0], 0
    for k, pr in enumerate(pairs[1:], start=1):     # the further workers share the loaded world copy-on-write
        if os.fork() == 0:
            mine, index = pr, k
            break
    for pr in pairs:                                 # each worker keeps only its own pair, so that a closed pipe is seen
        if pr != mine:
            for fd in pr:
                if fd > 2:
                    os.close(fd)
    if a.kind == "thermal" and seeds[index] != seeds[0]:      # another vehicle's camera: its own non-uniformity and noise
        cam = S.ThermalCamera(c, bodies, S.FORWARD, spec, seed=seeds[index], gorge=g)
    elif a.kind == "thermal" and index:
        cam.rng = np.random.default_rng((seeds[index], index))   # each worker its own temporal noise
    try:
        serve(render, *mine)
    finally:
        os._exit(0)


if __name__ == "__main__":
    main()
