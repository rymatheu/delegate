"""Render worker of the simulated camera payload (camera_component.py starts one or more per stream).

    python camera_render.py --kind rgb|thermal [--width W --height H] [--hfov DEG] [--seed N] [--gorge-seed 7]

Runs in the simulator's Python (PyBullet). Loads the gorge's visual world ("rgb") or thermal twin
("thermal") into its own PyBullet client and renders with sensors.py's cameras on the FORWARD mount
(0.20 m ahead of the base, 30 deg below the nose), exactly as fly_gorge.py's cameras do:
- rgb: sensors.RGBCamera (TinyRenderer, sun-direction diffuse light, sky gradient, ember glow);
- thermal: sensors.ThermalCamera (Lepton 3.5 class, 160 x 120, 57 deg, radiometric chain: band
  radiance, emissivity, atmosphere, 4 x 4 supersampling, PSF, NETD noise, saturation at 400 C), whose
  apparent temperature is shown with the fixed mapping THERMAL_LO_C .. THERMAL_HI_C -> sensors.PALETTE
  (seven hand-chosen control points, black - violet - magenta - red - orange - yellow - near white,
  linearly interpolated; generated in code): T <= 20 C black, 80 C and above near white (the
  scene spans about 25 to 52 C, ash beds 150 C, embers saturate).

Protocol on stdin/stdout (binary, little-endian): after loading it writes b"RDY\\n"; then for each request
REQ = <I3d4d> (frame index, ENU position of the base, PyBullet quaternion x, y, z, w) it answers
<Id> (frame index, render time in ms) followed by H * W * 3 bytes of RGB (row 0 at the top).
"""
import argparse
import struct
import sys
import time
from pathlib import Path

import numpy as np
import pybullet as p

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import gorge as G  # noqa: E402
import sensors as S  # noqa: E402

REQ = struct.Struct("<I3d4d")
REP = struct.Struct("<Id")
THERMAL_LO_C, THERMAL_HI_C = 20.0, 80.0


def thermal_rgb(temp_c):
    """The fixed display mapping of the thermal stream: apparent temperature -> sensors.PALETTE."""
    return S.false_color((np.asarray(temp_c) - THERMAL_LO_C) / (THERMAL_HI_C - THERMAL_LO_C))


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--kind", choices=("rgb", "thermal"), required=True)
    ap.add_argument("--width", type=int, default=320)
    ap.add_argument("--height", type=int, default=240)
    ap.add_argument("--hfov", type=float, default=90.0)
    ap.add_argument("--seed", type=int, default=0, help="thermal noise seed")
    ap.add_argument("--gorge-seed", type=int, default=7)
    a = ap.parse_args()
    g = G.Gorge(a.gorge_seed)
    g.write_assets()
    c = p.connect(p.DIRECT)
    if a.kind == "rgb":
        cam = S.RGBCamera(c, g.load(c, "visual"), S.FORWARD, width=a.width, height=a.height, hfov_deg=a.hfov, gorge=g)
        render = lambda R_wb, pos: cam.capture(R_wb, pos)["rgb"]
    else:
        cam = S.ThermalCamera(c, g.load(c, "thermal"), S.FORWARD, seed=a.seed)
        render = lambda R_wb, pos: thermal_rgb(cam.capture(R_wb, pos)["temp_c"])
    inp, out = sys.stdin.buffer, sys.stdout.buffer
    out.write(b"RDY\n")
    out.flush()
    while True:
        req = inp.read(REQ.size)
        if len(req) < REQ.size:
            return
        idx, x, y, z, qx, qy, qz, qw = REQ.unpack(req)
        t0 = time.perf_counter()
        R_wb = np.array(p.getMatrixFromQuaternion((qx, qy, qz, qw))).reshape(3, 3)
        img = np.ascontiguousarray(render(R_wb, np.array([x, y, z])), dtype=np.uint8)
        out.write(REP.pack(idx, (time.perf_counter() - t0) * 1000) + img.tobytes())
        out.flush()


if __name__ == "__main__":
    main()
