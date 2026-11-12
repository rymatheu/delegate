"""Render-time benchmark of the live camera workers (camera_render.py's configuration): RGB 640 x 480
and thermal as streamed (core image through the AGC), over poses along the gorge route, with the
fires' time advancing. Run: python out/redesign/bench.py [--lod 0|1] [--every 4]"""
import argparse
import sys
import time
from pathlib import Path

import numpy as np
import pybullet as p

HERE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(HERE))
import camera_render as CR  # noqa: E402
import gorge as G  # noqa: E402
import sensors as S  # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lod", type=int, default=0)
    ap.add_argument("--every", type=int, default=4)
    ap.add_argument("--kinds", nargs="*", default=["rgb", "thermal"])
    a = ap.parse_args()
    t0 = time.perf_counter()
    g = G.Gorge(7)
    print(f"world ready in {time.perf_counter() - t0:.1f} s")
    Rn = np.array([[0, -1, 0], [1, 0, 0], [0, 0, 1.0]])
    pts = g.path_points(1.0)[::a.every]
    out = {}
    if "rgb" in a.kinds:
        c = p.connect(p.DIRECT)
        t0 = time.perf_counter()
        cam = S.RGBCamera(c, g.load(c, "visual", lod=a.lod), S.FORWARD, 640, 480, 90.0, gorge=g)
        print(f"rgb worker load {time.perf_counter() - t0:.1f} s")
        out[f"rgb 640x480 (lod {a.lod})"] = lambda q, t: cam.capture(Rn, q, t)["rgb"]
    if "thermal" in a.kinds:
        c2 = p.connect(p.DIRECT)
        core = S.ThermalSpec()
        spec = S.ThermalSpec(width=core.width // 2, height=core.height // 2, pitch_um=core.pitch_um * 2) if a.lod else core
        th = S.ThermalCamera(c2, g.load(c2, "thermal", lod=a.lod), S.FORWARD, spec, seed=0, gorge=g)
        agc = S.AGC()
        out[f"thermal {spec.width}x{spec.height} (lod {a.lod})"] = lambda q, t: CR.bin_to(agc(th.capture(Rn, q, t)["temp_c"]), 640, 512)
    def empty():
        c0 = p.connect(p.DIRECT)
        eye, fwd, up, right = S.camera_pose(Rn, pts[3], S.FORWARD)
        v, pr = S.matrices(eye, fwd, up, 90, 640, 480, 0.05, 200, c0)
        ts = []
        for _ in range(8):
            s0 = time.perf_counter(); S.tiny(c0, 640, 480, v, pr); ts.append(time.perf_counter() - s0)
        p.disconnect(c0)
        return 1000 * float(np.median(ts))
    print(f"empty-frame TinyRenderer baseline 640x480 (before): {empty():.1f} ms")
    for name, f in out.items():
        ts = []
        for i, q in enumerate(pts):
            s = time.perf_counter(); f(q, 0.1 * i); ts.append(time.perf_counter() - s)
        ts = np.array(ts[1:]) * 1000
        print(f"{name}: mean {ts.mean():.1f} ms, p95 {np.percentile(ts, 95):.1f}, max {ts.max():.1f} ({len(ts)} frames)")
    print(f"empty-frame TinyRenderer baseline 640x480 (after): {empty():.1f} ms")


main()
