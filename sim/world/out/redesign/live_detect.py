"""Thermal detection on the live level of detail: re-render the recorded frames of out/main (fly_gorge.py)
in a time window with the live thermal camera (Gorge.load(..., lod=2), 320 x 256, live fires) and, for
reference, the full camera (lod 0, 640 x 512); per fire: frames in view, frames detected; unmatched
detections. Run: python out/redesign/live_detect.py [T0 T1]"""
import sys
from pathlib import Path

import numpy as np
import pybullet as p

HERE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(HERE))
import gorge as G  # noqa: E402
import sensors as S  # noqa: E402


def main():
    t0, t1 = (float(sys.argv[1]), float(sys.argv[2])) if len(sys.argv) > 2 else (9.5, 14.5)
    g = G.Gorge(7)
    d = np.genfromtxt(HERE / "out" / "main" / "flight.csv", delimiter=",", names=True)
    core = S.ThermalSpec()
    cams = {}
    for name, lod, spec, q in (("live", 2, S.ThermalSpec(width=core.width // 2, height=core.height // 2, pitch_um=core.pitch_um * 2), "live"),
                               ("full", 0, core, "still")):
        c = p.connect(p.DIRECT)
        cams[name] = S.ThermalCamera(c, g.load(c, "thermal", lod=lod), S.FORWARD, spec, seed=0, gorge=g, fill=True, fire_quality=q)
    C = np.array([[0, 1, 0], [1, 0, 0], [0, 0, -1.0]])
    for name, cam in cams.items():
        inview, found, unmatched, ndet, frames = {}, {}, 0, 0, 0
        for tq in np.arange(t0, t1, 1 / 8.7):
            k = int(np.argmin(np.abs(d["t"] - tq)))
            pos = np.array([d["p_e"][k], d["p_n"][k], -d["p_d"][k]])
            Rn = np.array(p.getMatrixFromQuaternion([d["q_x"][k], d["q_y"][k], d["q_z"][k], d["q_w"][k]])).reshape(3, 3)
            fr = cam.capture(C @ Rn @ np.diag([1, -1, -1]), pos, float(d["t"][k]))
            frames += 1
            vis = {f for f, (hot, part) in fr["fill"].items() if part.max() > 0}
            dets = S.detect(fr)
            m = S.match(dets, g.firebrands)
            ndet += len(dets)
            unmatched += sum(1 for x in m if x < 0)
            for f in vis:
                inview[f] = inview.get(f, 0) + 1
                if f in m:
                    found[f] = found.get(f, 0) + 1
        per = ", ".join(f"fire {f} ({'hidden' if g.firebrands[f].hidden else 'open'}) {found.get(f, 0)}/{n}" for f, n in sorted(inview.items()))
        print(f"{name} ({cam.s.width} x {cam.s.height}), t {t0:g}..{t1:g} s, {frames} frames: detected in frames where in view: {per}; "
              f"{ndet} detections, {unmatched} unmatched")


main()
