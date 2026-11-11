"""Reference for the mixer of a parameter file and for `Checks.checkHover`.

Reads a leanfc parameter file (params/*.params) and prints, for its vehicle:
- the allocation matrix A (rows thrust, roll, pitch, yaw; columns motors 1..4 at FRD (l, l), (-l, -l),
  (l, -l), (-l, l), spins s = (+1, +1, -1, -1); motor i contributes (T_i, -y_i T_i, x_i T_i,
  s_i c T_i), c = km/kf) and its binary64 inverse (numpy `linalg.inv`), asserted equal to the closed
  form T/4 -+ tau_x/(4l) +- tau_y/(4l) +- tau_z/(4c);
- the three inverse entries as the controller computes them at load time (`Vehicle.make`): 1/4,
  1/(4 l), 1/(4 c) in binary32 from the binary32 values of l and c, and their relative distance to the
  binary64 inverse;
- the binary32 hover command `Mixer.step (mass * gravity) 0` gives: T = m g; motor 1 =
  ((1/4 * T + (-r) * 0) + r * 0) + y * 0; command = that / tMax, every literal rounded once to binary32
  (FloatLib's `OfScientific` is round-to-nearest-even, as numpy's float32 conversion). `Checks.hoverCf2x`
  and `Checks.hoverX500` are these values.

Run: /Users/ryan/Research/cpp2lean/sim/.venv/bin/python sim/mixer_inverse.py params/cf2x.params params/x500.params
"""
import sys
from pathlib import Path

import numpy as np

G = 9.80665
f = np.float32


def read(path):
    vals = {}
    for line in Path(path).read_text().splitlines():
        ws = line.split("#", 1)[0].split()
        if len(ws) == 2 and ws[0] != "SIM_VEHICLE":
            vals[ws[0]] = ws[1]
    return vals


for path in sys.argv[1:]:
    v = read(path)
    mass, l, c, t_max = (float(v[k]) for k in ("vehicle.mass", "vehicle.l", "vehicle.kmKf", "vehicle.tMax"))
    xy = [(l, l), (-l, -l), (l, -l), (-l, l)]
    spin = [1, 1, -1, -1]
    A = np.array([[1.0] * 4, [-y for _, y in xy], [x for x, _ in xy], [s * c for s in spin]])
    Ainv = np.linalg.inv(A)
    closed = np.array([[0.25, -np.sign(y) / (4 * l), np.sign(x) / (4 * l), s / (4 * c)] for (x, y), s in zip(xy, spin)])
    assert np.allclose(Ainv, closed, rtol=1e-14, atol=0)
    q32, r32, y32 = f(1) / f(4), f(1) / (f(4) * f(l)), f(1) / (f(4) * f(c))
    T = f(mass) * f(G)
    zero = f(0)
    m1 = ((q32 * T + (-r32) * zero) + r32 * zero) + y32 * zero
    h = m1 / f(t_max)
    print(f"== {path}")
    for i, row in enumerate(A):
        print("A", i, "  ".join(repr(float(x)) for x in row))
    for i, row in enumerate(Ainv):
        print("Ainv (binary64)", i, "  ".join(repr(float(x)) for x in row))
    print("binary32 entries: 1/4 =", np.format_float_positional(q32, unique=True),
          " 1/(4l) =", np.format_float_positional(r32, unique=True),
          f"(rel. {abs(float(r32) - 1 / (4 * l)) * 4 * l:.1e})",
          " 1/(4c) =", np.format_float_positional(y32, unique=True),
          f"(rel. {abs(float(y32) - 1 / (4 * c)) * 4 * c:.1e})")
    print("hover command (binary32, shortest round-trip decimal)", np.format_float_positional(h, unique=True),
          f"= 0x{h.view(np.uint32):08x}  (binary64 m g / (4 tMax) = {mass * G / (4 * t_max):.10f})")
