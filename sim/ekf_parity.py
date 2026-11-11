#!/usr/bin/env python3
"""Bit parity of the Lean EKF (Leanfc/EKF.lean) with the Python prototype it ports (pyfc ekf.py).

One recorded sensor sequence (a `run_leanfc.py --record FILE` file: the calibration samples, then one
line per 400 Hz tick) is fed open loop to both filters:

- Lean: `leanfc --params ... --ekf-only --calibrate N`, which prints its derived constants, the state
  after calibration and the whole state (q, omega, p, v, bg, ba, P) after every tick as binary32 hex words;
- Python: `pyfc.ekf.EKF` imported read-only from /Users/ryan/Research/delegate/staging/pyfc (no bytecode
  is written there), with `EKFParams` set to the Lean file's binary32 parameter values.

The inputs are rounded to binary32 once, here, and the Lean side is sent the shortest decimal of each
binary32 value, so both filters start every tick from the same words.

ekf.py computes its derived constants (Q per tick, the R variances, the low-pass coefficient) in binary64
and rounds once; EKF.make computes them in binary32. The comparison is therefore run twice:
(A) with ekf.py's own constants, (B) with the Lean constants installed in the Python object. The
prototype has no gyro-bias prior from the calibration (one of the two fixes the port adds): the Python
side gets the same rule, max(sigma_gyro^2 / n, sigma_min^2), in binary32 in (B) and from its own
binary64 squares in (A).

Usage: ekf_parity.py RECORD [--params FILE ...] [--calibrate 400] [--ticks N]
"""
import argparse
import subprocess
import sys
from pathlib import Path

import numpy as np

sys.dont_write_bytecode = True        # write nothing into the pyfc tree
sys.path.insert(0, "/Users/ryan/Research/delegate/staging/pyfc")
from pyfc.ekf import EKF, EKFParams   # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
F = np.float32
FIELDS = (["q_w", "q_x", "q_y", "q_z"] + [f"omega_{c}" for c in "xyz"] + [f"p_{c}" for c in "neD"]
          + [f"v_{c}" for c in "neD"] + [f"bg_{c}" for c in "xyz"] + [f"ba_{c}" for c in "xyz"]
          + [f"P[{i}][{j}]" for i in range(15) for j in range(15)])


def bits(x):
    return np.asarray(x, dtype=F).view(np.uint32)


def from_hex(ws):
    return np.array([int(w, 16) for w in ws], dtype=np.uint32).view(F)


def state_words(e):
    return np.concatenate([bits(e.q), bits(e.omega), bits(e.p), bits(e.v), bits(e.bg), bits(e.ba),
                           bits(e.P).reshape(-1)])


def lean_params(binary, files):
    out = subprocess.run([binary, *files, "--print-params"], capture_output=True, text=True, check=True).stdout
    vals = {}
    for ln in out.splitlines():
        ws = ln.split()
        if len(ws) == 2 and not ln.startswith("#") and ws[0] != "estimator":
            vals[ws[0]] = float(F(float(ws[1])))    # 9 significant digits: the exact binary32 value
    return vals


def python_ekf(v):
    pr = EKFParams(gyro_noise=v["ekf.gyroNoise"], accel_noise=v["ekf.accelNoise"],
                   gyro_bias_walk=v["ekf.gyroBiasWalk"], accel_bias_walk=v["ekf.accelBiasWalk"],
                   position_ne=v["ekf.posNE"], position_d=v["ekf.posD"], velocity=v["ekf.vel"],
                   heading=v["ekf.heading"], tilt0=v["ekf.tilt0"], yaw0=v["ekf.yaw0"], vel0=v["ekf.vel0"],
                   pos0=v["ekf.pos0"], gyro_bias0=v["ekf.gyroBias0"], accel_bias0=v["ekf.accelBias0"],
                   p_floor=v["ekf.pFloor"], gyro_cutoff_hz=v["ekf.cutoffHz"])
    p0 = np.array([v["start.x"], v["start.y"], v["start.z"]], dtype=F)
    return EKF(pr, v["dt"], p0=p0)


def ulps(a, b):
    ia, ib = (np.asarray(x, dtype=F).view(np.int32).astype(np.int64) for x in (a, b))
    ia = np.where(ia < 0, -(ia & 0x7FFFFFFF), ia)
    ib = np.where(ib < 0, -(ib & 0x7FFFFFFF), ib)
    return np.abs(ia - ib)


def compare_constants(e, const, v, n_cal):
    """ekf.py's own derived constants against the Lean ones (const = the `const` line as binary32)."""
    c = dict(dt=const[0], halfDt=const[1], halfDt2=const[2], Qd=const[3:18], R_pos=const[18:21],
             R_vel=const[21], R_hdg=const[22], floor=const[23], lp=const[24], gyroVar=const[25],
             gyroVarMin=const[26], P0=const[27:42])
    h = e.dt * F(0.5)
    py = dict(dt=e.dt, halfDt=h, halfDt2=h * e.dt, Qd=e.Qd, R_pos=e.R_pos, R_vel=e.R_vel, R_hdg=e.R_hdg,
              floor=e.floor, lp=e.lp, P0=np.diag(e.P).copy(),
              gyroVar=F(v["ekf.gyroNoise"] ** 2), gyroVarMin=F(v["ekf.gyroBiasMin"] ** 2))
    print("derived constants, ekf.py (binary64, rounded once) vs EKF.make (binary32):")
    for k in c:
        d = ulps(py[k], c[k])
        print(f"  {k:10s} " + ("equal" if d.max() == 0 else
              f"differ in {int((d > 0).sum())} of {d.size}, up to {int(d.max())} ulp; "
              f"ekf.py {np.atleast_1d(py[k])[d.argmax() if d.ndim else 0]!r} Lean {np.atleast_1d(c[k])[d.argmax() if d.ndim else 0]!r}"))
    return c


def run(record, files, binary, n_cal, n_ticks, install):
    lines = [ln for ln in Path(record).read_text().splitlines() if ln.strip()]
    nums = [np.array([float(t) for t in ln.split()], dtype=F) for ln in lines]   # the binary32 inputs
    cal, ticks = nums[:n_cal], nums[n_cal:n_cal + n_ticks] if n_ticks else nums[n_cal:]
    text = "".join(" ".join(repr(float(x)) for x in a) + "\n" for a in cal + ticks)
    out = subprocess.run([binary, *files, "--ekf-only", "--calibrate", str(n_cal)], input=text,
                         capture_output=True, text=True, check=True).stdout.splitlines()
    assert out[0].startswith("const ")
    const = from_hex(out[0].split()[1:])
    i = 1
    if n_cal:
        assert out[i] == "calibrated", out[i]
        i += 1
    assert out[i].startswith("init ")
    lean_init = np.array([int(w, 16) for w in out[i].split()[1:]], dtype=np.uint32)
    lean_ticks = out[i + 1:]
    assert len(lean_ticks) == len(ticks), (len(lean_ticks), len(ticks))

    v = lean_params(binary, files)
    e = python_ekf(v)
    c = compare_constants(e, const, v, n_cal) if not install else None
    if install:   # (B): the Lean constants in the Python object
        e.dt, e.Qd, e.R_pos, e.R_vel, e.R_hdg = const[0], const[3:18].copy(), const[18:21].copy(), const[21], const[22]
        e.floor, e.lp = const[23], const[24]
        gv, gmin = const[25], const[26]
    else:
        gv, gmin = F(v["ekf.gyroNoise"] ** 2), F(v["ekf.gyroBiasMin"] ** 2)
    if n_cal:
        e.calibrate([a[0:3] for a in cal])
        prior = max(gv / F(n_cal), gmin)
        for k in range(9, 12):
            e.P[k, k] = prior

    mode = "B, Lean constants installed" if install else "A, ekf.py's own constants"
    first, n_diff, maxabs, maxrel = None, 0, np.zeros(len(FIELDS)), 0.0

    def check(k, py_words, lean_words):
        nonlocal first, n_diff, maxrel
        d = py_words != lean_words
        if d.any():
            n_diff += 1
            j = int(np.argmax(d))
            if first is None:
                first = (k, FIELDS[j], py_words.view(F)[j], lean_words.view(F)[j])
            a, b = py_words.view(F).astype(float), lean_words.view(F).astype(float)
            np.maximum(maxabs, np.abs(a - b), out=maxabs)
            scale = np.maximum(np.abs(b), 1e-30)
            maxrel = max(maxrel, float(np.max(np.abs(a - b) / scale)))

    check("init", state_words(e), lean_init)
    for k, (a, ln) in enumerate(zip(ticks, lean_ticks)):
        fix = a[6] != 0
        pos_fix = fix and (len(a) < 17 or a[16] != 0)
        e.step(a[0:3], a[3:6], (a[7], a[8]) if fix else None, a[9:12].copy() if pos_fix else None,
               a[12:15].copy() if a[15] != 0 else None)
        check(k, state_words(e), np.array([int(w, 16) for w in ln.split()], dtype=np.uint32))

    print(f"({mode}): {len(ticks)} ticks compared (+ the state after {n_cal} calibration samples), "
          f"{len(state_words(e))} binary32 words per tick")
    if first is None:
        print("  bit for bit identical on every tick")
    else:
        k, f, a, b = first
        print(f"  first difference: tick {k}, field {f}: ekf.py {a!r} ({int(bits(a)):08x}), Lean {b!r} ({int(bits(b)):08x})")
        print(f"  ticks with any difference: {n_diff} of {len(ticks) + 1}; largest relative difference {maxrel:.3g}")
        groups = dict(q=slice(0, 4), omega=slice(4, 7), p=slice(7, 10), v=slice(10, 13), bg=slice(13, 16),
                      ba=slice(16, 19), P=slice(19, None))
        print("  largest absolute difference per group: " +
              ", ".join(f"{g} {maxabs[s].max():.3g}" for g, s in groups.items()))
    return first is None


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("record")
    ap.add_argument("--params", action="append", help="parameter files of the run (default params/x500.params)")
    ap.add_argument("--calibrate", type=int, default=400)
    ap.add_argument("--ticks", type=int, default=0, help="ticks to compare (default: all)")
    ap.add_argument("--bin", default=str(ROOT / ".lake/build/bin/leanfc"))
    a = ap.parse_args()
    files = [x for p in (a.params or [str(ROOT / "params/x500.params")]) for x in ("--params", p)]
    run(a.record, files, a.bin, a.calibrate, a.ticks, install=False)
    ok = run(a.record, files, a.bin, a.calibrate, a.ticks, install=True)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
