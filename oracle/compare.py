#!/usr/bin/env python3
"""Compare the C++ oracle (ArduPilot's control classes) with the Lean port, tick by tick.

Usage (from the package root, with the simulator's venv):
    sim/.venv/bin/python oracle/compare.py [--run DIR] [--params FILE]... [--hold-from N]
                                           [--port BIN] [--out DIR] [--no-replay]

What it does, open loop on the recorded inputs only:
1. reads the recorded flight DIR/{inputs.txt, motors.txt, trace.txt} (default the 1 m/s course);
2. replays the inputs through the port binary (--port, default sim/build/copter-c, which is built
   with -fno-builtin-sinf -fno-builtin-cosf) with --exact --trace, and compares the replay with the
   recording (the recording was made by an earlier build that fused sinf/cosf pairs into Apple's
   __sincosf_stret, see sim/README.md "Determinism");
3. runs the oracle binaries in oracle/build/ (oracle-nosincos, the oracle; oracle-sincos and
   oracle-gcc, other compilers/flags; oracle-diag-floattrig, the diagnostic variant) on the inputs,
   with the navigator's outputs taken from the recorded trace and AutoYaw HOLD from tick --hold-from
   (default 6618, from oracle/probe/ModeSchedule.lean for this flight), twice each for determinism;
4. compares every oracle output with the recording and with the replay: per quantity (4 actuators,
   18 trace numbers) the number of ticks with equal values, the first differing tick, the largest
   absolute difference, and the largest difference in units in the last place (float32; float64 for
   the position).

Equality is of values: the port prints exact decimals and drops the sign of zero, so +0 and -0 are
equal here; every other value is compared bit for bit (an exact decimal fixes the binary value).
"""
import argparse
import os
import subprocess
import sys
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
PKG = HERE.parent
NAMES = ["m1", "m2", "m3", "m4",
         "pos_n", "pos_e", "pos_d", "vel_n", "vel_e", "vel_d", "acc_n", "acc_e", "acc_d",
         "thr_n", "thr_e", "thr_d", "roll_t", "pitch_t", "yaw_t", "p_t", "q_t", "r_t"]
DOUBLE_COLS = {4, 5, 6}   # the position target is postype_t (double)


def read_table(path, ncols=22):
    """Rows of exact decimals (strings); an oracle line keeps only the part before '|'."""
    rows = []
    for line in Path(path).read_text().splitlines():
        if not line.strip():
            continue
        w = line.split("|")[0].split()
        if len(w) != ncols:
            raise SystemExit(f"{path}: line {len(rows) + 1} has {len(w)} numbers, expected {ncols}")
        rows.append(w)
    return rows


def to_arrays(rows):
    """float64 array; exact, since every float32 or float64 exact decimal is a double."""
    return np.array([[float(v) for v in r] for r in rows], dtype=np.float64)


def ulp_dist(x, y, double):
    """Distance in units in the last place, on the monotone integer line of the bit patterns."""
    if double:
        xi = x.view(np.int64).astype(object)
        yi = y.view(np.int64).astype(object)
        mono = lambda v: -(int(v) & ((1 << 63) - 1)) if int(v) < 0 else int(v)
        return np.array([abs(mono(p) - mono(q)) for p, q in zip(xi, yi)], dtype=np.float64)
    xi = x.astype(np.float32).view(np.int32).astype(np.int64)
    yi = y.astype(np.float32).view(np.int32).astype(np.int64)
    mx = np.where(xi < 0, -(xi & 0x7FFFFFFF), xi)
    my = np.where(yi < 0, -(yi & 0x7FFFFFFF), yi)
    return np.abs(mx - my).astype(np.float64)


def compare(a, b, label):
    """Print the per-quantity comparison of two (ticks x 22) value arrays; return a summary."""
    n = min(len(a), len(b))
    a, b = a[:n], b[:n]
    ncol = min(a.shape[1], b.shape[1])
    eq = (a[:, :ncol] == b[:, :ncol])
    rows_all_equal = int(eq.all(axis=1).sum())
    first_row = int(np.argmin(eq.all(axis=1))) + 1 if not eq.all() else None
    print(f"\n== {label}")
    print(f"   ticks compared {n}; ticks with all {ncol} quantities equal: {rows_all_equal}"
          + (f"; first tick with a difference: {first_row}" if first_row else "; no difference"))
    act_eq = int(eq[:, :4].all(axis=1).sum())
    first_act = int(np.argmin(eq[:, :4].all(axis=1))) + 1 if not eq[:, :4].all() else None
    print(f"   actuators: {act_eq} of {n} ticks with all four bit-identical"
          + (f", first difference at tick {first_act}" if first_act else ""))
    print(f"   {'quantity':8s} {'equal':>6s} {'differ':>6s} {'first':>6s} {'max |diff|':>11s} {'max ulp':>8s}")
    out = {}
    for j in range(ncol):
        d = ~eq[:, j]
        nd = int(d.sum())
        first = int(np.argmax(d)) + 1 if nd else None
        mad = float(np.max(np.abs(a[:, j] - b[:, j]))) if nd else 0.0
        mu = float(np.max(ulp_dist(a[d, j], b[d, j], j in DOUBLE_COLS))) if nd else 0.0
        print(f"   {NAMES[j]:8s} {n - nd:6d} {nd:6d} {first if first else '-':>6} {mad:11.3g} {mu:8.0f}")
        out[NAMES[j]] = (nd, first, mad, mu)
    return {"all_equal": rows_all_equal, "first": first_row, "act_equal": act_eq, "first_act": first_act, "cols": out}


def run(cmd, stdin_path, out_path, cwd=PKG):
    with open(stdin_path) as fi, open(out_path, "w") as fo:
        r = subprocess.run(cmd, stdin=fi, stdout=fo, stderr=subprocess.PIPE, text=True, cwd=cwd)
    if r.returncode != 0:
        raise SystemExit(f"{' '.join(map(str, cmd))} failed ({r.returncode}): {r.stderr[-2000:]}")
    return r.stderr.strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", default=str(PKG / "sim/out/copter-course-1ms/copter-bin"))
    ap.add_argument("--params", action="append", default=None)
    ap.add_argument("--hold-from", type=int, default=6618)
    ap.add_argument("--port", default=str(PKG / "sim/build/copter-c"))
    ap.add_argument("--out", default=str(HERE / "build/compare"))
    ap.add_argument("--no-replay", action="store_true")
    ap.add_argument("--variants", default="nosincos,sincos,gcc,diag-floattrig")
    args = ap.parse_args()
    params = args.params or [str(PKG / "sim/params/copter-cf2x.txt"), str(PKG / "sim/params/copter-course-speed.txt")]
    rund = Path(args.run)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    inputs, motors, trace = rund / "inputs.txt", rund / "motors.txt", rund / "trace.txt"

    # the recording: actuators + trace, 22 columns
    m = read_table(motors, 4)
    t = read_table(trace, 18)
    rec = to_arrays([a + b for a, b in zip(m, t)])
    print(f"recorded flight: {rund} ({len(rec)} ticks)")

    replay = None
    if not args.no_replay:
        pcmd = [args.port, "--exact", "--trace"] + sum([["--params", p] for p in params], [])
        run(pcmd, inputs, out / "port-replay.txt", cwd=PKG / "sim")
        replay = to_arrays(read_table(out / "port-replay.txt"))
        compare(replay, rec, f"port replay ({args.port}) vs recording")

    pfx = sum([["--params", p] for p in params], [])
    results = {}
    for v in args.variants.split(","):
        exe = HERE / "build" / f"oracle-{v}"
        if not exe.exists():
            print(f"\n(skipping {exe.name}: not built; run oracle/build.sh {v})")
            continue
        cmd = [str(exe), "--nav", str(trace), "--hold-from", str(args.hold_from)] + pfx
        err1 = run(cmd, inputs, out / f"oracle-{v}.txt")
        run(cmd, inputs, out / f"oracle-{v}-again.txt")
        same = (out / f"oracle-{v}.txt").read_bytes() == (out / f"oracle-{v}-again.txt").read_bytes()
        os.remove(out / f"oracle-{v}-again.txt")
        print(f"\n#### oracle-{v}: {err1}; second run byte-identical: {same}")
        o = to_arrays(read_table(out / f"oracle-{v}.txt"))
        results[v] = {"recording": compare(o, rec, f"oracle-{v} vs recording")}
        if replay is not None:
            results[v]["replay"] = compare(o, replay, f"oracle-{v} vs port replay")
    return 0


if __name__ == "__main__":
    sys.exit(main())
