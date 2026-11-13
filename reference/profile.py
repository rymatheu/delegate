#!/usr/bin/env python3
"""Speed of the reference vehicle on a recorded trace: wall time per step and the per-task breakdown.

    python3 reference/profile.py RUN_DIR [--storage IMAGE] [--runs N] [--flight-from S --flight-to S]

Replays RUN_DIR/inputs.txt through build/reference/copter_ref N times (no simulator), each run with
--timing-file (the wall time of the vehicle between two steps, i.e. one 400 Hz tick of ArduCopter
including the sensor back ends' timer processes, without the protocol's parsing and printing) and
--profile (a sampling thread that attributes wall time to the scheduler task running, or to the HAL's
phases). Checks that every replay reproduces RUN_DIR/outputs.txt, then prints a Markdown table.
"""
import argparse
import collections
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / "build" / "reference" / "copter_ref"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--storage", default=str(ROOT / "build" / "reference" / "storage-cf2x.bin"))
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--flight-from", type=float, help="start of the flying phase, s (from the run's events)")
    ap.add_argument("--flight-to", type=float)
    a = ap.parse_args()
    run = Path(a.run)
    ref = (run / "outputs.txt").read_bytes()
    tmp = Path(tempfile.mkdtemp())
    prof = tmp / "profile.txt"
    walls, per_step = [], []
    for i in range(a.runs):
        tf = tmp / f"timing{i}.txt"
        t0 = time.perf_counter()
        with open(run / "inputs.txt") as fi:
            p = subprocess.run([str(BIN), "--storage", a.storage, "--timing-file", str(tf), "--profile", str(prof)],
                               stdin=fi, capture_output=True)
        walls.append(time.perf_counter() - t0)
        if p.stdout != ref:
            sys.exit(f"replay {i} differs from outputs.txt")
        per_step.append([int(x) for x in tf.read_text().splitlines()[1:]])
    steps = len(per_step[0])
    # per step: the median over the runs (robust to scheduling noise), in microseconds
    med = [statistics.median(r[k] for r in per_step) / 1e3 for k in range(steps)]
    srt = sorted(med)

    def stats(v):
        v = sorted(v)
        return (statistics.fmean(v), v[len(v) // 2], v[len(v) * 99 // 100], v[-1])

    print(f"trace {run}: {steps} steps ({steps * 2.5e-3:.1f} s simulated), {a.runs} replays, all identical to outputs.txt")
    print(f"replay wall time (whole process: parse, vehicle, print): {statistics.median(walls):.3f} s median, "
          f"{statistics.median(walls) / steps * 1e6:.2f} us per step\n")
    print("| part of the trace | steps | mean us | p50 us | p99 us | max us |")
    print("|---|---|---|---|---|---|")
    rows = [("all", med)]
    if a.flight_from is not None and a.flight_to is not None:
        k0, k1 = int(a.flight_from / 2.5e-3), int(a.flight_to / 2.5e-3)
        rows += [("before arming", med[:k0]), ("armed, flying", med[k0:k1]), ("after landing", med[k1:])]
    for name, v in rows:
        m, p50, p99, mx = stats(v)
        print(f"| {name} | {len(v)} | {m:.2f} | {p50:.2f} | {p99:.2f} | {mx:.2f} |")
    c = collections.Counter()
    for line in prof.read_text().splitlines():
        *name, n = line.split()
        name = " ".join(name)
        if name != "steps":
            c[name] += int(n)
    tot = sum(c.values())
    total_us = statistics.median(walls) / steps * 1e6
    print(f"\nPer-task breakdown (sampled wall time, {tot} samples over {a.runs} replays; us per step = share x "
          f"{total_us:.2f} us, the whole replay per step):\n")
    print("| scheduler task or HAL phase | share | us per step |")
    print("|---|---|---|")
    for name, n in c.most_common():
        if n == 0:
            continue
        print(f"| {name} | {100 * n / tot:.1f} % | {n / tot * total_us:.2f} |")


if __name__ == "__main__":
    main()
