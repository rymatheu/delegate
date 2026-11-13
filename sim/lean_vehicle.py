#!/usr/bin/env python3
"""The translated whole vehicle as a lock-step vehicle binary (Phase 5c; README.md "Phase 5c summary").

sim/fly_reference.py runs a vehicle binary with `--timing-file F [--storage S] [--storage-out O]`, writes one protocol
line per 400 Hz step on its standard input (reference/REFERENCE.md "Protocol") and reads one output line per input line
(`t=<us> pwm=<16> [down=<hex>]`). This script stands in that place for the translated vehicle
(lean/.lake/build/bin/vehicle_replay in live mode, lean/VehicleReplay.lean): it starts it with LINES `-` and passes each
protocol line on, converted to the driver's tokens exactly as ardupilot/vehicle/vehicle_replay.py prepares a recorded
session (`F`, the estimator record of ardupilot/sensors_replay.py, the RC frame, the battery, the uplink bytes), and
passes the vehicle's output lines back unchanged. The vehicle writes output line k when it needs input line k + 1
(lockstep.cpp's order), so after each input line the next output line is read. Harness code: no vehicle logic.

Usage (as fly_reference.py's --bin): sim/lean_vehicle.py --timing-file F --storage S [--storage-out O]
Environment: LEAN_VEHICLE_EXE (default lean/.lake/build/bin/vehicle_replay), LEAN_VEHICLE_OUT (directory for the
driver's own output, task and storage files; default build/lean_vehicle), LEAN_VEHICLE_INS (the INS stored-id flags
`gyro,accel`, as vehicle_replay.py reads them from a session's est.txt header; default `1,1`).
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "ardupilot"))
import sensors_replay as sr  # noqa: E402


def kv(line):
    d = {}
    for tok in line.split():
        k, _, v = tok.partition("=")
        d[k] = v
    return d


def main():
    args = sys.argv[1:]

    def opt(name):
        return args[args.index(name) + 1] if name in args else None
    timing = opt("--timing-file")
    storage = opt("--storage")
    storage_out = opt("--storage-out")
    if storage is None:
        sys.exit("lean_vehicle: --storage is required (the translated vehicle boots from a storage image)")
    exe = os.environ.get("LEAN_VEHICLE_EXE", os.path.join(ROOT, "lean", ".lake", "build", "bin", "vehicle_replay"))
    out = os.environ.get("LEAN_VEHICLE_OUT", os.path.join(ROOT, "build", "lean_vehicle"))
    os.makedirs(out, exist_ok=True)
    gyro, accel = os.environ.get("LEAN_VEHICLE_INS", "1,1").split(",")
    op = os.path.join(out, "outputs.txt")
    proc = subprocess.Popen([exe, "-", storage, op, os.path.join(out, "tasks.txt"), gyro, accel, "-"],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1,
                            env=dict(os.environ, LEAN_NUM_THREADS="1"))
    n = 0
    waits = []
    for line in sys.stdin:
        if not line.strip():
            continue
        d = kv(line)
        toks = ["F"] + sr.record_tokens(line) + [d.get("rc", "-"), d.get("bat", "-"), d.get("up", "-") or "-"]
        t0 = time.perf_counter()
        proc.stdin.write(" ".join(toks) + "\n")
        proc.stdin.flush()
        reply = proc.stdout.readline()
        waits.append(time.perf_counter() - t0)
        if not reply:
            sys.exit("lean_vehicle: the vehicle exited (code %s) after %d lines" % (proc.wait(), n))
        sys.stdout.write(reply)
        sys.stdout.flush()
        n += 1
    proc.stdin.close()
    tail = proc.stdout.read()
    code = proc.wait()
    if tail:
        sys.stdout.write(tail)
        sys.stdout.flush()
    if storage_out:
        st = op + ".storage"
        if os.path.exists(st):
            with open(st, "rb") as fi, open(storage_out, "wb") as fo:
                fo.write(fi.read())
    if timing and waits:
        w = sorted(waits)
        k = len(w)
        with open(timing, "w") as f:
            f.write("lockstep timing: %d steps, vehicle compute per step (us): mean %.2f p50 %.2f p90 %.2f p99 %.2f max %.2f, "
                    "total %.3f s (the translated vehicle through sim/lean_vehicle.py, pipe included)\n"
                    % (k, 1e6 * sum(w) / k, 1e6 * w[k // 2], 1e6 * w[k * 9 // 10], 1e6 * w[k * 99 // 100], 1e6 * w[-1], sum(w)))
    sys.exit(code)


if __name__ == "__main__":
    main()
