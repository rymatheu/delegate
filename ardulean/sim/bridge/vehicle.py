#!/usr/bin/env python3
"""ArduLean (the executable .lake/build/bin/ardulean, Main.lean) as a lock-step vehicle program.

The flight programs start this script as the vehicle, with `--timing-file F --storage S [--storage-out O]`, write one
protocol line per 400 Hz step on its standard input (sim/bridge/protocol.py) and read one output line per input line
(`t=<us> pwm=<16> [down=<hex>]`). It starts the executable in live mode (LINES `-`) and passes each protocol line on,
converted to the driver's tokens (`F`, the estimator record of `record_tokens`, the RC frame, the battery, the uplink
bytes), and passes the vehicle's output lines back unchanged. The vehicle writes output line k when it needs input
line k + 1 (the lock-step order), so after each input line the next output line is read. No vehicle logic.

Usage: sim/bridge/vehicle.py --timing-file F --storage S [--storage-out O]
Environment: LEAN_VEHICLE_EXE (the executable; default .lake/build/bin/ardulean), LEAN_VEHICLE_OUT (directory for
the driver's own output, task and storage files; default out/lean_vehicle), LEAN_VEHICLE_INS (the INS stored-id flags
`gyro,accel`; default `1,1`, as in the tracked boot image).

`replay_check` (the flight programs' --replay-check) feeds a recorded inputs.txt back through this script without the
simulator and compares the output with outputs.txt byte for byte.
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def record_tokens(line):
    """The input line's estimator record (the sensor samples of the step) as the driver's tokens: the time, the IMU
    sample counts and 8 samples of 6 values per IMU (zero-padded), then barometer, compass and GPS, each a presence flag
    and its values (zeros when absent). Values are passed as the hexadecimal bit patterns of the protocol line."""
    t = {}
    for tok in line.split():
        k, _, v = tok.partition("=")
        t[k] = v
    zero32, zero64 = "00000000", "0000000000000000"
    out = [t["t"]]
    imu = []
    ns = []
    for i in (0, 1):
        samples = [s.split(",") for s in t["imu%d" % i].split(";")] if ("imu%d" % i) in t else []
        ns.append(str(len(samples)))
        imu.append(samples)
    out += ns
    for i in (0, 1):
        for j in range(8):
            s = imu[i][j] if j < len(imu[i]) else [zero32] * 6
            out += s
    if "baro" in t:
        out += ["1"] + t["baro"].split(",")
    else:
        out += ["0", zero32, zero32]
    if "mag" in t:
        out += ["1"] + t["mag"].split(",")
    else:
        out += ["0", zero32, zero32, zero32]
    if "gps" in t:
        out += ["1"] + t["gps"].split(",")
    else:
        out += ["0"] + [zero64] * 6
    return out


def line_tokens(line):
    """A protocol line as one input line of the driver: `F`, the record, the RC frame, the battery, the uplink."""
    d = kv(line)
    return ["F"] + record_tokens(line) + [d.get("rc", "-"), d.get("bat", "-"), d.get("up", "-") or "-"]


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
        sys.exit("vehicle.py: --storage is required (the translated vehicle boots from a storage image)")
    exe = os.environ.get("LEAN_VEHICLE_EXE", os.path.join(ROOT, ".lake", "build", "bin", "ardulean"))
    out = os.environ.get("LEAN_VEHICLE_OUT", os.path.join(ROOT, "out", "lean_vehicle"))
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
        toks = line_tokens(line)
        t0 = time.perf_counter()
        proc.stdin.write(" ".join(toks) + "\n")
        proc.stdin.flush()
        reply = proc.stdout.readline()
        waits.append(time.perf_counter() - t0)
        if not reply:
            sys.exit("vehicle.py: the vehicle exited (code %s) after %d lines" % (proc.wait(), n))
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
                    "total %.3f s (the translated vehicle through sim/bridge/vehicle.py, pipe included)\n"
                    % (k, 1e6 * sum(w) / k, 1e6 * w[k // 2], 1e6 * w[k * 9 // 10], 1e6 * w[k * 99 // 100], 1e6 * w[-1], sum(w)))
    sys.exit(code)


def replay_check(out, storage, log):
    """Feed OUT/inputs.txt back to the vehicle (no simulator), booting from storage, and compare its output (OUT/replay.txt)
    with OUT/outputs.txt."""
    cmd = [os.path.abspath(__file__), "--timing-file", os.path.join(out, "timing_replay.txt"), "--storage", str(storage)]
    t0 = time.perf_counter()
    with open(os.path.join(out, "inputs.txt")) as fi, open(os.path.join(out, "replay.txt"), "w") as fo:
        subprocess.run(cmd, stdin=fi, stdout=fo, check=False)
    wall = time.perf_counter() - t0
    with open(os.path.join(out, "outputs.txt"), "rb") as f:
        a = f.read()
    with open(os.path.join(out, "replay.txt"), "rb") as f:
        b = f.read()
    la, lb = a.count(b"\n"), b.count(b"\n")
    if a == b:
        log(f"replay: {lb} output lines, identical to outputs.txt byte for byte ({wall:.2f} s wall)")
    else:
        al, bl = a.split(b"\n"), b.split(b"\n")
        first = next((i for i, (x, y) in enumerate(zip(al, bl)) if x != y), min(len(al), len(bl)))
        log(f"replay: DIFFERS from outputs.txt ({la} vs {lb} lines), first difference at line {first + 1}")


if __name__ == "__main__":
    main()
