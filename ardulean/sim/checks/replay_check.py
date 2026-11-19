#!/usr/bin/env python3
"""The recorded-flight check: a recorded flight (a run folder of sim/fly_gorge.py or one vehicle's folder of
sim/fly_gorge_formation.py) replayed through the ArduLean executable in file mode, its output lines compared with the
recorded ones.

Prepares the input lines for the driver (per line, as sim/bridge/vehicle.py does: the estimator record's tokens, then
the RC frame, the battery and the uplink bytes, `-` when absent), runs `ardulean LINES ...` on them, and reports:
  * whether the output lines are byte-identical to the flight's outputs.txt (exit status 1 if not);
  * PWM per output line (the 16 values) and down bytes per output line, with the first difference of each;
  * whether a loop of the translation ran out of fuel or a recursive call ran out of depth (both must be false).

Usage: ../sim/.venv/bin/python sim/checks/replay_check.py RUN_DIR [--max-lines N] [--exe BIN] [--out-dir DIR]
RUN_DIR holds inputs.txt, outputs.txt and storage_in.bin. BIN defaults to $LEAN_VEHICLE_EXE or
.lake/build/bin/ardulean; DIR to out/replay_check. The INS stored-id flags are taken from $LEAN_VEHICLE_INS
(default `1,1`, as sim/bridge/vehicle.py).
"""
import os
import subprocess
import sys
import time

SIM = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ROOT = os.path.dirname(SIM)
sys.path.insert(0, SIM)
sys.dont_write_bytecode = True
from bridge.vehicle import kv, line_tokens  # noqa: E402

EXE = os.environ.get("LEAN_VEHICLE_EXE", os.path.join(ROOT, ".lake", "build", "bin", "ardulean"))


def main():
    if len(sys.argv) < 2 or sys.argv[1].startswith("-"):
        sys.exit(__doc__)
    sess = sys.argv[1]
    maxl = None
    if "--max-lines" in sys.argv:
        maxl = int(sys.argv[sys.argv.index("--max-lines") + 1])
    exe = EXE
    if "--exe" in sys.argv:
        exe = sys.argv[sys.argv.index("--exe") + 1]
    out_dir = os.path.join(ROOT, "out", "replay_check")
    if "--out-dir" in sys.argv:
        out_dir = sys.argv[sys.argv.index("--out-dir") + 1]
    os.makedirs(out_dir, exist_ok=True)
    inputs = open(os.path.join(sess, "inputs.txt")).read().split("\n")
    inputs = [l for l in inputs if l.strip()]
    if maxl:
        inputs = inputs[:maxl]
    outputs = [l for l in open(os.path.join(sess, "outputs.txt")).read().split("\n") if l.strip()][:len(inputs)]
    gyro, accel = os.environ.get("LEAN_VEHICLE_INS", "1,1").split(",")
    # no recorded frame is passed to the vehicle: every downlink frame is the translation's
    fp = "-"
    lp = os.path.join(out_dir, "lines.txt")
    with open(lp, "w") as f:
        for l in inputs:
            f.write(" ".join(line_tokens(l)) + "\n")
    op = os.path.join(out_dir, "outputs.txt")
    tp = os.path.join(out_dir, "tasks.txt")
    t0 = time.time()
    p = subprocess.run([exe, lp, os.path.join(sess, "storage_in.bin"), op, tp, gyro, accel, fp], capture_output=True, text=True)
    sys.stderr.write(p.stderr)
    if p.returncode != 0:
        sys.exit("ardulean failed (%d)" % p.returncode)
    print("ardulean: %.1f s wall" % (time.time() - t0))
    ours = [l for l in open(op).read().split("\n") if l.strip()]
    tl = open(tp).read().split("\n")
    for l in tl:
        if l.startswith("#"):
            print(l[:2000])
    # (total definitions) the sticky flag of the translation's fuel loops (support/ParamMemory.lean `PMem.Fuel`)
    fo = [l for l in tl if l.startswith("# fuel_out=")]
    print("fuel: %s" % ("no loop ran out of fuel" if fo == ["# fuel_out=false"] else
                        "A LOOP RAN OUT OF FUEL" if fo else "no fuel_out line"))
    # (total definitions) the sticky flag of the recursive components' depth (support/ParamMemory.lean `PMem.depthOut`)
    do_ = [l for l in tl if l.startswith("# depth_out=")]
    print("depth: %s" % ("no recursive call ran out of depth" if do_ == ["# depth_out=false"] else
                         "A RECURSIVE CALL RAN OUT OF DEPTH" if do_ else "no depth_out line"))
    n = len(outputs)
    pwm_eq = down_eq = both = 0
    first_pwm = first_down = None
    for k in range(n):
        r = kv(outputs[k])
        o = kv(ours[k]) if k < len(ours) else {}
        pe = r.get("pwm") == o.get("pwm") and r.get("t") == o.get("t")
        de = r.get("down", "") == o.get("down", "")
        pwm_eq += pe
        down_eq += de
        both += pe and de
        if not pe and first_pwm is None:
            first_pwm = (k + 1, r.get("t"), r.get("pwm"), o.get("t"), o.get("pwm"))
        if not de and first_down is None:
            first_down = (k + 1, r.get("t"), r.get("down", "")[:120], o.get("down", "")[:120])
    print("output lines: ours %d, recorded %d" % (len(ours), n))
    print("PWM identical on %d of %d lines; down bytes identical on %d; both on %d" % (pwm_eq, n, down_eq, both))
    print("first PWM difference: %s" % (first_pwm,))
    print("first down difference: %s" % (first_down,))
    identical = ours == outputs
    print("output lines byte-identical to the recorded outputs.txt: %s" % ("yes" if identical else "NO"))
    status = 0 if identical and fo == ["# fuel_out=false"] and do_ == ["# depth_out=false"] else 1
    sys.exit(status)


if __name__ == "__main__":
    main()
