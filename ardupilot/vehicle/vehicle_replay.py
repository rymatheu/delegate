#!/usr/bin/env python3
"""The whole-vehicle replay (README.md "Phase 5: the whole-vehicle replay"): the translated vehicle (lean/VehicleReplay.lean,
`lake build vehicle_replay`) on a recorded session, compared with the reference's output lines and its `--est` trace.

Prepares the input lines for the Lean HAL (per line: the estimator record's tokens as ardupilot/sensors_replay.py makes
them, then the RC frame, the battery and the uplink bytes, `-` when absent), runs the replay, and compares:
  * PWM per output line (the 16 values), down bytes per output line, the boot's output lines (est.txt `init=1`) apart;
  * per step the scheduler's tasks (`tasks=` of est.txt against the translated AP_Scheduler's `_last_run`), the tick;
  * the first difference of each, with its line and time.

Usage: ardupilot/vehicle/vehicle_replay.py SESSION_DIR [--max-lines N] [--est EST] [--exe BIN] [--out-dir DIR]
EST is the session's `copter_ref --est` file (default SESSION_DIR/est.txt; the QGroundControl session's is
build/gcs/qgc/est.txt).
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.dirname(HERE))
import sensors_replay as sr  # noqa: E402

EXE = os.path.join(ROOT, "lean", ".lake", "build", "bin", "vehicle_replay")


def kv(line):
    d = {}
    for tok in line.split():
        k, _, v = tok.partition("=")
        d[k] = v
    return d


def main():
    sess = sys.argv[1]
    maxl = None
    if "--max-lines" in sys.argv:
        maxl = int(sys.argv[sys.argv.index("--max-lines") + 1])
    exe = EXE
    if "--exe" in sys.argv:
        exe = sys.argv[sys.argv.index("--exe") + 1]
    out_dir = os.path.join(ROOT, "build", "vehicle_replay")
    if "--out-dir" in sys.argv:
        out_dir = sys.argv[sys.argv.index("--out-dir") + 1]
    os.makedirs(out_dir, exist_ok=True)
    inputs = open(os.path.join(sess, "inputs.txt")).read().split("\n")
    inputs = [l for l in inputs if l.strip()]
    if maxl:
        inputs = inputs[:maxl]
    outputs = [l for l in open(os.path.join(sess, "outputs.txt")).read().split("\n") if l.strip()][:len(inputs)]
    est_path = sys.argv[sys.argv.index("--est") + 1] if "--est" in sys.argv else os.path.join(sess, "est.txt")
    est_lines = open(est_path).read().split("\n")
    header = [l for l in est_lines if l.startswith("# params")]
    params = kv(header[0][len("# params "):]) if header else {}
    est = [kv(l) for l in est_lines if l.startswith("t=")][:len(inputs)]
    gyro = "1" if params.get("ins._gyro_id_old_param[0]", "0") != "0" else "0"
    accel = "1" if params.get("ins._accel_id_old_param[0]", "0") != "0" else "0"
    # (Phase 5c) no recorded frame is passed to the vehicle: every downlink frame is the translation's (before: Phase 4's
    # boundary frames, the content messages and STATUSTEXT, by message id with their step)
    fp = "-"
    lp = os.path.join(out_dir, "lines.txt")
    with open(lp, "w") as f:
        for k, l in enumerate(inputs):
            d = kv(l)
            toks = ["F"] + sr.record_tokens(l) + [d.get("rc", "-"), d.get("bat", "-"), d.get("up", "-") or "-"]
            f.write(" ".join(toks) + "\n")
    op = os.path.join(out_dir, "outputs.txt")
    tp = os.path.join(out_dir, "tasks.txt")
    t0 = time.time()
    p = subprocess.run([exe, lp, os.path.join(sess, "storage_in.bin"), op, tp, gyro, accel, fp], capture_output=True, text=True)
    sys.stderr.write(p.stderr)
    if p.returncode != 0:
        sys.exit("vehicle_replay failed (%d)" % p.returncode)
    print("vehicle_replay: %.1f s wall" % (time.time() - t0))
    ours = [l for l in open(op).read().split("\n") if l.strip()]
    tl = open(tp).read().split("\n")
    tasks = [l.split() for l in tl if l.startswith("T ")]
    for l in tl:
        if l.startswith("#"):
            print(l[:2000])
    n = len(outputs)
    pwm_eq = down_eq = both = 0
    first_pwm = first_down = None
    boot = sum(1 for d in est if d.get("init") == "1")
    boot_eq = 0
    for k in range(n):
        r = kv(outputs[k])
        o = kv(ours[k]) if k < len(ours) else {}
        pe = r.get("pwm") == o.get("pwm") and r.get("t") == o.get("t")
        de = r.get("down", "") == o.get("down", "")
        pwm_eq += pe
        down_eq += de
        both += pe and de
        if k < boot and pe and de:
            boot_eq += 1
        if not pe and first_pwm is None:
            first_pwm = (k + 1, r.get("t"), r.get("pwm"), o.get("t"), o.get("pwm"))
        if not de and first_down is None:
            first_down = (k + 1, r.get("t"), r.get("down", "")[:120], o.get("down", "")[:120])
    print("output lines: ours %d, recorded %d" % (len(ours), n))
    print("PWM identical on %d of %d lines; down bytes identical on %d; both on %d; boot (init, %d lines) both identical on %d"
          % (pwm_eq, n, down_eq, both, boot, boot_eq))
    print("first PWM difference: %s" % (first_pwm,))
    print("first down difference: %s" % (first_down,))
    t_eq = 0
    first_t = None
    tick_eq = 0
    for k in range(min(len(est), len(tasks))):
        e = est[k]
        tt = tasks[k]
        et = e.get("tasks", "-") if "tick" in e else "-"
        if et == tt[3]:
            t_eq += 1
        elif first_t is None:
            first_t = (k + 1, e.get("t"), "ref tick=%s tasks=%s dcb=%s" % (e.get("tick"), et, e.get("dcb")),
                       "ours tick=%s tasks=%s dcb=%s" % (tt[2], tt[3], tt[4]))
        if e.get("tick", "0") == tt[2]:
            tick_eq += 1
    print("tasks identical on %d of %d steps (tick identical on %d)" % (t_eq, len(est), tick_eq))
    print("first tasks difference: %s" % (first_t,))
    # by scheduler tick (the main loop's ticks, whatever line they fall on)
    ref, our = {}, {}
    for e in est:
        if "tick" in e and e["tick"] != "0" and e.get("init") != "1":
            ref.setdefault(int(e["tick"]), e.get("tasks", "-"))
    for tt in tasks:
        if tt[2] != "0":
            our.setdefault(int(tt[2]), tt[3])
    common = sorted(set(ref) & set(our))
    bad = [k for k in common if ref[k] != our[k]]
    print("tasks by scheduler tick: %d ticks compared, %d identical; first difference: %s"
          % (len(common), len(common) - len(bad), ("tick %d ref %s ours %s" % (bad[0], ref[bad[0]], our[bad[0]])) if bad else None))
    # the storage image at the end against the reference's (`copter_ref --storage-out` on the same session)
    ref_bin = os.path.join(ROOT, "build", "reference", "copter_ref")
    st_ours = op + ".storage"
    if os.path.exists(ref_bin) and os.path.exists(st_ours):
        st_ref = os.path.join(out_dir, "storage_ref.bin")
        with open(os.path.join(sess, "inputs.txt")) as fi:
            subprocess.run([ref_bin, "--storage", os.path.join(sess, "storage_in.bin"), "--storage-out", st_ref], stdin=fi,
                           stdout=subprocess.DEVNULL, check=True)
        a, b = open(st_ref, "rb").read(), open(st_ours, "rb").read()
        d = [i for i in range(min(len(a), len(b))) if a[i] != b[i]]
        print("storage at the end: %d bytes, %d differ from the reference's%s" % (len(a), len(d) + abs(len(a) - len(b)),
              (" (offsets %s)" % ",".join(str(i) for i in d[:40])) if d else ""))
    if "--compare-with" in sys.argv:
        other = [l for l in open(sys.argv[sys.argv.index("--compare-with") + 1]).read().split("\n") if l.strip()]
        diff = [k for k in range(min(len(other), len(ours))) if other[k] != ours[k]]
        print("against %s: %d of %d output lines differ; first at line %s" % (sys.argv[sys.argv.index("--compare-with") + 1],
              len(diff), len(ours), diff[0] + 1 if diff else None))


if __name__ == "__main__":
    main()
