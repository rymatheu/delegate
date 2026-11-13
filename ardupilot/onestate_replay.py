#!/usr/bin/env python3
"""The combined replay over ONE state (README.md "Phase 5: the estimator bridge"): per recorded step, what
ardupilot/estimation_replay.py does (the translated estimator calls, now through the vehicle's bridge adapters, on the
World inside the memory state) and what ardupilot/gcs/gcs_replay.py does (AP_Param's boot over the bridged memory, GCS
receive/send, the IO process), in one process over one state: lean/OneStateReplay.lean (`lake build onestate_replay`).

The two scripts' preparation and comparison are reused unchanged: their harness invocations are intercepted and served
by one run of onestate_replay (the estimator commands with `L <image>` replaced by the boot `B`, interleaved per step
with the GCS schedule lines `G ...`); then each script compares as it always does (estimation keys against the `--est`
trace, the GCS frames against the recorded downlink).

Usage: ardupilot/onestate_replay.py SESSION_DIR [EST]   (EST as gcs_replay.py's: default SESSION_DIR/est.txt)
"""
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "gcs"))
import estimation_replay as er  # noqa: E402
import gcs_replay as gr  # noqa: E402

EXE = os.path.join(ROOT, "lean", ".lake", "build", "bin", "onestate_replay")
_run = subprocess.run
STATE = {}


class Captured(Exception):
    pass


def run_patched(args, *a, **k):
    exe = os.path.basename(args[0]) if isinstance(args, list) else ""
    if exe == "estimation_replay":
        if "out" in STATE:
            return subprocess.CompletedProcess(args, 0, STATE["out"], "")
        STATE["cmds"] = k["input"]
        raise Captured()
    if exe == "gcs_replay":
        sched, frames, answers, storage, outp, snap = args[1:7]
        cmds = STATE["cmds"].split("\n")
        sl = open(sched).read().split("\n")
        sl = [l for l in sl if l]
        merged = []
        si = 0
        for c in cmds:
            if not c:
                continue
            if c.startswith("L "):
                merged.append("B")
                continue
            merged.append(c)
            if c.startswith("E "):
                merged.append("G " + sl[si])
                si += 1
        merged += ["G " + l for l in sl[si:]]
        t0 = time.time()
        p = _run([EXE, frames, answers, storage, outp, snap], input="\n".join(merged) + "\n", capture_output=True, text=True)
        STATE["secs"] = time.time() - t0
        if p.returncode != 0:
            sys.exit("onestate_replay failed: " + p.stderr[-3000:])
        STATE["out"] = p.stdout
        STATE["outp"] = outp
        return subprocess.CompletedProcess(args, 0, "", p.stderr)
    return _run(args, *a, **k)


WORLD_PARAM_PREFIXES = (b"AHRS_", b"EK3_", b"EK2_", b"INS_", b"COMPASS_", b"BARO", b"GPS", b"RTC_")


def vehicle_frame_5b(b, mid):
    """(Phase 5b) the frames this replay still takes from the recording: STATUSTEXT (formatting, D10) and the PARAM_VALUE
    notifications (index 65535) of the vehicle's own parameters (ESC_CALIBRATION, MIS_TOTAL, ...: saved by vehicle code
    that this replay does not run). The notifications of the estimator's parameters (the prefixes above: saved or
    notified by World code, AP_Param::save/notify events replayed on the memory, written by the translated save_sync
    -> GCS::send_parameter_value) are the translation's."""
    if mid == 253:
        return True
    if mid == 22 and len(b) >= 10 + 8 and b[10 + 6] == 0xff and b[10 + 7] == 0xff:
        name = b[10 + 8:10 + 24].split(b"\0")[0]
        return not name.startswith(WORLD_PARAM_PREFIXES)
    return False


def main():
    gr.vehicle_frame = vehicle_frame_5b
    d = sys.argv[1]
    est = sys.argv[2] if len(sys.argv) > 2 else None
    subprocess.run = run_patched
    flight = os.path.basename(os.path.normpath(d))
    nlines = ["--lines", str(sum(1 for _ in open(os.path.join(d, "inputs.txt"))))]
    # 1. the estimator commands (estimation_replay.py's), captured at its harness call
    sys.argv = ["estimation_replay.py", d, "--no-build"] + nlines + (["--est", est] if est else [])
    try:
        er.main()
    except Captured:
        pass
    # 2. the GCS replay (gcs_replay.py), whose harness call runs the one-state replay
    print("== GCS byte replay (one state) ==")
    sys.argv = ["gcs_replay.py", d] + ([est] if est else [])
    gr.main()
    # 3. the estimation comparison of the same run
    print("== estimation comparison (one state) ==")
    sys.argv = ["estimation_replay.py", d, "--no-build"] + nlines + (["--est", est] if est else [])
    try:
        er.main()
    except SystemExit as e:
        if e.code not in (0, None):
            print("(estimation replay: differences)")
    # per-step time of the combined replay (estimator calls + GCS work of each step)
    ns = None
    for l in open(STATE["outp"]):
        if l.startswith("# step ns "):
            ns = [int(x) / 1000.0 for x in l.split()[3].split(",") if x]
    if ns:
        s = sorted(ns)
        print("one-state replay %s: %d steps, per step (estimator calls + GCS work) mean %.1f us, median %.1f, p99 %.1f, max %.1f; whole process %.1f s"
              % (flight, len(ns), sum(ns) / len(ns), s[len(s) // 2], s[min(len(s) - 1, int(0.99 * len(s)))], s[-1], STATE["secs"]))


if __name__ == "__main__":
    main()
