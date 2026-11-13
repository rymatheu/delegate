#!/usr/bin/env python3
"""The scenario suite (Phase 5d; README.md "Phase 5d summary"): six short sessions recorded with the reference vehicle
(build/reference/copter_ref) through sim/fly_reference.py's scripted ground station, each checked on the translated
whole vehicle. Harness code only.

    python3 sim/scenarios.py [--record] [--live] [--only NAME[,NAME...]] [--exe BIN]

--record   records each scenario with the reference (sim/out/scenario-NAME: inputs.txt, outputs.txt, storage_in.bin,
           log.txt, summary.txt) and its estimation trace (`copter_ref --est`, build/scenarios/NAME/est.txt; the reference
           re-run on the recorded inputs must reproduce outputs.txt byte for byte)
(default)  the whole-vehicle replay of each recording (ardupilot/vehicle/vehicle_replay.py): one line per scenario with
           PWM, down bytes, tasks and storage
--live     also flies each scenario closed loop with the translated vehicle (sim/lean_vehicle.py as fly_reference.py's
           --bin, build/scenarios/NAME/live) and compares inputs.txt and outputs.txt with the recording (cmp)

The scenarios (fly_reference.py SCENARIOS): loiter (LOITER with stick input, then LAND), brake (GUIDED toward a point,
BRAKE while moving, ALT_HOLD with sticks, LAND), rtl (RTL from 12 m), guided (DO_REPOSITION, CONDITION_YAW,
DO_CHANGE_SPEED, a velocity target, NAV_LAND), battery (battery failsafe, LAND), prearm (arming refused with its texts,
an arming in STABILIZE and the auto-disarm, then the radio failsafe in flight).
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
NAMES = ["loiter", "brake", "rtl", "guided", "battery", "prearm"]
REF = os.path.join(ROOT, "build", "reference", "copter_ref")
PY = os.path.join(ROOT, "build", "reference", "venv", "bin", "python")
STORAGE = os.path.join(ROOT, "build", "reference", "storage-cf2x.bin")


def rec_dir(n):
    return os.path.join(HERE, "out", "scenario-" + n)


def work_dir(n):
    return os.path.join(ROOT, "build", "scenarios", n)


def record(n):
    d, w = rec_dir(n), work_dir(n)
    os.makedirs(w, exist_ok=True)
    p = subprocess.run([PY, os.path.join(HERE, "fly_reference.py"), "--script", n, "--storage", STORAGE, "--duration", "90",
                        "--out", d], cwd=ROOT, capture_output=True, text=True)
    if p.returncode != 0:
        return "%s: recording FAILED (%s)" % (n, p.stdout.strip().splitlines()[-1:] or p.stderr[-300:])
    est = os.path.join(w, "est.txt")
    rep = os.path.join(w, "ref_replay.txt")
    with open(os.path.join(d, "inputs.txt")) as fi, open(rep, "w") as fo:
        subprocess.run([REF, "--storage", os.path.join(d, "storage_in.bin"), "--est", est], stdin=fi, stdout=fo, check=True)
    same = open(rep, "rb").read() == open(os.path.join(d, "outputs.txt"), "rb").read()
    summ = open(os.path.join(d, "summary.txt")).read().splitlines()
    return "%s: recorded %s; %s; reference re-run %s" % (n, summ[1].split(",")[0], summ[0],
                                                          "identical" if same else "DIFFERS")


def ensure_est(n):
    est = os.path.join(work_dir(n), "est.txt")
    if not os.path.exists(est):
        os.makedirs(work_dir(n), exist_ok=True)
        d = rec_dir(n)
        with open(os.path.join(d, "inputs.txt")) as fi:
            subprocess.run([REF, "--storage", os.path.join(d, "storage_in.bin"), "--est", est], stdin=fi,
                           stdout=subprocess.DEVNULL, check=True)
    return est


def replay(n, exe):
    est = ensure_est(n)
    cmd = [sys.executable, os.path.join(ROOT, "ardupilot", "vehicle", "vehicle_replay.py"), rec_dir(n), "--est", est,
           "--out-dir", os.path.join(work_dir(n), "replay")]
    if exe:
        cmd += ["--exe", exe]
    p = subprocess.run(cmd, capture_output=True, text=True, env=dict(os.environ, LEAN_NUM_THREADS="1"))
    o = p.stdout
    with open(os.path.join(work_dir(n), "replay.log"), "w") as f:
        f.write(o + p.stderr)
    if p.returncode != 0:
        return "%s: replay FAILED (%s)" % (n, (p.stdout + p.stderr).strip().splitlines()[-1:])

    def g(pat):
        m = re.search(pat, o)
        return m.groups() if m else None
    pwm = g(r"PWM identical on (\d+) of (\d+) lines; down bytes identical on (\d+)")
    tasks = g(r"tasks identical on (\d+) of (\d+) steps")
    st = g(r"storage at the end: \d+ bytes, (\d+) differ")
    fpd = g(r"first PWM difference: (.*)")
    fdd = g(r"first down difference: (\(\d+, '\d+')")
    step = g(r"step_us mean=([\d.]+) p99=([\d.]+) max=([\d.]+)")
    ok = pwm and pwm[0] == pwm[1] == pwm[2] and tasks and tasks[0] == tasks[1] and st and st[0] == "0"
    return ("%s: %s replay: PWM %s of %s, down %s, tasks %s of %s, storage %s bytes differ%s%s; step mean %.0f us p99 %.0f us"
            % (n, "ok  " if ok else "DIFF", pwm[0], pwm[1], pwm[2], tasks[0], tasks[1], st[0] if st else "?",
               "" if not fpd or fpd[0] == "None" else "; first PWM difference " + fpd[0][:60],
               "" if not fdd else "; first down difference (line, t) " + fdd[0] + ")",
               float(step[0]), float(step[1])) if pwm and tasks and step else "%s: replay output not parsed" % n)


def live(n, exe):
    w = os.path.join(work_dir(n), "live")
    os.makedirs(w, exist_ok=True)
    env = dict(os.environ, LEAN_VEHICLE_OUT=os.path.join(w, "lean"))
    if exe:
        env["LEAN_VEHICLE_EXE"] = exe
    p = subprocess.run([PY, os.path.join(HERE, "fly_reference.py"), "--script", n, "--bin", os.path.join(HERE, "lean_vehicle.py"),
                        "--storage", STORAGE, "--duration", "90", "--out", w], cwd=ROOT, capture_output=True, text=True, env=env)
    res = []
    for f in ("inputs.txt", "outputs.txt"):
        a = open(os.path.join(rec_dir(n), f), "rb").read()
        b = open(os.path.join(w, f), "rb").read() if os.path.exists(os.path.join(w, f)) else b""
        if a == b:
            res.append("%s identical (%d lines)" % (f, a.count(b"\n")))
        else:
            al, bl = a.split(b"\n"), b.split(b"\n")
            k = next((i for i, (x, y) in enumerate(zip(al, bl)) if x != y), min(len(al), len(bl)))
            res.append("%s DIFFERS at line %d (%d vs %d lines)" % (f, k + 1, a.count(b"\n"), b.count(b"\n")))
    summ = open(os.path.join(w, "summary.txt")).read().splitlines() if os.path.exists(os.path.join(w, "summary.txt")) else [p.stderr[-200:]]
    tim = next((l for l in summ if l.startswith("lockstep timing")), "")
    m = re.search(r"mean ([\d.]+) .*p99 ([\d.]+) max ([\d.]+)", tim)
    return "%s: %s closed loop: %s; %s%s" % (n, "ok  " if all("identical" in r for r in res) else "DIFF", "; ".join(res),
                                             summ[0], ("; step mean %.0f us p99 %.0f us max %.0f us" % tuple(float(x) for x in m.groups())) if m else "")


def main():
    a = sys.argv[1:]
    names = a[a.index("--only") + 1].split(",") if "--only" in a else NAMES
    exe = a[a.index("--exe") + 1] if "--exe" in a else None
    for n in names:
        if "--record" in a:
            print(record(n), flush=True)
            continue
        print(replay(n, exe), flush=True)
        if "--live" in a:
            print(live(n, exe), flush=True)


if __name__ == "__main__":
    main()
