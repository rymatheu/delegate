#!/usr/bin/env python3
"""Replay of the estimator World with AP_AHRS (ardupilot/out/Estimator, README.md "Phase 3: AP_AHRS in the estimator
World, the full estimation replay") on a recorded flight, against the reference vehicle's estimation output, step by
step, bit for bit.

The World holds the sensor front ends with the reference's stand-ins and scheduler stand-in, AP_DAL, NavEKF3 (with its
AP_NavEKF_Source, cores and EKFGSF_yaw banks) and AP_AHRS (with its DCM and EKF3 backends and the view). The vehicle and
the HAL's other drivers are not translated: this script and lean/EstimationReplay.lean (the harness) make the calls the
vehicle makes on the translated objects, at the places the reference's trace (`copter_ref --est`) says they were made,
and set the boundary inputs from the trace (the armed flag, the time flying). The harness's commands extend those of
ardupilot/sensors_replay.py (see its docstring: P F S A BI CI GI BC II WS IU GU CT CV CR BU E) with:

  AV                 Copter::allocate_motors's `ahrs.create_view(ROTATION_NONE)` (after barometer.init)
  AI                 Copter::startup_INS_ground's `ahrs.init()`, `ahrs.set_vehicle_class(COPTER)` (before ins.init)
  AR                 its `ahrs.reset()` (after ins.init)
  AU flying last_ms  `ahrs.update(true)` (fast task 3, read_AHRS); AP_Vehicle's time flying from `flying=` (the step before)
  HE armed           Copter::update_home_from_EKF (fast task 7): set_home_to_current_location through AP_AHRS's
                     get_location, get_origin, set_home while home is not set
  TH b               `ahrs.set_terrain_hgt_stable(b)` (task 11, throttle_loop; b the vehicle's value, `thgt=` after it)
  HA                 AP_Arming_Copter::arm's home handling (task 28, in the step that arms)

After every line the harness prints the probe's AP_AHRS keys (`q rpy dcm vel pos loc gyro accef resets healthy initialised
origin ekf fs`), EKF3 keys (`primary ncores gbias abias var` and per core `c<k>.x c<k>.fs c<k>.P c<k>.out c<k>.imu c<k>.var
c<k>.gsf`), the front ends' keys and the vehicle-side keys the World holds (`tkd thgt home cfg comp bgnd`); this script
compares them with the trace.

The parameters (Phase 4, README.md "Phase 4: AP_Param"): the translated AP_Param's load_all on the flight's storage image
(`L <image>`: lean/ParamBoot.lean runs the vehicle's AP_Param boot sequence, then every parameter path of the World is read
from the parameter memory at its address, lean/ParamHarnessData.lean), set before the objects' init. The reference's
`# params` line (every parameter the World holds: AP_Baro, Compass, AP_InertialSensor, AP_GPS, NavEKF3 and its
AP_NavEKF_Source, AP_AHRS, as the vehicle holds them after load_all) is no longer the source: it names the paths and is
compared with the values the translated load_all gives (`lean/.lake/build/bin/param_dump IMAGE --est`). Before Phase 4
the replay set them from `# params` (`P name value`; ESTIMATION_REPLAY_PARAMS=probe restores that).

Usage: ardupilot/estimation_replay.py FLIGHT_DIR [--lines N] [--est EST] [--bench K] [--no-build]
EST defaults to build/est/<flight>.txt, which the reference writes if missing or older than copter_ref:
build/reference/copter_ref --storage FLIGHT_DIR/storage_in.bin --est build/est/<flight>.txt < FLIGHT_DIR/inputs.txt.
--bench K: K launches of the harness in timing mode (one process each, the first discarded), the time per step.
ESTIMATION_REPLAY_DROP=C1,C2 leaves out the harness commands named (sensitivity checks).
"""
import argparse
import json
import os
import re
import statistics
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")
sys.path.insert(0, HERE)
import sensors_replay as sr  # noqa: E402

AHRS_KEYS = re.compile(r"^(q|rpy|dcm|vel|pos|loc|gyro|accef|resets|healthy|initialised|origin|ekf|fs)$")
EKF_KEYS = re.compile(r"^(primary|ncores|gbias|abias|var|c\d+\.(x|fs|P|out|imu|var|gsf))$")
FE_KEYS = re.compile(r"^(baro|mag|ins|imu\d+|gps\d*|ev|evx)$")
VEH_KEYS = re.compile(r"^(tkd|thgt|home|cfg|comp|bgnd)$")
KEYS = (AHRS_KEYS, EKF_KEYS, FE_KEYS, VEH_KEYS)


def parse_est(path, n):
    params, lines = {}, []
    with open(path) as f:
        for line in f:
            if line.startswith("# params"):
                for tok in line.split()[2:]:
                    k, _, v = tok.partition("=")
                    params[k] = v
                continue
            if line.startswith("#"):
                continue
            lines.append(dict(tok.partition("=")[::2] for tok in line.split()))
            if len(lines) >= n:
                break
    return params, lines


def gen_params(sig, names):
    """lean/EstimationReplayParams.lean: `setParam w name value` for the parameters the reference prints."""
    leaves = {}
    for w in sig["world"]:
        if w.get("class") is None:
            continue
        c = next(c for c in sig["classes"] if c["cxx"] == w["class"])
        for lf in c["leaves"]:
            leaves["%s.%s" % (w["name"], lf["cxx"])] = (w["name"], lf)
    lines = ["import Estimator_lib", "", "/-! Generated by ardupilot/estimation_replay.py: the World's parameters by the names the reference's",
             "probe prints (reference/hal/est_probe.cpp, `# params`). -/", "", "open FloatLib.Floats (Binary32 Binary64)", "open Estimator_lib", "",
             "private def hexNat' (s : String) : Nat :=",
             "  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10)) 0",
             "private def f32 (s : String) : Binary32 := Binary32.ofBits (UInt32.ofNat (hexNat' s))",
             "private def nat (s : String) : Nat := s.toNat?.getD 0", "private def int (s : String) : Int := s.toInt?.getD 0", "",
             "def setParam (w : World) (name : String) (v : String) : World :=", "  match name with"]
    missing = []
    for nm in names:
        obj, _, rest = nm.partition(".")
        m = re.match(r"^(.*)\.([xyz])$", rest)
        cands = ["%s.%s._value" % (obj, rest)] + (["%s.%s._value.%s" % (obj, m.group(1), m.group(2))] if m else []) + ["%s.%s" % (obj, rest)]
        hit = next((leaves[c] for c in cands if c in leaves), None)
        if hit is None:
            missing.append(nm)
            continue
        wname, lf = hit
        lines.append("  | \"%s\" => %s" % (nm, sr.update_expr("w", [("f", wname)] + sr.lean_steps(lf["lean"]), sr.CONV[lf["type"]])))
    lines.append("  | _ => w")
    with open(os.path.join(LEAN, "EstimationReplayParams.lean"), "w") as f:
        f.write("\n".join(lines) + "\n")
    return missing


def commands(params, est, inputs, image=None):
    if image is not None:
        out = ["L " + image.hex()]
    else:
        out = ["P %s %s" % (k, v) for k, v in params.items()]
    fed = 0
    calibrated = False
    gyro_stored = "1" if params.get("ins._gyro_id_old_param[0]", "0") != "0" else "0"
    accel_stored = "1" if params.get("ins._accel_id_old_param[0]", "0") != "0" else "0"
    prev = {"armed": "0", "flying": "0,0", "thgt": "3"}
    for k, d in enumerate(est, 1):
        while fed < min(len(inputs), k + 1000):
            out.append("F " + " ".join(sr.record_tokens(inputs[fed])))
            fed += 1
        out.append("A %s" % prev["armed"])
        out.append("S %d" % k)
        ev = int(d.get("ev", "0"))
        evx = int(d.get("evx", "0"))
        init = d.get("init") == "1"
        tasks = [x for x in d.get("tasks", "-").split(",") if x != "-"]
        if init:
            if ev & 1:
                out += ["BI", "AV"]         # barometer.init, then allocate_motors's create_view (ArduCopter/system.cpp:35, :454)
            if ev & 4:
                out += ["GI", "CI"]
            if ev & 2 and not calibrated:
                out.append("BC")
                calibrated = True
            if evx & 1:
                out += ["AI", "II 400 %s %s" % (gyro_stored, accel_stored), "AR"]     # startup_INS_ground
        if tasks:
            out.append("WS")
            for x in tasks:
                if x == "0":
                    out.append("IU")
                elif x == "3":
                    fl = prev["flying"].split(",")
                    out.append("AU %s %s" % (fl[0], fl[1]))
                elif x == "7":
                    out.append("HE %s" % prev["armed"])
                elif x == "11":
                    out.append("TH %s" % ("1" if d["thgt"] == "1" else "0"))
                elif x == "12":
                    out.append("GU")
        elif d.get("thgt", "3") != prev["thgt"]:
            sys.exit("estimation_replay: thgt changed outside task 11 at line %d" % k)
        if not init:
            if "13" in tasks:
                thr, volt = d["cin"].split(",")       # the vehicle's motors->get_throttle(), battery.voltage()
                out += ["CT %s" % thr, "CV %s" % volt, "CR"]
            if ev & 2:
                out.append("BU %s" % d["armed"])
            if "28" in tasks and prev["armed"] == "0" and d["armed"] == "1":
                out.append("HA")            # AP_Arming_Copter::arm, from the arming command (GCS::update_receive, task 28)
        if d.get("tkd", "0,0,0,0") != "0,0,0,0":
            sys.exit("estimation_replay: takeoff/touchdown expected at line %d: not modeled (AP_GroundEffect is compiled out)" % k)
        out.append("E %d %s" % (k, d["t"]))
        for key in prev:
            if key in d:
                prev[key] = d[key]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("flight")
    ap.add_argument("--lines", type=int, default=36013)
    ap.add_argument("--est", default=None)
    ap.add_argument("--bench", type=int, default=0)
    ap.add_argument("--no-build", action="store_true")
    a = ap.parse_args()
    name = os.path.basename(a.flight.rstrip("/"))
    est_path = a.est
    ref = os.path.join(ROOT, "build", "reference", "copter_ref")
    if est_path is None:
        est_path = os.path.join(ROOT, "build", "est", name + ".txt")
        if not os.path.exists(est_path) or os.path.getmtime(est_path) < os.path.getmtime(ref):
            os.makedirs(os.path.dirname(est_path), exist_ok=True)
            with open(os.path.join(a.flight, "inputs.txt")) as fin:
                p = subprocess.run([ref, "--storage", os.path.join(a.flight, "storage_in.bin"), "--est", est_path], stdin=fin, stdout=subprocess.DEVNULL)
            if p.returncode != 0:
                sys.exit("estimation_replay: copter_ref failed (build it with reference/build.py)")
    params, est = parse_est(est_path, a.lines)
    if not any(k.startswith("ahrs.") for k in params) or "cin" not in est[0]:
        sys.exit("estimation_replay: %s has no AP_AHRS parameters in `# params` or no `cin=` (rebuild copter_ref)" % est_path)
    with open(os.path.join(a.flight, "inputs.txt")) as f:
        inputs = [l for _, l in zip(range(a.lines + 1100), f)]
    with open(os.path.join(HERE, "out", "Estimator", "Estimator_lib.signatures.json")) as f:
        sig = json.load(f)
    missing = gen_params(sig, list(params))
    if missing:
        sys.exit("estimation_replay: parameters without a World leaf: %s" % ", ".join(missing))
    if not a.no_build:
        p = subprocess.run(["lake", "build", "estimation_replay", "param_dump"], cwd=LEAN, capture_output=True, text=True)
        if p.returncode != 0:
            sys.exit(p.stdout[-3000:] + p.stderr[-3000:])
        if "warning" in p.stdout + p.stderr:
            sys.exit("estimation_replay: warnings in the Lean build:\n" + "\n".join(l for l in (p.stdout + p.stderr).splitlines() if "warning" in l)[-3000:])
    image = None
    if os.environ.get("ESTIMATION_REPLAY_PARAMS") != "probe":
        # the parameters from the translated AP_Param's load_all (the same boot sequence in-process: `L`); the probe's
        # `# params` compared with them
        storage = os.path.join(a.flight, "storage_in.bin")
        with open(storage, "rb") as f:
            image = f.read()
        tmp = os.path.join(ROOT, "build", "est", name + ".lean_params.txt")
        os.makedirs(os.path.dirname(tmp), exist_ok=True)
        r = subprocess.run([os.path.join(LEAN, ".lake", "build", "bin", "param_dump"), storage, "--est", tmp], capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit("estimation_replay: param_dump failed: " + r.stderr[-2000:])
        with open(tmp) as f:
            lean_params = dict(l.strip().split("=", 1) for l in f if "=" in l)
        same = sum(1 for k in params if lean_params.get(k) == params[k])
        print("parameters: %d from the translated AP_Param::load_all on %s (the probe's `# params`: %d, %d equal)"
              % (len(lean_params), os.path.relpath(storage, ROOT), len(params), same))
        if set(lean_params) != set(params):
            sys.exit("estimation_replay: the translated load_all's paths differ from the probe's")
        params = lean_params
    cl = commands(params, est, inputs, image)
    if os.environ.get("ESTIMATION_REPLAY_DROP"):       # (sensitivity checks: leave out the harness commands named)
        drop = os.environ["ESTIMATION_REPLAY_DROP"].split(",")
        cl = [c for c in cl if c.split()[0] not in drop]
    cmds = "\n".join(cl) + "\n"
    if os.environ.get("ESTIMATION_REPLAY_CMDS"):
        with open(os.environ["ESTIMATION_REPLAY_CMDS"], "w") as f:
            f.write(cmds)
    exe = os.path.join(LEAN, ".lake", "build", "bin", "estimation_replay")
    if a.bench:
        bench(exe, cmds, a.bench, est, name)
        return
    r = subprocess.run([exe], input=cmds, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(r.stderr[-3000:])
    got = r.stdout.splitlines()
    compared = skipped = diff = values = equal = 0
    first = None
    perkey = {}             # key (cores' keys as c<k>.*) -> [values, equal, steps compared, steps differing, first differing line]
    groups = {g: [0, 0] for g in ("AHRS", "EKF3", "front ends", "vehicle side")}
    gname = dict(zip(KEYS, groups))
    for line in got:
        toks = line.split()
        k, t, lines_consumed = int(toks[0]), toks[1], int(toks[2])
        if lines_consumed != k:
            skipped += 1            # inside a front-end call in the reference (barometer.calibrate's and ins.init's delays)
            continue
        ref_d = est[k - 1]
        mine = dict(x.partition("=")[::2] for x in toks[3:])
        compared += 1
        keys = sorted(set(key for key in ref_d if any(r.match(key) for r in KEYS)) | set(mine))
        bad = []
        for key in keys:
            rv = ref_d.get(key, "").split(",") if key in ref_d else []
            mv = mine.get(key, "").split(",") if key in mine else []
            n = max(len(rv), len(mv))
            eq = sum(1 for i in range(min(len(rv), len(mv))) if rv[i] == mv[i])
            values += n
            equal += eq
            g = groups[gname[next(r for r in KEYS if r.match(key))]]
            g[0] += n
            g[1] += eq
            pk = perkey.setdefault(re.sub(r"^c\d+\.", "c<k>.", key), [0, 0, 0, 0, None])
            pk[0] += n
            pk[1] += eq
            pk[2] += 1
            if eq != n:
                bad.append(key)
                pk[3] += 1
                if pk[4] is None:
                    pk[4] = k
        if bad:
            diff += 1
            if first is None:
                first = (k, t, bad, {b: (ref_d.get(b), mine.get(b)) for b in bad[:4]})
    print("estimation replay %s: %d lines (boot init through %d main loops); steps compared: %d (%d inside barometer.calibrate and ins.init not "
          "compared); values compared: %d, equal: %d, different: %d; %d steps differ"
          % (name, len(got), sum(1 for d in est if d.get("init") == "0"), compared, skipped, values, equal, values - equal, diff))
    print("  by group: " + "; ".join("%s %d values, %d different" % (g, v[0], v[0] - v[1]) for g, v in groups.items()))
    print("  by key (values compared/different, steps with the key): " + ", ".join(
        "%s %d/%d/%d" % (key, v[0], v[0] - v[1], v[2]) for key, v in sorted(perkey.items())))
    if first:
        print("  first difference: line %d (%s) keys %s: %s" % first)
        for key, v in sorted(((key, v) for key, v in perkey.items() if v[3]), key=lambda x: x[1][4]):
            print("  %s: %d steps differ, first at line %d" % (key, v[3], v[4]))
    sys.exit(1 if diff else 0)


def bench(exe, cmds, launches, est, name):
    """K launches of the harness in timing mode (`--bench`: the commands parsed first, the parameters set and the input
    records fed into the scheduler's ring outside the timed region, IO.monoNanosNow around each line's calls and around
    its AP_AHRS::update); the first launch is discarded as warm-up. Each line's time is the median over the launches."""
    runs = []
    for i in range(launches):
        r = subprocess.run([exe, "--bench"], input=cmds, capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(r.stderr[-3000:])
        runs.append([tuple(int(y) for y in x.split("/")) for x in r.stdout.split()])
        if len(runs[-1]) != len(est):
            sys.exit("estimation_replay: %d timed lines for %d steps" % (len(runs[-1]), len(est)))
        print("launch %d: %d steps, %.2f s in steps, %.2f s in AP_AHRS::update" % (i + 1, len(runs[-1]), sum(x[0] for x in runs[-1]) / 1e9,
                                                                                sum(x[1] for x in runs[-1]) / 1e9), file=sys.stderr)
    runs = runs[1:] if len(runs) > 1 else runs
    per = [statistics.median(r[j][0] for r in runs) / 1000.0 for j in range(len(est))]      # µs per step
    ahrs = [statistics.median(r[j][1] for r in runs) / 1000.0 for j in range(len(est))]
    boot = lambda d: d.get("init") == "1" and d.get("tasks", "-") == "-"
    if os.environ.get("EST_BENCH_DUMP"):
        # (Phase 5d, profiling) per step: the step's time and its AP_AHRS::update time, µs
        with open(os.environ["EST_BENCH_DUMP"], "w") as f:
            for j in range(len(est)):
                f.write("%d %.1f %.1f\n" % (j + 1, per[j], ahrs[j]))

    def row(nm, xs):
        xs2 = sorted(xs)
        p99 = xs2[min(len(xs2) - 1, int(0.99 * len(xs2)))]
        return "| %s | %d | %.1f | %.1f | %.1f | %.1f | %.2f s |" % (nm, len(xs), statistics.mean(xs), statistics.median(xs), p99, max(xs), sum(xs) / 1e6)
    print("estimator speed %s (%d launches, first discarded; per step the median over the launches; µs)" % (name, launches))
    print("| part | steps | mean | median | p99 | max | total |")
    print("|---|---|---|---|---|---|---|")
    print(row("all steps", per))
    print(row("boot init (lines consumed inside setup())", [p for p, d in zip(per, est) if boot(d)]))
    print(row("main loop", [p for p, d in zip(per, est) if not boot(d)]))
    print(row("main loop, EKF3 running", [p for p, d in zip(per, est) if not boot(d) and int(d.get("ncores", "0")) > 0]))
    print(row("main loop, AP_AHRS::update alone (DCM, EKF3 through AP_DAL, the view)", [a for a, d in zip(ahrs, est) if not boot(d)]))
    print(row("main loop, the rest (front ends, scheduler, stand-ins)", [p - a for p, a, d in zip(per, ahrs, est) if not boot(d)]))
    over = [(p, d["t"]) for p, d in zip(per, est) if p > 2500]
    print("steps over the 2,500 µs budget: %d (%s)" % (len(over), ", ".join("%.0f µs at t=%.3f s" % (p, int(t) / 1e6) for p, t in sorted(over, reverse=True)[:5])))
    big = [a for a, d in zip(ahrs, est) if not boot(d) and a > 200]
    print("main-loop steps whose AP_AHRS::update takes over 200 µs: %d, mean %.0f µs" % (len(big), statistics.mean(big) if big else 0))
    print("mean per step per launch: %s µs" % ", ".join("%.1f" % (sum(x[0] for x in r) / 1e3 / len(r)) for r in runs))


if __name__ == "__main__":
    main()
