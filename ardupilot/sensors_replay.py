#!/usr/bin/env python3
"""Replay of the sensor front ends' World (ardupilot/out/Sensors, README.md "Phase 3: sensor front ends and
AP_Param") on a recorded flight, against the reference vehicle's estimation output.

The reference (`copter_ref --est`, reference/hal/est_probe.cpp) writes, per input line, the front ends' state
after the step (`baro=`, `mag=`), the stand-ins' events of the step (`ev=`: AP_Baro_SITL constructed, its
update run, AP_Compass_SITL constructed), the scheduler's tasks, the values the rest of the vehicle gave the
estimator (`comp=` the compass's throttle and voltage, `origin=`, `loc=`, `armed=`), and once, at the first
line, the front ends' parameters as AP_Param loaded them (`# params`). This script turns that and the flight's
input lines into commands for lean/SensorsReplay.lean (the harness over the translated World):

  P name value       a parameter as loaded at boot (before the front ends' init)
  F record           an input line, fed to the scheduler stand-in's ring ahead of its consumption
  S k                the vehicle consumes line k outside the front ends (a delay elsewhere in setup(), or the
                     end of a main loop): the World steps until it has consumed k lines
  A b                the armed flag the IMU back end and AP_RTC read (the vehicle's, at the end of the previous step)
  BI, CI             barometer.init, compass.init (the step whose events say the back end was constructed)
  GI                 gps.init (Copter::init_ardupilot calls it right before compass.init: at the compass's event)
  BC                 barometer.calibrate(true) (the first AP_Baro_SITL::update of the boot; it consumes the
                     lines its delays consume)
  II r g a           ins.init(r) (the step whose `evx=` says AP_InertialSensor_SITL was constructed; its gyro
                     calibration consumes the lines its delays consume), with r the loop rate (400) and whether the
                     gyro and accel ids were stored (non-zero at boot: AP_Param::load finds them)
  WS, IU, GU         a main loop ran in the step (`tasks=` not `-`): AP_InertialSensor::wait_for_sample (the
                     scheduler, before the tasks), then AP_InertialSensor::update (task 0) and AP_GPS::update (task
                     12) where `tasks=` lists them; AP_InertialSensor::periodic (task 30) has no effect in the model
                     (the batch sampler is compiled out) and is not called
  CT/CV/CR ...       compass.set_throttle, set_voltage, read (task 13, update_batt_compass), with the
                     throttle and voltage the reference shows and its AHRS location (try_set_initial_location)
  BU ...             barometer.update (task 16, update_altitude, or its event), with the armed flag and the
                     EKF origin (the field elevation)
  E k                print the front ends' state after step k

and compares the harness's lines with the reference's tokens (every front-end key: `baro=`, `mag=`, `ins=`,
`imu<i>=`, `gps=`, `gps<i>=`, `ev=`, `evx=`), line by line; a line the World consumed inside a front-end call
(barometer.calibrate's and ins.init's delays) is in the middle of that call in the reference and is not compared. Usage: ardupilot/sensors_replay.py FLIGHT_DIR [--lines N] [--est EST]. EST defaults to FLIGHT_DIR/est.txt
if it has the front ends' keys (`# params`), else the reference vehicle writes it:
build/reference/copter_ref --storage FLIGHT_DIR/storage_in.bin --est build/est/<flight>.txt < FLIGHT_DIR/inputs.txt.
"""
import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
LEAN = os.path.join(ROOT, "lean")


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
            d = {}
            for tok in line.split():
                k, _, v = tok.partition("=")
                d[k] = v
            lines.append(d)
            if len(lines) >= n:
                break
    return params, lines


def record_tokens(line):
    """The input line's record (reference/hal/est_input.h) as the harness's tokens."""
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


def lean_steps(lean_path):
    """`sensors[0]!.ground_pressure._value` -> [("f","sensors"),("i","0"),("f","ground_pressure"),("f","_value")]."""
    out = []
    for comp in re.findall(r"(«[^»]+»|[^.\[\]!]+)(\[\d+\]!)?", lean_path):
        out.append(("f", comp[0]))
        if comp[1]:
            out.append(("i", comp[1][1:-2]))
    return out


def update_expr(base, steps, value):
    if not steps:
        return value
    k, x = steps[0]
    b = base if re.match(r"^[\w.'«»]+$", base) else "(%s)" % base
    if k == "f":
        return "{ %s with %s := %s }" % (b, x, update_expr("%s.%s" % (b, x), steps[1:], value))
    return "%s.set! %s (%s)" % (b, x, update_expr("%s[%s]!" % (b, x), steps[1:], value))


CONV = {"float": "f32 v", "int8_t": "Int8.ofInt (int v)", "int16_t": "Int16.ofInt (int v)", "int32_t": "Int32.ofInt (int v)",
        "uint8_t": "UInt8.ofNat (nat v)", "uint16_t": "UInt16.ofNat (nat v)", "uint32_t": "UInt32.ofNat (nat v)"}


def gen_params(sig, names):
    """lean/SensorsReplayParams.lean: `setParam w name value` for the parameters the reference prints."""
    leaves = {}
    for w in sig["world"]:
        if w.get("class") is None:
            continue        # a static data member (AP_InertialSensor_SITL's bus_id), not a parameter
        c = next(c for c in sig["classes"] if c["cxx"] == w["class"])
        for lf in c["leaves"]:
            leaves["%s.%s" % (w["name"], lf["cxx"])] = (w["name"], lf)
    lines = ["import Sensors_lib", "", "/-! Generated by ardupilot/sensors_replay.py: the World's parameters by the names the reference's probe",
             "prints (reference/hal/est_probe.cpp, `# params`). -/", "", "open FloatLib.Floats (Binary32 Binary64)", "open Sensors_lib", "",
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
        val = CONV[lf["type"]]
        lines.append("  | \"%s\" => %s" % (nm, update_expr("w", [("f", wname)] + lean_steps(lf["lean"]), val)))
    lines.append("  | _ => w")
    with open(os.path.join(LEAN, "SensorsReplayParams.lean"), "w") as f:
        f.write("\n".join(lines) + "\n")
    return missing


def commands(params, est, inputs):
    out = ["P %s %s" % (k, v) for k, v in params.items()]
    fed = 0
    calibrated = False
    armed = "0"
    gyro_stored = "1" if params.get("ins._gyro_id_old_param[0]", "0") != "0" else "0"
    accel_stored = "1" if params.get("ins._accel_id_old_param[0]", "0") != "0" else "0"
    for k, d in enumerate(est, 1):
        while fed < min(len(inputs), k + 1000):
            out.append("F " + " ".join(record_tokens(inputs[fed])))
            fed += 1
        out.append("A %s" % armed)
        out.append("S %d" % k)
        ev = int(d.get("ev", "0"))
        evx = int(d.get("evx", "0"))
        init = d.get("init") == "1"
        tasks = [x for x in d.get("tasks", "-").split(",") if x != "-"]
        if init:
            if ev & 1:
                out.append("BI")
            if ev & 4:
                out += ["GI", "CI"]
            if ev & 2 and not calibrated:
                out.append("BC")
                calibrated = True
            if evx & 1:
                out.append("II 400 %s %s" % (gyro_stored, accel_stored))
        if tasks:
            # a main loop: the scheduler's wait_for_sample, then the front ends' tasks in execution order
            out.append("WS")
            for x in tasks:
                if x == "0":
                    out.append("IU")
                elif x == "12":
                    out.append("GU")
        armed = d.get("armed", "0")
        if not init:
            if "13" in tasks:
                thr, volt = d["comp"].split(",")
                loc = d["loc"].split(",")
                out += ["CT %s" % thr, "CV %s" % volt, "CR %s %s %s %s" % (loc[0], loc[1], loc[2], loc[3])]
            if ev & 2:
                org = d["origin"].split(",")
                out.append("BU %s %s %s %s %s" % (d["armed"], org[0], org[1], org[2], org[3]))
        out.append("E %d %s" % (k, d["t"]))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("flight")
    ap.add_argument("--lines", type=int, default=36013)
    ap.add_argument("--est", default=None)
    a = ap.parse_args()
    est_path = a.est or os.path.join(a.flight, "est.txt")
    if a.est is None and not (os.path.exists(est_path) and open(est_path).readline().startswith("# params")):
        # the recorded estimation output predates the front ends' keys: the reference writes it again
        os.makedirs(os.path.join(ROOT, "build", "est"), exist_ok=True)
        est_path = os.path.join(ROOT, "build", "est", os.path.basename(a.flight.rstrip("/")) + ".txt")
        with open(os.path.join(a.flight, "inputs.txt")) as fin:
            p = subprocess.run([os.path.join(ROOT, "build", "reference", "copter_ref"), "--storage", os.path.join(a.flight, "storage_in.bin"),
                                "--est", est_path], stdin=fin, stdout=subprocess.DEVNULL)
        if p.returncode != 0:
            sys.exit("sensors_replay: copter_ref failed (build it with reference/build.py)")
    params, est = parse_est(est_path, a.lines)
    with open(os.path.join(a.flight, "inputs.txt")) as f:
        inputs = [l for _, l in zip(range(a.lines + 1100), f)]
    with open(os.path.join(HERE, "out", "Sensors", "Sensors_lib.signatures.json")) as f:
        sig = json.load(f)
    missing = gen_params(sig, list(params))
    if missing:
        sys.exit("sensors_replay: parameters without a World leaf: %s" % ", ".join(missing))
    p = subprocess.run(["lake", "build", "sensors_replay"], cwd=LEAN, capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit(p.stdout[-3000:] + p.stderr[-3000:])
    cmds = "\n".join(commands(params, est, inputs)) + "\n"
    if os.environ.get("SENSORS_REPLAY_CMDS"):
        with open(os.environ["SENSORS_REPLAY_CMDS"], "w") as f:       # (the harness's input, for debugging)
            f.write(cmds)
    exe = os.path.join(LEAN, ".lake", "build", "bin", "sensors_replay")
    r = subprocess.run([exe], input=cmds, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(r.stderr[-3000:])
    got = r.stdout.splitlines()
    compared = skipped = diff = values = 0
    first = None
    for line in got:
        toks = line.split()
        k, t, lines_consumed = int(toks[0]), toks[1], int(toks[2])
        if lines_consumed != k:
            skipped += 1            # inside a front-end call in the reference (barometer.calibrate's delays)
            continue
        ref = est[k - 1]
        mine = dict(x.partition("=")[::2] for x in toks[3:])
        compared += 1
        keys = [key for key in ref if re.match(r"^(baro|mag|ins|imu\d+|gps\d*|ev|evx)$", key)]
        values += sum(len(ref[key].split(",")) for key in keys)
        bad = [key for key in sorted(set(keys) | set(mine)) if mine.get(key) != ref.get(key)]
        if bad:
            diff += 1
            if first is None:
                first = (k, t, bad, {b: (ref.get(b), mine.get(b)) for b in bad})
    print("sensors replay %s: %d lines (boot init through %d main loops): %d compared (baro=, mag=, ins=, imu<i>=, gps=, gps<i>=, ev=, evx=: %d values), "
          "%d inside barometer.calibrate and ins.init not compared; %d differ"
          % (os.path.basename(a.flight.rstrip("/")), len(got), sum(1 for d in est if d.get("init") == "0"), compared, values, skipped, diff))
    if first:
        print("  first difference: line %d (t=%s) keys %s: %s" % first)
    sys.exit(1 if diff else 0)


if __name__ == "__main__":
    main()
