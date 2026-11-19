#!/usr/bin/env python3
"""Compare the flights of the two vehicles tick by tick and write sim/RESULTS.md and
sim/out/compare-<mission>.csv (run by sim/fly.sh).

For each mission, the runs sim/out/lean-<mission> (lean/.lake/build/bin/copter_lean) and
sim/out/ref-<mission> (build/vehicle/copter_ref) are compared:
- the flown actuator lines (motors.txt, exact decimals as the vehicles printed them in the loop) and
  the simulator's state lines (inputs.txt), tick by tick;
- the bit patterns of all 22 values of each tick: each run's recorded state lines are replayed
  through its own binary with `--exact --trace --bits` (the same command as the flight, from the
  first line of summary.txt), which prints the 4 actuators and the 18 trace numbers as exact
  decimals and then as bit patterns; the replayed actuators are checked against the flown ones.
The summary numbers come from each run's summary.txt and flight.csv.

Usage: sim/.venv/bin/python sim/compare_flights.py MISSION...
"""
import csv
import math
import re
import subprocess
import sys
from pathlib import Path

SIM = Path(__file__).resolve().parent
OUT = SIM / "out"
NAMES = ["m1", "m2", "m3", "m4", "sp_n", "sp_e", "sp_d", "vsp_n", "vsp_e", "vsp_d", "asp_n", "asp_e", "asp_d",
         "thr_n", "thr_e", "thr_d", "roll_t", "pitch_t", "yaw_t", "p_t", "q_t", "r_t"]
TITLES = {"hover": "Hover 1 m above the origin (copter-cf2x.txt + copter-hover.txt + copter-cf2x-tuned.txt, 10 s)",
          "course-1ms": "Figure-eight course at 1 m/s (copter-cf2x.txt + copter-course-speed.txt + copter-cf2x-tuned.txt, up to 60 s)",
          "figure8": "Figure-eight course with ArduPilot's default WP_SPD 10 m/s, WP_ACC 2.5 m/s^2 (copter-cf2x.txt + copter-cf2x-tuned.txt, up to 30 s)"}


def replay(run):
    """The run's state lines through its own binary with --exact --trace --bits: [(decimals, hex)]."""
    first = (run / "summary.txt").read_text().splitlines()[0]
    m = re.match(r"^.*?: (.*) \(cwd (.*)\)$", first)
    cmd = m.group(1).split() + ["--trace", "--bits"]
    res = subprocess.run(cmd, cwd=m.group(2), input=(run / "inputs.txt").read_text(), capture_output=True, text=True, check=True)
    out = []
    for line in res.stdout.splitlines():
        dec, hx = line.split("|")
        out.append((dec.split(), hx.split()))
    return out


def stats(run):
    s = (run / "summary.txt").read_text()
    rows = list(csv.DictReader(open(run / "flight.csv")))
    err = [math.dist((float(r["x_n"]), float(r["y_e"]), float(r["z_d"])), (float(r["sp_n"]), float(r["sp_e"]), float(r["sp_d"])))
           for r in rows]
    end = re.search(r"^end: (.*?); (\d+) ticks, ([\d.]+) s simulated", s, re.M)
    fin = re.search(r"final position error to last waypoint: ([\d.]+) cm \(pos NED (\S+) (\S+) ([^\s,]+)", s)
    passed = re.search(r"waypoints passed in order within ([\d.]+) m: (\d+) of (\d+)", s)
    within = re.findall(r"^waypoint (\d+) .*?(first within [\d.]+ m at [\d.]+ s|not within [\d.]+ m)", s, re.M)
    reached = sum(1 for _, w in within if w.startswith("first within"))
    last = re.search(r"at ([\d.]+) s", within[-1][1]) if within else None
    return {"end": end.group(1), "ticks": int(end.group(2)), "time": float(end.group(3)),
            "err_mean": 100 * sum(err) / len(err), "err_max": 100 * max(err), "err_rms": 100 * math.sqrt(sum(e * e for e in err) / len(err)),
            "final": float(fin.group(1)), "final_pos": (fin.group(2), fin.group(3), fin.group(4)),
            "passed": "%s of %s (within %s m)" % (passed.group(2), passed.group(3), passed.group(1)),
            "reached": "%d of %d (within 0.1 m)" % (reached, len(within)), "rows": rows,
            "last": ("%s s" % last.group(1)) if last else "not within 0.1 m"}


def main():
    missions = sys.argv[1:]
    md = ["# Flights of the two vehicles", "",
          "Each mission is flown twice in gym-pybullet-drones (CF2X, PyBullet physics at 1200 Hz, control at 400 Hz,",
          "start at rest on the ground at the origin, facing north), once with `copter_lean` (the Lean translations",
          "of AP_MotorsMatrix, AC_AttitudeControl_Multi, AC_PosControl, AC_WPNav and the AHRS view, with the mission",
          "harness of `lean/Vehicle.lean`) and once with `copter_ref` (ArduPilot's classes compiled unmodified, with",
          "the same harness in C++, `ardupilot/vehicle/copter_ref.cpp`). The two runs are separate processes and",
          "separate simulations; they start from the same initial conditions. Commands: `sim/fly.sh` (README.md).",
          "",
          "Tracking error: the distance from the simulated vehicle to AC_PosControl's position target after the",
          "same tick (`--trace`). Final position error: distance to the last waypoint at the end of the run.",
          "Waypoints passed: in order within 0.2 m (the run's end condition); reached: closest approach within",
          "0.1 m. The per-tick comparison is bit for bit: the actuators the simulator received, and all 22 values",
          "of the tick (4 actuators, 18 trace numbers) from each run's replay with `--exact --trace --bits`.", ""]
    for m in missions:
        lean, ref = OUT / ("lean-" + m), OUT / ("ref-" + m)
        sl, sr = stats(lean), stats(ref)
        fl = (lean / "motors.txt").read_text().splitlines()
        fr = (ref / "motors.txt").read_text().splitlines()
        il = (lean / "inputs.txt").read_text().splitlines()
        ir = (ref / "inputs.txt").read_text().splitlines()
        rl, rr = replay(lean), replay(ref)
        for run, flown, rep in ((lean, fl, rl), (ref, fr, rr)):
            bad = [k for k in range(len(flown)) if " ".join(rep[k][0][:4]) != flown[k]]
            if bad or len(rep) != len(flown):
                sys.exit("compare_flights.py: the replay of %s differs from its flight at tick %s" % (run, bad[:1]))
        n = min(len(fl), len(fr))
        same_act = sum(1 for k in range(n) if fl[k] == fr[k])
        same_in = sum(1 for k in range(n) if il[k] == ir[k])
        same_hex_act = sum(1 for k in range(n) if rl[k][1][:4] == rr[k][1][:4])
        same_all = sum(1 for k in range(n) if rl[k][1] == rr[k][1])
        first = next((k for k in range(n) if rl[k][1] != rr[k][1]), None)
        if first is None:
            fd = "none"
        else:
            fields = ["%s Lean %s C++ %s" % (NAMES[j], rl[first][1][j], rr[first][1][j]) for j in range(22) if rl[first][1][j] != rr[first][1][j]]
            fd = "tick %d: %s" % (first + 1, "; ".join(fields[:4]))
        trace_ok = all("trace replay" not in (OUT / (v + "-" + m + ".log")).read_text() for v in ("lean", "ref"))
        # the per-tick CSV for figures
        with open(OUT / ("compare-%s.csv" % m), "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(["tick", "t", "lean_m1", "lean_m2", "lean_m3", "lean_m4", "ref_m1", "ref_m2", "ref_m3", "ref_m4",
                        "lean_x_n", "lean_y_e", "lean_z_d", "ref_x_n", "ref_y_e", "ref_z_d",
                        "lean_sp_n", "lean_sp_e", "lean_sp_d", "ref_sp_n", "ref_sp_e", "ref_sp_d"])
            for k in range(max(len(fl), len(fr))):
                a = sl["rows"][k] if k < len(sl["rows"]) else None
                b = sr["rows"][k] if k < len(sr["rows"]) else None
                row = [k + 1, (a or b)["t"]]
                row += rl[k][1][:4] if a else [""] * 4
                row += rr[k][1][:4] if b else [""] * 4
                row += [a["x_n"], a["y_e"], a["z_d"]] if a else [""] * 3
                row += [b["x_n"], b["y_e"], b["z_d"]] if b else [""] * 3
                row += rl[k][0][4:7] if a else [""] * 3
                row += rr[k][0][4:7] if b else [""] * 3
                w.writerow(row)
        md += ["## %s" % TITLES.get(m, m), "",
               "| | `copter_lean` | `copter_ref` |", "|---|---|---|",
               "| end of the run | %s | %s |" % (sl["end"], sr["end"]),
               "| flight time, ticks | %.4f s, %d | %.4f s, %d |" % (sl["time"], sl["ticks"], sr["time"], sr["ticks"]),
               "| tracking error mean, rms, max | %.2f, %.2f, %.2f cm | %.2f, %.2f, %.2f cm |" % (sl["err_mean"], sl["err_rms"], sl["err_max"], sr["err_mean"], sr["err_rms"], sr["err_max"]),
               "| final position error (final position NED, m) | %.2f cm (%s) | %.2f cm (%s) |" % (sl["final"], " ".join(sl["final_pos"]), sr["final"], " ".join(sr["final_pos"])),
               "| waypoints passed | %s | %s |" % (sl["passed"], sr["passed"]),
               "| waypoints reached | %s | %s |" % (sl["reached"], sr["reached"]),
               "| last waypoint first within 0.1 m | %s | %s |" % (sl["last"], sr["last"]),
               "| output directory | `sim/out/lean-%s` | `sim/out/ref-%s` |" % (m, m), "",
               "Per-tick comparison: %d ticks compared (%d and %d flown); simulator states identical on %d; "
               "actuators identical (as flown) on %d, (bits) on %d; all 22 values identical (bits) on %d; first "
               "differing tick: %s. `run_copter.py`'s own `--trace` replay check: %s for both. Per-tick data: "
               "`sim/out/compare-%s.csv`." % (n, len(fl), len(fr), same_in, same_act, same_hex_act, same_all, fd,
                                               "passed" if trace_ok else "FAILED", m), ""]
        print("%s: %d ticks compared; actuators identical on %d; all 22 values on %d; first difference %s" % (m, n, same_hex_act, same_all, fd))
    (SIM / "RESULTS.md").write_text("\n".join(md))


if __name__ == "__main__":
    main()
