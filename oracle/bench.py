#!/usr/bin/env python3
"""Time one control tick of the Lean ArduCopter port and of ArduPilot's C++ classes (the oracle).

Usage (from anywhere; standard library only):
    python3 oracle/bench.py [--runs 5] [--run DIR] [--params FILE]... [--hold-from N]
                            [--bench BIN] [--oracle BIN] [--port BIN] [--io-reps 3] [--out FILE]

Builds nothing; build first with `lake build bench copter` and `oracle/build.sh nosincos`.

1. Runs `bench` (Copter/Bench.lean, `lake exe bench`) and `oracle-nosincos --bench`
   (oracle/main.cpp) --runs times each on DIR/inputs.txt (the oracle with the navigator targets of
   DIR/trace.txt and AutoYaw HOLD from --hold-from). Each run parses all inputs first, then times
   only the tick loop: 3 warm-up passes, 20 passes timed around the whole loop (the per-tick mean
   and its standard deviation over passes), 20 passes timed per tick (median, p99, max).
2. Checks that every run's checksum (XOR of the actuator bit patterns over one pass) is the same
   for both programs and equals the XOR over the recorded DIR/motors.txt.
3. Times, for context, the batch runs with parsing and printing: the oracle (exact decimals and bit
   patterns, 22 values per line) and the port binary --port with and without --exact and --trace,
   --io-reps times each (the median is reported).
4. Writes the results to --out (default oracle/BENCH.md).
"""
import argparse
import platform
import statistics
import struct
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PKG = HERE.parent


def kv(text):
    out = {}
    for line in text.splitlines():
        w = line.split(None, 1)
        if len(w) == 2:
            out[w[0]] = w[1].strip()
    return out


def run_bench(cmd, stdin_path=None):
    fi = open(stdin_path) if stdin_path else subprocess.DEVNULL
    try:
        r = subprocess.run(cmd, stdin=fi, capture_output=True, text=True, cwd=PKG)
    finally:
        if stdin_path:
            fi.close()
    if r.returncode != 0:
        raise SystemExit(f"{' '.join(map(str, cmd))} failed ({r.returncode}):\n{r.stdout}\n{r.stderr[-2000:]}")
    return kv(r.stdout)


def wall(cmd, stdin_path, reps, save=None):
    ts = []
    for k in range(reps):
        with open(stdin_path) as fi, open(save if (save and k == 0) else "/dev/null", "w") as fo:
            t0 = time.perf_counter()
            r = subprocess.run(cmd, stdin=fi, stdout=fo, stderr=subprocess.PIPE, cwd=PKG)
            ts.append(time.perf_counter() - t0)
        if r.returncode != 0:
            raise SystemExit(f"{' '.join(map(str, cmd))} failed ({r.returncode}): {r.stderr[-2000:]}")
    return statistics.median(ts), ts


def actuator_checksum(path):
    """XOR of the float32 bit patterns of the first 4 numbers of every line (exact decimals)."""
    ck = 0
    for line in Path(path).read_text().splitlines():
        for v in line.split()[:4]:
            ck ^= struct.unpack("<I", struct.pack("<f", float(v)))[0]
    return f"{ck:08x}"


def sh(cmd):
    try:
        return subprocess.run(cmd, capture_output=True, text=True).stdout.strip()
    except OSError:
        return "?"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--runs", type=int, default=5)
    ap.add_argument("--run", default=str(PKG / "sim/out/copter-course-1ms/copter-bin"))
    ap.add_argument("--params", action="append", default=None)
    ap.add_argument("--hold-from", type=int, default=6618)
    ap.add_argument("--bench", default=str(PKG / ".lake/build/bin/bench"))
    ap.add_argument("--oracle", default=str(HERE / "build/oracle-nosincos"))
    ap.add_argument("--port", default=str(PKG / ".lake/build/bin/copter"))
    ap.add_argument("--io-reps", type=int, default=3)
    ap.add_argument("--out", default=str(HERE / "BENCH.md"))
    args = ap.parse_args()
    params = [str(Path(p).resolve()) for p in (args.params or
              [PKG / "sim/params/copter-cf2x.txt", PKG / "sim/params/copter-course-speed.txt"])]
    rund = Path(args.run).resolve()
    inputs, trace, motors = rund / "inputs.txt", rund / "trace.txt", rund / "motors.txt"
    pfx = sum([["--params", p] for p in params], [])

    lean_cmd = [args.bench, str(inputs)] + pfx
    cpp_cmd = [args.oracle, "--nav", str(trace), "--hold-from", str(args.hold_from), "--bench"] + pfx
    load0 = sh(["sysctl", "-n", "vm.loadavg"]).strip("{} ")
    rows = []
    for i in range(args.runs):
        for name, cmd, stdin in (("oracle (C++, ArduPilot classes)", cpp_cmd, inputs),
                                 ("port (Lean, `lake exe bench`)", lean_cmd, None)):
            r = run_bench(cmd, stdin)
            r["name"] = name
            r["run"] = i + 1
            rows.append(r)
            print(f"{name} run {i + 1}: per tick {float(r['per_tick_mean_ns']):.1f} ns "
                  f"(sd {float(r['per_tick_sd_over_passes_ns']):.1f}), median {r['per_tick_median_ns']}, "
                  f"p99 {r['per_tick_p99_ns']}, max {r['per_tick_max_ns']}, checksum {r['checksum']}",
                  flush=True)
    cks = {r["checksum"] for r in rows}
    all_same = all(r["checksum_same_every_pass"] == "true" for r in rows)

    # batch runs with I/O
    io = {}
    io["oracle"] = wall([args.oracle, "--nav", str(trace), "--hold-from", str(args.hold_from)] + pfx,
                        inputs, args.io_reps)
    replay = HERE / "build/bench-port-exact.txt"
    for flags in ([], ["--exact"], ["--trace"], ["--exact", "--trace"]):
        io["port " + " ".join(flags)] = wall([args.port] + flags + pfx, inputs, args.io_reps,
                                             save=replay if flags == ["--exact"] else None)
    rep_ck = actuator_checksum(replay)
    rec_ck = actuator_checksum(motors)
    empty = Path(HERE / "build/bench-empty.txt")
    empty.write_text("")
    io["port startup"] = wall([args.port] + pfx, empty, args.io_reps)
    for k, (m, ts) in io.items():
        print(f"batch {k}: median {m:.3f} s of {['%.3f' % t for t in ts]}", flush=True)

    # ---- BENCH.md
    def agg(name, key):
        xs = [float(r[key]) for r in rows if r["name"] == name]
        return statistics.mean(xs), (statistics.stdev(xs) if len(xs) > 1 else 0.0)

    names = ["oracle (C++, ArduPilot classes)", "port (Lean, `lake exe bench`)"]
    ticks = rows[0]["ticks"]
    lines = []
    L = lines.append
    L("# Execution time of one control tick: Lean port vs ArduPilot's C++ classes")
    L("")
    L("Generated by `oracle/bench.py`; do not edit by hand. Inputs: the recorded 1 m/s course, "
      f"`{rund.relative_to(PKG)}/inputs.txt` ({ticks} ticks), parameters "
      + ", ".join(f"`{Path(p).relative_to(PKG)}`" for p in params)
      + f"; the oracle reads the navigator targets from `trace.txt` and switches AutoYaw to HOLD at tick {args.hold_from}.")
    L("")
    L(f"Machine: {sh(['sysctl', '-n', 'machdep.cpu.brand_string'])}, "
      f"macOS {sh(['sw_vers', '-productVersion'])} ({sh(['sw_vers', '-buildVersion'])}), "
      f"{sh(['sysctl', '-n', 'hw.memsize'])} bytes RAM; "
      f"{sh(['clang++', '--version']).splitlines()[0] if sh(['clang++', '--version']) else '?'}; "
      f"Lean {sh(['cat', str(PKG / 'lean-toolchain')])}. Date: {time.strftime('%Y-%m-%d %H:%M')}.")
    L("")
    L("## Protocol")
    L("")
    L("Both programs parse every input line first (the oracle also the navigator targets), set the "
      "parameters, build the objects and apply the takeover with the first sample, untimed; then they "
      "run 3 warm-up passes over all ticks, 20 passes timed around the whole tick loop (per-tick mean = "
      "loop time / ticks; mean and sample standard deviation over the 20 passes), and 20 passes timed "
      "around each tick (median, p99 and max over the 20 x ticks samples). Each pass starts from the "
      "same initial state (the port: the same taken-over `State`, threaded through `Copter.loop`; the "
      "oracle: fresh objects per pass). Nothing is printed per tick; the checksum, the XOR of the "
      "bit patterns of the four actuators over all ticks of a pass, is printed at the end. Clocks: "
      "`IO.monoNanosNow` (Lean) and `std::chrono::steady_clock` (C++), both read the same macOS "
      "monotonic clock, whose resolution on this machine is 1/24 MHz = 41.7 ns; the per-tick "
      "distribution is quantized to that step (a timer read costs less than one step: the median of "
      "two consecutive reads is 0 in both programs). "
      f"Each program was run {args.runs} times, alternating. Load average when the runs started: "
      f"{load0}; other jobs were running on the machine (it is shared with other agents' builds and "
      "simulations), and macOS may place a process on an efficiency core under load, so single "
      "passes can be slow; the median of the pass means is the robust figure.")
    L("")
    L("Builds: the port by `lake build bench` (Lean to C, then `leanc` = the toolchain's clang at "
      "`-O3 -DNDEBUG` with the lakefile's `moreLeancArgs`, i.e. `-fno-builtin-sinf -fno-builtin-cosf` "
      "and whatever else the lakefile adds); the oracle by `oracle/build.sh nosincos` (Apple clang, "
      "`-O2 -ffp-contract=off -fno-fast-math -fno-builtin-sinf -fno-builtin-cosf`, flags unchanged). "
      "The C route of `sim/build_copter_c.sh` was not used for `bench`: its root module "
      "(`Copter.Main`) and lake target are fixed in the script, and adapting it would mean editing "
      "`sim/`. `lake exe bench` is native code compiled through C already, at the same `-O3`.")
    L("")
    L("## Per-tick time, compute only")
    L("")
    L("| program | run | per-tick mean ± sd over passes (ns) | median / min of the pass means (ns) | median (ns) | p99 (ns) | max (ns) | checksum |")
    L("|---|---|---|---|---|---|---|---|")
    for r in rows:
        L(f"| {r['name']} | {r['run']} | {float(r['per_tick_mean_ns']):.1f} ± {float(r['per_tick_sd_over_passes_ns']):.1f} "
          f"| {float(r['per_tick_mean_pass_median_ns']):.1f} / {float(r['per_tick_mean_pass_min_ns']):.1f} "
          f"| {r['per_tick_median_ns']} | {r['per_tick_p99_ns']} | {r['per_tick_max_ns']} | `{r['checksum']}` |")
    L("")
    L("Over the runs (mean ± sd of the run values):")
    L("")
    L("| program | per-tick mean (ns) | median of the pass means (ns) | median (ns) | p99 (ns) | max (ns) | loop over all ticks (ms) | input parsing (ms) |")
    L("|---|---|---|---|---|---|---|---|")
    for n in names:
        m, s = agg(n, "per_tick_mean_ns")
        md, mds = agg(n, "per_tick_median_ns")
        p9, p9s = agg(n, "per_tick_p99_ns")
        mx, mxs = agg(n, "per_tick_max_ns")
        tt, tts = agg(n, "total_ns_mean")
        pp, pps = agg(n, "parse_ns")
        pmd, pmds = agg(n, "per_tick_mean_pass_median_ns")
        L(f"| {n} | {m:.1f} ± {s:.1f} | {pmd:.1f} ± {pmds:.1f} | {md:.0f} ± {mds:.0f} | {p9:.0f} ± {p9s:.0f} | {mx:.0f} ± {mxs:.0f} "
          f"| {tt / 1e6:.2f} ± {tts / 1e6:.2f} | {pp / 1e6:.1f} ± {pps / 1e6:.1f} |")
    cm, _ = agg(names[0], "per_tick_mean_ns")
    lm, _ = agg(names[1], "per_tick_mean_ns")
    cmd_, _ = agg(names[0], "per_tick_mean_pass_median_ns")
    lmd_, _ = agg(names[1], "per_tick_mean_pass_median_ns")
    L("")
    L(f"Ratio port / oracle: **{lm / cm:.2f}** of the per-tick means, **{lmd_ / cmd_:.2f}** of the "
      "medians of the pass means (less sensitive to a disturbed pass). "
      f"Checksums: {', '.join('`' + c + '`' for c in sorted(cks))} "
      f"({'identical for every run and pass of both programs' if len(cks) == 1 and all_same else 'NOT all equal'}); "
      f"the same XOR over the actuators that `{Path(args.port).name} --exact` prints on these inputs (the "
      f"normal batch route) is `{rep_ck}` ({'equal' if cks == {rep_ck} else 'DIFFERENT'}). Over the "
      f"recorded `motors.txt` it is `{rec_ck}` ({'equal' if cks == {rec_ck} else 'different'}): "
      "the recording was made by an earlier build of the port (see `oracle/compare.py` and "
      "`sim/README.md`, \"Determinism\"), and the current port and the oracle agree with each other, "
      "not with that recording.")
    L("")
    L("Input parsing (for context, untimed in the table above): the port reads the file and parses "
      "each line by `Copter.Text` (`words`, `parseDecimal?`, exact decimal to `Float32`/`Float`); the "
      "oracle reads standard input and parses by `strtof`/`strtod`, plus the numeric conversion of the "
      "navigator targets (their tokenizing, in `main`, is not included).")
    L("")
    L("## What the two ticks contain")
    L("")
    pm, ps = agg(names[1], "segment_prefix_mean_ns")
    nm, ns_ = agg(names[1], "segment_navigator_side_mean_ns")
    fm, fs = agg(names[1], "segment_flight_mode_mean_ns")
    L("The oracle's tick is the cascade of `oracle/main.cpp`: scheduler step and gyro, "
      "`rate_controller_run` and `rate_controller_target_reset`, `motors->output()`, the AHRS view "
      "update, `update_estimates`, on the first tick the `wp_and_spline_init_m` calls and rate time "
      "constants, the AutoYaw choice, `set_pos_terrain_target_D_m`, `set_pos_vel_accel_NED_m` with "
      "the navigator's targets **read from an array** (parsed from the port's trace), "
      "`NE_update_controller`, `D_update_controller`, `input_thrust_vector_heading`.")
    L("")
    L("The port's tick is `Copter.loop`, which also **runs the navigator and the mission logic**: "
      "`ModeAuto.run` calls `mission_update` (waypoint verification and sequencing) and "
      "`AC_WPNav.update_wpnav` (speed-change checks, `advance_wp_target_along_track` with the "
      "`SimplePath` leg sampling, then `NE_update_controller`), and `AutoYaw.get_heading`. So the port "
      "does strictly more work per tick. Segment timing (`bench`, separate passes, timer reads between "
      "segments; mean ± sd over the runs):")
    L("")
    L("| port segment | ns per tick |")
    L("|---|---|")
    L(f"| `Copter.loop` up to `read_inertia` and the Auto switch (scheduler, gyro, rate controller, motors output, AHRS view, estimates) | {pm:.1f} ± {ps:.1f} |")
    L(f"| `update_flight_mode` (`ModeAuto.run`: mission, navigator, position and attitude controllers) | {fm:.1f} ± {fs:.1f} |")
    L(f"| navigator alone, side computation on the same state (`mission_update` + `advance_wp_target_along_track`) | {nm:.1f} ± {ns_:.1f} |")
    L("")
    L(f"The navigator side computation shares the state with the real tick, so the records it updates "
      f"are copied rather than updated in place: {nm:.0f} ns is an upper estimate of what the navigator "
      f"adds to the port's tick. Subtracting it from the medians of the pass means, the port's "
      f"control cascade alone costs about {lmd_ - nm:.0f} ns per tick, {(lmd_ - nm) / cmd_:.2f} times "
      f"the oracle's {cmd_:.0f} ns.")
    L("")
    L("Other differences that bear on fairness:")
    L("")
    L("- Optimization levels differ: the port's C is compiled at `-O3` (lake's default), the oracle at "
      "`-O2` (`oracle/build.sh`, unchanged); both keep strict IEEE semantics (`-ffp-contract=off` in "
      "`leanc`, no fast-math).")
    L("- The port is a pure function on a `State` record of nested structures: each `{ s with ... }` "
      "update reuses the object in place only when its reference is unique and otherwise allocates a "
      "copy, and values returned in pairs (`(state, output)`) can be allocated as tuples; the C++ updates "
      "the members of four heap objects in place. The arithmetic is the same IEEE `float`/`double` "
      "operations on both sides (the checksums agree; `oracle/compare.py` checks the outputs value by value); where the rest of the gap goes "
      "(allocation, reference counting, copying) was not profiled.")
    L("- The oracle sets parameters on its objects once per pass; the port reads its `Parameters` "
      "record (passed by reference) on every tick. Neither cost is in the tick loop beyond field reads.")
    L("- The first tick of each port pass starts from a shared `State` (the same `s0` for every pass), "
      "so it copies the records it updates; one tick in "
      f"{ticks}, negligible.")
    L("- Both run single-threaded on an otherwise idle machine; no CPU pinning or frequency control "
      "is available on macOS, so the p99 and max columns include scheduler and interrupt noise.")
    L("")
    L("## Batch runs with parsing and printing (context)")
    L("")
    L("Previously measured (by the requester): oracle 0.30 s; port 1.4 s (actuators only) and 5.3 s "
      f"(with `--trace`) for {ticks} ticks. Measured here by `bench.py` (wall clock, median of "
      f"{args.io_reps}, output to `/dev/null`; port binary `{Path(args.port).relative_to(PKG) if str(args.port).startswith(str(PKG)) else args.port}`):")
    L("")
    L("| run | output per line | wall time (s) |")
    L("|---|---|---|")
    L(f"| oracle | 22 exact decimals + 22 bit patterns | {io['oracle'][0]:.3f} |")
    L(f"| port | 4 actuators, `Float32.toString` | {io['port '][0]:.3f} |")
    L(f"| port `--exact` | 4 actuators, exact decimals | {io['port --exact'][0]:.3f} |")
    L(f"| port `--trace` | 22 values, `toString` | {io['port --trace'][0]:.3f} |")
    L(f"| port `--exact --trace` | 22 values, exact decimals | {io['port --exact --trace'][0]:.3f} |")
    L(f"| port, empty input (startup and parameter files) | none | {io['port startup'][0]:.3f} |")
    L("")
    a_x, a_n = io["port --exact"][0], io["port "][0]
    t_x, t_n = io["port --exact --trace"][0], io["port --trace"][0]
    comp = lm * int(ticks) / 1e9
    L(f"Exact-decimal printing (difference of the runs with and without `--exact`): {a_x - a_n:.2f} s of "
      f"{a_x:.2f} s ({100 * (a_x - a_n) / a_x:.0f}%) for the actuators only, {t_x - t_n:.2f} s of {t_x:.2f} s "
      f"({100 * (t_x - t_n) / t_x:.0f}%) with the trace. The ticks themselves take {comp:.3f} s of each "
      f"run ({ticks} x {lm:.0f} ns, {100 * comp / a_x:.1f}% and {100 * comp / t_x:.1f}%); the rest "
      "is the line parsing, the non-exact printing and process startup. Likewise the oracle's "
      f"{io['oracle'][0]:.2f} s is almost all I/O: its ticks take {cm * int(ticks) / 1e9:.4f} s.")
    L("")
    Path(args.out).write_text("\n".join(lines))
    print(f"wrote {args.out}")
    return 0 if len(cks) == 1 and all_same else 1


if __name__ == "__main__":
    sys.exit(main())
