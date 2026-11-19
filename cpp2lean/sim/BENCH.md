# Execution time of the two vehicles

Per-tick execution time of the controller alone, for `copter_lean` (the Lean translations of
ArduPilot's classes with the Lean harness, compiled through Lean's C backend) and `copter_ref`
(ArduPilot's classes compiled unmodified with the same harness in C++), measured on the recorded
flights of `sim/out/` with the tuned gains.

## Method

Both vehicles have a `--bench` mode (`lean/VehicleMain.lean`, `ardupilot/vehicle/copter_ref.cpp`).
It reads every input line of standard input and parses the samples first, then runs the ticks over
the parsed samples with nothing else inside the timed region: no parsing, no formatting, no I/O. The
first sample goes through the same takeover as in protocol mode. The elapsed time is taken with a
monotonic clock (`std::chrono::steady_clock`, `IO.monoNanosNow`) around the whole pass, and the
output is one line `ns ticks checksum`, where the checksum is the sum of the 32-bit patterns of
every actuator value, so the work cannot be discarded and the two vehicles can be seen to have
computed the same actuators. Each measurement is one process launch; a mission is measured by 30
launches of each vehicle, one process at a time, and the first 3 launches are discarded as warm-up.
The per-tick time of a launch is its elapsed time divided by its tick count.

Reproduce (from the project root, after `ardupilot/vehicle/build.sh`):

```
P=sim/params
build/vehicle/copter_ref           --params $P/copter-cf2x.txt --params $P/copter-course-speed.txt --params $P/copter-cf2x-tuned.txt --bench < sim/out/lean-course-1ms/inputs.txt
lean/.lake/build/bin/copter_lean   --params $P/copter-cf2x.txt --params $P/copter-course-speed.txt --params $P/copter-cf2x-tuned.txt --bench < sim/out/lean-course-1ms/inputs.txt
```

(hover: `copter-hover.txt` in place of `copter-course-speed.txt`, input `sim/out/lean-hover/inputs.txt`).

## Builds

- C++: `clang++ -std=gnu++11 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math -fno-builtin-sinf
  -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos -fno-builtin -cl-single-precision-constant ...`
  (`ardupilot/vehicle/build.sh`), the flags of the translations plus the code-generation flags of the
  compilation assumptions.
- Lean: Lake's release build, `leanc -O3 -DNDEBUG` plus `moreLeancArgs = -ffp-contract=off
  -fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos -fno-builtin`
  (`lean/lakefile.toml`), Lean `v4.33.0-rc1`.

The floating-point flags are the same on both sides; the optimization levels are each toolchain's
default release level and were not changed for the measurement.

## Machine

Apple M4 (10 cores), 16 GB, macOS 15.6.1, Apple clang 17.0.0 (clang-1700.6.4.2), 2026-11-05.

## Results

Microseconds per tick over 27 launches (30 minus 3 warm-up); the two vehicles' checksums agree on
each mission (`00000f5a8e37bff7` hover, `00001dee4e46deba` course).

| mission (ticks) | vehicle | mean | sd | median | min | max |
|---|---|---|---|---|---|---|
| hover (4000) | `copter_ref` | 0.81 | 0.01 | 0.81 | 0.77 | 0.82 |
| hover (4000) | `copter_lean` | 9.10 | 0.66 | 8.93 | 8.62 | 12.11 |
| course-1ms (7797) | `copter_ref` | 1.04 | 0.32 | 0.98 | 0.92 | 2.62 |
| course-1ms (7797) | `copter_lean` | 10.31 | 0.18 | 10.29 | 10.02 | 10.86 |

Ratio of means, Lean to C++: 11.3 on the hover, 9.9 on the course. Both are far inside the 2500 µs
control period of the 400 Hz loop. The one slow `copter_ref` launch on the course (2.62 µs per tick)
is a single outlier; the median is unaffected.

Why the Lean vehicle is slower: the translated functions pass whole `State` records by value and
return them, Lean's runtime reference-counts and copies records that are shared, the boundary
mechanism replays ordered `Outputs` logs through arrays, and `Id.run do` blocks allocate for their
mutable locals; none of this exists in the C++ which mutates objects in place. The translated code
was not changed for this measurement.
