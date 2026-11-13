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
- Lean: Lake's release build, `leanc -O3 -DNDEBUG`. Before the FloatLib port (results of 2026-11-05):
  Lean `v4.33.0-rc1`, `Float32`/`Float` on the FPU, `moreLeancArgs = -ffp-contract=off
  -fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos -fno-builtin`, the platform's
  libm on both sides. Since the port (results of 2026-11-11): Lean `v4.35.0`, FloatLib `acba2057`
  (every float is a `Binary32`/`Binary64` computed in software), musl's math functions on both sides
  (the C++ links musl's sources, the Lean runs their translation: README.md, "The C library").

The optimization levels are each toolchain's default release level and were not changed for the
measurement.

## Machine

Apple M4 (10 cores), 16 GB, macOS 15.6.1, Apple clang 17.0.0 (clang-1700.6.4.2), 2026-11-05.

## Results since the FloatLib port (2026-11-11)

Microseconds per tick, `copter_ref` over 27 launches (30 minus 3 warm-up), `copter_lean` over 5 (6
minus 1; a course launch takes 22 s), on the flights of `sim/out/` flown on 2026-11-11 with musl's
functions; the two vehicles' checksums agree on each mission (`00000f5a8e37c004` hover,
`00001dee4e46dcdc` course).

| mission (ticks) | vehicle | mean | sd | median | min | max |
|---|---|---|---|---|---|---|
| hover (4000) | `copter_ref` | 0.82 | 0.00 | 0.82 | 0.82 | 0.83 |
| hover (4000) | `copter_lean` | 2633.30 | 12.38 | 2629.45 | 2619.95 | 2653.26 |
| course-1ms (7797) | `copter_ref` | 1.04 | 0.01 | 1.04 | 1.03 | 1.05 |
| course-1ms (7797) | `copter_lean` | 2810.29 | 20.24 | 2814.37 | 2776.86 | 2831.62 |

`copter_lean` now takes longer than the 2500 µs control period of the 400 Hz loop (2.6 ms on the
hover, 2.8 ms on the course; ratio to C++ about 3200 and 2700). Where the time goes (a sample profile;
README.md, "The two vehicles", "Speed"): FloatLib's comparisons, which align two dyadic numbers with
big integers (about 2 µs each), half of it; the rounding of rationals for literals and conversions
of integer constants (about 1 µs each), a third; the arithmetic itself (FloatLib's word kernels,
7 to 20 ns per operation) 2%, musl's functions 3%. Emitting literals and constant conversions as bit
patterns brings the recorded flight from 2.88 to 1.91 ms per tick (measured, same checksum);
comparisons and conversions on the bit patterns, proved equal to FloatLib's specifications, would
remove most of the rest.

## Results before the FloatLib port (2026-11-05)

Microseconds per tick over 27 launches (30 minus 3 warm-up); the two vehicles' checksums agree on
each mission (`00000f5a8e37bff7` hover, `00001dee4e46deba` course).

| mission (ticks) | vehicle | mean | sd | median | min | max |
|---|---|---|---|---|---|---|
| hover (4000) | `copter_ref` | 0.81 | 0.01 | 0.81 | 0.77 | 0.82 |
| hover (4000) | `copter_lean` | 9.10 | 0.66 | 8.93 | 8.62 | 12.11 |
| course-1ms (7797) | `copter_ref` | 1.04 | 0.32 | 0.98 | 0.92 | 2.62 |
| course-1ms (7797) | `copter_lean` | 10.31 | 0.18 | 10.29 | 10.02 | 10.86 |

Ratio of means, Lean to C++: 11.3 on the hover, 9.9 on the course. Both were far inside the 2500 µs
control period of the 400 Hz loop. The one slow `copter_ref` launch on the course (2.62 µs per tick)
is a single outlier; the median is unaffected.

Why the Lean vehicle is slower: the translated functions pass whole `State` records by value and
return them, Lean's runtime reference-counts and copies records that are shared, the boundary
mechanism replays ordered `Outputs` logs through arrays, and `Id.run do` blocks allocate for their
mutable locals; none of this exists in the C++ which mutates objects in place. The translated code
was not changed for this measurement.
