# ArduCopter port: conventions

Target: ArduPilot (https://github.com/ArduPilot/ardupilot) at commit 802db19de1 (master after 4.7),
SITL build configuration (`HAL_WITH_POSTYPE_DOUBLE = 1`, `HAL_WITH_EKF_DOUBLE = 1`), Auto mode
waypoint flight, 400 Hz main loop, `FSTRATE_ENABLE = 0`, `MOT_HOVER_LEARN = 0` for runs and proofs.
The ArduPilot source is not part of this repository; the C++ oracle (`oracle/`) reads a checkout of
it from the `AP` variable of `oracle/build.sh`. The port's plan and its review notes (the review
with citations into the ArduPilot source) are not part of the repository either.

Conventions:
- One Lean directory per ArduPilot library, one namespace per C++ class, the same method
  names (snake_case as in C++), the same argument order, the same parameter names as the
  ArduPilot parameters (for example `ATC_ANG_RLL_P`).
- Numeric types: `ftype := Float32` for every control quantity; `postype := Float` for
  positions; literals are `Float32` literals. `ftype` here is ArduPilot's `float` and `postype` is
  ArduPilot's `postype_t` (`double` in SITL); the names are the port's. ArduPilot's own `ftype`
  typedef is a different type, `double` under `HAL_WITH_EKF_DOUBLE` (`AP_Math/ftype.h`), used by
  the EKF and by templates on `double` arguments (see `AP_Math/ftype.lean`).
  Conversions `tofloat`/`topostype` wrap the core conversions, which are opaque.
- Every file header cites the C++ file and line range it mirrors, and lists what is left out.
- No `sorry`, no `axiom`. Facts about opaque functions are hypotheses (structures of `Prop`).
- Old `Flight/` stays until the port replaces it; do not edit it.
