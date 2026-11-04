# ArduCopter port: conventions

Target: ArduPilot commit 802db19de1 (master after 4.7), SITL build configuration
(`HAL_WITH_POSTYPE_DOUBLE = 1`, `HAL_WITH_EKF_DOUBLE = 1`), Auto mode waypoint flight,
400 Hz main loop, `FSTRATE_ENABLE = 0`, `MOT_HOVER_LEARN = 0` for runs and proofs.
Plan: /Users/ryan/Research/delegate/staging/text/rewrite-plan.md.
Review with citations: /Users/ryan/Research/delegate/staging/text/ardupilot-review.md.
ArduPilot source: /Users/ryan/Research/delegate/ardupilot.

Conventions:
- One Lean directory per ArduPilot library, one namespace per C++ class, the same method
  names (snake_case as in C++), the same argument order, the same parameter names as the
  ArduPilot parameters (for example `ATC_ANG_RLL_P`).
- Numeric types: `ftype := Float32` for every control quantity; `postype := Float` for
  positions; literals are `Float32` literals. Conversions `tofloat`/`topostype` wrap the
  core conversions, which are opaque.
- Every file header cites the C++ file and line range it mirrors, and lists what is left out.
- No `sorry`, no `axiom`. Facts about opaque functions are hypotheses (structures of `Prop`).
- Old `Flight/` stays until the port replaces it; do not edit it.
- Nothing is pushed; commits on branch `port` only.
