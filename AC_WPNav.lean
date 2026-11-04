import AC_WPNav.SimplePath
import AC_WPNav.AC_WPNav

/-!
# `AC_WPNav`

Lean port of ArduPilot `libraries/AC_WPNav` (see PORT.md), straight waypoint legs only.

- `AC_WPNav.SimplePath`: the stand-in for `SCurve`. **The S-curve path generator is NOT ported**:
  straight legs with blended corners and a trapezoidal speed profile stand in for it.
- `AC_WPNav.AC_WPNav`: `AC_WPNav` (parameters, leg bookkeeping, `advance_wp_target_along_track`,
  `update_wpnav`), driving `AC_PosControl`.
-/
