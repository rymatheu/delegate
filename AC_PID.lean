import AC_PID.Compat
import AC_PID.AP_PIDInfo
import AC_PID.AC_PID
import AC_PID.AC_PID_2D
import AC_PID.AC_PID_Basic
import AC_PID.AC_P
import AC_PID.AC_P_1D
import AC_PID.AC_P_2D

/-!
# `AC_PID`

Lean port of ArduPilot `libraries/AC_PID` (commit 802db19de1; see PORT.md): `AC_PID`,
`AC_PID_2D`, `AC_PID_Basic`, `AC_P`, `AC_P_1D`, `AC_P_2D` and `AP_PIDInfo`. Not ported:
`AC_PI`, `AC_PI_2D`, `AC_HELI_PID` (not on the Copter Auto-mode path). The `AP_Math`
helpers they need live in `AC_PID/Compat.lean` until the `AP_Math` port replaces them.
-/
