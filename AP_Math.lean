import AP_Math.ftype
import AP_Math.definitions
import AP_Math.AP_Math
import AP_Math.vector2
import AP_Math.vector3
import AP_Math.matrix3
import AP_Math.quaternion
import AP_Math.control
-- PORT FIX: added with the AC_WPNav port
import AP_Math.location

/-!
# `AP_Math`

Lean port of the subset of ArduPilot `libraries/AP_Math` (commit 802db19de1, SITL configuration)
that the Auto-mode flight cascade uses. See PORT.md and the header of each submodule for the C++
line ranges mirrored and what is left out.

- `AP_Math.ftype`: `ftype`, `postype`, `tofloat`, `topostype`, `FLT_EPSILON`, `is_zero`.
- `AP_Math.definitions`: `M_PI` and the other `float` constants.
- `AP_Math.AP_Math`: scalar helpers (`is_positive`, `constrain_float`, `safe_sqrt`, `wrap_PI`, ...).
- `AP_Math.vector2`, `AP_Math.vector3`: `Vector2f`, `Vector2p`, `Vector3f`, `Vector3p`.
- `AP_Math.matrix3`: the `Matrix3f` product used by `Quaternion.earth_to_body`.
- `AP_Math.quaternion`: `Quaternion` (`QuaternionT<float>`).
- `AP_Math.control`: `control.cpp` (square-root controller, shaping, kinematic limits).
- `AP_Math.location`: `get_horizontal_distance`, `get_bearing_rad`, `get_bearing_cd` (PORT FIX,
  added with `AC_WPNav`).

`AP_Math.Check` (not imported) prints each function on hand-picked inputs:
`lake env lean --run AP_Math/Check.lean`.
-/
