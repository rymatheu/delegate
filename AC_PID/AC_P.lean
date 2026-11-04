import AC_PID.Compat

/-!
# `AC_P`

Mirrors `libraries/AC_PID/AC_P.h:13-61` and `libraries/AC_PID/AC_P.cpp:7-18` (ArduPilot commit
802db19de1): the proportional controller used for the attitude angle loops
(`_p_angle_roll/pitch/yaw`, parameters `ATC_ANG_RLL_P`, ...). It has no internal state.

Left out: `load_gains`, `save_gains` and the `AP_Param` plumbing.
-/

namespace AC_P

open AC_PID.Compat

/-- `var_info`, `AC_P.cpp:7-13`. C++ member `_kp` (`AC_P.h:58`). -/
structure Params where
  P : ftype
deriving Repr

/-- Constructor `AC_P(initial_p = 0.0f)`, `AC_P.h:24-28`. -/
def init (initial_p : ftype := 0.0) : Params := { P := initial_p }

/-- `get_p(error)`, `AC_P.cpp:15-18`: `error * _kp`. -/
def get_p (p : Params) (error : ftype) : ftype := error * p.P

/-- `kP()`, `AC_P.h:51-52`. -/
def kP (p : Params) : ftype := p.P
/-- `set_kP(v)`, `AC_P.h:53`. -/
def set_kP (p : Params) (v : ftype) : Params := { p with P := v }

end AC_P
