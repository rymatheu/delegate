import AP_Math

/-!
# `AC_P_2D`

Mirrors `libraries/AC_PID/AC_P_2D.h:11-60` and `libraries/AC_PID/AC_P_2D.cpp:7-77` (ArduPilot
commit 802db19de1): the 2-D position P controller with a `sqrt_controller` output, used for
the horizontal position loop of `AC_PosControl` (`_p_pos_ne_m`, `PSC_NE_POS_P`). The target is
a `Vector2p` (`double` components on SITL) passed by reference and rewritten when the error
is clamped; here `update_all` returns the new target.

Left out: `save_gains` and the `AP_Param` plumbing.
-/

namespace AC_P_2D

open AP_Math

/-- `var_info`, `AC_P_2D.cpp:7-13`. C++ member `_kp` (`AC_P_2D.h:52`). -/
structure Params where
  P : ftype
deriving Repr

/-- Internal variables, `AC_P_2D.h:54-57`. -/
structure State where
  _error : Vector2f
  _error_max : ftype
  _D1_max : ftype
deriving Repr

/-- Constructor `AC_P_2D(initial_p)`, `AC_P_2D.cpp:15-21`. The internal variables start at
zero, as ArduPilot zero-fills its objects. -/
def init (initial_p : ftype) : Params × State :=
  ({ P := initial_p }, { _error := ({} : Vector2f), _error_max := 0, _D1_max := 0 })

def kP (p : Params) : ftype := p.P
def set_kP (p : Params) (v : ftype) : Params := { p with P := v }
def get_error (s : State) : Vector2f := s._error
def get_error_max (s : State) : ftype := s._error_max

/-- `update_all(Vector2p &target, const Vector2p &measurement)`, `AC_P_2D.cpp:23-38`. Returns
the new state, the new `target`, and the output. The error is formed in `postype_t` and
narrowed componentwise at :29; it is widened back when the target is rewritten (:33). -/
def update_all (p : Params) (s : State) (target measurement : Vector2p) :
    State × Vector2p × Vector2f := Id.run do
  -- Compute vector error between target and measurement (NED frame)
  let mut s := { s with _error := (target - measurement).tofloat }
  let mut target := target
  -- Limit error vector length to prevent exceeding output constraints (`&&` short-circuits:
  -- `limit_length` runs only if `_error_max` is positive)
  if is_positive s._error_max then
    let (e', limited) := s._error.limit_length s._error_max
    s := { s with _error := e' }
    if limited then
      target := measurement + s._error.topostype
  -- Use sqrt_controller to limit output and/or its derivative
  return (s, target, sqrt_controller_xy s._error p.P s._D1_max 0.0)

/-- `set_limits(output_max, D_Out_max = 0, D2_Out_max = 0)`, `AC_P_2D.cpp:40-63`. -/
def set_limits (p : Params) (s : State) (output_max : ftype) (D_Out_max : ftype := 0.0)
    (D2_Out_max : ftype := 0.0) : State := Id.run do
  -- Reset all limits to zero before applying new ones
  let mut s := { s with _D1_max := 0.0, _error_max := 0.0 }
  -- Set first derivative (acceleration) limit if specified
  if is_positive D_Out_max then
    s := { s with _D1_max := D_Out_max }
  -- If second derivative (jerk) limit is specified, constrain velocity limit accordingly
  if is_positive D2_Out_max && is_positive p.P then
    s := { s with _D1_max := MIN s._D1_max (D2_Out_max / p.P) }
  -- Compute min/max allowable error from output limits
  if is_positive output_max && is_positive p.P then
    s := { s with _error_max := inv_sqrt_controller output_max p.P s._D1_max }
  return s

/-- `set_error_max(error_max)`, `AC_P_2D.cpp:65-77`. -/
def set_error_max (s : State) (error_max : ftype) : State :=
  -- Update _error_max if it's non-zero and the new value is more conservative
  if is_positive error_max then
    if !is_zero s._error_max then
      { s with _error_max := MIN s._error_max error_max }
    else
      { s with _error_max := error_max }
  else
    s

end AC_P_2D
