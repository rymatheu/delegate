import AP_Math

/-!
# `AC_P_1D`

Mirrors `libraries/AC_PID/AC_P_1D.h:11-64` and `libraries/AC_PID/AC_P_1D.cpp:7-94` (ArduPilot
commit 802db19de1): the 1-D position P controller with a `sqrt_controller` output, used for
the vertical position loop of `AC_PosControl` (`_p_pos_d_m`, `PSC_D_POS_P`). The target is a
`postype_t` (`double` on SITL) passed by reference and rewritten when the error is clamped;
here `update_all` returns the new target.

Left out: `save_gains` and the `AP_Param` plumbing.
-/

namespace AC_P_1D

open AP_Math

/-- `var_info`, `AC_P_1D.cpp:7-13`. C++ member `_kp` (`AC_P_1D.h:55`). -/
structure Params where
  P : ftype
deriving Repr

/-- Internal variables, `AC_P_1D.h:57-61`. -/
structure State where
  _error : ftype
  _error_min : ftype
  _error_max : ftype
  _D1_max : ftype
deriving Repr

/-- Constructor `AC_P_1D(initial_p)`, `AC_P_1D.cpp:15-21`. The internal variables start at
zero, as ArduPilot zero-fills its objects. -/
def init (initial_p : ftype) : Params × State :=
  ({ P := initial_p }, { _error := 0, _error_min := 0, _error_max := 0, _D1_max := 0 })

def kP (p : Params) : ftype := p.P
def set_kP (p : Params) (v : ftype) : Params := { p with P := v }
def get_error (s : State) : ftype := s._error
def get_error_min (s : State) : ftype := s._error_min
def get_error_max (s : State) : ftype := s._error_max

/-- `update_all(postype_t &target, postype_t measurement)`, `AC_P_1D.cpp:23-42`. Returns the
new state, the new `target`, and the output. The error is narrowed to `float` at :29, and
widened back when the target is rewritten (:34, :37). -/
def update_all (p : Params) (s : State) (target measurement : postype) :
    State × postype × ftype := Id.run do
  -- Compute position error between target and measurement
  let mut s := { s with _error := tofloat (target - measurement) }
  let mut target := target
  -- Clamp error to configured min/max bounds
  if is_negative s._error_min && s._error < s._error_min then
    s := { s with _error := s._error_min }
    target := measurement + topostype s._error
  else if is_positive s._error_max && s._error > s._error_max then
    s := { s with _error := s._error_max }
    target := measurement + topostype s._error
  -- Use sqrt_controller to limit output and/or its derivative
  return (s, target, sqrt_controller s._error p.P s._D1_max 0.0)

/-- `set_limits(output_min, output_max, D_Out_max = 0, D2_Out_max = 0)`,
`AC_P_1D.cpp:44-71`. -/
def set_limits (p : Params) (s : State) (output_min output_max : ftype)
    (D_Out_max : ftype := 0.0) (D2_Out_max : ftype := 0.0) : State := Id.run do
  -- Reset all limits to zero before applying new ones
  let mut s := { s with _D1_max := 0.0, _error_min := 0.0, _error_max := 0.0 }
  -- Set first derivative (acceleration) limit if specified
  if is_positive D_Out_max then
    s := { s with _D1_max := D_Out_max }
  -- If second derivative (jerk) limit is specified, constrain velocity limit accordingly
  if is_positive D2_Out_max && is_positive p.P then
    s := { s with _D1_max := MIN s._D1_max (D2_Out_max / p.P) }
  -- Compute min/max allowable error from output limits
  if is_negative output_min && is_positive p.P then
    s := { s with _error_min := inv_sqrt_controller output_min p.P s._D1_max }
  if is_positive output_max && is_positive p.P then
    s := { s with _error_max := inv_sqrt_controller output_max p.P s._D1_max }
  return s

/-- `set_error_limits(error_min, error_max)`, `AC_P_1D.cpp:73-94`. -/
def set_error_limits (s : State) (error_min error_max : ftype) : State := Id.run do
  let mut s := s
  -- Update _error_min if it's non-zero and the new value is more conservative
  if is_negative error_min then
    if !is_zero s._error_min then
      s := { s with _error_min := MAX s._error_min error_min }
    else
      s := { s with _error_min := error_min }
  -- Update _error_max if it's non-zero and the new value is more conservative
  if is_positive error_max then
    if !is_zero s._error_max then
      s := { s with _error_max := MIN s._error_max error_max }
    else
      s := { s with _error_max := error_max }
  return s

end AC_P_1D
