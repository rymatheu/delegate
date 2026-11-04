import AP_Math
import AC_PID.AP_PIDInfo

/-!
# `AC_PID_Basic`

Mirrors `libraries/AC_PID/AC_PID_Basic.h:12-105` and `libraries/AC_PID/AC_PID_Basic.cpp:11-183`
(ArduPilot commit 802db19de1): the PID used for the vertical velocity loop of
`AC_PosControl` (`_pid_vel_d_m`). Parameters `Params` (`var_info`, `AC_PID_Basic.cpp:11-50`),
internal variables `State` (`AC_PID_Basic.h:88-95`).

Not one to one: C++ overloads cannot share a name in Lean.
- `update_all(target, measurement, dt, limit_neg, limit_pos)` (`AC_PID_Basic.cpp:74-120`,
  the implementation, called by `AC_PosControl.cpp:1115`) is `update_all`;
  `update_all(target, measurement, dt, limit)` (`:69-72`) is `update_all_limit`.
- `set_integrator(i)` is `set_integrator`; `set_integrator(error, i)` is
  `set_integrator_error`; `set_integrator(target, measurement, i)` is
  `set_integrator_target`.

Left out: the `INTERNAL_ERROR` report on non-finite input (`:82`, no effect on the result);
`save_gains` and the `AP_Param` plumbing; logging.
-/

namespace AC_PID_Basic

open AP_Math

/-- `var_info`, `AC_PID_Basic.cpp:11-50`, fields named as the parameter suffixes
(`PSC_D_VEL_P`, ...). C++ members `_kp`, `_ki`, `_kd`, `_kff`, `_kimax`, `_filt_E_hz`,
`_filt_D_hz` (`AC_PID_Basic.h:80-86`). -/
structure Params where
  P : ftype
  I : ftype
  IMAX : ftype
  FLTE : ftype
  D : ftype
  FLTD : ftype
  FF : ftype
deriving Repr

/-- Internal variables, `AC_PID_Basic.h:88-95`. -/
structure State where
  _target : ftype
  _error : ftype
  _derivative : ftype
  _integrator : ftype
  _reset_filter : Bool
  _pid_info : AP_PIDInfo
deriving Repr

/-- Constructor `AC_PID_Basic(initial_p, initial_i, initial_d, initial_ff, initial_imax,
initial_filt_E_hz, initial_filt_D_hz)`, `AC_PID_Basic.cpp:52-67`. Members it does not set
start at zero. -/
def init (initial_p initial_i initial_d initial_ff initial_imax initial_filt_E_hz
    initial_filt_D_hz : ftype) : Params × State :=
  ({ P := initial_p, I := initial_i, IMAX := initial_imax, FLTE := initial_filt_E_hz,
     D := initial_d, FLTD := initial_filt_D_hz, FF := initial_ff },
   { _target := 0, _error := 0, _derivative := 0, _integrator := 0, _reset_filter := true,
     _pid_info := {} })

/-! ### Accessors and setters, `AC_PID_Basic.h:31-64` -/

def get_p (p : Params) (s : State) : ftype := s._error * p.P
def get_i (s : State) : ftype := s._integrator
def get_d (p : Params) (s : State) : ftype := s._derivative * p.D
def get_ff (p : Params) (s : State) : ftype := s._target * p.FF
def get_error (s : State) : ftype := s._error

def kP (p : Params) : ftype := p.P
def kI (p : Params) : ftype := p.I
def kD (p : Params) : ftype := p.D
def ff (p : Params) : ftype := p.FF
def filt_E_hz (p : Params) : ftype := p.FLTE
def filt_D_hz (p : Params) : ftype := p.FLTD
def imax (p : Params) : ftype := p.IMAX

def set_kP (p : Params) (v : ftype) : Params := { p with P := v }
def set_kI (p : Params) (v : ftype) : Params := { p with I := v }
def set_kD (p : Params) (v : ftype) : Params := { p with D := v }
def set_ff (p : Params) (v : ftype) : Params := { p with FF := v }
def set_imax (p : Params) (v : ftype) : Params := { p with IMAX := v.abs }
def set_filt_E_hz (p : Params) (hz : ftype) : Params := { p with FLTE := hz.abs }
def set_filt_D_hz (p : Params) (hz : ftype) : Params := { p with FLTD := hz.abs }

/-- `reset_filter()`, `AC_PID_Basic.h:41`. -/
def reset_filter (s : State) : State := { s with _reset_filter := true }

def get_pid_info (s : State) : AP_PIDInfo := s._pid_info

/-- `get_filt_E_alpha`, `AC_PID_Basic.cpp:155-159`. -/
def get_filt_E_alpha (p : Params) (dt : ftype) : ftype := calc_lowpass_alpha_dt dt p.FLTE
/-- `get_filt_D_alpha`, `AC_PID_Basic.cpp:161-165`. -/
def get_filt_D_alpha (p : Params) (dt : ftype) : ftype := calc_lowpass_alpha_dt dt p.FLTD

/-- `update_i(dt, limit_neg, limit_pos)`, `AC_PID_Basic.cpp:122-136`. With `limit_neg` the
integrator does not integrate a negative error, with `limit_pos` not a positive one. Unlike
`AC_PID::update_i` there is no `is_positive(dt)` test. -/
def update_i (p : Params) (s : State) (dt : ftype) (limit_neg limit_pos : Bool) : State :=
  if !is_zero p.I then
    -- Ensure that integrator can only be reduced if the output is saturated
    if !((limit_neg && is_negative s._error) || (limit_pos && is_positive s._error)) then
      let integrator := s._integrator + ((s._error * p.I) * dt)
      let integrator := constrain_float integrator (-p.IMAX) p.IMAX
      { s with _integrator := integrator }
    else
      s
  else
    { s with _integrator := 0.0 }

/-- `update_all(target, measurement, dt, limit_neg, limit_pos)`, `AC_PID_Basic.cpp:74-120`.
Returns 0 without touching the state on a non-finite input (:79-84). -/
def update_all (p : Params) (s : State) (target measurement dt : ftype)
    (limit_neg limit_pos : Bool) : State × ftype := Id.run do
  -- Return zero if inputs are invalid (NaN or infinite)
  if !target.isFinite || target.isNaN || !measurement.isFinite || measurement.isNaN then
    return (s, 0.0)
  let mut s := { s with _target := target }
  -- Reset filter state to match current inputs (on first run or after reset)
  if s._reset_filter then
    s := { s with _reset_filter := false }
    s := { s with _error := s._target - measurement }
    s := { s with _derivative := 0.0 }
  else
    let error_last := s._error
    s := { s with _error := s._error + get_filt_E_alpha p dt * ((s._target - measurement) - s._error) }
    -- Compute and low-pass filter the error derivative (D term)
    if is_positive dt then
      let derivative := (s._error - error_last) / dt
      s := { s with _derivative := s._derivative + get_filt_D_alpha p dt * (derivative - s._derivative) }
  -- update I term
  s := update_i p s dt limit_neg limit_pos
  let P_out := s._error * p.P
  let D_out := s._derivative * p.D
  s := { s with _pid_info := { s._pid_info with
    target := s._target, actual := measurement, error := s._error, P := s._error * p.P,
    I := s._integrator, D := s._derivative * p.D, FF := s._target * p.FF } }
  return (s, P_out + s._integrator + D_out + s._target * p.FF)

/-- `update_all(target, measurement, dt, limit)`, `AC_PID_Basic.cpp:69-72`: `limit` blocks
integration away from zero, read from the integrator before the update. -/
def update_all_limit (p : Params) (s : State) (target measurement dt : ftype)
    (limit : Bool := false) : State × ftype :=
  update_all p s target measurement dt (limit && is_negative s._integrator)
    (limit && is_positive s._integrator)

/-- `reset_I()`, `AC_PID_Basic.cpp:138-141`. -/
def reset_I (s : State) : State := { s with _integrator := 0.0 }

/-- `set_integrator(float i)`, `AC_PID_Basic.cpp:179-183`. -/
def set_integrator (p : Params) (s : State) (i : ftype) : State :=
  { s with _integrator := constrain_float i (-p.IMAX) p.IMAX }

/-- `set_integrator(float error, float i)`, `AC_PID_Basic.cpp:173-177`. -/
def set_integrator_error (p : Params) (s : State) (error i : ftype) : State :=
  set_integrator p s (i - error * p.P)

/-- `set_integrator(float target, float measurement, float i)`, `AC_PID_Basic.cpp:167-171`. -/
def set_integrator_target (p : Params) (s : State) (target measurement i : ftype) : State :=
  set_integrator_error p s (target - measurement) i

end AC_PID_Basic
