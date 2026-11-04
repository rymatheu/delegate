import AP_Math
import AC_PID.AP_PIDInfo

/-!
# `AC_PID_2D`

Mirrors `libraries/AC_PID/AC_PID_2D.h:14-111` and `libraries/AC_PID/AC_PID_2D.cpp:9-217`
(ArduPilot commit 802db19de1): the 2-D PID used for the horizontal velocity loop of
`AC_PosControl` (`_pid_vel_ne_m`). Parameters `Params` (`var_info`, `AC_PID_2D.cpp:9-48`),
internal variables `State` (`AC_PID_2D.h:93-101`).

Not one to one: C++ overloads cannot share a name in Lean.
- `update_all(const Vector2f&, ...)` is `update_all`; `update_all(const Vector3f&, ...)`
  (`AC_PID_2D.cpp:122-125`) is `update_all_v3`.
- `set_integrator(i)` is `set_integrator`; `set_integrator(error, i)` is
  `set_integrator_error`; `set_integrator(target, measurement, i)` is
  `set_integrator_target`; `set_integrator(const Vector3f&)` is `set_integrator_v3`.
- `get_ff()` also writes `_pid_info_x/y.FF` in C++ (`AC_PID_2D.cpp:162-168`); here it is
  split into `get_ff` (the value) and `get_ff_update_info` (the state update).

Left out: `save_gains` and the `AP_Param` plumbing; logging.
-/

namespace AC_PID_2D

open AP_Math

/-- `var_info`, `AC_PID_2D.cpp:9-48`, fields named as the parameter suffixes
(`PSC_NE_VEL_P`, ...). C++ members `_kp`, `_ki`, `_kd`, `_kff`, `_kimax`, `_filt_E_hz`,
`_filt_D_hz` (`AC_PID_2D.h:85-91`). -/
structure Params where
  P : ftype
  I : ftype
  IMAX : ftype
  FLTE : ftype
  D : ftype
  FLTD : ftype
  FF : ftype
deriving Repr

/-- Internal variables, `AC_PID_2D.h:93-101`. -/
structure State where
  _target : Vector2f
  _error : Vector2f
  _derivative : Vector2f
  _integrator : Vector2f
  _reset_filter : Bool
  _pid_info_x : AP_PIDInfo
  _pid_info_y : AP_PIDInfo
deriving Repr

/-- Constructor `AC_PID_2D(initial_kP, initial_kI, initial_kD, initial_kFF, initial_imax,
initial_filt_E_hz, initial_filt_D_hz)`, `AC_PID_2D.cpp:50-65`. Members it does not set start
at zero. -/
def init (initial_kP initial_kI initial_kD initial_kFF initial_imax initial_filt_E_hz
    initial_filt_D_hz : ftype) : Params × State :=
  ({ P := initial_kP, I := initial_kI, IMAX := initial_imax, FLTE := initial_filt_E_hz,
     D := initial_kD, FLTD := initial_filt_D_hz, FF := initial_kFF },
   { _target := ({} : Vector2f), _error := ({} : Vector2f), _derivative := ({} : Vector2f),
     _integrator := ({} : Vector2f), _reset_filter := true, _pid_info_x := {},
     _pid_info_y := {} })

/-! ### Accessors and setters, `AC_PID_2D.h:38-67` -/

def kP (p : Params) : ftype := p.P
def kI (p : Params) : ftype := p.I
def kD (p : Params) : ftype := p.D
def ff (p : Params) : ftype := p.FF
def filt_E_hz (p : Params) : ftype := p.FLTE
def filt_D_hz (p : Params) : ftype := p.FLTD
def imax (p : Params) : ftype := p.IMAX
def get_error (s : State) : Vector2f := s._error

def set_kP (p : Params) (v : ftype) : Params := { p with P := v }
def set_kI (p : Params) (v : ftype) : Params := { p with I := v }
def set_kD (p : Params) (v : ftype) : Params := { p with D := v }
def set_ff (p : Params) (v : ftype) : Params := { p with FF := v }
def set_imax (p : Params) (v : ftype) : Params := { p with IMAX := v.abs }
def set_filt_E_hz (p : Params) (hz : ftype) : Params := { p with FLTE := hz.abs }
def set_filt_D_hz (p : Params) (hz : ftype) : Params := { p with FLTD := hz.abs }

/-- `reset_filter()`, `AC_PID_2D.h:44`. -/
def reset_filter (s : State) : State := { s with _reset_filter := true }

def get_pid_info_x (s : State) : AP_PIDInfo := s._pid_info_x
def get_pid_info_y (s : State) : AP_PIDInfo := s._pid_info_y

/-- `get_filt_E_alpha`, `AC_PID_2D.cpp:187-191`. -/
def get_filt_E_alpha (p : Params) (dt : ftype) : ftype := calc_lowpass_alpha_dt dt p.FLTE
/-- `get_filt_D_alpha`, `AC_PID_2D.cpp:193-197`. -/
def get_filt_D_alpha (p : Params) (dt : ftype) : ftype := calc_lowpass_alpha_dt dt p.FLTD

/-- `update_i(dt, limit)`, `AC_PID_2D.cpp:127-145`. The integrator may not grow in length
along the direction of `limit`; it is then clamped to length `IMAX`. -/
def update_i (p : Params) (s : State) (dt : ftype) (limit : Vector2f) : State := Id.run do
  let mut info_x := { s._pid_info_x with limit := false }
  let mut info_y := { s._pid_info_y with limit := false }
  let delta_integrator : Vector2f := (s._error * p.I) * dt
  let integrator_length := s._integrator.length
  let mut integrator := s._integrator + delta_integrator
  -- Compute integrator delta and apply anti-windup by limiting growth in the direction of
  -- the limit vector (`&&` short-circuits: `limit_length` runs only if the dot product is
  -- positive)
  if is_positive (delta_integrator.dot limit) then
    let (i', limited) := integrator.limit_length integrator_length
    integrator := i'
    if limited then
      info_x := { info_x with limit := true }
      info_y := { info_y with limit := true }
  -- Clamp integrator to maximum length (IMAX)
  integrator := (integrator.limit_length p.IMAX).1
  return { s with _integrator := integrator, _pid_info_x := info_x, _pid_info_y := info_y }

/-- `update_all(const Vector2f &target, const Vector2f &measurement, float dt,
const Vector2f &limit)`, `AC_PID_2D.cpp:67-120`. Returns the zero vector without touching
the state if any component is NaN or infinite (:72-76). -/
def update_all (p : Params) (s : State) (target measurement : Vector2f) (dt : ftype)
    (limit : Vector2f) : State × Vector2f := Id.run do
  -- Return zero if any component is NaN or infinite
  if target.is_nan || target.is_inf || measurement.is_nan || measurement.is_inf then
    return (s, ({} : Vector2f))
  let mut s := { s with _target := target }
  -- reset input filter to value received
  if s._reset_filter then
    -- Reset filters to match the current inputs
    s := { s with _reset_filter := false }
    s := { s with _error := s._target - measurement }
    -- Reset the derivative to avoid transients
    s := { s with _derivative := ({} : Vector2f) }
  else
    let error_last := s._error
    -- Apply first-order low-pass filter to error
    s := { s with _error := s._error + ((s._target - measurement) - s._error) * get_filt_E_alpha p dt }
    -- Compute and low-pass filter the derivative
    if is_positive dt then
      let derivative : Vector2f := (s._error - error_last) / dt
      s := { s with _derivative := s._derivative + (derivative - s._derivative) * get_filt_D_alpha p dt }
  -- update I term
  s := update_i p s dt limit
  s := { s with
    _pid_info_x := { s._pid_info_x with
      target := s._target.x, actual := measurement.x, error := s._error.x,
      P := s._error.x * p.P, I := s._integrator.x, D := s._derivative.x * p.D,
      FF := s._target.x * p.FF },
    _pid_info_y := { s._pid_info_y with
      target := s._target.y, actual := measurement.y, error := s._error.y,
      P := s._error.y * p.P, I := s._integrator.y, D := s._derivative.y * p.D,
      FF := s._target.y * p.FF } }
  -- Return total control output: P + I + D + FF terms
  return (s, s._error * p.P + s._integrator + s._derivative * p.D + s._target * p.FF)

/-- `update_all(const Vector3f &target, const Vector3f &measurement, float dt,
const Vector3f &limit)`, `AC_PID_2D.cpp:122-125`: the horizontal components. -/
def update_all_v3 (p : Params) (s : State) (target measurement : Vector3f) (dt : ftype)
    (limit : Vector3f) : State × Vector2f :=
  update_all p s ⟨target.x, target.y⟩ ⟨measurement.x, measurement.y⟩ dt ⟨limit.x, limit.y⟩

/-- `get_p()`, `AC_PID_2D.cpp:147-150`. -/
def get_p (p : Params) (s : State) : Vector2f := s._error * p.P
/-- `get_i()`, `AC_PID_2D.cpp:152-155`. -/
def get_i (s : State) : Vector2f := s._integrator
/-- `get_d()`, `AC_PID_2D.cpp:157-160`. -/
def get_d (p : Params) (s : State) : Vector2f := s._derivative * p.D
/-- Return value of `get_ff()`, `AC_PID_2D.cpp:162-168`. -/
def get_ff (p : Params) (s : State) : Vector2f := s._target * p.FF
/-- State update of `get_ff()`, `AC_PID_2D.cpp:165-166` (logging fields only). -/
def get_ff_update_info (p : Params) (s : State) : State :=
  { s with _pid_info_x := { s._pid_info_x with FF := s._target.x * p.FF },
           _pid_info_y := { s._pid_info_y with FF := s._target.y * p.FF } }

/-- `reset_I()`, `AC_PID_2D.cpp:170-173`. -/
def reset_I (s : State) : State := { s with _integrator := ({} : Vector2f) }

/-- `set_integrator(const Vector2f& i)`, `AC_PID_2D.cpp:211-216`: clamp to length `IMAX`. -/
def set_integrator (p : Params) (s : State) (i : Vector2f) : State :=
  { s with _integrator := (i.limit_length p.IMAX).1 }

/-- `set_integrator(const Vector2f& error, const Vector2f& i)`, `AC_PID_2D.cpp:205-209`. -/
def set_integrator_error (p : Params) (s : State) (error i : Vector2f) : State :=
  set_integrator p s (i - error * p.P)

/-- `set_integrator(target, measurement, i)`, `AC_PID_2D.cpp:199-203`. -/
def set_integrator_target (p : Params) (s : State) (target measurement i : Vector2f) : State :=
  set_integrator_error p s (target - measurement) i

/-- `set_integrator(const Vector3f& i)`, `AC_PID_2D.h:73`. -/
def set_integrator_v3 (p : Params) (s : State) (i : Vector3f) : State :=
  set_integrator p s ⟨i.x, i.y⟩

end AC_PID_2D
