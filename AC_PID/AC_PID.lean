import AP_Math
import AC_PID.AP_PIDInfo

/-!
# `AC_PID`

Mirrors `libraries/AC_PID/AC_PID.h:14-216` and `libraries/AC_PID/AC_PID.cpp:9-448` (ArduPilot
commit 802db19de1). One C++ object is split into `Params` (the `AP_Param` table, `var_info`,
`AC_PID.cpp:9-100`) and `State` (the internal variables, `AC_PID.h:186-204`). Every mutating
method is a pure function `Params → State → inputs → State × output`.

Left out:
- the notch filters (`AP_FILTER_ENABLED` branches, `AC_PID.cpp:156-191`, `:212-217`,
  `:221-226`, `:235-240`, `:247-252`); the port is exact when `NTF = NEF = 0` (the default),
  for which the notch pointers stay null;
- the slew limiter (`Filter/SlewLimiter.cpp:45-137`, called at `AC_PID.cpp:274-275`): with
  `SMAX ≤ 0` (the default `srmax = 0`) `modifier` returns `1.0` (`SlewLimiter.cpp:83-85`, or
  `:47-49` when `dt` is not positive), so `Dmod = 1`. Its internal filter state, which only
  feeds `get_slew_rate()` for logging, is not modelled: `_pid_info.slew_rate` stays as it was.
  `SMAX`, `_slew_rate_tau` and `_slew_limit_scale` therefore have no effect here; the first is
  kept as a parameter field, the other two are dropped;
- `load_gains`, `save_gains`, `set_notch_sample_rate` and the rest of the `AP_Param` plumbing;
- logging.

`Faithful p` states the configuration under which this port equals the C++.
-/

namespace AC_PID

open AP_Math

/-- `AC_PID_TFILT_HZ_DEFAULT`, `AC_PID.h:14`. -/
def AC_PID_TFILT_HZ_DEFAULT : ftype := 0.0
/-- `AC_PID_EFILT_HZ_DEFAULT`, `AC_PID.h:15`. -/
def AC_PID_EFILT_HZ_DEFAULT : ftype := 0.0
/-- `AC_PID_DFILT_HZ_DEFAULT`, `AC_PID.h:16`. -/
def AC_PID_DFILT_HZ_DEFAULT : ftype := 20.0
/-- `AC_PID_RESET_TC`, `AC_PID.h:17`. -/
def AC_PID_RESET_TC : ftype := 0.16

/-- `AC_PID::Defaults`, `AC_PID.h:26-38`. -/
structure Defaults where
  p : ftype
  i : ftype
  d : ftype
  ff : ftype
  imax : ftype
  filt_T_hz : ftype
  filt_E_hz : ftype
  filt_D_hz : ftype
  srmax : ftype := 0
  srtau : ftype := 1.0
  dff : ftype := 0
deriving Repr

/-- The parameter table `AC_PID::var_info`, `AC_PID.cpp:9-100`, fields named as the
parameter suffixes (`ATC_RAT_RLL_P`, ... `PSC_D_ACC_IMAX`, ...). C++ members: `_kp`, `_ki`,
`_kd`, `_kff`, `_kimax`, `_filt_T_hz`, `_filt_E_hz`, `_filt_D_hz`, `_slew_rate_max`,
`_kpdmax`, `_kdff`, `_notch_T_filter`, `_notch_E_filter` (`AC_PID.h:165-179`). -/
structure Params where
  P : ftype
  I : ftype
  D : ftype
  FF : ftype
  IMAX : ftype
  FLTT : ftype
  FLTE : ftype
  FLTD : ftype
  /-- Unused by this port: see the header (`Faithful` requires `SMAX ≤ 0`). -/
  SMAX : ftype
  PDMX : ftype
  D_FF : ftype
  /-- Unused by this port: see the header (`Faithful` requires `NTF = 0`). -/
  NTF : Int8
  /-- Unused by this port: see the header (`Faithful` requires `NEF = 0`). -/
  NEF : Int8
deriving Repr

/-- `struct ac_pid_flags`, `AC_PID.h:187-190`. -/
structure ac_pid_flags where
  _reset_filter : Bool
  _I_set : Bool
deriving Repr

/-- Internal variables, `AC_PID.h:186-204` (notch pointers and `_slew_limit_scale` left out). -/
structure State where
  _flags : ac_pid_flags
  _integrator : ftype
  _target : ftype
  _error : ftype
  _derivative : ftype
  _target_derivative : ftype
  _pid_info : AP_PIDInfo
deriving Repr

/-- The configuration under which this port is exact: no slew limiting and no notch filters. -/
structure Faithful (p : Params) : Prop where
  smax_off : p.SMAX ≤ 0
  ntf_off : p.NTF = 0
  nef_off : p.NEF = 0

/-- Constructor, `AC_PID.cpp:103-130`, with `AP_Param::setup_object_defaults` loading the
table defaults (`PDMX`, `NTF`, `NEF` default to 0, `AC_PID.cpp:73`, `:89`, `:96`). Members the
constructor does not set start at zero, as ArduPilot zero-fills its objects. -/
def init (d : Defaults) : Params × State :=
  ({ P := d.p, I := d.i, D := d.d, FF := d.ff, IMAX := d.imax, FLTT := d.filt_T_hz,
     FLTE := d.filt_E_hz, FLTD := d.filt_D_hz, SMAX := d.srmax, PDMX := 0, D_FF := d.dff,
     NTF := 0, NEF := 0 },
   { _flags := { _reset_filter := true, _I_set := false }, _integrator := 0, _target := 0,
     _error := 0, _derivative := 0, _target_derivative := 0, _pid_info := {} })

/-! ### Accessors, `AC_PID.h:96-110` -/

def kP (p : Params) : ftype := p.P
def kI (p : Params) : ftype := p.I
def kD (p : Params) : ftype := p.D
def kIMAX (p : Params) : ftype := p.IMAX
def kPDMAX (p : Params) : ftype := p.PDMX
def ff (p : Params) : ftype := p.FF
def filt_T_hz (p : Params) : ftype := p.FLTT
def filt_E_hz (p : Params) : ftype := p.FLTE
def filt_D_hz (p : Params) : ftype := p.FLTD
def slew_limit (p : Params) : ftype := p.SMAX
def kDff (p : Params) : ftype := p.D_FF
def imax (p : Params) : ftype := p.IMAX
def pdmax (p : Params) : ftype := p.PDMX

/-! ### Setters, `AC_PID.h:120-130`, `AC_PID.cpp:132-154` -/

def set_kP (p : Params) (v : ftype) : Params := { p with P := v }
def set_kI (p : Params) (v : ftype) : Params := { p with I := v }
def set_kD (p : Params) (v : ftype) : Params := { p with D := v }
def set_ff (p : Params) (v : ftype) : Params := { p with FF := v }
def set_imax (p : Params) (v : ftype) : Params := { p with IMAX := v.abs }
def set_pdmax (p : Params) (v : ftype) : Params := { p with PDMX := v.abs }
def set_filt_T_hz (p : Params) (hz : ftype) : Params := { p with FLTT := hz.abs }
def set_filt_E_hz (p : Params) (hz : ftype) : Params := { p with FLTE := hz.abs }
def set_filt_D_hz (p : Params) (hz : ftype) : Params := { p with FLTD := hz.abs }
def set_slew_limit (p : Params) (smax : ftype) : Params := { p with SMAX := smax.abs }
def set_kDff (p : Params) (v : ftype) : Params := { p with D_FF := v }

/-- `reset_filter()`, `AC_PID.h:85-87`. -/
def reset_filter (s : State) : State := { s with _flags := { s._flags with _reset_filter := true } }

/-- `set_target_rate`, `AC_PID.h:133`. -/
def set_target_rate (s : State) (target : ftype) : State :=
  { s with _pid_info := { s._pid_info with target := target } }
/-- `set_actual_rate`, `AC_PID.h:134`. -/
def set_actual_rate (s : State) (actual : ftype) : State :=
  { s with _pid_info := { s._pid_info with actual := actual } }

/-- `get_pid_info()`, `AC_PID.h:149`. -/
def get_pid_info (s : State) : AP_PIDInfo := s._pid_info

/-- `get_filt_T_alpha`, `AC_PID.cpp:414-418`. -/
def get_filt_T_alpha (p : Params) (dt : ftype) : ftype := calc_lowpass_alpha_dt dt p.FLTT
/-- `get_filt_E_alpha`, `AC_PID.cpp:420-424`. -/
def get_filt_E_alpha (p : Params) (dt : ftype) : ftype := calc_lowpass_alpha_dt dt p.FLTE
/-- `get_filt_D_alpha`, `AC_PID.cpp:426-430`. -/
def get_filt_D_alpha (p : Params) (dt : ftype) : ftype := calc_lowpass_alpha_dt dt p.FLTD

/-- `SlewLimiter::modifier(sample, dt)` under `Faithful` (`SMAX ≤ 0`): `1.0`
(`SlewLimiter.cpp:47-49`, `:83-85`). Not a model of the limiter for `SMAX > 0`. -/
def slew_limiter_modifier_smax_off (_sample _dt : ftype) : ftype := 1.0

/-- `update_i(dt, limit, i_scale)`, `AC_PID.cpp:337-351`. If `limit` holds, the integrator
changes only when the error has the opposite sign to it (anti-windup). -/
def update_i (p : Params) (s : State) (dt : ftype) (limit : Bool) (i_scale : ftype := 1.0) :
    State :=
  if !is_zero p.I && is_positive dt then
    if !limit || ((is_positive s._integrator && is_negative s._error) ||
                  (is_negative s._integrator && is_positive s._error)) then
      let integrator := s._integrator + ((s._error * p.I) * i_scale * dt)
      let integrator := constrain_float integrator (-p.IMAX) p.IMAX
      { s with _integrator := integrator }
    else
      s
  else
    { s with _integrator := 0.0 }

/-- `update_all(target, measurement, dt, limit, pd_scale, i_scale)`, `AC_PID.cpp:193-311`.
Returns 0 without touching the state on a non-finite input (:198-201). -/
def update_all (p : Params) (s : State) (target measurement dt : ftype) (limit : Bool := false)
    (pd_scale : ftype := 1.0) (i_scale : ftype := 1.0) : State × ftype := Id.run do
  -- Return zero if input is invalid (NaN or infinite)
  if !target.isFinite || !measurement.isFinite then
    return (s, 0.0)
  let mut s := s
  let mut info := s._pid_info
  -- Flag used for logging to indicate a filter reset occurred
  info := { info with reset := s._flags._reset_filter }
  if s._flags._reset_filter then
    s := { s with _flags := { s._flags with _reset_filter := false } }
    -- Reset target filter
    s := { s with _target := target }
    -- Calculate error and reset error filter
    s := { s with _error := s._target - measurement }
    -- Clear derivative history to avoid spikes after reset
    s := { s with _derivative := 0.0, _target_derivative := 0.0 }
  else
    -- Apply target filters
    let target_last := s._target
    -- Apply first-order low-pass filter to target value
    s := { s with _target := s._target + get_filt_T_alpha p dt * (target - s._target) }
    -- Calculate error and apply error filter
    let error_last := s._error
    let error := s._target - measurement
    s := { s with _error := s._error + get_filt_E_alpha p dt * (error - s._error) }
    if is_positive dt then
      -- Compute and low-pass filter the error derivative (D term)
      let derivative := (s._error - error_last) / dt
      s := { s with _derivative := s._derivative + get_filt_D_alpha p dt * (derivative - s._derivative) }
      -- Calculate target derivative for D_FF contribution
      s := { s with _target_derivative := (s._target - target_last) / dt }
  -- Integrate error (with wind-up protection if limit is active)
  s := update_i p s dt limit i_scale
  let mut P_out := s._error * p.P
  let mut D_out := s._derivative * p.D
  let I_out := s._integrator
  -- Calculate dynamic modifier to reduce P+D output based on slew rate limiter
  -- (`_slew_limit_scale = 1`, AC_PID.cpp:129)
  info := { info with Dmod := slew_limiter_modifier_smax_off (info.P + info.D) dt }
  P_out := P_out * info.Dmod
  D_out := D_out * info.Dmod
  -- scale pd output if required
  P_out := P_out * pd_scale
  D_out := D_out * pd_scale
  info := { info with PD_limit := false }
  -- Apply PD sum limit if enabled
  if is_positive p.PDMX then
    let PD_sum_abs := (P_out + D_out).abs
    if PD_sum_abs > p.PDMX then
      let pd_limit_scale := p.PDMX / PD_sum_abs
      P_out := P_out * pd_limit_scale
      D_out := D_out * pd_limit_scale
      info := { info with PD_limit := true }
  info := { info with target := s._target, actual := measurement, error := s._error,
                      P := P_out, D := D_out, I := I_out, limit := limit }
  -- Set I set flag for logging and clear
  info := { info with I_term_set := s._flags._I_set }
  s := { s with _flags := { s._flags with _I_set := false } }
  info := { info with FF := s._target * p.FF, DFF := s._target_derivative * p.D_FF }
  s := { s with _pid_info := info }
  return (s, P_out + D_out + I_out)

/-- `update_error(error, dt, limit)`, `AC_PID.cpp:313-335`. -/
def update_error (p : Params) (s : State) (error dt : ftype) (limit : Bool := false) :
    State × ftype :=
  -- don't process inf or NaN
  if !error.isFinite then
    (s, 0.0)
  else
    let s := { s with _target := 0.0 }
    let (s, output) := update_all p s 0.0 (-error) dt limit
    let s := { s with _pid_info := { s._pid_info with target := 0.0, actual := 0.0 } }
    (s, output)

/-- `get_p()`, `AC_PID.cpp:353-356`. -/
def get_p (s : State) : ftype := s._pid_info.P
/-- `get_i()`, `AC_PID.cpp:358-361`. -/
def get_i (s : State) : ftype := s._integrator
/-- `get_d()`, `AC_PID.cpp:363-366`. -/
def get_d (s : State) : ftype := s._pid_info.D
/-- `get_ff()`, `AC_PID.cpp:368-371`: `FF + DFF`. -/
def get_ff (s : State) : ftype := s._pid_info.FF + s._pid_info.DFF
/-- `get_ff_component()`, `AC_PID.cpp:373-376`. -/
def get_ff_component (s : State) : ftype := s._pid_info.FF
/-- `get_dff_component()`, `AC_PID.cpp:378-381`. -/
def get_dff_component (s : State) : ftype := s._pid_info.DFF

/-- `reset_I()`, `AC_PID.cpp:383-388`. -/
def reset_I (s : State) : State :=
  { s with _flags := { s._flags with _I_set := true }, _integrator := 0.0 }

/-- `set_integrator(i)`, `AC_PID.cpp:432-437`. -/
def set_integrator (p : Params) (s : State) (integrator : ftype) : State :=
  { s with _flags := { s._flags with _I_set := true },
           _integrator := constrain_float integrator (-p.IMAX) p.IMAX }

/-- `relax_integrator(integrator, dt, time_constant)`, `AC_PID.cpp:439-448`. -/
def relax_integrator (p : Params) (s : State) (integrator dt time_constant : ftype) : State :=
  let integrator := constrain_float integrator (-p.IMAX) p.IMAX
  if is_positive dt then
    { s with _flags := { s._flags with _I_set := true },
             _integrator := s._integrator + (integrator - s._integrator) * (dt / (dt + time_constant)) }
  else
    s

end AC_PID
