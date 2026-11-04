import AP_Math

/-!
# `AP_Motors` interface seen by the controllers

Mirrors the part of `libraries/AP_Motors/AP_Motors_Class.h` (lines 192-224, 263-276) and
`AP_MotorsMulticopter.h` (lines 55-62) that `AC_AttitudeControl`, `AC_AttitudeControl_Multi` and
`AC_PosControl` read or write: the roll/pitch/yaw inputs and their feed-forwards, the throttle input,
the throttle average maximum, the throttle filter cutoff, the hover throttle, and the `limit` flags
that the PIDs use for anti-windup. The owner of `AP_Motors/` extends this file; other libraries only
import it. Setters are pure functions returning the updated record.
-/

namespace AP_Motors

open AP_Math

/-- `AP_Motors::limit` (AP_Motors_Class.h:263-272): which outputs saturated on the last tick. -/
structure Limit where
  roll : Bool := false
  pitch : Bool := false
  yaw : Bool := false
  throttle_lower : Bool := false
  throttle_upper : Bool := false
  deriving Repr

/-- `set_rpy` (AP_Motors_Class.h:270). -/
def Limit.set_rpy (l : Limit) (flag : Bool) : Limit := { l with roll := flag, pitch := flag, yaw := flag }

/-- `set_throttle` (AP_Motors_Class.h:271). -/
def Limit.set_throttle (l : Limit) (flag : Bool) : Limit := { l with throttle_lower := flag, throttle_upper := flag }

/-- `set_all` (AP_Motors_Class.h:269, AP_Motors_Class.cpp:357-361): `set_rpy` then `set_throttle`. -/
def Limit.set_all (l : Limit) (flag : Bool) : Limit := (l.set_rpy flag).set_throttle flag

/-- The controller-facing state of the motors object. Fields named as the C++ members. -/
structure Inputs where
  _roll_in : ftype := 0
  _pitch_in : ftype := 0
  _yaw_in : ftype := 0
  _roll_in_ff : ftype := 0
  _pitch_in_ff : ftype := 0
  _yaw_in_ff : ftype := 0
  _throttle_in : ftype := 0
  _throttle_avg_max : ftype := 0
  /-- Cutoff of the throttle low-pass filter, set by `set_throttle_filter_cutoff`. -/
  _throttle_filter_cutoff : ftype := 0
  /-- `MOT_THST_HOVER` after `get_throttle_hover`'s constraint; written by the motors library. -/
  _throttle_hover : ftype := 0.35
  /-- Output of the throttle filter, read back by `get_throttle`. -/
  _throttle_filter_value : ftype := 0
  /-- `_throttle_out`, read back by `get_throttle_out`. -/
  _throttle_out : ftype := 0
  /-- `_throttle_thrust_max` (AP_MotorsMulticopter.h:220). -/
  _throttle_thrust_max : ftype := 0
  limit : Limit := {}
  deriving Repr

def set_roll (m : Inputs) (roll_in : ftype) : Inputs := { m with _roll_in := roll_in }
def set_roll_ff (m : Inputs) (roll_in : ftype) : Inputs := { m with _roll_in_ff := roll_in }
def set_pitch (m : Inputs) (pitch_in : ftype) : Inputs := { m with _pitch_in := pitch_in }
def set_pitch_ff (m : Inputs) (pitch_in : ftype) : Inputs := { m with _pitch_in_ff := pitch_in }
def set_yaw (m : Inputs) (yaw_in : ftype) : Inputs := { m with _yaw_in := yaw_in }
def set_yaw_ff (m : Inputs) (yaw_in : ftype) : Inputs := { m with _yaw_in_ff := yaw_in }
/-- AP_Motors_Class.h:198. -/
def set_throttle (m : Inputs) (throttle_in : ftype) : Inputs := { m with _throttle_in := throttle_in }
/-- AP_Motors_Class.h:199. -/
def set_throttle_avg_max (m : Inputs) (throttle_avg_max : ftype) : Inputs :=
  { m with _throttle_avg_max := constrain_float throttle_avg_max 0.0 1.0 }
/-- AP_Motors_Class.h:200. -/
def set_throttle_filter_cutoff (m : Inputs) (filt_hz : ftype) : Inputs := { m with _throttle_filter_cutoff := filt_hz }
/-- AP_MotorsMulticopter.h:55, with `AP_MOTORS_THST_HOVER_MIN = 0.125`, `AP_MOTORS_THST_HOVER_MAX = 0.6875`. -/
def get_throttle_hover (m : Inputs) : ftype := constrain_float m._throttle_hover 0.125 0.6875
/-- AP_Motors_Class.h:219. -/
def get_throttle (m : Inputs) : ftype := constrain_float m._throttle_filter_value 0.0 1.0
/-- AP_Motors_Class.h:215. -/
def get_throttle_out (m : Inputs) : ftype := m._throttle_out
/-- AP_MotorsMulticopter.h:62. -/
def get_throttle_thrust_max (m : Inputs) : ftype := m._throttle_thrust_max

end AP_Motors
