import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_PID.AC_PID
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.libraries.AC_PID.AC_PID_2

/-!
ArduPilot `libraries/AC_AttitudeControl`, part 2 of 2. Sources: `libraries/AC_AttitudeControl/AC_AttitudeControl.cpp`, `libraries/AC_AttitudeControl/AC_PosControl.cpp`, `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AC_PosControl::D_init_controller : void ()`, `AC_PosControl.cpp:895-929`. -/
def AC_PosControl.D_init_controller (this : UInt64) : PMem.M Unit := do
  AC_PosControl.init_terrain this
  AC_PosControl.D_init_offsets this
  let t'1 ← PMem.ldF64 ((this + 704) + 16)
  PMem.stF64 ((this + 752) + 16) t'1
  let t'2 ← PMem.ldF64 ((this + 752) + 16)
  let t'3 ← PMem.ldF64 ((this + 888) + 16)
  let t'4 := (t'2 - t'3)
  PMem.stF64 ((this + 728) + 16) t'4
  let t'5 ← PMem.ldF32 ((this + 776) + 8)
  PMem.stF32 ((this + 800) + 8) t'5
  let t'6 ← PMem.ldF32 ((this + 800) + 8)
  let t'7 ← PMem.ldF32 ((this + 924) + 8)
  let t'8 := (t'6 - t'7)
  PMem.stF32 ((this + 788) + 8) t'8
  AC_PID_Basic.reset_filter (this + 264)
  AC_PID_Basic.set_integrator (this + 264) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'9 ← AC_PosControl.get_estimated_accel_D_mss this
  let t'10 ← PMem.ldF32 (this + 652)
  let t'11 ← PMem.ldF32 (this + 652)
  let t'12 ← constrain_value_line'float t'9 (-t'10) t'11 (Int32.toUInt32 ((913 : Int32)))
  PMem.stF32 ((this + 824) + 8) t'12
  let t'13 ← PMem.ldF32 ((this + 824) + 8)
  let t'14 ← PMem.ldF32 ((this + 948) + 8)
  let t'15 ← PMem.ldF32 (this + 860)
  let t'16 := (t'13 - (t'14 + t'15))
  PMem.stF32 ((this + 812) + 8) t'16
  AC_PID.reset_filter (this + 384)
  let t'17 ← PMem.ldU64 (this + 16)
  let t'18 ← AC_AttitudeControl.get_throttle_in t'17
  let t'19 ← PMem.ldU64 (this + 8)
  let t'20 ← AP_MotorsMulticopter.get_throttle_hover t'19
  let t'21 ← AC_PID.kP (this + 384)
  let t'22 ← AP_ParamT'float_4.operator_const_float__'1 t'21
  let t'23 ← PMem.ldF32 t'22
  let t'24 ← PMem.ldF32 ((this + 824) + 8)
  let t'25 ← AC_PosControl.get_estimated_accel_D_mss this
  let t'26 ← AC_PID.ff (this + 384)
  let t'27 ← AP_ParamT'float_4.operator_const_float__'1 t'26
  let t'28 ← PMem.ldF32 t'27
  let t'29 ← PMem.ldF32 ((this + 824) + 8)
  AC_PID.set_integrator (this + 384) (((-(t'18 - t'20)) - (t'23 * (t'24 - t'25))) - (t'28 * t'29))
  AC_PosControl.D_init_ekf_reset this
  let t'30 ← AP.scheduler
  let t'31 ← AP_Scheduler.ticks32 t'30
  PMem.stU32 (this + 632) t'31
  return ()

/-- C++ `AC_PosControl::D_set_max_speed_accel_m : void (float, float, float)`, `AC_PosControl.cpp:806-827`. -/
def AC_PosControl.D_set_max_speed_accel_m.body (fp : UInt64) (this : UInt64) (decent_speed_max_ms : Binary32) (climb_speed_max_ms : Binary32) (accel_max_d_mss : Binary32) : PMem.M Unit := do
  let mut decent_speed_max_ms := decent_speed_max_ms
  let mut climb_speed_max_ms := climb_speed_max_ms
  let mut accel_max_d_mss := accel_max_d_mss
  let t'1 ← is_zero decent_speed_max_ms
  if !t'1 then
    let t'2 := (Binary32.abs decent_speed_max_ms)
    PMem.stF32 (this + 644) t'2
  let t'3 ← is_zero climb_speed_max_ms
  if !t'3 then
    let t'4 := (Binary32.abs climb_speed_max_ms)
    PMem.stF32 (this + 640) t'4
  let t'5 ← is_zero accel_max_d_mss
  if !t'5 then
    let t'6 := (Binary32.abs accel_max_d_mss)
    PMem.stF32 (this + 652) t'6
  let t'7 ← AP_ParamT'float_4.operator_const_float__'1 (this + 32)
  let t'8 ← PMem.ldF32 t'7
  PMem.stF32 (this + 660) t'8
  let t'9 ← AC_PID.filt_T_hz (this + 384)
  discard <| PMem.memcpy (fp + 0) t'9 4
  let t'10 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if t'10 then
    PMem.stF32 (fp + 8) (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/)
    let t'11 ← MIN'float_float (fp + 8) (this + 652)
    let t'12 ← PMem.ldF32 t'11
    let t'13 ← AC_PID.filt_T_hz (this + 384)
    let t'14 ← AP_ParamT'float_4.operator_const_float__'1 t'13
    let t'15 ← PMem.ldF32 t'14
    PMem.stF32 (fp + 4) ((t'12 * (((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))) * t'15)) / (Binary64.toBinary32 ((Binary64.ofBits 0x4014000000000000 /- 5 -/))))
    let t'16 ← MIN'float_float (this + 660) (fp + 4)
    let t'17 ← PMem.ldF32 t'16
    PMem.stF32 (this + 660) t'17
  let t'18 ← AC_PID.filt_E_hz (this + 384)
  discard <| PMem.memcpy (fp + 16) t'18 4
  let t'19 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 16)
  if t'19 then
    PMem.stF32 (fp + 24) (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/)
    let t'20 ← MIN'float_float (fp + 24) (this + 652)
    let t'21 ← PMem.ldF32 t'20
    let t'22 ← AC_PID.filt_E_hz (this + 384)
    let t'23 ← AP_ParamT'float_4.operator_const_float__'1 t'22
    let t'24 ← PMem.ldF32 t'23
    PMem.stF32 (fp + 20) ((t'21 * (((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))) * t'24)) / (Binary64.toBinary32 ((Binary64.ofBits 0x4014000000000000 /- 5 -/))))
    let t'25 ← MIN'float_float (this + 660) (fp + 20)
    let t'26 ← PMem.ldF32 t'25
    PMem.stF32 (this + 660) t'26
  return ()

def AC_PosControl.D_set_max_speed_accel_m (this : UInt64) (decent_speed_max_ms : Binary32) (climb_speed_max_ms : Binary32) (accel_max_d_mss : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← AC_PosControl.D_set_max_speed_accel_m.body fp this decent_speed_max_ms climb_speed_max_ms accel_max_d_mss
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::D_set_correction_speed_accel_m : void (float, float, float)`, `AC_PosControl.cpp:841-845`. -/
def AC_PosControl.D_set_correction_speed_accel_m (this : UInt64) (decent_speed_max_ms : Binary32) (climb_speed_max_ms : Binary32) (accel_max_d_mss : Binary32) : PMem.M Unit := do
  let mut decent_speed_max_ms := decent_speed_max_ms
  let mut climb_speed_max_ms := climb_speed_max_ms
  let mut accel_max_d_mss := accel_max_d_mss
  AC_P_1D.set_limits (this + 60) (-(Binary32.abs decent_speed_max_ms)) (Binary32.abs climb_speed_max_ms) (Binary32.abs accel_max_d_mss) (Binary32.ofBits 0x00000000 /- 0 -/)
  return ()

/-- C++ `AC_PosControl::NE_set_correction_speed_accel_m : void (float, float)`, `AC_PosControl.cpp:493-497`. -/
def AC_PosControl.NE_set_correction_speed_accel_m (this : UInt64) (speed_ne_ms : Binary32) (accel_ne_mss : Binary32) : PMem.M Unit := do
  let mut speed_ne_ms := speed_ne_ms
  let mut accel_ne_mss := accel_ne_mss
  AC_P_2D.set_limits (this + 36) speed_ne_ms accel_ne_mss (Binary32.ofBits 0x00000000 /- 0 -/)
  return ()

/-- C++ `AC_PosControl::NE_is_active : bool () const`, `AC_PosControl.cpp:689-693`. -/
def AC_PosControl.NE_is_active (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP.scheduler
  let t'2 ← AP_Scheduler.ticks32 t'1
  let t'3 ← PMem.ldU32 (this + 628)
  let mut dt_ticks : UInt32 := (t'2 - t'3)
  return (decide (dt_ticks ≤ (Int32.toUInt32 ((1 : Int32)))))

/-- C++ `AC_PosControl::get_lean_angle_max_rad : float () const`, `AC_PosControl.cpp:1170-1179`. -/
def AC_PosControl.get_lean_angle_max_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 976)
  let t'2 ← is_positive'float t'1
  if t'2 then
    let t'3 ← PMem.ldF32 (this + 976)
    return t'3
  discard <| PMem.memcpy (fp + 0) (this + 24) 4
  let t'4 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if !t'4 then
    let t'5 ← PMem.ldU64 (this + 16)
    let t'6 ← AC_AttitudeControl.lean_angle_max_rad t'5
    return t'6
  let t'7 ← AP_ParamT'float_4.operator_const_float__'1 (this + 24)
  let t'8 ← PMem.ldF32 t'7
  let t'9 ← radians t'8
  return t'9

def AC_PosControl.get_lean_angle_max_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← AC_PosControl.get_lean_angle_max_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::NE_init_controller : void ()`, `AC_PosControl.cpp:544-586`. -/
def AC_PosControl.NE_init_controller.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AC_PosControl.NE_init_offsets this
  let t'1 ← PMem.ldU64 (this + 16)
  let t'2 ← AC_AttitudeControl.get_att_target_euler_rad t'1
  let att_target_euler_rad : UInt64 := t'2
  let t'3 ← PMem.ldF32 att_target_euler_rad
  PMem.stF32 (this + 688) t'3
  let t'4 ← PMem.ldF32 (att_target_euler_rad + 4)
  PMem.stF32 (this + 692) t'4
  let t'5 ← PMem.ldF32 (att_target_euler_rad + 8)
  PMem.stF32 (this + 696) t'5
  let t'6 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 700) t'6
  let t'7 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 976) t'7
  let t'8 ← Vector3'double.xy (this + 752)
  let t'9 ← Vector3'double.xy (this + 704)
  discard <| PMem.memcpy t'8 t'9 16
  discard <| pure (t'8)
  let t'10 ← Vector3'double.xy (this + 728)
  let t'11 ← Vector3'double.xy (this + 752)
  let t'12 ← Vector3'double.xy (this + 888)
  Vector2'double.operator_ t'11 (fp + 0) t'12
  let t'13 := (fp + 0)
  discard <| PMem.memcpy t'10 t'13 16
  discard <| pure (t'10)
  let t'14 ← Vector3'float.xy (this + 800)
  let t'15 ← Vector3'float.xy (this + 776)
  discard <| PMem.memcpy t'14 t'15 8
  discard <| pure (t'14)
  let t'16 ← Vector3'float.xy (this + 788)
  let t'17 ← Vector3'float.xy (this + 800)
  let t'18 ← Vector3'float.xy (this + 924)
  Vector2'float.operator_ t'17 (fp + 16) t'18
  let t'19 := (fp + 16)
  discard <| PMem.memcpy t'16 t'19 8
  discard <| pure (t'16)
  let t'20 ← Vector3'float.xy (this + 812)
  Vector2'float.zero t'20
  let t'21 ← AC_PosControl.NE_is_active this
  if !t'21 then
    AC_PosControl.lean_angles_to_accel_NE_mss this (this + 824) ((this + 824) + 4)
  let t'22 ← PMem.ldU64 (this + 16)
  let t'23 ← AC_AttitudeControl.get_althold_lean_angle_max_rad t'22
  PMem.stF32 (fp + 24) t'23
  let t'24 ← AC_PosControl.get_lean_angle_max_rad this
  PMem.stF32 (fp + 28) t'24
  let t'25 ← MIN'float_float (fp + 24) (fp + 28)
  let t'26 ← PMem.ldF32 t'25
  let mut angle_max_rad : Binary32 := t'26
  let t'27 ← angle_rad_to_accel_mss angle_max_rad
  let mut accel_max_mss : Binary32 := t'27
  let t'28 ← Vector3'float.xy (this + 824)
  let t'29 ← Vector2'float.limit_length t'28 accel_max_mss
  discard <| pure (t'29)
  AC_PID_2D.reset_filter (this + 84)
  let t'30 ← Vector3'float.xy (this + 824)
  let t'31 ← Vector3'float.xy (this + 800)
  let t'32 ← AC_PID_2D.ff (this + 84)
  let t'33 ← AP_ParamT'float_4.operator_const_float__'1 t'32
  let t'34 ← PMem.ldF32 t'33
  Vector2'float.operator_'2 t'31 (fp + 32) t'34
  let t'35 := (fp + 32)
  Vector2'float.operator_ t'30 (fp + 40) t'35
  let t'36 := (fp + 40)
  AC_PID_2D.set_integrator (this + 84) t'36
  AC_PosControl.NE_init_ekf_reset this
  let t'37 ← AP.scheduler
  let t'38 ← AP_Scheduler.ticks32 t'37
  PMem.stU32 (this + 628) t'38
  return ()

def AC_PosControl.NE_init_controller (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 48
  let r ← AC_PosControl.NE_init_controller.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::D_is_active : bool () const`, `AC_PosControl.cpp:1069-1073`. -/
def AC_PosControl.D_is_active (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP.scheduler
  let t'2 ← AP_Scheduler.ticks32 t'1
  let t'3 ← PMem.ldU32 (this + 632)
  let mut dt_ticks : UInt32 := (t'2 - t'3)
  return (decide (dt_ticks ≤ (Int32.toUInt32 ((1 : Int32)))))

/-- C++ `AC_AttitudeControl::get_slew_yaw_max_rads : float () const`, `AC_AttitudeControl.cpp:211-217`. -/
def AC_AttitudeControl.get_slew_yaw_max_rads.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  discard <| PMem.memcpy (fp + 0) (this + 20) 4
  let t'1 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if !t'1 then
    let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
    let t'3 ← PMem.ldF32 t'2
    let t'4 ← radians t'3
    return t'4
  let t'5 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'6 ← PMem.ldF32 t'5
  let t'7 ← radians t'6
  PMem.stF32 (fp + 4) t'7
  let t'8 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
  let t'9 ← PMem.ldF32 t'8
  let t'10 ← radians t'9
  PMem.stF32 (fp + 8) t'10
  let t'11 ← MIN'float_float (fp + 4) (fp + 8)
  let t'12 ← PMem.ldF32 t'11
  return t'12

def AC_AttitudeControl.get_slew_yaw_max_rads (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 12
  let r ← AC_AttitudeControl.get_slew_yaw_max_rads.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::get_stopping_point_D_m : void (postype_t &) const`, `AC_PosControl.cpp:1413-1429`. -/
def AC_PosControl.get_stopping_point_D_m.body (fp : UInt64) (this : UInt64) (stopping_point_d_m : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF64 ((this + 704) + 16)
  let mut curr_pos_d_m : Binary32 := Binary64.toBinary32 (t'1)
  let t'2 ← PMem.ldF64 ((this + 888) + 16)
  let t'3 := (curr_pos_d_m - (Binary64.toBinary32 (t'2)))
  curr_pos_d_m := t'3
  let t'4 ← PMem.ldF32 ((this + 776) + 8)
  let mut curr_vel_d_ms : Binary32 := t'4
  let t'5 ← PMem.ldF32 ((this + 924) + 8)
  let t'6 := (curr_vel_d_ms - t'5)
  curr_vel_d_ms := t'6
  let t'7 ← AC_P_1D.kP (this + 60)
  discard <| PMem.memcpy (fp + 0) t'7 4
  let t'8 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  let mut sc'11 := !t'8
  if !sc'11 then
    let t'9 ← PMem.ldF32 (this + 652)
    let t'10 ← is_positive'float t'9
    sc'11 := !t'10
  if sc'11 then
    let t'12 := Binary32.toBinary64 (curr_pos_d_m)
    PMem.stF64 stopping_point_d_m t'12
    return ()
  let t'13 ← AC_P_1D.kP (this + 60)
  let t'14 ← AP_ParamT'float_4.operator_const_float__'1 t'13
  let t'15 ← PMem.ldF32 t'14
  let t'16 ← PMem.ldF32 (this + 652)
  let t'17 ← stopping_distance curr_vel_d_ms t'15 t'16
  let t'18 ← constrain_value_line'float t'17 (-(Binary32.ofBits 0x40400000 /- 3 -/)) (Binary32.ofBits 0x40000000 /- 2 -/) (Int32.toUInt32 ((1428 : Int32)))
  let t'19 := Binary32.toBinary64 ((curr_pos_d_m + t'18))
  PMem.stF64 stopping_point_d_m t'19
  return ()

def AC_PosControl.get_stopping_point_D_m (this : UInt64) (stopping_point_d_m : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AC_PosControl.get_stopping_point_D_m.body fp this stopping_point_d_m
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::D_init_controller_stopping_point : void ()`, `AC_PosControl.cpp:868-877`. -/
def AC_PosControl.D_init_controller_stopping_point (this : UInt64) : PMem.M Unit := do
  AC_PosControl.D_init_controller this
  AC_PosControl.get_stopping_point_D_m this ((this + 728) + 16)
  let t'1 ← PMem.ldF64 ((this + 728) + 16)
  let t'2 ← PMem.ldF64 ((this + 888) + 16)
  let t'3 := (t'1 + t'2)
  PMem.stF64 ((this + 752) + 16) t'3
  let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((this + 788) + 8) t'4
  let t'5 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((this + 812) + 8) t'5
  return ()

/-- C++ `AC_PosControl::NE_init_controller_stopping_point : void ()`, `AC_PosControl.cpp:502-510`. -/
def AC_PosControl.NE_init_controller_stopping_point.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AC_PosControl.NE_init_controller this
  let t'1 ← Vector3'double.xy (this + 728)
  AC_PosControl.get_stopping_point_NE_m this t'1
  let t'2 ← Vector3'double.xy (this + 752)
  let t'3 ← Vector3'double.xy (this + 728)
  let t'4 ← Vector3'double.xy (this + 888)
  Vector2'double.operator_'2 t'3 (fp + 0) t'4
  let t'5 := (fp + 0)
  discard <| PMem.memcpy t'2 t'5 16
  discard <| pure (t'2)
  let t'6 ← Vector3'float.xy (this + 788)
  Vector2'float.zero t'6
  let t'7 ← Vector3'float.xy (this + 812)
  Vector2'float.zero t'7
  return ()

def AC_PosControl.NE_init_controller_stopping_point (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← AC_PosControl.NE_init_controller_stopping_point.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::accel_limiting : void (bool)`, `AC_AttitudeControl.cpp:1377-1395`. -/
def AC_AttitudeControl.accel_limiting.body (fp : UInt64) (this : UInt64) (enable_limits : Bool) : PMem.M Unit := do
  let mut enable_limits := enable_limits
  if enable_limits then
    discard <| PMem.memcpy (fp + 0) (this + 24) 4
    let t'1 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
    if t'1 then
      let t'2 ← AP_Param.load (this + 24)
      discard <| pure (t'2)
    discard <| PMem.memcpy (fp + 8) (this + 28) 4
    let t'3 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 8)
    if t'3 then
      let t'4 ← AP_Param.load (this + 28)
      discard <| pure (t'4)
    discard <| PMem.memcpy (fp + 16) (this + 32) 4
    let t'5 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 16)
    if t'5 then
      let t'6 ← AP_Param.load (this + 32)
      discard <| pure (t'6)
  else
    PMem.stF32 (fp + 20) (Binary32.ofBits 0x00000000 /- 0 -/)
    AP_ParamTBase'float_4.set (this + 24) (fp + 20)
    PMem.stF32 (fp + 24) (Binary32.ofBits 0x00000000 /- 0 -/)
    AP_ParamTBase'float_4.set (this + 28) (fp + 24)
    PMem.stF32 (fp + 28) (Binary32.ofBits 0x00000000 /- 0 -/)
    AP_ParamTBase'float_4.set (this + 32) (fp + 28)
  return ()

def AC_AttitudeControl.accel_limiting (this : UInt64) (enable_limits : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← AC_AttitudeControl.accel_limiting.body fp this enable_limits
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::pre_arm_checks : bool (const char *, char *, const uint8_t)`, `AC_PosControl.cpp:1768-1794`. -/
def AC_PosControl.pre_arm_checks.body (fp : UInt64) (this : UInt64) (param_prefix : UInt64) (failure_msg : UInt64) (failure_msg_len : UInt8) : PMem.M Bool := do
  let mut param_prefix := param_prefix
  let mut failure_msg := failure_msg
  let mut failure_msg_len := failure_msg_len
  let t'1 ← AC_PosControl.NE_get_pos_p this
  let t'2 ← AC_P_2D.kP t'1
  discard <| PMem.memcpy (fp + 0) t'2 4
  let t'3 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if !t'3 then
    PMem.stU64 (fp + 8) param_prefix
    let t'4 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1ab3a : UInt64) /- "%s_NE_POS_P must be > 0" -/ (fp + 8)
    discard <| pure (t'4)
    return false
  let t'5 ← AC_PosControl.D_get_pos_p this
  let t'6 ← AC_P_1D.kP t'5
  discard <| PMem.memcpy (fp + 16) t'6 4
  let t'7 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 16)
  if !t'7 then
    PMem.stU64 (fp + 24) param_prefix
    let t'8 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1ab52 : UInt64) /- "%s_D_POS_P must be > 0" -/ (fp + 24)
    discard <| pure (t'8)
    return false
  let t'9 ← AC_PosControl.D_get_vel_pid this
  let t'10 ← AC_PID_Basic.kP t'9
  discard <| PMem.memcpy (fp + 32) t'10 4
  let t'11 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 32)
  if !t'11 then
    PMem.stU64 (fp + 40) param_prefix
    let t'12 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1ab69 : UInt64) /- "%s_D_VEL_P must be > 0" -/ (fp + 40)
    discard <| pure (t'12)
    return false
  let t'13 ← AC_PosControl.D_get_accel_pid this
  let t'14 ← AC_PID.kP t'13
  discard <| PMem.memcpy (fp + 48) t'14 4
  let t'15 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 48)
  if !t'15 then
    PMem.stU64 (fp + 56) param_prefix
    let t'16 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1ab80 : UInt64) /- "%s_D_ACC_P must be > 0" -/ (fp + 56)
    discard <| pure (t'16)
    return false
  let t'17 ← AC_PosControl.D_get_accel_pid this
  let t'18 ← AC_PID.kI t'17
  discard <| PMem.memcpy (fp + 64) t'18 4
  let t'19 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 64)
  if !t'19 then
    PMem.stU64 (fp + 72) param_prefix
    let t'20 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1ab97 : UInt64) /- "%s_D_ACC_I must be > 0" -/ (fp + 72)
    discard <| pure (t'20)
    return false
  return true

def AC_PosControl.pre_arm_checks (this : UInt64) (param_prefix : UInt64) (failure_msg : UInt64) (failure_msg_len : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 80
  let r ← AC_PosControl.pre_arm_checks.body fp this param_prefix failure_msg failure_msg_len
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::pre_arm_checks : bool (const char *, char *, const uint8_t)`, `AC_AttitudeControl.cpp:1469-1539`. -/
def AC_AttitudeControl.pre_arm_checks.body (fp : UInt64) (this : UInt64) (param_prefix : UInt64) (failure_msg : UInt64) (failure_msg_len : UInt8) : PMem.M Bool := do
  let mut param_prefix := param_prefix
  let mut failure_msg := failure_msg
  let mut failure_msg_len := failure_msg_len
  PMem.stU64 (((fp + 0) + 0) + 0) (0x1aa0f : UInt64) /- "ANG_PIT" -/
  let t'1 ← AC_AttitudeControl.get_angle_pitch_p this
  PMem.stU64 (((fp + 0) + 0) + 8) t'1
  PMem.stU64 (((fp + 0) + 16) + 0) (0x1aa17 : UInt64) /- "ANG_RLL" -/
  let t'2 ← AC_AttitudeControl.get_angle_roll_p this
  PMem.stU64 (((fp + 0) + 16) + 8) t'2
  PMem.stU64 (((fp + 0) + 32) + 0) (0x1aa1f : UInt64) /- "ANG_YAW" -/
  let t'3 ← AC_AttitudeControl.get_angle_yaw_p this
  PMem.stU64 (((fp + 0) + 32) + 8) t'3
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'4 := true
  for _ in PMem.loopFuel do
    if !first'4 then
      let t'5 := i
      let t'6 := (t'5 + 1)
      i := t'6
      pure ()
    first'4 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((48 : UInt64) / (16 : UInt64))))) then break
    let t'7 ← PMem.ldU64 (((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64) + 8)
    let t'8 ← AC_P.kP t'7
    discard <| PMem.memcpy (fp + 48) t'8 4
    let t'9 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 48)
    if !t'9 then
      PMem.stU64 (fp + 56) param_prefix
      let t'10 ← PMem.ldU64 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
      PMem.stU64 (fp + 64) t'10
      let t'11 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1aa27 : UInt64) /- "%s_%s_P must be > 0" -/ (fp + 56)
      discard <| pure (t'11)
      return false
  PMem.stU64 (((fp + 72) + 0) + 0) (0x1aa3b : UInt64) /- "RAT_RLL" -/
  let t'12 ← AC_AttitudeControl_Multi.get_rate_roll_pid this
  PMem.stU64 (((fp + 72) + 0) + 8) t'12
  PMem.stU64 (((fp + 72) + 16) + 0) (0x1aa43 : UInt64) /- "RAT_PIT" -/
  let t'13 ← AC_AttitudeControl_Multi.get_rate_pitch_pid this
  PMem.stU64 (((fp + 72) + 16) + 8) t'13
  PMem.stU64 (((fp + 72) + 32) + 0) (0x1aa4b : UInt64) /- "RAT_YAW" -/
  let t'14 ← AC_AttitudeControl_Multi.get_rate_yaw_pid this
  PMem.stU64 (((fp + 72) + 32) + 8) t'14
  let mut i'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'15 := true
  for _ in PMem.loopFuel do
    if !first'15 then
      let t'16 := i'2
      let t'17 := (t'16 + 1)
      i'2 := t'17
      pure ()
    first'15 := false
    if !((decide ((UInt8.toUInt64 (i'2)) < ((48 : UInt64) / (16 : UInt64))))) then break
    let t'18 ← PMem.ldU64 (((fp + 72) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 16).toUInt64) + 8)
    let pid : UInt64 := t'18
    let t'19 ← PMem.ldU64 ((fp + 72) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 16).toUInt64)
    let mut pid_name : UInt64 := t'19
    let t'20 ← AC_PID.ff pid
    discard <| PMem.memcpy (fp + 120) t'20 4
    let t'21 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 120)
    if t'21 then
      let t'22 ← AC_PID.kP pid
      discard <| PMem.memcpy (fp + 128) t'22 4
      let t'23 ← is_negative'AP_ParamT_float_AP_PARAM_FLOAT (fp + 128)
      if t'23 then
        PMem.stU64 (fp + 136) param_prefix
        PMem.stU64 (fp + 144) pid_name
        let t'24 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1aa53 : UInt64) /- "%s_%s_P must be >= 0" -/ (fp + 136)
        discard <| pure (t'24)
        return false
      let t'25 ← AC_PID.kI pid
      discard <| PMem.memcpy (fp + 152) t'25 4
      let t'26 ← is_negative'AP_ParamT_float_AP_PARAM_FLOAT (fp + 152)
      if t'26 then
        PMem.stU64 (fp + 160) param_prefix
        PMem.stU64 (fp + 168) pid_name
        let t'27 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1aa68 : UInt64) /- "%s_%s_I must be >= 0" -/ (fp + 160)
        discard <| pure (t'27)
        return false
    else
      let t'28 ← AC_PID.kP pid
      discard <| PMem.memcpy (fp + 176) t'28 4
      let t'29 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 176)
      if !t'29 then
        PMem.stU64 (fp + 184) param_prefix
        PMem.stU64 (fp + 192) pid_name
        let t'30 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1aa27 : UInt64) /- "%s_%s_P must be > 0" -/ (fp + 184)
        discard <| pure (t'30)
        return false
      let t'31 ← AC_PID.kI pid
      discard <| PMem.memcpy (fp + 200) t'31 4
      let t'32 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 200)
      if !t'32 then
        PMem.stU64 (fp + 208) param_prefix
        PMem.stU64 (fp + 216) pid_name
        let t'33 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1aa7d : UInt64) /- "%s_%s_I must be > 0" -/ (fp + 208)
        discard <| pure (t'33)
        return false
    let t'34 ← AC_PID.kD pid
    discard <| PMem.memcpy (fp + 224) t'34 4
    let t'35 ← is_negative'AP_ParamT_float_AP_PARAM_FLOAT (fp + 224)
    if t'35 then
      PMem.stU64 (fp + 232) param_prefix
      PMem.stU64 (fp + 240) pid_name
      let t'36 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1aa91 : UInt64) /- "%s_%s_D must be >= 0" -/ (fp + 232)
      discard <| pure (t'36)
      return false
  let t'37 ← AP_ParamTBase'float_4.get (this + 84)
  let t'38 ← PMem.ldF32 t'37
  let mut sc'41 := (decide (t'38 < (Int32.toBinary32 ((10 : Int32)))))
  if !sc'41 then
    let t'39 ← AP_ParamTBase'float_4.get (this + 84)
    let t'40 ← PMem.ldF32 t'39
    sc'41 := (decide (t'40 > (Int32.toBinary32 ((80 : Int32)))))
  if sc'41 then
    PMem.stU64 (fp + 248) param_prefix
    let t'42 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x1aaa6 : UInt64) /- "%s_ANGLE_MAX must be >= 10 and <= 80" -/ (fp + 248)
    discard <| pure (t'42)
    return false
  return true

def AC_AttitudeControl.pre_arm_checks (this : UInt64) (param_prefix : UInt64) (failure_msg : UInt64) (failure_msg_len : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 256
  let r ← AC_AttitudeControl.pre_arm_checks.body fp this param_prefix failure_msg failure_msg_len
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::NE_relax_velocity_controller : void ()`, `AC_PosControl.cpp:514-524`. -/
def AC_PosControl.NE_relax_velocity_controller (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 624)
  let t'2 ← is_positive'float t'1
  if t'2 then
    let t'3 ← PMem.ldF32 (this + 624)
    let t'4 ← PMem.ldF32 (this + 624)
    let mut decay : Binary32 := ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - (t'3 / (t'4 + (Binary32.ofBits 0x3e23d70a /- 39999999/250000000 -/))))
    let t'5 ← Vector3'float.xy (this + 824)
    let t'6 ← Vector2'float.operator__'3 t'5 decay
    discard <| pure (t'6)
  AC_PosControl.NE_init_controller this
  return ()

/-- C++ `AC_AttitudeControl::convert_parameters : void ()`, `AC_AttitudeControl.cpp:1166-1201`. -/
def AC_AttitudeControl.convert_parameters (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.configured (this + 84)
  if t'1 then
    return ()
  AP_Param.convert_old_parameters_scaled (0xdf28 : UInt64) /- &AC_AttitudeControl::convert_parameters(...)::conversion_info_001 -/ (UInt64.toUInt8 (((120 : UInt64) / (24 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- C++ `AC_PosControl::convert_parameters : void ()`, `AC_PosControl.cpp:1810-1921`. -/
def AC_PosControl.convert_parameters.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.find_key_by_pointer this (fp + 0)
  if !t'1 then
    return ()
  let t'2 ← AC_PID.kP (this + 384)
  let t'3 ← AP_Param.configured t'2
  if t'3 then
    return ()
  let t'4 ← PMem.ldU16 (fp + 0)
  AP_Param.convert_old_parameters'2 t'4 (0xdff8 : UInt64) /- &AC_PosControl::convert_parameters(...)::conversion_info -/ (UInt64.toUInt8 (((336 : UInt64) / (16 : UInt64)))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'5 ← PMem.ldU16 (fp + 0)
  AP_Param.convert_old_parameters_scaled'2 t'5 (0xe298 : UInt64) /- &AC_PosControl::convert_parameters(...)::conversion_info_01 -/ (UInt64.toUInt8 (((48 : UInt64) / (16 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'6 ← AC_PID.kP (this + 384)
  AP_Param.save t'6 true
  let t'7 ← PMem.ldU16 (fp + 0)
  AP_Param.convert_old_parameters_scaled'2 t'7 (0xe2f8 : UInt64) /- &AC_PosControl::convert_parameters(...)::conversion_info_001 -/ (UInt64.toUInt8 (((32 : UInt64) / (16 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let t'8 ← PMem.ldU16 (fp + 0)
  AP_Param.convert_old_parameters_scaled'2 t'8 (0xe338 : UInt64) /- &AC_PosControl::convert_parameters(...)::conversion_info_0001 -/ (UInt64.toUInt8 (((16 : UInt64) / (16 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f50624dd2f1a9fc /- 1/1000 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

def AC_PosControl.convert_parameters (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← AC_PosControl.convert_parameters.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl_Multi::parameter_sanity_check : void ()`, `AC_AttitudeControl_Multi.cpp:494-514`. -/
def AC_AttitudeControl_Multi.parameter_sanity_check.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1096)
  let t'2 ← PMem.ldF32 t'1
  let mut sc'5 := (decide (t'2 < (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/)))
  if !sc'5 then
    let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1096)
    let t'4 ← PMem.ldF32 t'3
    sc'5 := (decide (t'4 > (Binary32.ofBits 0x40800000 /- 4 -/)))
  if sc'5 then
    let t'6 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1096)
    let t'7 ← PMem.ldF32 t'6
    let t'8 ← constrain_value_line'float t'7 (Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/))) (Binary32.ofBits 0x40800000 /- 4 -/) (Int32.toUInt32 ((500 : Int32)))
    PMem.stF32 (fp + 0) t'8
    AP_ParamTBase'float_4.set_and_save (this + 1096) (fp + 0)
  let t'9 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1100)
  let t'10 ← PMem.ldF32 t'9
  let mut sc'13 := (decide (t'10 < (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/)))
  if !sc'13 then
    let t'11 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1100)
    let t'12 ← PMem.ldF32 t'11
    sc'13 := (decide (t'12 > (Binary32.ofBits 0x3f000000 /- 1/2 -/)))
  if sc'13 then
    let t'14 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1100)
    let t'15 ← PMem.ldF32 t'14
    let t'16 ← constrain_value_line'float t'15 (Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/))) (Binary32.ofBits 0x3f000000 /- 1/2 -/) (Int32.toUInt32 ((503 : Int32)))
    PMem.stF32 (fp + 4) t'16
    AP_ParamTBase'float_4.set_and_save (this + 1100) (fp + 4)
  let t'17 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1104)
  let t'18 ← PMem.ldF32 t'17
  let mut sc'21 := (decide (t'18 < (Binary32.ofBits 0x3f000000 /- 1/2 -/)))
  if !sc'21 then
    let t'19 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1104)
    let t'20 ← PMem.ldF32 t'19
    sc'21 := (decide (t'20 > (Binary32.ofBits 0x40a00000 /- 5 -/)))
  if sc'21 then
    let t'22 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1104)
    let t'23 ← PMem.ldF32 t'22
    let t'24 ← constrain_value_line'float t'23 (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) (Binary32.ofBits 0x40a00000 /- 5 -/) (Int32.toUInt32 ((508 : Int32)))
    PMem.stF32 (fp + 8) t'24
    AP_ParamTBase'float_4.set_and_save (this + 1104) (fp + 8)
  let t'25 ← AP_ParamT'float_4.operator_ (this + 1100) (this + 1104)
  if t'25 then
    PMem.stF32 (fp + 12) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/)
    AP_ParamTBase'float_4.set_and_save (this + 1100) (fp + 12)
    PMem.stF32 (fp + 16) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
    AP_ParamTBase'float_4.set_and_save (this + 1104) (fp + 16)
  return ()

def AC_AttitudeControl_Multi.parameter_sanity_check (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← AC_AttitudeControl_Multi.parameter_sanity_check.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl_Multi::update_throttle_gain_boost : void ()`, `AC_AttitudeControl_Multi.cpp:416-426`. -/
def AC_AttitudeControl_Multi.update_throttle_gain_boost.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 360)
  let t'2 ← AP_Motors.get_throttle_slew_rate t'1
  if (decide (t'2 > (Binary32.ofBits 0x3f800000 /- 1 -/))) then
    let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1108)
    let t'4 ← PMem.ldF32 t'3
    let t'5 ← constrain_value_line'float (t'4 + (Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) (Int32.toUInt32 ((420 : Int32)))
    let mut pd_boost : Binary32 := t'5
    Vector3'float.Vector3 (fp + 0) pd_boost pd_boost (Binary32.ofBits 0x3f800000 /- 1 -/)
    AC_AttitudeControl.set_PD_scale_mult this (fp + 0)
    let t'6 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1108)
    let t'7 ← PMem.ldF32 t'6
    let t'8 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1108)
    let t'9 ← PMem.ldF32 t'8
    let t'10 ← constrain_value_line'float ((t'7 + (Binary32.ofBits 0x3f800000 /- 1 -/)) * (t'9 + (Binary32.ofBits 0x3f800000 /- 1 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x4010000000000000 /- 4 -/))) (Int32.toUInt32 ((423 : Int32)))
    let mut angle_p_boost : Binary32 := t'10
    Vector3'float.Vector3 (fp + 16) angle_p_boost angle_p_boost (Binary32.ofBits 0x3f800000 /- 1 -/)
    AC_AttitudeControl.set_angle_P_scale_mult this (fp + 16)
  return ()

def AC_AttitudeControl_Multi.update_throttle_gain_boost (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← AC_AttitudeControl_Multi.update_throttle_gain_boost.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl_Multi::update_throttle_rpy_mix : void ()`, `AC_AttitudeControl_Multi.cpp:429-454`. -/
def AC_AttitudeControl_Multi.update_throttle_rpy_mix.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 260)
  let t'2 ← PMem.ldF32 (this + 256)
  if (decide (t'1 < t'2)) then
    let t'3 := (this + 260)
    let t'4 ← PMem.ldF32 t'3
    let t'5 ← PMem.ldF32 (this + 112)
    PMem.stF32 (fp + 0) ((Binary32.ofBits 0x40000000 /- 2 -/) * t'5)
    let t'6 ← PMem.ldF32 (this + 256)
    let t'7 ← PMem.ldF32 (this + 260)
    PMem.stF32 (fp + 4) (t'6 - t'7)
    let t'8 ← MIN'float_float (fp + 0) (fp + 4)
    let t'9 ← PMem.ldF32 t'8
    let t'10 := (t'4 + t'9)
    PMem.stF32 t'3 t'10
  else
    let t'11 ← PMem.ldF32 (this + 260)
    let t'12 ← PMem.ldF32 (this + 256)
    if (decide (t'11 > t'12)) then
      let t'13 := (this + 260)
      let t'14 ← PMem.ldF32 t'13
      let t'15 ← PMem.ldF32 (this + 112)
      PMem.stF32 (fp + 8) ((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'15)
      let t'16 ← PMem.ldF32 (this + 260)
      let t'17 ← PMem.ldF32 (this + 256)
      PMem.stF32 (fp + 12) (t'16 - t'17)
      let t'18 ← MIN'float_float (fp + 8) (fp + 12)
      let t'19 ← PMem.ldF32 t'18
      let t'20 := (t'14 - t'19)
      PMem.stF32 t'13 t'20
      let t'21 ← PMem.ldU64 (this + 360)
      let t'22 ← AP_MotorsMulticopter.get_throttle_hover t'21
      let mut throttle_hover : Binary32 := t'22
      let t'23 ← PMem.ldU64 (this + 360)
      let t'24 ← AP_Motors.get_throttle t'23
      PMem.stF32 (fp + 16) t'24
      let t'25 ← PMem.ldU64 (this + 360)
      let t'26 ← AP_Motors.get_throttle_out t'25
      PMem.stF32 (fp + 20) t'26
      let t'27 ← MAX'float_float (fp + 20) (fp + 16)
      let t'28 ← PMem.ldF32 t'27
      let mut throttle_out : Binary32 := t'28
      if (decide (throttle_out < throttle_hover)) then
        let t'29 ← PMem.ldF32 (fp + 16)
        let t'30 ← PMem.ldF32 (fp + 16)
        let t'31 := ((throttle_out - t'29) / (throttle_hover - t'30))
        PMem.stF32 (fp + 24) t'31
      else
        let t'32 := (throttle_out / throttle_hover)
        PMem.stF32 (fp + 24) t'32
      let t'33 ← MAX'float_float (fp + 24) (this + 256)
      let t'34 ← MIN'float_float (this + 260) t'33
      let t'35 ← PMem.ldF32 t'34
      PMem.stF32 (this + 260) t'35
  let t'36 ← PMem.ldF32 (this + 260)
  let t'37 ← constrain_value_line'float t'36 (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/) (Binary32.ofBits 0x40a00000 /- 5 -/) (Int32.toUInt32 ((453 : Int32)))
  PMem.stF32 (this + 260) t'37
  return ()

def AC_AttitudeControl_Multi.update_throttle_rpy_mix (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← AC_AttitudeControl_Multi.update_throttle_rpy_mix.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl_Multi::rate_controller_run_dt : void (const Vector3f &, float)`, `AC_AttitudeControl_Multi.cpp:456-484`. -/
def AC_AttitudeControl_Multi.rate_controller_run_dt.body (fp : UInt64) (this : UInt64) (gyro_rads : UInt64) (dt : Binary32) : PMem.M Unit := do
  let mut dt := dt
  Vector3'float.Vector3'4 (fp + 0) (this + 180)
  AC_AttitudeControl_Multi.update_throttle_gain_boost this
  AC_AttitudeControl_Multi.update_throttle_rpy_mix this
  let t'1 ← Vector3'float.operator__'3 (fp + 0) (this + 192)
  discard <| pure (t'1)
  discard <| PMem.memcpy (this + 88) gyro_rads 12
  discard <| pure ((this + 88))
  let t'2 := (← PMem.clock)
  PMem.stU64 (this + 104) t'2
  let t'3 ← PMem.ldF32 (fp + 0)
  let t'4 ← PMem.ldF32 gyro_rads
  let t'5 ← PMem.ldU64 (this + 360)
  let t'6 ← PMem.ldB (t'5 + 8)
  let t'7 ← PMem.ldF32 (this + 300)
  let t'8 ← PMem.ldF32 (this + 324)
  let t'9 ← AC_AttitudeControl_Multi.get_rate_roll_pid this
  let t'10 ← AC_PID.update_all t'9 t'3 t'4 dt t'6 t'7 t'8
  let t'11 ← PMem.ldF32 (this + 204)
  let t'12 ← PMem.ldU64 (this + 360)
  AP_Motors.set_roll t'12 (t'10 + t'11)
  let t'13 ← AC_AttitudeControl_Multi.get_rate_roll_pid this
  let t'14 ← AC_PID.get_ff t'13
  let t'15 ← PMem.ldU64 (this + 360)
  AP_Motors.set_roll_ff t'15 t'14
  let t'16 ← PMem.ldF32 ((fp + 0) + 4)
  let t'17 ← PMem.ldF32 (gyro_rads + 4)
  let t'18 ← PMem.ldU64 (this + 360)
  let t'19 ← PMem.ldB ((t'18 + 8) + 1)
  let t'20 ← PMem.ldF32 ((this + 300) + 4)
  let t'21 ← PMem.ldF32 ((this + 324) + 4)
  let t'22 ← AC_AttitudeControl_Multi.get_rate_pitch_pid this
  let t'23 ← AC_PID.update_all t'22 t'16 t'17 dt t'19 t'20 t'21
  let t'24 ← PMem.ldF32 ((this + 204) + 4)
  let t'25 ← PMem.ldU64 (this + 360)
  AP_Motors.set_pitch t'25 (t'23 + t'24)
  let t'26 ← AC_AttitudeControl_Multi.get_rate_pitch_pid this
  let t'27 ← AC_PID.get_ff t'26
  let t'28 ← PMem.ldU64 (this + 360)
  AP_Motors.set_pitch_ff t'28 t'27
  let t'29 ← PMem.ldF32 ((fp + 0) + 8)
  let t'30 ← PMem.ldF32 (gyro_rads + 8)
  let t'31 ← PMem.ldU64 (this + 360)
  let t'32 ← PMem.ldB ((t'31 + 8) + 2)
  let t'33 ← PMem.ldF32 ((this + 300) + 8)
  let t'34 ← PMem.ldF32 ((this + 324) + 8)
  let t'35 ← AC_AttitudeControl_Multi.get_rate_yaw_pid this
  let t'36 ← AC_PID.update_all t'35 t'29 t'30 dt t'32 t'33 t'34
  let t'37 ← PMem.ldF32 ((this + 204) + 8)
  let t'38 ← PMem.ldU64 (this + 360)
  AP_Motors.set_yaw t'38 (t'36 + t'37)
  let t'39 ← AC_AttitudeControl_Multi.get_rate_yaw_pid this
  let t'40 ← AC_PID.get_ff t'39
  let t'41 ← PMem.ldF32 (this + 264)
  let t'42 ← PMem.ldU64 (this + 360)
  AP_Motors.set_yaw_ff t'42 (t'40 * t'41)
  discard <| PMem.memcpy (this + 312) (this + 300) 12
  discard <| pure ((this + 312))
  discard <| PMem.memcpy (this + 336) (this + 324) 12
  discard <| pure ((this + 336))
  discard <| PMem.memcpy (this + 288) (this + 276) 12
  discard <| pure ((this + 288))
  return ()

def AC_AttitudeControl_Multi.rate_controller_run_dt (this : UInt64) (gyro_rads : UInt64) (dt : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_AttitudeControl_Multi.rate_controller_run_dt.body fp this gyro_rads dt
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl_Multi::rate_controller_run : void ()`, `AC_AttitudeControl_Multi.cpp:487-491`. -/
def AC_AttitudeControl_Multi.rate_controller_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 352)
  VehicleBridge.AP_AHRS_View.get_gyro_latest'0 t'1 (fp + 16)
  let t'2 := (fp + 16)
  Vector3'float.Vector3'3 (fp + 0) t'2
  let t'3 ← PMem.ldF32 (this + 112)
  AC_AttitudeControl_Multi.rate_controller_run_dt this (fp + 0) t'3
  return ()

def AC_AttitudeControl_Multi.rate_controller_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← AC_AttitudeControl_Multi.rate_controller_run.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::landed_gain_reduction : void (bool)`, `AC_AttitudeControl.cpp:299-315`. -/
def AC_AttitudeControl.landed_gain_reduction.body (fp : UInt64) (this : UInt64) (landed : Bool) : PMem.M Unit := do
  let mut landed := landed
  discard <| PMem.memcpy (fp + 0) (this + 68) 4
  let t'1 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if t'1 then
    let t'2 ← PMem.ldF32 (this + 112)
    let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'4 ← PMem.ldF32 t'3
    let mut spool_step : Binary32 := (t'2 / ((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * t'4))
    if landed then
      PMem.stF32 (fp + 4) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
      let t'5 ← PMem.ldF32 (this + 348)
      PMem.stF32 (fp + 8) (t'5 + spool_step)
      let t'6 ← MIN'float_float (fp + 4) (fp + 8)
      let t'7 ← PMem.ldF32 t'6
      PMem.stF32 (this + 348) t'7
    else
      PMem.stF32 (fp + 12) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
      let t'8 ← PMem.ldF32 (this + 348)
      PMem.stF32 (fp + 16) (t'8 - spool_step)
      let t'9 ← MAX'float_float (fp + 12) (fp + 16)
      let t'10 ← PMem.ldF32 t'9
      PMem.stF32 (this + 348) t'10
  else
    let mut c'11 : Binary32 := default
    if landed then
      c'11 := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
    else
      c'11 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 (this + 348) c'11
  let t'12 ← PMem.ldF32 (this + 348)
  Vector3'float.operator_ (0x135d0 : UInt64) /- &AC_AttitudeControl::VECTORF_111 -/ (fp + 40) ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - t'12)
  let t'13 := (fp + 40)
  let t'14 ← AP_ParamT'float_4.operator_const_float__'1 (this + 72)
  let t'15 ← PMem.ldF32 t'14
  let t'16 ← AP_ParamT'float_4.operator_const_float__'1 (this + 76)
  let t'17 ← PMem.ldF32 t'16
  let t'18 ← AP_ParamT'float_4.operator_const_float__'1 (this + 80)
  let t'19 ← PMem.ldF32 t'18
  Vector3'float.Vector3 (fp + 56) t'15 t'17 t'19
  let t'20 ← PMem.ldF32 (this + 348)
  Vector3'float.operator_ (fp + 56) (fp + 72) t'20
  let t'21 := (fp + 72)
  Vector3'float.operator_'5 t'13 (fp + 88) t'21
  let t'22 := (fp + 88)
  Vector3'float.Vector3'3 (fp + 24) t'22
  AC_AttitudeControl.set_PD_scale_mult this (fp + 24)
  AC_AttitudeControl.set_angle_P_scale_mult this (fp + 24)
  return ()

def AC_AttitudeControl.landed_gain_reduction (this : UInt64) (landed : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 100
  let r ← AC_AttitudeControl.landed_gain_reduction.body fp this landed
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::D_relax_controller : void (float)`, `AC_PosControl.cpp:882-890`. -/
def AC_PosControl.D_relax_controller (this : UInt64) (throttle_setting : Binary32) : PMem.M Unit := do
  let mut throttle_setting := throttle_setting
  AC_PosControl.D_init_controller this
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AP_MotorsMulticopter.get_throttle_hover t'1
  let t'3 ← PMem.ldF32 (this + 624)
  AC_PID.relax_integrator (this + 384) (-(throttle_setting - t'2)) t'3 (Binary32.ofBits 0x3e23d70a /- 39999999/250000000 -/)
  return ()

/-- C++ `AC_AttitudeControl_Multi::update_althold_lean_angle_max : void (float)`, `AC_AttitudeControl_Multi.cpp:349-362`. -/
def AC_AttitudeControl_Multi.update_althold_lean_angle_max (this : UInt64) (throttle_in : Binary32) : PMem.M Unit := do
  let mut throttle_in := throttle_in
  let t'1 ← PMem.ldU64 (this + 368)
  let t'2 ← AP_MotorsMulticopter.get_throttle_thrust_max t'1
  let mut thr_max : Binary32 := t'2
  let t'3 ← is_zero thr_max
  if t'3 then
    let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 252) t'4
    return ()
  let t'5 ← constrain_value_line'float (throttle_in / ((Binary32.ofBits 0x3f4ccccd /- 800000011/1000000000 -/) * thr_max)) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((360 : Int32)))
  let mut althold_lean_angle_max : Binary32 := (Musl.acosf.acosf t'5)
  let t'6 ← PMem.ldF32 (this + 252)
  let t'7 ← PMem.ldF32 (this + 112)
  let t'8 ← PMem.ldF32 (this + 112)
  let t'9 ← AP_ParamT'float_4.operator_const_float__'1 (this + 64)
  let t'10 ← PMem.ldF32 t'9
  let t'11 ← PMem.ldF32 (this + 252)
  let t'12 := (t'6 + ((t'7 / (t'8 + t'10)) * (althold_lean_angle_max - t'11)))
  PMem.stF32 (this + 252) t'12
  return ()

/-- C++ `AC_AttitudeControl_Multi::get_throttle_avg_max : float (float)`, `AC_AttitudeControl_Multi.cpp:409-413`. -/
def AC_AttitudeControl_Multi.get_throttle_avg_max.body (fp : UInt64) (this : UInt64) (throttle_in : Binary32) : PMem.M Binary32 := do
  PMem.stF32 (fp + 0) throttle_in
  let t'1 ← PMem.ldF32 (fp + 0)
  let t'2 ← constrain_value_line'float t'1 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((411 : Int32)))
  PMem.stF32 (fp + 0) t'2
  let t'3 ← PMem.ldF32 (fp + 0)
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'4 ← PMem.ldF32 (this + 260)
  PMem.stF32 (fp + 12) ((Binary32.ofBits 0x3f800000 /- 1 -/) - t'4)
  let t'5 ← MAX'float_float (fp + 8) (fp + 12)
  let t'6 ← PMem.ldF32 t'5
  let t'7 ← PMem.ldU64 (this + 360)
  let t'8 ← AP_MotorsMulticopter.get_throttle_hover t'7
  let t'9 ← PMem.ldF32 (this + 260)
  PMem.stF32 (fp + 4) ((t'3 * t'6) + (t'8 * t'9))
  let t'10 ← MAX'float_float (fp + 0) (fp + 4)
  let t'11 ← PMem.ldF32 t'10
  return t'11

def AC_AttitudeControl_Multi.get_throttle_avg_max (this : UInt64) (throttle_in : Binary32) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← AC_AttitudeControl_Multi.get_throttle_avg_max.body fp this throttle_in
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl_Multi::set_throttle_out : void (float, bool, float)`, `AC_AttitudeControl_Multi.cpp:364-378`. -/
def AC_AttitudeControl_Multi.set_throttle_out.body (fp : UInt64) (this : UInt64) (throttle_in : Binary32) (apply_angle_boost : Bool) (filter_cutoff : Binary32) : PMem.M Unit := do
  PMem.stF32 (fp + 0) throttle_in
  let mut apply_angle_boost := apply_angle_boost
  let mut filter_cutoff := filter_cutoff
  let t'1 ← PMem.ldF32 (fp + 0)
  PMem.stF32 (this + 240) t'1
  let t'2 ← PMem.ldF32 (fp + 0)
  AC_AttitudeControl_Multi.update_althold_lean_angle_max this t'2
  let t'3 ← PMem.ldU64 (this + 360)
  AP_Motors.set_throttle_filter_cutoff t'3 filter_cutoff
  if apply_angle_boost then
    let t'4 ← PMem.ldF32 (fp + 0)
    let t'5 ← AC_AttitudeControl_Multi.get_throttle_boosted this t'4
    PMem.stF32 (fp + 0) t'5
  else
    let t'6 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 244) t'6
  let t'7 ← PMem.ldF32 (fp + 0)
  let t'8 ← PMem.ldU64 (this + 360)
  AP_Motors.set_throttle t'8 t'7
  let t'9 ← MAX'float_float (fp + 0) (this + 240)
  let t'10 ← PMem.ldF32 t'9
  let t'11 ← AC_AttitudeControl_Multi.get_throttle_avg_max this t'10
  let t'12 ← PMem.ldU64 (this + 360)
  AP_Motors.set_throttle_avg_max t'12 t'11
  return ()

def AC_AttitudeControl_Multi.set_throttle_out (this : UInt64) (throttle_in : Binary32) (apply_angle_boost : Bool) (filter_cutoff : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AC_AttitudeControl_Multi.set_throttle_out.body fp this throttle_in apply_angle_boost filter_cutoff
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::thrust_heading_rotation_angles : void (Quaternion &, const Quaternion &, Vector3f &, float &, float &) const`, `AC_AttitudeControl.cpp:1033-1052`. -/
def AC_AttitudeControl.thrust_heading_rotation_angles.body (fp : UInt64) (this : UInt64) (attitude_target : UInt64) (attitude_body : UInt64) (attitude_error_rad : UInt64) (thrust_angle_rad : UInt64) (thrust_error_angle_rad : UInt64) : PMem.M Unit := do
  QuaternionT'float.QuaternionT (fp + 0)
  AC_AttitudeControl.thrust_vector_rotation_angles this attitude_target attitude_body (fp + 0) attitude_error_rad thrust_angle_rad thrust_error_angle_rad
  QuaternionT'float.QuaternionT (fp + 16)
  let t'1 ← AC_AttitudeControl.get_accel_yaw_max_radss this
  let t'2 ← radians (Binary32.ofBits 0x41200000 /- 10 -/)
  let t'3 ← radians (Binary32.ofBits 0x42f00000 /- 120 -/)
  let t'4 ← constrain_value_line'float (t'1 / (Binary32.ofBits 0x40000000 /- 2 -/)) t'2 t'3 (Int32.toUInt32 ((1043 : Int32)))
  let mut heading_accel_max : Binary32 := t'4
  let t'5 ← AC_AttitudeControl_Multi.get_rate_yaw_pid'2 this
  let t'6 ← AC_PID.kP t'5
  discard <| PMem.memcpy (fp + 32) t'6 4
  let t'7 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 32)
  if !t'7 then
    let t'8 ← AC_AttitudeControl_Multi.get_rate_yaw_pid'2 this
    let t'9 ← AC_PID.kP t'8
    let t'10 ← AP_ParamT'float_4.operator_const_float__'1 t'9
    let t'11 ← PMem.ldF32 t'10
    let t'12 ← AC_P.kP (this + 56)
    let t'13 ← AP_ParamT'float_4.operator_const_float__'1 t'12
    let t'14 ← PMem.ldF32 t'13
    let t'15 ← inv_sqrt_controller ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) / t'11) t'14 heading_accel_max
    PMem.stF32 (fp + 36) t'15
    let t'16 ← radians (Binary32.ofBits 0x42340000 /- 45 -/)
    PMem.stF32 (fp + 40) t'16
    let t'17 ← MIN'float_float (fp + 36) (fp + 40)
    let t'18 ← PMem.ldF32 t'17
    let mut heading_error_max : Binary32 := t'18
    let t'19 ← AC_P.kP (this + 56)
    discard <| PMem.memcpy (fp + 48) t'19 4
    let t'20 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 48)
    let mut sc'22 := !t'20
    if sc'22 then
      let t'21 ← PMem.ldF32 (attitude_error_rad + 8)
      sc'22 := (decide ((Binary32.abs t'21) > heading_error_max))
    if sc'22 then
      let t'23 ← PMem.ldF32 (attitude_error_rad + 8)
      let t'24 ← wrap_PI'float t'23
      let t'25 ← constrain_value_line'float t'24 (-heading_error_max) heading_error_max (Int32.toUInt32 ((1047 : Int32)))
      PMem.stF32 (attitude_error_rad + 8) t'25
      let t'26 ← PMem.ldF32 (attitude_error_rad + 8)
      Vector3'float.Vector3 (fp + 72) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) t'26
      Vector3'float.Vector3'3 (fp + 56) (fp + 72)
      QuaternionT'float.from_axis_angle (fp + 16) (fp + 56)
      QuaternionT'float.operator_ attitude_body (fp + 88) (fp + 0)
      let t'27 := (fp + 88)
      QuaternionT'float.operator_ t'27 (fp + 104) (fp + 16)
      let t'28 := (fp + 104)
      discard <| PMem.memcpy attitude_target t'28 16
      discard <| pure (attitude_target)
  return ()

def AC_AttitudeControl.thrust_heading_rotation_angles (this : UInt64) (attitude_target : UInt64) (attitude_body : UInt64) (attitude_error_rad : UInt64) (thrust_angle_rad : UInt64) (thrust_error_angle_rad : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 120
  let r ← AC_AttitudeControl.thrust_heading_rotation_angles.body fp this attitude_target attitude_body attitude_error_rad thrust_angle_rad thrust_error_angle_rad
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::attitude_controller_run_quat : void ()`, `AC_AttitudeControl.cpp:989-1029`. -/
def AC_AttitudeControl.attitude_controller_run_quat.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  QuaternionT'float.QuaternionT (fp + 0)
  let t'1 ← PMem.ldU64 (this + 352)
  VehicleBridge.AP_AHRS_View.get_quat_body_to_ned'1 t'1 (fp + 0)
  Vector3'float.Vector3'2 (fp + 16)
  AC_AttitudeControl.thrust_heading_rotation_angles this (this + 140) (fp + 0) (fp + 16) (this + 232) (this + 236)
  AC_AttitudeControl.update_ang_vel_target_from_att_error this (fp + 48) (fp + 16)
  let t'2 := (fp + 48)
  Vector3'float.Vector3'3 (fp + 32) t'2
  let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'4 ← PMem.ldF32 t'3
  let t'5 ← radians t'4
  let t'6 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'7 ← PMem.ldF32 t'6
  let t'8 ← radians t'7
  let t'9 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'10 ← PMem.ldF32 t'9
  let t'11 ← radians t'10
  AC_AttitudeControl.ang_vel_limit this (fp + 32) t'5 t'8 t'11
  QuaternionT'float.inverse (fp + 0) (fp + 80)
  let t'12 := (fp + 80)
  QuaternionT'float.operator_ t'12 (fp + 96) (this + 140)
  let t'13 := (fp + 96)
  QuaternionT'float.QuaternionT'3 (fp + 64) t'13
  QuaternionT'float.operator_'2 (fp + 64) (fp + 128) (this + 156)
  let t'14 := (fp + 128)
  Vector3'float.Vector3'3 (fp + 112) t'14
  AC_AttitudeControl.get_latest_gyro this (fp + 160)
  let t'15 := (fp + 160)
  Vector3'float.Vector3'4 (fp + 144) t'15
  let t'16 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  PMem.stF32 (this + 264) t'16
  let t'17 ← PMem.ldF32 (this + 236)
  let t'18 ← radians (Binary32.ofBits 0x41f00000 /- 30 -/)
  if (decide (t'17 > (t'18 * (Binary32.ofBits 0x40000000 /- 2 -/)))) then
    let t'19 ← PMem.ldF32 ((fp + 144) + 8)
    PMem.stF32 ((fp + 32) + 8) t'19
  else
    let t'20 ← PMem.ldF32 (this + 236)
    let t'21 ← radians (Binary32.ofBits 0x41f00000 /- 30 -/)
    if (decide (t'20 > t'21)) then
      let t'22 ← PMem.ldF32 (this + 236)
      let t'23 ← radians (Binary32.ofBits 0x41f00000 /- 30 -/)
      let t'24 ← radians (Binary32.ofBits 0x41f00000 /- 30 -/)
      let t'25 := ((Binary32.ofBits 0x3f800000 /- 1 -/) - ((t'22 - t'23) / t'24))
      PMem.stF32 (this + 264) t'25
      let t'26 ← PMem.ldF32 (fp + 32)
      let t'27 ← PMem.ldF32 (fp + 112)
      let t'28 ← PMem.ldF32 (this + 264)
      let t'29 := (t'26 + (t'27 * t'28))
      PMem.stF32 (fp + 32) t'29
      let t'30 := ((fp + 32) + 4)
      let t'31 ← PMem.ldF32 t'30
      let t'32 ← PMem.ldF32 ((fp + 112) + 4)
      let t'33 ← PMem.ldF32 (this + 264)
      let t'34 := (t'31 + (t'32 * t'33))
      PMem.stF32 t'30 t'34
      let t'35 := ((fp + 32) + 8)
      let t'36 ← PMem.ldF32 t'35
      let t'37 ← PMem.ldF32 ((fp + 112) + 8)
      let t'38 := (t'36 + t'37)
      PMem.stF32 t'35 t'38
      let t'39 ← PMem.ldF32 ((fp + 144) + 8)
      let t'40 ← PMem.ldF32 (this + 264)
      let t'41 ← PMem.ldF32 ((fp + 32) + 8)
      let t'42 ← PMem.ldF32 (this + 264)
      let t'43 := ((t'39 * ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - t'40)) + (t'41 * t'42))
      PMem.stF32 ((fp + 32) + 8) t'43
    else
      let t'44 ← Vector3'float.operator__'3 (fp + 32) (fp + 112)
      discard <| pure (t'44)
  QuaternionT'float.inverse (fp + 0) (fp + 176)
  let t'45 := (fp + 176)
  QuaternionT'float.operator_ t'45 (fp + 192) (this + 140)
  let t'46 := (fp + 192)
  discard <| PMem.memcpy (this + 216) t'46 16
  discard <| pure ((this + 216))
  discard <| PMem.memcpy (this + 180) (fp + 32) 12
  discard <| pure ((this + 180))
  return ()

def AC_AttitudeControl.attitude_controller_run_quat (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 208
  let r ← AC_AttitudeControl.attitude_controller_run_quat.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::input_euler_angle_roll_pitch_euler_rate_yaw_rad : void (float, float, float)`, `AC_AttitudeControl.cpp:404-457`. -/
def AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad.body (fp : UInt64) (this : UInt64) (euler_roll_angle_rad : Binary32) (euler_pitch_angle_rad : Binary32) (euler_yaw_rate_rads : Binary32) : PMem.M Unit := do
  let mut euler_roll_angle_rad := euler_roll_angle_rad
  let mut euler_pitch_angle_rad := euler_pitch_angle_rad
  let mut euler_yaw_rate_rads := euler_yaw_rate_rads
  AC_AttitudeControl.update_attitude_target this
  QuaternionT'float.to_euler'2 (this + 140) (this + 116)
  let t'1 ← AC_AttitudeControl.get_roll_trim_rad this
  let t'2 := (euler_roll_angle_rad + t'1)
  euler_roll_angle_rad := t'2
  let t'3 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 36)
  let t'4 ← PMem.ldI8 t'3
  if t'4 != (0 : Int8) then
    let t'5 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'6 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'7 ← AC_AttitudeControl.get_accel_yaw_max_radss this
    Vector3'float.Vector3 (fp + 16) t'5 t'6 t'7
    AC_AttitudeControl.body_to_euler_limit this (fp + 32) (this + 140) (fp + 16)
    let t'8 := (fp + 32)
    Vector3'float.Vector3'3 (fp + 0) t'8
    let t'9 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
    let t'10 ← PMem.ldF32 t'9
    let t'11 ← radians t'10
    let t'12 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'13 ← PMem.ldF32 t'12
    let t'14 ← radians t'13
    let t'15 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
    let t'16 ← PMem.ldF32 t'15
    let t'17 ← radians t'16
    Vector3'float.Vector3 (fp + 64) t'11 t'14 t'17
    AC_AttitudeControl.body_to_euler_limit this (fp + 80) (this + 140) (fp + 64)
    let t'18 := (fp + 80)
    Vector3'float.Vector3'3 (fp + 48) t'18
    Vector3'float.Vector3'2 (fp + 96)
    let t'19 ← AC_AttitudeControl.body_to_euler_derivative this (this + 140) (this + 168) (fp + 96)
    discard <| pure (t'19)
    let t'20 ← PMem.ldF32 (this + 116)
    let t'21 ← wrap_PI'float (euler_roll_angle_rad - t'20)
    let t'22 ← PMem.ldF32 (fp + 48)
    let t'23 ← PMem.ldF32 (fp + 0)
    let t'24 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'25 ← PMem.ldF32 t'24
    let t'26 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'21 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (this + 128) (fp + 96) (Binary32.abs t'22) t'23 t'25 t'26
    let t'27 ← PMem.ldF32 ((this + 116) + 4)
    let t'28 ← wrap_PI'float (euler_pitch_angle_rad - t'27)
    let t'29 ← PMem.ldF32 ((fp + 48) + 4)
    let t'30 ← PMem.ldF32 ((fp + 0) + 4)
    let t'31 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'32 ← PMem.ldF32 t'31
    let t'33 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'28 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) ((this + 128) + 4) ((fp + 96) + 4) (Binary32.abs t'29) t'30 t'32 t'33
    let t'34 ← PMem.ldF32 ((fp + 48) + 8)
    let t'35 ← PMem.ldF32 ((fp + 0) + 8)
    let t'36 ← PMem.ldF32 (this + 272)
    let t'37 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) euler_yaw_rate_rads ((this + 128) + 8) ((fp + 96) + 8) (Binary32.abs t'34) t'35 t'36 t'37
    AC_AttitudeControl.euler_derivative_to_body this (this + 140) (this + 128) (this + 156)
    AC_AttitudeControl.euler_derivative_to_body this (this + 140) (fp + 96) (this + 168)
  else
    PMem.stF32 (this + 116) euler_roll_angle_rad
    PMem.stF32 ((this + 116) + 4) euler_pitch_angle_rad
    let t'38 := ((this + 116) + 8)
    let t'39 ← PMem.ldF32 t'38
    let t'40 ← PMem.ldF32 (this + 112)
    let t'41 := (t'39 + (euler_yaw_rate_rads * t'40))
    PMem.stF32 t'38 t'41
    let t'42 ← PMem.ldF32 (this + 116)
    let t'43 ← PMem.ldF32 ((this + 116) + 4)
    let t'44 ← PMem.ldF32 ((this + 116) + 8)
    QuaternionT'float.from_euler'2 (this + 140) t'42 t'43 t'44
    Vector3'float.zero (this + 128)
    Vector3'float.zero (this + 156)
    Vector3'float.zero (this + 168)
  AC_AttitudeControl.attitude_controller_run_quat this
  return ()

def AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad (this : UInt64) (euler_roll_angle_rad : Binary32) (euler_pitch_angle_rad : Binary32) (euler_yaw_rate_rads : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 108
  let r ← AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad.body fp this euler_roll_angle_rad euler_pitch_angle_rad euler_yaw_rate_rads
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::get_throttle_with_vibration_override : float ()`, `AC_PosControl.cpp:1470-1485`. -/
def AC_PosControl.get_throttle_with_vibration_override (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AP_MotorsMulticopter.get_throttle_hover t'1
  let mut thr_per_accel_d_mss : Binary32 := (t'2 / (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))
  let t'3 ← PMem.ldU64 (this + 8)
  let t'4 ← PMem.ldB ((t'3 + 8) + 3)
  let mut sc'7 := t'4
  if !sc'7 then
    let t'5 ← PMem.ldU64 (this + 8)
    let t'6 ← PMem.ldB ((t'5 + 8) + 4)
    sc'7 := t'6
  let mut sc'19 := !sc'7
  if !sc'19 then
    let t'8 ← AC_PID.get_i (this + 384)
    let t'9 ← is_positive'float t'8
    let mut sc'12 := t'9
    if sc'12 then
      let t'10 ← AC_PID_Basic.get_error (this + 264)
      let t'11 ← is_negative'float t'10
      sc'12 := t'11
    let mut sc'18 := sc'12
    if !sc'18 then
      let t'13 ← AC_PID.get_i (this + 384)
      let t'14 ← is_negative'float t'13
      let mut sc'17 := t'14
      if sc'17 then
        let t'15 ← AC_PID_Basic.get_error (this + 264)
        let t'16 ← is_positive'float t'15
        sc'17 := t'16
      sc'18 := sc'17
    sc'19 := sc'18
  if sc'19 then
    let t'20 ← AC_PID.get_i (this + 384)
    let t'21 ← PMem.ldF32 (this + 624)
    let t'22 ← AC_PID_Basic.get_error (this + 264)
    let t'23 ← AC_PID_Basic.kP (this + 264)
    let t'24 ← AP_ParamT'float_4.operator_const_float__'1 t'23
    let t'25 ← PMem.ldF32 t'24
    AC_PID.set_integrator (this + 384) (t'20 + ((((t'21 * thr_per_accel_d_mss) * t'22) * t'25) * (Binary32.ofBits 0x3e000000 /- 1/8 -/)))
  let t'26 ← PMem.ldF32 ((this + 824) + 8)
  let t'27 ← AC_PID.get_i (this + 384)
  return ((((Binary32.ofBits 0x3e800000 /- 1/4 -/) * thr_per_accel_d_mss) * t'26) + t'27)

/-- C++ `AC_PosControl::D_update_controller : void ()`, `AC_PosControl.cpp:1079-1162`. -/
def AC_PosControl.D_update_controller (this : UInt64) : PMem.M Unit := do
  AC_PosControl.D_handle_ekf_reset this
  let t'1 ← AC_PosControl.D_is_active this
  if !t'1 then
    AC_PosControl.D_init_controller this
    let t'2 ← AC_PosControl.has_good_timing this
    if t'2 then
      pure ()
  let t'3 ← AP.scheduler
  let t'4 ← AP_Scheduler.ticks32 t'3
  PMem.stU32 (this + 632) t'4
  AC_PosControl.D_update_offsets this
  AC_PosControl.update_terrain this
  let t'5 ← PMem.ldF64 ((this + 728) + 16)
  let t'6 ← PMem.ldF64 ((this + 888) + 16)
  let t'7 ← PMem.ldF32 (this + 852)
  let t'8 := ((t'5 + t'6) + (Binary32.toBinary64 (t'7)))
  PMem.stF64 ((this + 752) + 16) t'8
  let t'9 ← PMem.ldF64 ((this + 704) + 16)
  let t'10 ← AC_P_1D.update_all (this + 60) ((this + 752) + 16) t'9
  PMem.stF32 ((this + 800) + 8) t'10
  let t'11 := ((this + 800) + 8)
  let t'12 ← PMem.ldF32 t'11
  let t'13 ← VehicleBridge.ahrs'0
  let t'14 ← VehicleBridge.AP_AHRS.get_control_gain_scaler_Z'0 t'13
  let t'15 := (t'12 * t'14)
  PMem.stF32 t'11 t'15
  let t'16 ← PMem.ldF64 ((this + 752) + 16)
  let t'17 ← PMem.ldF64 ((this + 888) + 16)
  let t'18 ← PMem.ldF32 (this + 852)
  let t'19 := (t'16 - (t'17 + (Binary32.toBinary64 (t'18))))
  PMem.stF64 ((this + 728) + 16) t'19
  let t'20 := ((this + 800) + 8)
  let t'21 ← PMem.ldF32 t'20
  let t'22 ← PMem.ldF32 ((this + 788) + 8)
  let t'23 ← PMem.ldF32 ((this + 924) + 8)
  let t'24 ← PMem.ldF32 (this + 856)
  let t'25 := (t'21 + ((t'22 + t'23) + t'24))
  PMem.stF32 t'20 t'25
  let t'26 ← PMem.ldF32 ((this + 800) + 8)
  let t'27 ← PMem.ldF32 ((this + 776) + 8)
  let t'28 ← PMem.ldF32 (this + 624)
  let t'29 ← PMem.ldU64 (this + 8)
  let t'30 ← PMem.ldB ((t'29 + 8) + 3)
  let t'31 ← PMem.ldU64 (this + 8)
  let t'32 ← PMem.ldB ((t'31 + 8) + 4)
  let t'33 ← AC_PID_Basic.update_all (this + 264) t'26 t'27 t'28 t'30 t'32
  PMem.stF32 ((this + 824) + 8) t'33
  let t'34 := ((this + 824) + 8)
  let t'35 ← PMem.ldF32 t'34
  let t'36 ← VehicleBridge.ahrs'0
  let t'37 ← VehicleBridge.AP_AHRS.get_control_gain_scaler_Z'0 t'36
  let t'38 := (t'35 * t'37)
  PMem.stF32 t'34 t'38
  let t'39 := ((this + 824) + 8)
  let t'40 ← PMem.ldF32 t'39
  let t'41 ← PMem.ldF32 ((this + 812) + 8)
  let t'42 ← PMem.ldF32 ((this + 948) + 8)
  let t'43 ← PMem.ldF32 (this + 860)
  let t'44 := (t'40 + ((t'41 + t'42) + t'43))
  PMem.stF32 t'39 t'44
  let t'45 ← AC_PosControl.get_estimated_accel_D_mss this
  let mut estimated_accel_d_mss : Binary32 := t'45
  let t'46 ← PMem.ldU64 (this + 8)
  let t'47 ← AP_MotorsMulticopter.get_throttle_hover t'46
  let t'48 ← AC_PID.imax (this + 384)
  if (decide (t'47 > t'48)) then
    let t'49 ← PMem.ldU64 (this + 8)
    let t'50 ← AP_MotorsMulticopter.get_throttle_hover t'49
    AC_PID.set_imax (this + 384) t'50
  let mut thrust_d_norm : Binary32 := default  -- uninitialized in C
  let t'51 ← PMem.ldB (this + 973)
  if t'51 then
    let t'52 ← AC_PosControl.get_throttle_with_vibration_override this
    thrust_d_norm := t'52
  else
    let t'53 ← PMem.ldF32 ((this + 824) + 8)
    let t'54 ← PMem.ldF32 (this + 624)
    let t'55 ← PMem.ldU64 (this + 8)
    let t'56 ← PMem.ldB ((t'55 + 8) + 3)
    let mut sc'59 := t'56
    if !sc'59 then
      let t'57 ← PMem.ldU64 (this + 8)
      let t'58 ← PMem.ldB ((t'57 + 8) + 4)
      sc'59 := t'58
    let t'60 ← AC_PID.update_all (this + 384) t'53 estimated_accel_d_mss t'54 sc'59 (Binary32.ofBits 0x3f800000 /- 1 -/) (Binary32.ofBits 0x3f800000 /- 1 -/)
    thrust_d_norm := t'60
    let t'61 ← AC_PID.get_ff (this + 384)
    let t'62 := (thrust_d_norm + t'61)
    thrust_d_norm := t'62
  let t'63 ← PMem.ldU64 (this + 8)
  let t'64 ← AP_MotorsMulticopter.get_throttle_hover t'63
  let t'65 := (thrust_d_norm - t'64)
  thrust_d_norm := t'65
  let t'66 ← PMem.ldU64 (this + 16)
  AC_AttitudeControl_Multi.set_throttle_out t'66 (-thrust_d_norm) true (Binary32.ofBits 0x40000000 /- 2 -/)
  let t'67 ← AC_PID_Basic.get_error (this + 264)
  let t'68 ← PMem.ldF32 (this + 644)
  let mut error_ratio : Binary32 := (t'67 / t'68)
  let t'69 := (this + 664)
  let t'70 ← PMem.ldF32 t'69
  let t'71 ← PMem.ldF32 (this + 624)
  let t'72 := (t'70 + ((t'71 * (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/)) * ((Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) - error_ratio)))
  PMem.stF32 t'69 t'72
  let t'73 ← PMem.ldF32 (this + 664)
  let t'74 ← constrain_value_line'float t'73 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x40000000 /- 2 -/) (Int32.toUInt32 ((1152 : Int32)))
  PMem.stF32 (this + 664) t'74
  let t'75 ← PMem.ldU64 (this + 8)
  let t'76 ← PMem.ldB ((t'75 + 8) + 4)
  if t'76 then
    let t'77 := -(Binary32.ofBits 0x3f800000 /- 1 -/)
    PMem.stF32 ((this + 836) + 8) t'77
  else
    let t'78 ← PMem.ldU64 (this + 8)
    let t'79 ← PMem.ldB ((t'78 + 8) + 3)
    if t'79 then
      let t'80 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 ((this + 836) + 8) t'80
    else
      let t'81 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 ((this + 836) + 8) t'81
  return ()

/-- C++ `AC_PosControl::NE_update_controller : void ()`, `AC_PosControl.cpp:697-788`. -/
def AC_PosControl.NE_update_controller.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AC_PosControl.NE_handle_ekf_reset this
  let t'1 ← AC_PosControl.NE_is_active this
  if !t'1 then
    AC_PosControl.NE_init_controller this
    let t'2 ← AC_PosControl.has_good_timing this
    if t'2 then
      pure ()
  let t'3 ← AP.scheduler
  let t'4 ← AP_Scheduler.ticks32 t'3
  PMem.stU32 (this + 628) t'4
  let t'5 ← VehicleBridge.ahrs'0
  let t'6 ← VehicleBridge.AP_AHRS.get_control_gain_scaler_XY'0 t'5
  let mut ahrsControlScaleXY : Binary32 := t'6
  AC_PosControl.NE_update_offsets this
  let t'7 ← Vector3'double.xy (this + 752)
  let t'8 ← Vector3'double.xy (this + 728)
  let t'9 ← Vector3'double.xy (this + 888)
  Vector2'double.operator_'2 t'8 (fp + 0) t'9
  let t'10 := (fp + 0)
  discard <| PMem.memcpy t'7 t'10 16
  discard <| pure (t'7)
  let t'11 ← Vector3'double.xy (this + 704)
  Vector2'double.Vector2'4 (fp + 16) t'11
  Vector2'float.todouble (this + 668) (fp + 32)
  let t'12 := (fp + 32)
  let t'13 ← Vector2'double.operator__'2 (fp + 16) t'12
  discard <| pure (t'13)
  let t'14 ← Vector3'double.xy (this + 752)
  AC_P_2D.update_all (this + 36) (fp + 56) t'14 (fp + 16)
  let t'15 := (fp + 56)
  Vector2'float.Vector2'3 (fp + 48) t'15
  let t'16 ← Vector3'double.xy (this + 728)
  let t'17 ← Vector3'double.xy (this + 752)
  let t'18 ← Vector3'double.xy (this + 888)
  Vector2'double.operator_ t'17 (fp + 64) t'18
  let t'19 := (fp + 64)
  discard <| PMem.memcpy t'16 t'19 16
  discard <| pure (t'16)
  let t'20 ← Vector2'float.operator__'3 (fp + 48) ahrsControlScaleXY
  discard <| pure (t'20)
  let t'21 ← PMem.ldF32 (this + 684)
  let t'22 ← Vector2'float.operator__'3 (fp + 48) t'21
  discard <| pure (t'22)
  let t'23 ← Vector3'float.xy (this + 800)
  discard <| PMem.memcpy t'23 (fp + 48) 8
  discard <| pure (t'23)
  let t'24 ← Vector3'float.xy (this + 800)
  let t'25 ← Vector3'float.xy (this + 788)
  let t'26 ← Vector3'float.xy (this + 924)
  Vector2'float.operator_'3 t'25 (fp + 80) t'26
  let t'27 := (fp + 80)
  let t'28 ← Vector2'float.operator__ t'24 t'27
  discard <| pure (t'28)
  let t'29 ← Vector3'float.xy (this + 776)
  Vector2'float.Vector2'4 (fp + 88) t'29
  let t'30 ← Vector2'float.operator__ (fp + 88) (this + 676)
  discard <| pure (t'30)
  let t'31 ← Vector3'float.xy (this + 800)
  let t'32 ← PMem.ldF32 (this + 624)
  let t'33 ← Vector3'float.xy (this + 836)
  AC_PID_2D.update_all (this + 84) (fp + 104) t'31 (fp + 88) t'32 t'33
  let t'34 := (fp + 104)
  Vector2'float.Vector2'3 (fp + 96) t'34
  let t'35 ← Vector2'float.operator__'3 (fp + 96) ahrsControlScaleXY
  discard <| pure (t'35)
  let t'36 ← PMem.ldF32 (this + 684)
  let t'37 ← Vector2'float.operator__'3 (fp + 96) t'36
  discard <| pure (t'37)
  let t'38 := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  PMem.stF32 (this + 684) t'38
  let t'39 ← Vector3'float.xy (this + 824)
  discard <| PMem.memcpy t'39 (fp + 96) 8
  discard <| pure (t'39)
  let t'40 ← Vector3'float.xy (this + 824)
  let t'41 ← Vector3'float.xy (this + 812)
  let t'42 ← Vector3'float.xy (this + 948)
  Vector2'float.operator_'3 t'41 (fp + 112) t'42
  let t'43 := (fp + 112)
  let t'44 ← Vector2'float.operator__ t'40 t'43
  discard <| pure (t'44)
  let t'45 ← PMem.ldU64 (this + 16)
  let t'46 ← AC_AttitudeControl.get_althold_lean_angle_max_rad t'45
  PMem.stF32 (fp + 120) t'46
  let t'47 ← AC_PosControl.get_lean_angle_max_rad this
  PMem.stF32 (fp + 124) t'47
  let t'48 ← MIN'float_float (fp + 120) (fp + 124)
  let t'49 ← PMem.ldF32 t'48
  let mut angle_max_rad : Binary32 := t'49
  let t'50 ← angle_rad_to_accel_mss angle_max_rad
  let mut accel_max_mss : Binary32 := t'50
  let t'51 ← Vector3'float.xy (this + 836)
  let t'52 ← Vector3'float.xy (this + 824)
  discard <| PMem.memcpy t'51 t'52 8
  discard <| pure (t'51)
  Vector2'float.Vector2 (fp + 128)
  let t'53 ← PMem.ldF32 (this + 636)
  let t'54 ← is_positive'float t'53
  if t'54 then
    let t'55 ← Vector3'float.xy (this + 788)
    let t'56 ← PMem.ldF32 (this + 636)
    Vector2'float.operator_'5 t'55 (fp + 136) t'56
    let t'57 := (fp + 136)
    discard <| PMem.memcpy (fp + 128) t'57 8
    discard <| pure ((fp + 128))
  let t'58 ← Vector3'float.xy (this + 824)
  let t'59 ← limit_accel_xy (fp + 128) t'58 accel_max_mss
  if !t'59 then
    let t'60 ← Vector3'float.xy (this + 836)
    Vector2'float.zero t'60
  let t'61 ← PMem.ldF32 (this + 824)
  let t'62 ← PMem.ldF32 ((this + 824) + 4)
  AC_PosControl.accel_NE_mss_to_lean_angles_rad this t'61 t'62 (this + 688) (this + 692)
  AC_PosControl.calculate_yaw_and_rate_yaw this
  Vector2'float.zero (this + 668)
  Vector2'float.zero (this + 676)
  return ()

def AC_PosControl.NE_update_controller (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 144
  let r ← AC_PosControl.NE_update_controller.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::input_thrust_vector_rate_heading_rads : void (const Vector3f &, float, bool)`, `AC_AttitudeControl.cpp:832-885`. -/
def AC_AttitudeControl.input_thrust_vector_rate_heading_rads.body (fp : UInt64) (this : UInt64) (thrust_vector : UInt64) (heading_rate_rads : Binary32) (slew_yaw : Bool) : PMem.M Unit := do
  let mut heading_rate_rads := heading_rate_rads
  let mut slew_yaw := slew_yaw
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← radians t'2
  let mut yaw_rate_max_rads : Binary32 := t'3
  if slew_yaw then
    let t'4 ← AC_AttitudeControl.get_slew_yaw_max_rads this
    yaw_rate_max_rads := t'4
  AC_AttitudeControl.update_attitude_target this
  QuaternionT'float.to_euler'2 (this + 140) (this + 116)
  Vector3'float.Vector3'4 (fp + 16) thrust_vector
  AC_AttitudeControl.attitude_from_thrust_vector this (fp + 32) (fp + 16) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'5 := (fp + 32)
  QuaternionT'float.QuaternionT'3 (fp + 0) t'5
  QuaternionT'float.QuaternionT (fp + 56)
  Vector3'float.Vector3'2 (fp + 72)
  AC_AttitudeControl.thrust_vector_rotation_angles this (fp + 0) (this + 140) (fp + 56) (fp + 72) (fp + 88) (fp + 48)
  let t'6 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 36)
  let t'7 ← PMem.ldI8 t'6
  if t'7 != (0 : Int8) then
    let t'8 ← PMem.ldF32 (fp + 72)
    let t'9 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
    let t'10 ← PMem.ldF32 t'9
    let t'11 ← radians t'10
    let t'12 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'13 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'14 ← PMem.ldF32 t'13
    let t'15 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'8 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (this + 156) (this + 168) t'11 t'12 t'14 t'15
    let t'16 ← PMem.ldF32 ((fp + 72) + 4)
    let t'17 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'18 ← PMem.ldF32 t'17
    let t'19 ← radians t'18
    let t'20 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'21 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'22 ← PMem.ldF32 t'21
    let t'23 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'16 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) ((this + 156) + 4) ((this + 168) + 4) t'19 t'20 t'22 t'23
    let t'24 ← AC_AttitudeControl.get_accel_yaw_max_radss this
    let t'25 ← PMem.ldF32 (this + 272)
    let t'26 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) heading_rate_rads ((this + 156) + 8) ((this + 168) + 8) yaw_rate_max_rads t'24 t'25 t'26
  else
    let t'27 ← is_positive'float yaw_rate_max_rads
    if t'27 then
      let t'28 ← constrain_value_line'float heading_rate_rads (-yaw_rate_max_rads) yaw_rate_max_rads (Int32.toUInt32 ((867 : Int32)))
      heading_rate_rads := t'28
    QuaternionT'float.QuaternionT (fp + 96)
    let t'29 ← PMem.ldF32 (this + 112)
    Vector3'float.Vector3 (fp + 128) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (heading_rate_rads * t'29)
    Vector3'float.Vector3'3 (fp + 112) (fp + 128)
    QuaternionT'float.from_axis_angle (fp + 96) (fp + 112)
    QuaternionT'float.operator_ (this + 140) (fp + 144) (fp + 56)
    let t'30 := (fp + 144)
    QuaternionT'float.operator_ t'30 (fp + 160) (fp + 96)
    let t'31 := (fp + 160)
    discard <| PMem.memcpy (this + 140) t'31 16
    discard <| pure ((this + 140))
    QuaternionT'float.normalize (this + 140)
    Vector3'float.zero (this + 128)
    Vector3'float.zero (this + 156)
    Vector3'float.zero (this + 168)
  let t'32 ← AC_AttitudeControl.body_to_euler_derivative this (this + 140) (this + 156) (this + 128)
  discard <| pure (t'32)
  AC_AttitudeControl.attitude_controller_run_quat this
  return ()

def AC_AttitudeControl.input_thrust_vector_rate_heading_rads (this : UInt64) (thrust_vector : UInt64) (heading_rate_rads : Binary32) (slew_yaw : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 176
  let r ← AC_AttitudeControl.input_thrust_vector_rate_heading_rads.body fp this thrust_vector heading_rate_rads slew_yaw
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::input_thrust_vector_heading_rad : void (const Vector3f &, float, float)`, `AC_AttitudeControl.cpp:890-929`. -/
def AC_AttitudeControl.input_thrust_vector_heading_rad.body (fp : UInt64) (this : UInt64) (thrust_vector : UInt64) (heading_angle_rad : Binary32) (heading_rate_rads : Binary32) : PMem.M Unit := do
  let mut heading_angle_rad := heading_angle_rad
  let mut heading_rate_rads := heading_rate_rads
  AC_AttitudeControl.update_attitude_target this
  QuaternionT'float.to_euler'2 (this + 140) (this + 116)
  Vector3'float.Vector3'4 (fp + 16) thrust_vector
  AC_AttitudeControl.attitude_from_thrust_vector this (fp + 32) (fp + 16) heading_angle_rad
  let t'1 := (fp + 32)
  QuaternionT'float.QuaternionT'3 (fp + 0) t'1
  let t'2 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 36)
  let t'3 ← PMem.ldI8 t'2
  if t'3 != (0 : Int8) then
    Vector3'float.Vector3'2 (fp + 48)
    QuaternionT'float.QuaternionT (fp + 72)
    AC_AttitudeControl.thrust_vector_rotation_angles this (fp + 0) (this + 140) (fp + 72) (fp + 48) (fp + 88) (fp + 64)
    let t'4 ← PMem.ldF32 (fp + 48)
    let t'5 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
    let t'6 ← PMem.ldF32 t'5
    let t'7 ← radians t'6
    let t'8 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'9 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'10 ← PMem.ldF32 t'9
    let t'11 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'4 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (this + 156) (this + 168) t'7 t'8 t'10 t'11
    let t'12 ← PMem.ldF32 ((fp + 48) + 4)
    let t'13 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'14 ← PMem.ldF32 t'13
    let t'15 ← radians t'14
    let t'16 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'17 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'18 ← PMem.ldF32 t'17
    let t'19 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'12 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) ((this + 156) + 4) ((this + 168) + 4) t'15 t'16 t'18 t'19
    let t'20 ← PMem.ldF32 ((fp + 48) + 8)
    let t'21 ← AC_AttitudeControl.get_slew_yaw_max_rads this
    let t'22 ← AC_AttitudeControl.get_accel_yaw_max_radss this
    let t'23 ← PMem.ldF32 (this + 272)
    let t'24 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'20 heading_rate_rads ((this + 156) + 8) ((this + 168) + 8) t'21 t'22 t'23 t'24
  else
    discard <| PMem.memcpy (this + 140) (fp + 0) 16
    discard <| pure ((this + 140))
    Vector3'float.zero (this + 128)
    Vector3'float.zero (this + 156)
    Vector3'float.zero (this + 168)
  let t'25 ← AC_AttitudeControl.body_to_euler_derivative this (this + 140) (this + 156) (this + 128)
  discard <| pure (t'25)
  AC_AttitudeControl.attitude_controller_run_quat this
  return ()

def AC_AttitudeControl.input_thrust_vector_heading_rad (this : UInt64) (thrust_vector : UInt64) (heading_angle_rad : Binary32) (heading_rate_rads : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 92
  let r ← AC_AttitudeControl.input_thrust_vector_heading_rad.body fp this thrust_vector heading_angle_rad heading_rate_rads
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::input_thrust_vector_heading : void (const Vector3f &, HeadingCommand)`, `AC_AttitudeControl.cpp:932-945`. -/
def AC_AttitudeControl.input_thrust_vector_heading (this : UInt64) (thrust_vector : UInt64) (heading : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI32 (heading + 8)
  let sw'2 := t'1
  if sw'2 == (2 : Int32) then
    let t'3 ← PMem.ldF32 (heading + 4)
    AC_AttitudeControl.input_thrust_vector_rate_heading_rads this thrust_vector t'3 true
  else if sw'2 == (0 : Int32) then
    let t'4 ← PMem.ldF32 heading
    AC_AttitudeControl.input_thrust_vector_heading_rad this thrust_vector t'4 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  else if sw'2 == (1 : Int32) then
    let t'5 ← PMem.ldF32 heading
    let t'6 ← PMem.ldF32 (heading + 4)
    AC_AttitudeControl.input_thrust_vector_heading_rad this thrust_vector t'5 t'6
  else
    pure ()
  return ()

/-- C++ `AC_AttitudeControl::input_rate_bf_roll_pitch_yaw_rads : void (float, float, float)`, `AC_AttitudeControl.cpp:609-641`. -/
def AC_AttitudeControl.input_rate_bf_roll_pitch_yaw_rads.body (fp : UInt64) (this : UInt64) (roll_rate_bf_rads : Binary32) (pitch_rate_bf_rads : Binary32) (yaw_rate_bf_rads : Binary32) : PMem.M Unit := do
  let mut roll_rate_bf_rads := roll_rate_bf_rads
  let mut pitch_rate_bf_rads := pitch_rate_bf_rads
  let mut yaw_rate_bf_rads := yaw_rate_bf_rads
  AC_AttitudeControl.update_attitude_target this
  QuaternionT'float.to_euler'2 (this + 140) (this + 116)
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 36)
  let t'2 ← PMem.ldI8 t'1
  if t'2 != (0 : Int8) then
    let t'3 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'4 ← PMem.ldF32 (this + 268)
    let t'5 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) roll_rate_bf_rads (this + 156) (this + 168) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'3 t'4 t'5
    let t'6 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'7 ← PMem.ldF32 (this + 268)
    let t'8 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) pitch_rate_bf_rads ((this + 156) + 4) ((this + 168) + 4) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'6 t'7 t'8
    let t'9 ← AC_AttitudeControl.get_accel_yaw_max_radss this
    let t'10 ← PMem.ldF32 (this + 272)
    let t'11 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) yaw_rate_bf_rads ((this + 156) + 8) ((this + 168) + 8) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'9 t'10 t'11
    let t'12 ← AC_AttitudeControl.body_to_euler_derivative this (this + 140) (this + 156) (this + 128)
    discard <| pure (t'12)
  else
    QuaternionT'float.QuaternionT (fp + 0)
    Vector3'float.Vector3 (fp + 32) roll_rate_bf_rads pitch_rate_bf_rads yaw_rate_bf_rads
    let t'13 ← PMem.ldF32 (this + 112)
    Vector3'float.operator_ (fp + 32) (fp + 48) t'13
    let t'14 := (fp + 48)
    Vector3'float.Vector3'3 (fp + 16) t'14
    QuaternionT'float.from_axis_angle (fp + 0) (fp + 16)
    QuaternionT'float.operator_ (this + 140) (fp + 64) (fp + 0)
    let t'15 := (fp + 64)
    discard <| PMem.memcpy (this + 140) t'15 16
    discard <| pure ((this + 140))
    QuaternionT'float.normalize (this + 140)
    Vector3'float.zero (this + 128)
    Vector3'float.zero (this + 156)
    Vector3'float.zero (this + 168)
  AC_AttitudeControl.attitude_controller_run_quat this
  return ()

def AC_AttitudeControl.input_rate_bf_roll_pitch_yaw_rads (this : UInt64) (roll_rate_bf_rads : Binary32) (pitch_rate_bf_rads : Binary32) (yaw_rate_bf_rads : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 80
  let r ← AC_AttitudeControl.input_rate_bf_roll_pitch_yaw_rads.body fp this roll_rate_bf_rads pitch_rate_bf_rads yaw_rate_bf_rads
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::input_quaternion : void (Quaternion &, Vector3f)`, `AC_AttitudeControl.cpp:344-386`. -/
def AC_AttitudeControl.input_quaternion.body (fp : UInt64) (this : UInt64) (attitude_desired_quat : UInt64) (ang_vel_body_rads : UInt64) : PMem.M Unit := do
  AC_AttitudeControl.update_attitude_target this
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← radians t'2
  let t'4 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'5 ← PMem.ldF32 t'4
  let t'6 ← radians t'5
  let t'7 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'8 ← PMem.ldF32 t'7
  let t'9 ← radians t'8
  AC_AttitudeControl.ang_vel_limit this ang_vel_body_rads t'3 t'6 t'9
  QuaternionT'float.operator_'2 attitude_desired_quat (fp + 16) ang_vel_body_rads
  let t'10 := (fp + 16)
  Vector3'float.Vector3'3 (fp + 0) t'10
  let t'11 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 36)
  let t'12 ← PMem.ldI8 t'11
  if t'12 != (0 : Int8) then
    QuaternionT'float.inverse (this + 140) (fp + 48)
    let t'13 := (fp + 48)
    QuaternionT'float.operator_ t'13 (fp + 64) attitude_desired_quat
    let t'14 := (fp + 64)
    QuaternionT'float.QuaternionT'3 (fp + 32) t'14
    Vector3'float.Vector3'2 (fp + 80)
    QuaternionT'float.to_axis_angle (fp + 32) (fp + 80)
    let t'15 ← PMem.ldF32 (fp + 80)
    let t'16 ← wrap_PI'float t'15
    let t'17 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
    let t'18 ← PMem.ldF32 t'17
    let t'19 ← radians t'18
    let t'20 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'21 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'22 ← PMem.ldF32 t'21
    let t'23 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'16 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (this + 156) (this + 168) t'19 t'20 t'22 t'23
    let t'24 ← PMem.ldF32 ((fp + 80) + 4)
    let t'25 ← wrap_PI'float t'24
    let t'26 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'27 ← PMem.ldF32 t'26
    let t'28 ← radians t'27
    let t'29 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'30 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'31 ← PMem.ldF32 t'30
    let t'32 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'25 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) ((this + 156) + 4) ((this + 168) + 4) t'28 t'29 t'31 t'32
    let t'33 ← PMem.ldF32 ((fp + 80) + 8)
    let t'34 ← wrap_PI'float t'33
    let t'35 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
    let t'36 ← PMem.ldF32 t'35
    let t'37 ← radians t'36
    let t'38 ← AC_AttitudeControl.get_accel_yaw_max_radss this
    let t'39 ← PMem.ldF32 (this + 272)
    let t'40 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'34 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) ((this + 156) + 8) ((this + 168) + 8) t'37 t'38 t'39 t'40
  else
    discard <| PMem.memcpy (this + 140) attitude_desired_quat 16
    discard <| pure ((this + 140))
    discard <| PMem.memcpy (this + 156) (fp + 0) 12
    discard <| pure ((this + 156))
  QuaternionT'float.to_euler'2 (this + 140) (this + 116)
  let t'41 ← AC_AttitudeControl.body_to_euler_derivative this (this + 140) (this + 156) (this + 128)
  discard <| pure (t'41)
  QuaternionT'float.QuaternionT (fp + 96)
  let t'42 ← PMem.ldF32 (this + 112)
  Vector3'float.operator_ (fp + 0) (fp + 128) t'42
  let t'43 := (fp + 128)
  Vector3'float.Vector3'3 (fp + 112) t'43
  QuaternionT'float.from_axis_angle (fp + 96) (fp + 112)
  QuaternionT'float.operator_ attitude_desired_quat (fp + 144) (fp + 96)
  let t'44 := (fp + 144)
  discard <| PMem.memcpy attitude_desired_quat t'44 16
  discard <| pure (attitude_desired_quat)
  QuaternionT'float.normalize attitude_desired_quat
  AC_AttitudeControl.attitude_controller_run_quat this
  return ()

def AC_AttitudeControl.input_quaternion (this : UInt64) (attitude_desired_quat : UInt64) (ang_vel_body_rads : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 160
  let r ← AC_AttitudeControl.input_quaternion.body fp this attitude_desired_quat ang_vel_body_rads
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::input_euler_angle_roll_pitch_yaw_rad : void (float, float, float, bool)`, `AC_AttitudeControl.cpp:476-536`. -/
def AC_AttitudeControl.input_euler_angle_roll_pitch_yaw_rad.body (fp : UInt64) (this : UInt64) (euler_roll_angle_rad : Binary32) (euler_pitch_angle_rad : Binary32) (euler_yaw_angle_rad : Binary32) (slew_yaw : Bool) : PMem.M Unit := do
  let mut euler_roll_angle_rad := euler_roll_angle_rad
  let mut euler_pitch_angle_rad := euler_pitch_angle_rad
  let mut euler_yaw_angle_rad := euler_yaw_angle_rad
  let mut slew_yaw := slew_yaw
  AC_AttitudeControl.update_attitude_target this
  QuaternionT'float.to_euler'2 (this + 140) (this + 116)
  let t'1 ← AC_AttitudeControl.get_roll_trim_rad this
  let t'2 := (euler_roll_angle_rad + t'1)
  euler_roll_angle_rad := t'2
  let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'4 ← PMem.ldF32 t'3
  let t'5 ← radians t'4
  let mut yaw_rate_max_rads : Binary32 := t'5
  if slew_yaw then
    let t'6 ← AC_AttitudeControl.get_slew_yaw_max_rads this
    yaw_rate_max_rads := t'6
  let t'7 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 36)
  let t'8 ← PMem.ldI8 t'7
  if t'8 != (0 : Int8) then
    let t'9 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'10 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'11 ← AC_AttitudeControl.get_accel_yaw_max_radss this
    Vector3'float.Vector3 (fp + 16) t'9 t'10 t'11
    AC_AttitudeControl.body_to_euler_limit this (fp + 32) (this + 140) (fp + 16)
    let t'12 := (fp + 32)
    Vector3'float.Vector3'3 (fp + 0) t'12
    let t'13 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
    let t'14 ← PMem.ldF32 t'13
    let t'15 ← radians t'14
    let t'16 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'17 ← PMem.ldF32 t'16
    let t'18 ← radians t'17
    Vector3'float.Vector3 (fp + 64) t'15 t'18 yaw_rate_max_rads
    AC_AttitudeControl.body_to_euler_limit this (fp + 80) (this + 140) (fp + 64)
    let t'19 := (fp + 80)
    Vector3'float.Vector3'3 (fp + 48) t'19
    Vector3'float.Vector3'2 (fp + 96)
    let t'20 ← AC_AttitudeControl.body_to_euler_derivative this (this + 140) (this + 168) (fp + 96)
    discard <| pure (t'20)
    let t'21 ← PMem.ldF32 (this + 116)
    let t'22 ← wrap_PI'float (euler_roll_angle_rad - t'21)
    let t'23 ← PMem.ldF32 (fp + 48)
    let t'24 ← PMem.ldF32 (fp + 0)
    let t'25 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'26 ← PMem.ldF32 t'25
    let t'27 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'22 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (this + 128) (fp + 96) (Binary32.abs t'23) t'24 t'26 t'27
    let t'28 ← PMem.ldF32 ((this + 116) + 4)
    let t'29 ← wrap_PI'float (euler_pitch_angle_rad - t'28)
    let t'30 ← PMem.ldF32 ((fp + 48) + 4)
    let t'31 ← PMem.ldF32 ((fp + 0) + 4)
    let t'32 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'33 ← PMem.ldF32 t'32
    let t'34 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'29 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) ((this + 128) + 4) ((fp + 96) + 4) (Binary32.abs t'30) t'31 t'33 t'34
    let t'35 ← PMem.ldF32 ((this + 116) + 8)
    let t'36 ← wrap_PI'float (euler_yaw_angle_rad - t'35)
    let t'37 ← PMem.ldF32 ((fp + 48) + 8)
    let t'38 ← PMem.ldF32 ((fp + 0) + 8)
    let t'39 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'40 ← PMem.ldF32 t'39
    let t'41 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'36 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) ((this + 128) + 8) ((fp + 96) + 8) (Binary32.abs t'37) t'38 t'40 t'41
    AC_AttitudeControl.euler_derivative_to_body this (this + 140) (this + 128) (this + 156)
    AC_AttitudeControl.euler_derivative_to_body this (this + 140) (fp + 96) (this + 168)
  else
    PMem.stF32 (this + 116) euler_roll_angle_rad
    PMem.stF32 ((this + 116) + 4) euler_pitch_angle_rad
    let t'42 ← is_positive'float yaw_rate_max_rads
    if t'42 then
      let t'43 ← PMem.ldF32 ((this + 116) + 8)
      let t'44 ← wrap_PI'float (euler_yaw_angle_rad - t'43)
      let mut yaw_error : Binary32 := t'44
      let t'45 ← PMem.ldF32 (this + 112)
      let t'46 ← PMem.ldF32 (this + 112)
      let t'47 ← constrain_value_line'float yaw_error ((-yaw_rate_max_rads) * t'45) (yaw_rate_max_rads * t'46) (Int32.toUInt32 ((519 : Int32)))
      let mut yaw_step : Binary32 := t'47
      let t'48 ← PMem.ldF32 ((this + 116) + 8)
      let t'49 ← wrap_PI'float (t'48 + yaw_step)
      PMem.stF32 ((this + 116) + 8) t'49
    else
      PMem.stF32 ((this + 116) + 8) euler_yaw_angle_rad
    let t'50 ← PMem.ldF32 (this + 116)
    let t'51 ← PMem.ldF32 ((this + 116) + 4)
    let t'52 ← PMem.ldF32 ((this + 116) + 8)
    QuaternionT'float.from_euler'2 (this + 140) t'50 t'51 t'52
    Vector3'float.zero (this + 128)
    Vector3'float.zero (this + 156)
    Vector3'float.zero (this + 168)
  AC_AttitudeControl.attitude_controller_run_quat this
  return ()

def AC_AttitudeControl.input_euler_angle_roll_pitch_yaw_rad (this : UInt64) (euler_roll_angle_rad : Binary32) (euler_pitch_angle_rad : Binary32) (euler_yaw_angle_rad : Binary32) (slew_yaw : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 108
  let r ← AC_AttitudeControl.input_euler_angle_roll_pitch_yaw_rad.body fp this euler_roll_angle_rad euler_pitch_angle_rad euler_yaw_angle_rad slew_yaw
  PMem.leave fp
  return r

end Vehicle_lib
