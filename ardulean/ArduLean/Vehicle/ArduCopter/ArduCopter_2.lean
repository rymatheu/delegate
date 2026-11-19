import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_PID.AC_PID
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl
import ArduLean.Vehicle.libraries.AC_WPNav.AC_WPNav
import ArduLean.Vehicle.libraries.AP_SurfaceDistance.AP_SurfaceDistance
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.AP_BoardConfig.AP_BoardConfig
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.libraries.AP_Notify.AP_Notify
import ArduLean.Vehicle.Dispatch
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor
import ArduLean.Vehicle.libraries.AP_Vehicle.AP_Vehicle
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.SRV_Channel.SRV_Channel
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2
import ArduLean.Vehicle.libraries.Filter.Filter_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl_2
import ArduLean.Vehicle.libraries.AC_WPNav.AC_WPNav_2
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel_2
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming_2

/-!
ArduPilot `ArduCopter`, part 2 of 3. Sources: `ArduCopter/mode_guided.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `ArduCopter/mode_auto.cpp`, `ArduCopter/mode.cpp`, `ArduCopter/autoyaw.cpp`, `ArduCopter/mode_rtl.cpp`, `ArduCopter/system.cpp`, `ArduCopter/Attitude.cpp` and 18 more.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `GCS_MAVLINK_Copter::packetReceived : void (const mavlink_status_t &, const mavlink_message_t &)`, `GCS_MAVLink_Copter.cpp:346-357`. -/
def GCS_MAVLINK_Copter.packetReceived (this : UInt64) (status : UInt64) (msg : UInt64) : PMem.M Unit := do
  GCS_MAVLINK.packetReceived this status msg
  return ()

/-- C++ `ModeGuided::pva_control_start : void ()`, `mode_guided.cpp:252-271`. -/
def ModeGuided.pva_control_start (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_default_speed_NE_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.get_wp_acceleration_mss t'5
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.NE_set_max_speed_accel_m t'8 t'3 t'6
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_WPNav.get_default_speed_NE_ms t'10
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← PMem.ldU64 t'12
  let t'14 ← AC_WPNav.get_wp_acceleration_mss t'13
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.NE_set_correction_speed_accel_m t'16 t'11 t'14
  let t'17 ← PMem.ldU64 (this + 24)
  let t'18 ← PMem.ldU64 t'17
  let t'19 ← AC_WPNav.get_default_speed_down_ms t'18
  let t'20 ← PMem.ldU64 (this + 24)
  let t'21 ← PMem.ldU64 t'20
  let t'22 ← AC_WPNav.get_default_speed_up_ms t'21
  let t'23 ← PMem.ldU64 (this + 24)
  let t'24 ← PMem.ldU64 t'23
  let t'25 ← AC_WPNav.get_accel_D_mss t'24
  let t'26 ← PMem.ldU64 (this + 40)
  let t'27 ← PMem.ldU64 t'26
  AC_PosControl.D_set_max_speed_accel_m t'27 t'19 t'22 t'25
  let t'28 ← PMem.ldU64 (this + 24)
  let t'29 ← PMem.ldU64 t'28
  let t'30 ← AC_WPNav.get_default_speed_down_ms t'29
  let t'31 ← PMem.ldU64 (this + 24)
  let t'32 ← PMem.ldU64 t'31
  let t'33 ← AC_WPNav.get_default_speed_up_ms t'32
  let t'34 ← PMem.ldU64 (this + 24)
  let t'35 ← PMem.ldU64 t'34
  let t'36 ← AC_WPNav.get_accel_D_mss t'35
  let t'37 ← PMem.ldU64 (this + 40)
  let t'38 ← PMem.ldU64 t'37
  AC_PosControl.D_set_correction_speed_accel_m t'38 t'30 t'33 t'36
  let t'39 ← PMem.ldU64 (this + 40)
  let t'40 ← PMem.ldU64 t'39
  AC_PosControl.D_init_controller t'40
  let t'41 ← PMem.ldU64 (this + 40)
  let t'42 ← PMem.ldU64 t'41
  AC_PosControl.NE_init_controller t'42
  Mode.AutoYaw.set_mode_to_default (0xeb78 : UInt64) /- &Mode::auto_yaw -/ false
  PMem.stB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/ false
  return ()

/-- C++ `ModeGuided::velaccel_control_start : void ()`, `mode_guided.cpp:294-301`. -/
def ModeGuided.velaccel_control_start (this : UInt64) : PMem.M Unit := do
  PMem.stI32 (this + 112) (4 : Int32)
  ModeGuided.pva_control_start this
  return ()

/-- C++ `ModeGuided::hold_position : void ()`, `mode_guided.cpp:52-60`. -/
def ModeGuided.hold_position (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldI32 (this + 112)
  if (t'1 != (4 : Int32)) then
    ModeGuided.velaccel_control_start this
  Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
  Vector3'float.zero (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
  return ()

/-- C++ `ModeGuided::angle_control_start : void ()`, `mode_guided.cpp:343-362`. -/
def ModeGuided.angle_control_start.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stI32 (this + 112) (6 : Int32)
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_default_speed_down_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.get_default_speed_up_ms t'5
  let t'7 ← PMem.ldU64 (this + 24)
  let t'8 ← PMem.ldU64 t'7
  let t'9 ← AC_WPNav.get_accel_D_mss t'8
  let t'10 ← PMem.ldU64 (this + 40)
  let t'11 ← PMem.ldU64 t'10
  AC_PosControl.D_set_max_speed_accel_m t'11 t'3 t'6 t'9
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← PMem.ldU64 t'12
  let t'14 ← AC_WPNav.get_default_speed_down_ms t'13
  let t'15 ← PMem.ldU64 (this + 24)
  let t'16 ← PMem.ldU64 t'15
  let t'17 ← AC_WPNav.get_default_speed_up_ms t'16
  let t'18 ← PMem.ldU64 (this + 24)
  let t'19 ← PMem.ldU64 t'18
  let t'20 ← AC_WPNav.get_accel_D_mss t'19
  let t'21 ← PMem.ldU64 (this + 40)
  let t'22 ← PMem.ldU64 t'21
  AC_PosControl.D_set_correction_speed_accel_m t'22 t'14 t'17 t'20
  let t'23 ← PMem.ldU64 (this + 40)
  let t'24 ← PMem.ldU64 t'23
  let t'25 ← AC_PosControl.D_is_active t'24
  if !t'25 then
    let t'26 ← PMem.ldU64 (this + 40)
    let t'27 ← PMem.ldU64 t'26
    AC_PosControl.D_init_controller t'27
  let t'28 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (0x12e00 : UInt64) /- &guided_angle_state -/ t'28
  let t'29 ← PMem.ldU64 (this + 56)
  let t'30 ← PMem.ldU64 t'29
  let t'31 ← AC_AttitudeControl.get_att_target_euler_rad t'30
  let t'32 ← PMem.ldF32 (t'31 + 8)
  Vector3'float.Vector3 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'32
  QuaternionT'float.from_euler ((0x12e00 : UInt64) /- &guided_angle_state -/ + 4) (fp + 0)
  Vector3'float.zero ((0x12e00 : UInt64) /- &guided_angle_state -/ + 20)
  let t'33 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 32) t'33
  return ()

def ModeGuided.angle_control_start (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← ModeGuided.angle_control_start.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeGuided::set_angle : void (const Quaternion &, const Vector3f &, float, bool)`, `mode_guided.cpp:682-714`. -/
def ModeGuided.set_angle.body (fp : UInt64) (this : UInt64) (attitude_quat : UInt64) (ang_vel_body : UInt64) (climb_rate_ms_or_thrust : Binary32) (use_thrust : Bool) : PMem.M Unit := do
  let mut climb_rate_ms_or_thrust := climb_rate_ms_or_thrust
  let mut use_thrust := use_thrust
  let t'1 ← PMem.ldI32 (this + 112)
  if (t'1 != (6 : Int32)) then
    ModeGuided.angle_control_start this
  else
    let mut sc'3 := !use_thrust
    if sc'3 then
      let t'2 ← PMem.ldB ((0x12e00 : UInt64) /- &guided_angle_state -/ + 40)
      sc'3 := t'2
    if sc'3 then
      let t'4 ← PMem.ldU64 (this + 40)
      let t'5 ← PMem.ldU64 t'4
      AC_PosControl.D_init_controller t'5
  discard <| PMem.memcpy ((0x12e00 : UInt64) /- &guided_angle_state -/ + 4) attitude_quat 16
  discard <| pure (((0x12e00 : UInt64) /- &guided_angle_state -/ + 4))
  discard <| PMem.memcpy ((0x12e00 : UInt64) /- &guided_angle_state -/ + 20) ang_vel_body 12
  discard <| pure (((0x12e00 : UInt64) /- &guided_angle_state -/ + 20))
  PMem.stB ((0x12e00 : UInt64) /- &guided_angle_state -/ + 40) use_thrust
  if use_thrust then
    PMem.stF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 36) climb_rate_ms_or_thrust
    let t'6 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 32) t'6
  else
    let t'7 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 36) t'7
    PMem.stF32 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 32) climb_rate_ms_or_thrust
  let t'8 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (0x12e00 : UInt64) /- &guided_angle_state -/ t'8
  QuaternionT'float.to_euler attitude_quat (fp + 0) (fp + 8) (fp + 16)
  return ()

def ModeGuided.set_angle (this : UInt64) (attitude_quat : UInt64) (ang_vel_body : UInt64) (climb_rate_ms_or_thrust : Binary32) (use_thrust : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← ModeGuided.set_angle.body fp this attitude_quat ang_vel_body climb_rate_ms_or_thrust use_thrust
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK_Copter::handle_message_set_attitude_target : void (const mavlink_message_t &)`, `GCS_MAVLink_Copter.cpp:892-966`. -/
def GCS_MAVLINK_Copter.handle_message_set_attitude_target.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_set_attitude_target_t.__mavlink_set_attitude_target_t (fp + 0)
  mavlink_msg_set_attitude_target_decode msg (fp + 0)
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'in_guided_mode'11 t'1
  if !t'2 then
    return ()
  let t'3 ← PMem.ldU8 ((fp + 0) + 38)
  let mut roll_rate_ignore : Bool := ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) &&& (UInt32.toInt32 ((1 : UInt32)))) != (0 : Int32)
  let t'4 ← PMem.ldU8 ((fp + 0) + 38)
  let mut pitch_rate_ignore : Bool := ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) &&& (UInt32.toInt32 ((2 : UInt32)))) != (0 : Int32)
  let t'5 ← PMem.ldU8 ((fp + 0) + 38)
  let mut yaw_rate_ignore : Bool := ((UInt32.toInt32 (UInt8.toUInt32 (t'5))) &&& (UInt32.toInt32 ((4 : UInt32)))) != (0 : Int32)
  let t'6 ← PMem.ldU8 ((fp + 0) + 38)
  let mut throttle_ignore : Bool := ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) &&& (UInt32.toInt32 ((64 : UInt32)))) != (0 : Int32)
  let t'7 ← PMem.ldU8 ((fp + 0) + 38)
  let mut attitude_ignore : Bool := ((UInt32.toInt32 (UInt8.toUInt32 (t'7))) &&& (UInt32.toInt32 ((128 : UInt32)))) != (0 : Int32)
  if throttle_ignore then
    ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
    return ()
  QuaternionT'float.QuaternionT (fp + 40)
  if attitude_ignore then
    QuaternionT'float.zero (fp + 40)
  else
    let t'8 ← PMem.ldF32 (((fp + 0) + 4) + ((Int32.toInt64 ((0 : Int32))) * 4).toUInt64)
    let t'9 ← PMem.ldF32 (((fp + 0) + 4) + ((Int32.toInt64 ((1 : Int32))) * 4).toUInt64)
    let t'10 ← PMem.ldF32 (((fp + 0) + 4) + ((Int32.toInt64 ((2 : Int32))) * 4).toUInt64)
    let t'11 ← PMem.ldF32 (((fp + 0) + 4) + ((Int32.toInt64 ((3 : Int32))) * 4).toUInt64)
    QuaternionT'float.QuaternionT'2 (fp + 56) t'8 t'9 t'10 t'11
    discard <| PMem.memcpy (fp + 40) (fp + 56) 16
    discard <| pure ((fp + 40))
    let t'12 ← QuaternionT'float.is_unit_length (fp + 40)
    if !t'12 then
      ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
      return ()
  Vector3'float.Vector3'2 (fp + 72)
  if (((!roll_rate_ignore) && (!pitch_rate_ignore)) && (!yaw_rate_ignore)) then
    let t'13 ← PMem.ldF32 ((fp + 0) + 20)
    PMem.stF32 (fp + 72) t'13
    let t'14 ← PMem.ldF32 ((fp + 0) + 24)
    PMem.stF32 ((fp + 72) + 4) t'14
    let t'15 ← PMem.ldF32 ((fp + 0) + 28)
    PMem.stF32 ((fp + 72) + 8) t'15
  else
    if !((roll_rate_ignore && pitch_rate_ignore) && yaw_rate_ignore) then
      ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
      return ()
  let t'16 ← ModeGuided.set_attitude_target_provides_thrust ((0x86d8 : UInt64) /- &copter -/ + 12520)
  let mut use_thrust : Bool := t'16
  let mut climb_rate_ms_or_thrust : Binary32 := default  -- uninitialized in C
  if use_thrust then
    let t'17 ← PMem.ldF32 ((fp + 0) + 32)
    let t'18 ← constrain_value_line'float t'17 (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((949 : Int32)))
    climb_rate_ms_or_thrust := t'18
  else
    let t'19 ← PMem.ldF32 ((fp + 0) + 32)
    let t'20 ← constrain_value_line'float t'19 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((952 : Int32)))
    PMem.stF32 ((fp + 0) + 32) t'20
    let t'21 ← PMem.ldF32 ((fp + 0) + 32)
    let t'22 ← is_equal'float_float t'21 (Binary32.ofBits 0x3f000000 /- 1/2 -/)
    if t'22 then
      let t'23 := (Binary32.ofBits 0x00000000 /- 0 -/)
      climb_rate_ms_or_thrust := t'23
    else
      let t'24 ← PMem.ldF32 ((fp + 0) + 32)
      if (decide (t'24 > (Binary32.ofBits 0x3f000000 /- 1/2 -/))) then
        let t'25 ← PMem.ldF32 ((fp + 0) + 32)
        let t'26 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
        let t'27 ← AC_WPNav.get_default_speed_up_ms t'26
        let t'28 := (((t'25 - (Binary32.ofBits 0x3f000000 /- 1/2 -/)) * (Binary32.ofBits 0x40000000 /- 2 -/)) * t'27)
        climb_rate_ms_or_thrust := t'28
      else
        let t'29 ← PMem.ldF32 ((fp + 0) + 32)
        let t'30 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
        let t'31 ← AC_WPNav.get_default_speed_down_ms t'30
        let t'32 := ((((Binary32.ofBits 0x3f000000 /- 1/2 -/) - t'29) * (Binary32.ofBits 0x40000000 /- 2 -/)) * (-t'31))
        climb_rate_ms_or_thrust := t'32
  ModeGuided.set_angle ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 40) (fp + 72) climb_rate_ms_or_thrust use_thrust
  return ()

def GCS_MAVLINK_Copter.handle_message_set_attitude_target (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 84
  let r ← GCS_MAVLINK_Copter.handle_message_set_attitude_target.body fp this msg
  PMem.leave fp
  return r

/-- C++ `ModeGuided::posvelaccel_control_start : void ()`, `mode_guided.cpp:304-311`. -/
def ModeGuided.posvelaccel_control_start (this : UInt64) : PMem.M Unit := do
  PMem.stI32 (this + 112) (3 : Int32)
  ModeGuided.pva_control_start this
  return ()

/-- C++ `Mode::AutoYaw::set_fixed_yaw_rad : void (float, float, int8_t, bool)`, `autoyaw.cpp:115-146`. -/
def Mode.AutoYaw.set_fixed_yaw_rad.body (fp : UInt64) (this : UInt64) (yaw_rad : Binary32) (yaw_rate_rads : Binary32) (direction : Int8) (relative_angle : Bool) : PMem.M Unit := do
  let mut yaw_rad := yaw_rad
  PMem.stF32 (fp + 0) yaw_rate_rads
  let mut direction := direction
  let mut relative_angle := relative_angle
  let t'1 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 28) t'1
  let mut angle_rad : Binary32 := yaw_rad
  if relative_angle then
    let t'2 ← PMem.ldI32 this
    if (t'2 == (0 : Int32)) then
      let t'3 ← VehicleBridge.AP_AHRS.get_yaw_rad'0 ((0x86d8 : UInt64) /- &copter -/ + 4080)
      PMem.stF32 (this + 36) t'3
    let mut c'4 : Binary32 := default
    if (decide ((Int8.toInt32 (direction)) ≥ (0 : Int32))) then
      c'4 := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
    else
      c'4 := -(Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
    let t'5 := (angle_rad * c'4)
    PMem.stF32 (this + 20) t'5
  else
    let t'6 ← PMem.ldF32 (this + 36)
    let t'7 ← wrap_PI'float (angle_rad - t'6)
    PMem.stF32 (this + 20) t'7
    let mut sc'10 := (decide ((Int8.toInt32 (direction)) < (0 : Int32)))
    if sc'10 then
      let t'8 ← PMem.ldF32 (this + 20)
      let t'9 ← is_positive'float t'8
      sc'10 := t'9
    if sc'10 then
      let t'11 := (this + 20)
      let t'12 ← PMem.ldF32 t'11
      let t'13 := (t'12 - ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))))
      PMem.stF32 t'11 t'13
    else
      let mut sc'16 := (decide ((Int8.toInt32 (direction)) > (0 : Int32)))
      if sc'16 then
        let t'14 ← PMem.ldF32 (this + 20)
        let t'15 ← is_negative'float t'14
        sc'16 := t'15
      if sc'16 then
        let t'17 := (this + 20)
        let t'18 ← PMem.ldF32 t'17
        let t'19 := (t'18 + ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))))
        PMem.stF32 t'17 t'19
  let t'20 ← PMem.ldF32 (fp + 0)
  let t'21 ← is_positive'float t'20
  if !t'21 then
    let t'22 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    let t'23 ← AC_AttitudeControl.get_slew_yaw_max_rads t'22
    PMem.stF32 (this + 24) t'23
  else
    let t'24 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
    let t'25 ← AC_AttitudeControl.get_slew_yaw_max_rads t'24
    PMem.stF32 (fp + 4) t'25
    let t'26 ← MIN'float_float (fp + 4) (fp + 0)
    let t'27 ← PMem.ldF32 t'26
    PMem.stF32 (this + 24) t'27
  Mode.AutoYaw.set_mode this (3 : Int32)
  return ()

def Mode.AutoYaw.set_fixed_yaw_rad (this : UInt64) (yaw_rad : Binary32) (yaw_rate_rads : Binary32) (direction : Int8) (relative_angle : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Mode.AutoYaw.set_fixed_yaw_rad.body fp this yaw_rad yaw_rate_rads direction relative_angle
  PMem.leave fp
  return r

/-- C++ `ModeGuided::set_yaw_state_rad : void (bool, float, bool, float, bool)`, `mode_guided.cpp:1047-1060`. -/
def ModeGuided.set_yaw_state_rad (this : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_angle : Bool) : PMem.M Unit := do
  let mut use_yaw := use_yaw
  let mut yaw_rad := yaw_rad
  let mut use_yaw_rate := use_yaw_rate
  let mut yaw_rate_rads := yaw_rate_rads
  let mut relative_angle := relative_angle
  if (use_yaw && relative_angle) then
    Mode.AutoYaw.set_fixed_yaw_rad (0xeb78 : UInt64) /- &Mode::auto_yaw -/ yaw_rad (Binary32.ofBits 0x00000000 /- 0 -/) (Int32.toInt8 ((0 : Int32))) relative_angle
  else
    if (use_yaw && use_yaw_rate) then
      Mode.AutoYaw.set_yaw_angle_and_rate_rad (0xeb78 : UInt64) /- &Mode::auto_yaw -/ yaw_rad yaw_rate_rads
    else
      if (use_yaw && (!use_yaw_rate)) then
        Mode.AutoYaw.set_yaw_angle_and_rate_rad (0xeb78 : UInt64) /- &Mode::auto_yaw -/ yaw_rad (Binary32.ofBits 0x00000000 /- 0 -/)
      else
        if use_yaw_rate then
          Mode.AutoYaw.set_rate_rad (0xeb78 : UInt64) /- &Mode::auto_yaw -/ yaw_rate_rads
        else
          Mode.AutoYaw.set_mode_to_default (0xeb78 : UInt64) /- &Mode::auto_yaw -/ false
  return ()

/-- C++ `ModeGuided::set_pos_vel_accel_NED_m : bool (const Vector3p &, const Vector3f &, const Vector3f &, bool, float, bool, float, bool)`, `mode_guided.cpp:618-649`. -/
def ModeGuided.set_pos_vel_accel_NED_m (this : UInt64) (pos_ned_m : UInt64) (vel_ned_ms : UInt64) (accel_ned_mss : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) : PMem.M Bool := do
  let mut use_yaw := use_yaw
  let mut yaw_rad := yaw_rad
  let mut use_yaw_rate := use_yaw_rate
  let mut yaw_rate_rads := yaw_rate_rads
  let mut relative_yaw := relative_yaw
  let t'1 ← PMem.ldI32 (this + 112)
  if (t'1 != (3 : Int32)) then
    ModeGuided.posvelaccel_control_start this
  ModeGuided.set_yaw_state_rad this use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
  let t'2 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (0x12e30 : UInt64) /- &update_time_ms -/ t'2
  discard <| PMem.memcpy (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/ pos_ned_m 24
  discard <| pure ((0x12e38 : UInt64) /- &guided_pos_target_ned_m -/)
  PMem.stB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/ false
  discard <| PMem.memcpy (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/ vel_ned_ms 12
  discard <| pure ((0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/)
  discard <| PMem.memcpy (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/ accel_ned_mss 12
  discard <| pure ((0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/)
  return true

/-- C++ `ModeGuided::set_vel_accel_NED_m : void (const Vector3f &, const Vector3f &, bool, float, bool, float, bool, bool)`, `mode_guided.cpp:586-609`. -/
def ModeGuided.set_vel_accel_NED_m (this : UInt64) (vel_ned_ms : UInt64) (accel_ned_mss : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) (log_request : Bool) : PMem.M Unit := do
  let mut use_yaw := use_yaw
  let mut yaw_rad := yaw_rad
  let mut use_yaw_rate := use_yaw_rate
  let mut yaw_rate_rads := yaw_rate_rads
  let mut relative_yaw := relative_yaw
  let mut log_request := log_request
  let t'1 ← PMem.ldI32 (this + 112)
  if (t'1 != (4 : Int32)) then
    ModeGuided.velaccel_control_start this
  ModeGuided.set_yaw_state_rad this use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
  Vector3'double.zero (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/
  PMem.stB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/ false
  discard <| PMem.memcpy (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/ vel_ned_ms 12
  discard <| pure ((0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/)
  discard <| PMem.memcpy (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/ accel_ned_mss 12
  discard <| pure ((0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/)
  let t'2 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (0x12e30 : UInt64) /- &update_time_ms -/ t'2
  return ()

/-- C++ `ModeGuided::accel_control_start : void ()`, `mode_guided.cpp:284-291`. -/
def ModeGuided.accel_control_start (this : UInt64) : PMem.M Unit := do
  PMem.stI32 (this + 112) (5 : Int32)
  ModeGuided.pva_control_start this
  return ()

/-- C++ `ModeGuided::set_accel_NED_mss : void (const Vector3f &, bool, float, bool, float, bool, bool)`, `mode_guided.cpp:554-577`. -/
def ModeGuided.set_accel_NED_mss (this : UInt64) (accel_ned_mss : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) (log_request : Bool) : PMem.M Unit := do
  let mut use_yaw := use_yaw
  let mut yaw_rad := yaw_rad
  let mut use_yaw_rate := use_yaw_rate
  let mut yaw_rate_rads := yaw_rate_rads
  let mut relative_yaw := relative_yaw
  let mut log_request := log_request
  let t'1 ← PMem.ldI32 (this + 112)
  if (t'1 != (5 : Int32)) then
    ModeGuided.accel_control_start this
  ModeGuided.set_yaw_state_rad this use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
  Vector3'double.zero (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/
  PMem.stB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/ false
  Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
  discard <| PMem.memcpy (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/ accel_ned_mss 12
  discard <| pure ((0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/)
  let t'2 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (0x12e30 : UInt64) /- &update_time_ms -/ t'2
  return ()

/-- C++ `ModeGuided::wp_control_start : void ()`, `mode_guided.cpp:208-226`. -/
def ModeGuided.wp_control_start.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stI32 (this + 112) (1 : Int32)
  Vector3'double.Vector3 (fp + 24)
  Vector3'double.Vector3'2 (fp + 0) (fp + 24)
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  AC_WPNav.wp_and_spline_init_m t'2 (Binary32.ofBits 0x00000000 /- 0 -/) (fp + 0)
  Vector3'double.Vector3 (fp + 48)
  let t'3 ← PMem.ldU64 (this + 24)
  let t'4 ← PMem.ldU64 t'3
  AC_WPNav.get_wp_stopping_point_NED_m t'4 (fp + 48)
  let t'5 ← PMem.ldU64 (this + 24)
  let t'6 ← PMem.ldU64 t'5
  let t'7 ← AC_WPNav.set_wp_destination_NED_m t'6 (fp + 48) false (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  if !t'7 then
    pure ()
  Mode.AutoYaw.set_mode_to_default (0xeb78 : UInt64) /- &Mode::auto_yaw -/ false
  return ()

def ModeGuided.wp_control_start (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 72
  let r ← ModeGuided.wp_control_start.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeGuided::pos_control_start : void ()`, `mode_guided.cpp:274-281`. -/
def ModeGuided.pos_control_start (this : UInt64) : PMem.M Unit := do
  PMem.stI32 (this + 112) (2 : Int32)
  ModeGuided.pva_control_start this
  return ()

/-- C++ `ModeGuided::set_pos_NED_m : bool (const Vector3p &, bool, float, bool, float, bool, bool)`, `mode_guided.cpp:367-442`. -/
def ModeGuided.set_pos_NED_m.body (fp : UInt64) (this : UInt64) (pos_ned_m : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) (is_terrain_alt : Bool) : PMem.M Bool := do
  let mut use_yaw := use_yaw
  let mut yaw_rad := yaw_rad
  let mut use_yaw_rate := use_yaw_rate
  let mut yaw_rate_rads := yaw_rate_rads
  let mut relative_yaw := relative_yaw
  let mut is_terrain_alt := is_terrain_alt
  let t'1 ← ModeGuided.use_wpnav_for_position_control this
  if t'1 then
    let t'2 ← PMem.ldI32 (this + 112)
    if (t'2 != (1 : Int32)) then
      ModeGuided.wp_control_start this
    ModeGuided.set_yaw_state_rad this use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.set_wp_destination_NED_m t'4 pos_ned_m is_terrain_alt (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    discard <| pure (t'5)
    PMem.stB (this + 116) true
    return true
  let t'6 ← PMem.ldI32 (this + 112)
  if (t'6 != (2 : Int32)) then
    ModeGuided.pos_control_start this
  if is_terrain_alt then
    let t'7 ← PMem.ldU64 (this + 24)
    let t'8 ← PMem.ldU64 t'7
    let t'9 ← AC_WPNav.get_terrain_D_m t'8 (fp + 0)
    if !t'9 then
      ModeGuided.hold_position this
      return false
    let t'10 ← PMem.ldB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/
    if !t'10 then
      let t'11 ← PMem.ldF32 (fp + 0)
      let t'12 ← PMem.ldU64 (this + 40)
      let t'13 ← PMem.ldU64 t'12
      AC_PosControl.init_pos_terrain_D_m t'13 t'11
  else
    let t'14 ← PMem.ldU64 (this + 40)
    let t'15 ← PMem.ldU64 t'14
    AC_PosControl.init_pos_terrain_D_m t'15 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  ModeGuided.set_yaw_state_rad this use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
  discard <| PMem.memcpy (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/ pos_ned_m 24
  discard <| pure ((0x12e38 : UInt64) /- &guided_pos_target_ned_m -/)
  PMem.stB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/ is_terrain_alt
  Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
  Vector3'float.zero (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
  let t'16 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (0x12e30 : UInt64) /- &update_time_ms -/ t'16
  PMem.stB (this + 116) true
  return true

def ModeGuided.set_pos_NED_m (this : UInt64) (pos_ned_m : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) (is_terrain_alt : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← ModeGuided.set_pos_NED_m.body fp this pos_ned_m use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw is_terrain_alt
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK_Copter::handle_message_set_position_target_local_ned : void (const mavlink_message_t &)`, `GCS_MAVLink_Copter.cpp:968-1077`. -/
def GCS_MAVLINK_Copter.handle_message_set_position_target_local_ned.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_set_position_target_local_ned_t.__mavlink_set_position_target_local_ned_t (fp + 0)
  mavlink_msg_set_position_target_local_ned_decode msg (fp + 0)
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'in_guided_mode'11 t'1
  if !t'2 then
    return ()
  let t'3 ← PMem.ldU8 ((fp + 0) + 52)
  let mut sc'5 := ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) != (UInt32.toInt32 ((1 : UInt32))))
  if sc'5 then
    let t'4 ← PMem.ldU8 ((fp + 0) + 52)
    sc'5 := ((UInt32.toInt32 (UInt8.toUInt32 (t'4))) != (UInt32.toInt32 ((7 : UInt32))))
  let mut sc'7 := sc'5
  if sc'7 then
    let t'6 ← PMem.ldU8 ((fp + 0) + 52)
    sc'7 := ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) != (UInt32.toInt32 ((8 : UInt32))))
  let mut sc'9 := sc'7
  if sc'9 then
    let t'8 ← PMem.ldU8 ((fp + 0) + 52)
    sc'9 := ((UInt32.toInt32 (UInt8.toUInt32 (t'8))) != (UInt32.toInt32 ((9 : UInt32))))
  if sc'9 then
    ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
    return ()
  let t'10 ← PMem.ldU16 ((fp + 0) + 48)
  let mut pos_ignore : Bool := ((UInt16.toUInt32 (t'10)) &&& (7 : UInt32)) != (0 : UInt32)
  let t'11 ← PMem.ldU16 ((fp + 0) + 48)
  let mut vel_ignore : Bool := ((UInt16.toUInt32 (t'11)) &&& (56 : UInt32)) != (0 : UInt32)
  let t'12 ← PMem.ldU16 ((fp + 0) + 48)
  let mut acc_ignore : Bool := ((UInt16.toUInt32 (t'12)) &&& (448 : UInt32)) != (0 : UInt32)
  let t'13 ← PMem.ldU16 ((fp + 0) + 48)
  let mut yaw_ignore : Bool := ((UInt16.toUInt32 (t'13)) &&& (1024 : UInt32)) != (0 : UInt32)
  let t'14 ← PMem.ldU16 ((fp + 0) + 48)
  let mut yaw_rate_ignore : Bool := ((UInt16.toUInt32 (t'14)) &&& (2048 : UInt32)) != (0 : UInt32)
  let t'15 ← PMem.ldU16 ((fp + 0) + 48)
  let mut force_set : Bool := ((UInt16.toUInt32 (t'15)) &&& (512 : UInt32)) != (0 : UInt32)
  if (force_set && (!acc_ignore)) then
    ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
    return ()
  Vector3'double.Vector3 (fp + 56)
  if !pos_ignore then
    let t'16 ← PMem.ldF32 ((fp + 0) + 4)
    let t'17 ← PMem.ldF32 ((fp + 0) + 8)
    let t'18 ← PMem.ldF32 ((fp + 0) + 12)
    Vector3'double.Vector3'3 (fp + 80) (Binary32.toBinary64 (t'16)) (Binary32.toBinary64 (t'17)) (Binary32.toBinary64 (t'18))
    discard <| PMem.memcpy (fp + 56) (fp + 80) 24
    discard <| pure ((fp + 56))
    let t'19 ← PMem.ldU8 ((fp + 0) + 52)
    let mut sc'21 := ((UInt32.toInt32 (UInt8.toUInt32 (t'19))) == (UInt32.toInt32 ((8 : UInt32))))
    if !sc'21 then
      let t'20 ← PMem.ldU8 ((fp + 0) + 52)
      sc'21 := ((UInt32.toInt32 (UInt8.toUInt32 (t'20))) == (UInt32.toInt32 ((9 : UInt32))))
    if sc'21 then
      let t'22 ← Vector3'double.xy (fp + 56)
      let t'23 ← Vector3'double.xy (fp + 56)
      VehicleBridge.AP_AHRS.body_to_earth2D_p'1 ((0x86d8 : UInt64) /- &copter -/ + 4080) (fp + 104) t'23
      let t'24 := (fp + 104)
      discard <| PMem.memcpy t'22 t'24 16
      discard <| pure (t'22)
    let t'25 ← PMem.ldU8 ((fp + 0) + 52)
    let mut sc'27 := ((UInt32.toInt32 (UInt8.toUInt32 (t'25))) == (UInt32.toInt32 ((7 : UInt32))))
    if !sc'27 then
      let t'26 ← PMem.ldU8 ((fp + 0) + 52)
      sc'27 := ((UInt32.toInt32 (UInt8.toUInt32 (t'26))) == (UInt32.toInt32 ((8 : UInt32))))
    let mut sc'29 := sc'27
    if !sc'29 then
      let t'28 ← PMem.ldU8 ((fp + 0) + 52)
      sc'29 := ((UInt32.toInt32 (UInt8.toUInt32 (t'28))) == (UInt32.toInt32 ((9 : UInt32))))
    if sc'29 then
      Vector3'double.Vector3 (fp + 120)
      let t'30 ← VehicleBridge.ahrs'0
      let t'31 ← VehicleBridge.AP_AHRS.get_relative_position_NED_origin'1 t'30 (fp + 120)
      if !t'31 then
        ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
        return ()
      let t'32 ← Vector3'double.operator__ (fp + 56) (fp + 120)
      discard <| pure (t'32)
  Vector3'float.Vector3'2 (fp + 144)
  if !vel_ignore then
    let t'33 ← PMem.ldF32 ((fp + 0) + 16)
    let t'34 ← PMem.ldF32 ((fp + 0) + 20)
    let t'35 ← PMem.ldF32 ((fp + 0) + 24)
    Vector3'float.Vector3 (fp + 160) t'33 t'34 t'35
    discard <| PMem.memcpy (fp + 144) (fp + 160) 12
    discard <| pure ((fp + 144))
    let t'36 ← GCS_MAVLINK_Copter.sane_vel_or_acc_vector this (fp + 144)
    if !t'36 then
      ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
      return ()
    let t'37 ← PMem.ldU8 ((fp + 0) + 52)
    let mut sc'39 := ((UInt32.toInt32 (UInt8.toUInt32 (t'37))) == (UInt32.toInt32 ((8 : UInt32))))
    if !sc'39 then
      let t'38 ← PMem.ldU8 ((fp + 0) + 52)
      sc'39 := ((UInt32.toInt32 (UInt8.toUInt32 (t'38))) == (UInt32.toInt32 ((9 : UInt32))))
    if sc'39 then
      let t'40 ← Vector3'float.xy (fp + 144)
      let t'41 ← Vector3'float.xy (fp + 144)
      VehicleBridge.AP_AHRS.body_to_earth2D'1 ((0x86d8 : UInt64) /- &copter -/ + 4080) (fp + 176) t'41
      let t'42 := (fp + 176)
      discard <| PMem.memcpy t'40 t'42 8
      discard <| pure (t'40)
  Vector3'float.Vector3'2 (fp + 184)
  if !acc_ignore then
    let t'43 ← PMem.ldF32 ((fp + 0) + 28)
    let t'44 ← PMem.ldF32 ((fp + 0) + 32)
    let t'45 ← PMem.ldF32 ((fp + 0) + 36)
    Vector3'float.Vector3 (fp + 200) t'43 t'44 t'45
    discard <| PMem.memcpy (fp + 184) (fp + 200) 12
    discard <| pure ((fp + 184))
    let t'46 ← PMem.ldU8 ((fp + 0) + 52)
    let mut sc'48 := ((UInt32.toInt32 (UInt8.toUInt32 (t'46))) == (UInt32.toInt32 ((8 : UInt32))))
    if !sc'48 then
      let t'47 ← PMem.ldU8 ((fp + 0) + 52)
      sc'48 := ((UInt32.toInt32 (UInt8.toUInt32 (t'47))) == (UInt32.toInt32 ((9 : UInt32))))
    if sc'48 then
      let t'49 ← Vector3'float.xy (fp + 184)
      let t'50 ← Vector3'float.xy (fp + 184)
      VehicleBridge.AP_AHRS.body_to_earth2D'1 ((0x86d8 : UInt64) /- &copter -/ + 4080) (fp + 216) t'50
      let t'51 := (fp + 216)
      discard <| PMem.memcpy t'49 t'51 8
      discard <| pure (t'49)
  let mut yaw_rad : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut yaw_relative : Bool := false
  let mut yaw_rate_rads : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  if !yaw_ignore then
    let t'52 ← PMem.ldF32 ((fp + 0) + 40)
    yaw_rad := t'52
    let t'53 ← PMem.ldU8 ((fp + 0) + 52)
    let mut sc'55 := ((UInt32.toInt32 (UInt8.toUInt32 (t'53))) == (UInt32.toInt32 ((8 : UInt32))))
    if !sc'55 then
      let t'54 ← PMem.ldU8 ((fp + 0) + 52)
      sc'55 := ((UInt32.toInt32 (UInt8.toUInt32 (t'54))) == (UInt32.toInt32 ((9 : UInt32))))
    yaw_relative := sc'55
  if !yaw_rate_ignore then
    let t'56 ← PMem.ldF32 ((fp + 0) + 44)
    yaw_rate_rads := t'56
  if ((!pos_ignore) && (!vel_ignore)) then
    let t'57 ← ModeGuided.set_pos_vel_accel_NED_m ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 56) (fp + 144) (fp + 184) (!yaw_ignore) yaw_rad (!yaw_rate_ignore) yaw_rate_rads yaw_relative
    discard <| pure (t'57)
  else
    if (pos_ignore && (!vel_ignore)) then
      ModeGuided.set_vel_accel_NED_m ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 144) (fp + 184) (!yaw_ignore) yaw_rad (!yaw_rate_ignore) yaw_rate_rads yaw_relative true
    else
      if ((pos_ignore && vel_ignore) && (!acc_ignore)) then
        ModeGuided.set_accel_NED_mss ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 184) (!yaw_ignore) yaw_rad (!yaw_rate_ignore) yaw_rate_rads yaw_relative true
      else
        if (((!pos_ignore) && vel_ignore) && acc_ignore) then
          let t'58 ← ModeGuided.set_pos_NED_m ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 56) (!yaw_ignore) yaw_rad (!yaw_rate_ignore) yaw_rate_rads yaw_relative false
          discard <| pure (t'58)
        else
          ModeGuided.hold_position ((0x86d8 : UInt64) /- &copter -/ + 12520)
  return ()

def GCS_MAVLINK_Copter.handle_message_set_position_target_local_ned (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 224
  let r ← GCS_MAVLINK_Copter.handle_message_set_position_target_local_ned.body fp this msg
  PMem.leave fp
  return r

/-- C++ `ModeGuided::set_pos_vel_NED_m : bool (const Vector3p &, const Vector3f &, bool, float, bool, float, bool)`, `mode_guided.cpp:612-615`. -/
def ModeGuided.set_pos_vel_NED_m.body (fp : UInt64) (this : UInt64) (pos_ned_m : UInt64) (vel_ned_ms : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) : PMem.M Bool := do
  let mut use_yaw := use_yaw
  let mut yaw_rad := yaw_rad
  let mut use_yaw_rate := use_yaw_rate
  let mut yaw_rate_rads := yaw_rate_rads
  let mut relative_yaw := relative_yaw
  Vector3'float.Vector3'2 (fp + 0)
  let t'1 ← ModeGuided.set_pos_vel_accel_NED_m this pos_ned_m vel_ned_ms (fp + 0) use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
  return t'1

def ModeGuided.set_pos_vel_NED_m (this : UInt64) (pos_ned_m : UInt64) (vel_ned_ms : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 12
  let r ← ModeGuided.set_pos_vel_NED_m.body fp this pos_ned_m vel_ned_ms use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
  PMem.leave fp
  return r

/-- C++ `ModeGuided::set_destination : bool (const Location &, bool, float, bool, float, bool)`, `mode_guided.cpp:466-551`. -/
def ModeGuided.set_destination.body (fp : UInt64) (this : UInt64) (dest_loc : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) : PMem.M Bool := do
  let mut use_yaw := use_yaw
  let mut yaw_rad := yaw_rad
  let mut use_yaw_rate := use_yaw_rate
  let mut yaw_rate_rads := yaw_rate_rads
  let mut relative_yaw := relative_yaw
  let t'1 ← ModeGuided.use_wpnav_for_position_control this
  if t'1 then
    let t'2 ← PMem.ldI32 (this + 112)
    if (t'2 != (1 : Int32)) then
      ModeGuided.wp_control_start this
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.set_wp_destination_loc t'4 dest_loc (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    if !t'5 then
      return false
    ModeGuided.set_yaw_state_rad this use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
    PMem.stB (this + 116) true
    return true
  Vector3'double.Vector3 (fp + 0)
  let t'6 ← PMem.ldU64 (this + 24)
  let t'7 ← PMem.ldU64 t'6
  let t'8 ← AC_WPNav.get_vector_NED_m t'7 dest_loc (fp + 0) (fp + 24)
  if !t'8 then
    return false
  let t'9 ← PMem.ldI32 (this + 112)
  if (t'9 != (2 : Int32)) then
    ModeGuided.pos_control_start this
  ModeGuided.set_yaw_state_rad this use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
  let t'10 ← PMem.ldB (fp + 24)
  if t'10 then
    let t'11 ← PMem.ldU64 (this + 24)
    let t'12 ← PMem.ldU64 t'11
    let t'13 ← AC_WPNav.get_terrain_D_m t'12 (fp + 32)
    if !t'13 then
      ModeGuided.hold_position this
      return false
    let t'14 ← PMem.ldB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/
    if !t'14 then
      let t'15 ← PMem.ldF32 (fp + 32)
      let t'16 ← PMem.ldU64 (this + 40)
      let t'17 ← PMem.ldU64 t'16
      AC_PosControl.init_pos_terrain_D_m t'17 t'15
  else
    let t'18 ← PMem.ldU64 (this + 40)
    let t'19 ← PMem.ldU64 t'18
    AC_PosControl.init_pos_terrain_D_m t'19 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  discard <| PMem.memcpy (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/ (fp + 0) 24
  discard <| pure ((0x12e38 : UInt64) /- &guided_pos_target_ned_m -/)
  let t'20 ← PMem.ldB (fp + 24)
  PMem.stB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/ t'20
  Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
  Vector3'float.zero (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
  let t'21 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (0x12e30 : UInt64) /- &update_time_ms -/ t'21
  PMem.stB (this + 116) true
  return true

def ModeGuided.set_destination (this : UInt64) (dest_loc : UInt64) (use_yaw : Bool) (yaw_rad : Binary32) (use_yaw_rate : Bool) (yaw_rate_rads : Binary32) (relative_yaw : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 36
  let r ← ModeGuided.set_destination.body fp this dest_loc use_yaw yaw_rad use_yaw_rate yaw_rate_rads relative_yaw
  PMem.leave fp
  return r

/-- C++ `Copter::notify_flight_mode : void ()`, `mode.cpp:549-553`. -/
def Copter.notify_flight_mode (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 9488)
  let t'2 ← vcall'Mode'is_autopilot'0 t'1
  PMem.stB ((0xccc0 : UInt64) /- &flags -/ + 16) t'2
  let t'3 ← PMem.ldU64 (this + 9488)
  let t'4 ← vcall'Mode'mode_number'1 t'3
  PMem.stU8 ((0xccc0 : UInt64) /- &flags -/ + 3) t'4
  let t'5 ← PMem.ldU64 (this + 9488)
  let t'6 ← vcall'Mode'name4'2 t'5
  AP_Notify.set_flight_mode_str (this + 3992) t'6
  return ()

/-- C++ `Copter::gcs_mode_enabled : bool (const Mode::Number)`, `mode.cpp:186-217`. -/
def Copter.gcs_mode_enabled (this : UInt64) (mode_num : UInt8) : PMem.M Bool := do
  let mut mode_num := mode_num
  let t'1 ← AP_Vehicle.block_GCS_mode_change this mode_num (0xeb60 : UInt64) /- &Copter::gcs_mode_enabled(...)::mode_list -/ (UInt64.toUInt8 (((24 : UInt64) / (1 : UInt64))))
  return !t'1

/-- C++ `Mode::get_stopping_point : Location () const`, `mode.cpp:1167-1173`. -/
def Mode.get_stopping_point.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  Vector3'double.Vector3 (fp + 0)
  let t'1 ← Vector3'double.xy (fp + 0)
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  AC_PosControl.get_stopping_point_NE_m t'2 t'1
  let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  AC_PosControl.get_stopping_point_D_m t'3 ((fp + 0) + 16)
  Location.from_ekf_offset_NED_m (fp + 24) (fp + 0) (2 : Int32)
  let t'4 := (fp + 24)
  Location.Location'2 sret t'4
  return ()

def Mode.get_stopping_point (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 40
  let r ← Mode.get_stopping_point.body fp this sret
  PMem.leave fp
  return r

/-- C++ `Copter::ekf_has_absolute_position : bool () const`, `system.cpp:227-250`. -/
def Copter.ekf_has_absolute_position (this : UInt64) : PMem.M Bool := do
  let t'1 ← VehicleBridge.AP_AHRS.have_inertial_nav'0 (this + 4080)
  if !t'1 then
    return false
  let t'2 ← PMem.ldU64 (this + 9528)
  let t'3 ← AP_Motors.armed t'2
  if !t'3 then
    let t'4 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (16 : Int32)
    if t'4 then
      return true
    let t'5 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (512 : Int32)
    if t'5 then
      return true
    return false
  let t'6 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (128 : Int32)
  if t'6 then
    return false
  let t'7 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (16 : Int32)
  return t'7

/-- C++ `Copter::ekf_has_relative_position : bool () const`, `system.cpp:253-291`. -/
def Copter.ekf_has_relative_position (this : UInt64) : PMem.M Bool := do
  let t'1 ← VehicleBridge.AP_AHRS.have_inertial_nav'0 (this + 4080)
  if !t'1 then
    return false
  let mut enabled : Bool := false
  let t'2 ← PMem.ldB (this + 9520)
  let mut sc'4 := t'2
  if sc'4 then
    let t'3 ← PMem.ldB ((this + 9520) + 1)
    sc'4 := !t'3
  if sc'4 then
    enabled := true
  if !enabled then
    return false
  let t'5 ← PMem.ldU64 (this + 9528)
  let t'6 ← AP_Motors.armed t'5
  if !t'6 then
    let t'7 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (256 : Int32)
    return t'7
  let t'8 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (128 : Int32)
  if t'8 then
    return false
  let t'9 ← VehicleBridge.AP_AHRS.configured_backend_has_status'1 (this + 4080) (8 : Int32)
  if !t'9 then
    return false
  return true

/-- C++ `Copter::position_ok : bool () const`, `system.cpp:215-224`. -/
def Copter.position_ok (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldBits (this + 9508) 74 1
  if (UInt64.toUInt8 (t'1)) != (0 : UInt8) then
    return false
  let t'2 ← Copter.ekf_has_absolute_position this
  let mut sc'4 := t'2
  if !sc'4 then
    let t'3 ← Copter.ekf_has_relative_position this
    sc'4 := t'3
  return sc'4

/-- C++ `Copter::home_distance_m : float ()`, `navigation.cpp:12-18`. -/
def Copter.home_distance_m.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Copter.position_ok this
  if t'1 then
    VehicleBridge.AP_AHRS.get_home'0 (this + 4080) (fp + 0)
    let t'2 := (fp + 0)
    let t'3 ← Location.get_distance (this + 11148) t'2
    let t'4 := Binary64.toBinary32 (t'3)
    PMem.stF32 (this + 9548) t'4
  let t'5 ← PMem.ldF32 (this + 9548)
  return t'5

def Copter.home_distance_m (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← Copter.home_distance_m.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::home_bearing_rad : float ()`, `navigation.cpp:21-27`. -/
def Copter.home_bearing_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Copter.position_ok this
  if t'1 then
    VehicleBridge.AP_AHRS.get_home'0 (this + 4080) (fp + 0)
    let t'2 := (fp + 0)
    let t'3 ← Location.get_bearing (this + 11148) t'2
    let t'4 := Binary64.toBinary32 (t'3)
    PMem.stF32 (this + 9544) t'4
  let t'5 ← PMem.ldF32 (this + 9544)
  return t'5

def Copter.home_bearing_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← Copter.home_bearing_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::update_super_simple_bearing : void (bool)`, `Copter.cpp:857-880`. -/
def Copter.update_super_simple_bearing (this : UInt64) (force_update : Bool) : PMem.M Unit := do
  let mut force_update := force_update
  if !force_update then
    let t'1 ← PMem.ldI32 (this + 9552)
    if (t'1 != (2 : Int32)) then
      return ()
    let t'2 ← Copter.home_distance_m this
    if (decide (t'2 < (Binary64.toBinary32 ((Binary64.ofBits 0x4024000000000000 /- 10 -/))))) then
      return ()
  let t'3 ← Copter.home_bearing_rad this
  let mut bearing_rad : Binary32 := t'3
  let t'4 ← PMem.ldF32 (this + 9564)
  let t'5 ← wrap_PI'float (t'4 - bearing_rad)
  let t'6 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4014000000000000 /- 5 -/)))
  if (decide ((Binary32.abs t'5) < t'6)) then
    return ()
  PMem.stF32 (this + 9564) bearing_rad
  let t'7 ← PMem.ldF32 (this + 9564)
  let t'8 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4066800000000000 /- 180 -/)))
  let mut angle_rad : Binary32 := (t'7 + t'8)
  let t'9 := (Musl.cosf.cosf angle_rad)
  PMem.stF32 (this + 9568) t'9
  let t'10 := (Musl.sinf.sinf angle_rad)
  PMem.stF32 (this + 9572) t'10
  return ()

/-- C++ `AP_Arming_Copter::terrain_database_required : bool () const`, `AP_Arming_Copter.cpp:188-201`. -/
def AP_Arming_Copter.terrain_database_required (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  let t'2 ← AC_WPNav.get_terrain_source t'1
  if (t'2 == (1 : Int32)) then
    return false
  let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  let t'4 ← AC_WPNav.get_terrain_source t'3
  let mut sc'6 := (t'4 == (2 : Int32))
  if sc'6 then
    let t'5 ← ModeRTL.get_alt_type ((0x86d8 : UInt64) /- &copter -/ + 12888)
    sc'6 := (t'5 == (1 : Int8))
  if sc'6 then
    return true
  let t'7 ← AP_Arming.terrain_database_required this
  return t'7

/-- C++ `Copter::get_pilot_speed_dn_ms : float () const`, `Attitude.cpp:133-140`. -/
def Copter.get_pilot_speed_dn_ms.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  discard <| PMem.memcpy (fp + 0) ((this + 6840) + 1640) 4
  let t'1 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if t'1 then
    let t'2 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6840) + 1636)
    let t'3 ← PMem.ldF32 t'2
    return (Binary32.abs t'3)
  else
    let t'4 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6840) + 1640)
    let t'5 ← PMem.ldF32 t'4
    return (Binary32.abs t'5)

def Copter.get_pilot_speed_dn_ms (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← Copter.get_pilot_speed_dn_ms.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::get_pilot_speed_dn_adjusted_ms : float () const`, `Attitude.cpp:155-161`. -/
def Copter.get_pilot_speed_dn_adjusted_ms.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 11184)
  let t'2 ← AC_PosControl.get_vel_terrain_D_ms t'1
  let mut terrain_climb_ms : Binary32 := -t'2
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'3 ← Copter.get_pilot_speed_dn_ms this
  PMem.stF32 (fp + 4) (t'3 + terrain_climb_ms)
  let t'4 ← MAX'float_float (fp + 0) (fp + 4)
  let t'5 ← PMem.ldF32 t'4
  return t'5

def Copter.get_pilot_speed_dn_adjusted_ms (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 8
  let r ← Copter.get_pilot_speed_dn_adjusted_ms.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::get_pilot_desired_climb_rate_ms : float ()`, `Attitude.cpp:74-115`. -/
def Copter.get_pilot_desired_climb_rate_ms.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← rc
  let t'2 ← RC_Channels_Copter.has_valid_input t'1
  if !t'2 then
    return (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 8616)
  let t'4 ← RC_Channel.get_control_in t'3
  let mut throttle_control : Binary32 := Int16.toBinary32 (t'4)
  let t'5 ← constrain_value_line'float throttle_control (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x447a0000 /- 1000 -/) (Int32.toUInt32 ((92 : Int32)))
  throttle_control := t'5
  let t'6 ← AP_ParamT'short_2.operator_const_short__ ((this + 6776) + 30)
  let t'7 ← PMem.ldI16 t'6
  let t'8 ← constrain_int16 t'7 (Int32.toInt16 ((0 : Int32))) (Int32.toInt16 ((400 : Int32)))
  PMem.stI16 (fp + 0) t'8
  AP_ParamTBase'short_2.set ((this + 6776) + 30) (fp + 0)
  let mut desired_rate_ms : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'9 ← Copter.get_throttle_mid this
  let mut mid_stick : Binary32 := Int16.toBinary32 (t'9)
  let t'10 ← AP_ParamT'short_2.operator_const_short__ ((this + 6776) + 30)
  let t'11 ← PMem.ldI16 t'10
  let mut deadband_top : Binary32 := (mid_stick + (Int32.toBinary32 ((Int16.toInt32 (t'11)))))
  let t'12 ← AP_ParamT'short_2.operator_const_short__ ((this + 6776) + 30)
  let t'13 ← PMem.ldI16 t'12
  let mut deadband_bottom : Binary32 := (mid_stick - (Int32.toBinary32 ((Int16.toInt32 (t'13)))))
  if (decide (throttle_control < deadband_bottom)) then
    let t'14 ← Copter.get_pilot_speed_dn_adjusted_ms this
    let t'15 := ((t'14 * (throttle_control - deadband_bottom)) / deadband_bottom)
    desired_rate_ms := t'15
  else
    if (decide (throttle_control > deadband_top)) then
      let t'16 ← Copter.get_pilot_speed_up_adjusted_ms this
      let t'17 := ((t'16 * (throttle_control - deadband_top)) / ((Binary64.toBinary32 ((Binary64.ofBits 0x408f400000000000 /- 1000 -/))) - deadband_top))
      desired_rate_ms := t'17
    else
      let t'18 := (Binary32.ofBits 0x00000000 /- 0 -/)
      desired_rate_ms := t'18
  return desired_rate_ms

def Copter.get_pilot_desired_climb_rate_ms (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 2
  let r ← Copter.get_pilot_desired_climb_rate_ms.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_yaw : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2004-2011`. -/
def ModeAuto.do_yaw (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (cmd + 8)
  let t'2 ← radians t'1
  let t'3 ← PMem.ldF32 ((cmd + 8) + 4)
  let t'4 ← radians t'3
  let t'5 ← PMem.ldI8 ((cmd + 8) + 8)
  let t'6 ← PMem.ldU8 ((cmd + 8) + 9)
  Mode.AutoYaw.set_fixed_yaw_rad (0xeb78 : UInt64) /- &Mode::auto_yaw -/ t'2 t'4 t'5 (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'6))) > (0 : Int32)))
  return ()

/-- C++ `Mode::is_disarmed_or_landed : bool () const`, `mode.cpp:626-632`. -/
def Mode.is_disarmed_or_landed (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 64)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AP_Motors.armed t'2
  let mut sc'5 := !t'3
  if !sc'5 then
    let t'4 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 5)
    sc'5 := !t'4
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
    sc'7 := t'6
  if sc'7 then
    return true
  return false

/-- C++ `_AutoTakeoff::start_m : void (float, bool)`, `takeoff.cpp:224-239`. -/
def _AutoTakeoff.start_m (this : UInt64) (_complete_alt_m : Binary32) (_is_terrain_alt : Bool) : PMem.M Unit := do
  let mut _complete_alt_m := _complete_alt_m
  let mut _is_terrain_alt := _is_terrain_alt
  PMem.stF32 (this + 8) _complete_alt_m
  PMem.stB (this + 12) _is_terrain_alt
  PMem.stB this false
  let g2 : UInt64 := ((0x86d8 : UInt64) /- &copter -/ + 6840)
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let t'2 ← AC_PosControl.get_pos_estimate_U_m t'1
  let t'3 ← AP_ParamT'float_4.operator_const_float__'1 g2
  let t'4 ← PMem.ldF32 t'3
  let t'5 := (t'2 + t'4)
  PMem.stF32 (this + 4) t'5
  let t'6 ← AP_ParamT'float_4.operator_const_float__'1 g2
  let t'7 ← PMem.ldF32 t'6
  let mut sc'13 := (decide (t'7 > (Int32.toBinary32 ((0 : Int32)))))
  if sc'13 then
    let t'8 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'9 ← Mode.is_disarmed_or_landed t'8
    let mut sc'12 := t'9
    if !sc'12 then
      let t'10 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
      let t'11 ← AP_Motors.get_interlock t'10
      sc'12 := !t'11
    sc'13 := sc'12
  if sc'13 then
    PMem.stB (this + 1) true
  else
    PMem.stB (this + 1) false
  return ()

/-- C++ `Copter::landing_with_GPS : bool ()`, `mode_land.cpp:222-226`. -/
def Copter.landing_with_GPS (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 9488)
  let t'2 ← vcall'Mode'mode_number'1 t'1
  let mut sc'4 := (t'2 == (9 : UInt8))
  if sc'4 then
    let t'3 ← ModeLand.controlling_position (this + 12640)
    sc'4 := t'3
  return sc'4

/-- C++ `Copter::should_disarm_on_failsafe : bool ()`, `events.cpp:463-482`. -/
def Copter.should_disarm_on_failsafe (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB ((this + 9448) + 21)
  if t'1 then
    return true
  let t'2 ← PMem.ldU64 (this + 9488)
  let t'3 ← vcall'Mode'mode_number'1 t'2
  let sw'4 := t'3
  if sw'4 == (0 : UInt8) || sw'4 == (1 : UInt8) then
    let t'5 ← PMem.ldB ((this + 9448) + 15)
    let mut sc'7 := t'5
    if !sc'7 then
      let t'6 ← PMem.ldB ((this + 9448) + 7)
      sc'7 := t'6
    return sc'7
  else if sw'4 == (3 : UInt8) || sw'4 == (27 : UInt8) then
    let t'8 ← PMem.ldB ((this + 9448) + 5)
    let mut sc'10 := !t'8
    if sc'10 then
      let t'9 ← PMem.ldB ((this + 9448) + 7)
      sc'10 := t'9
    return sc'10
  else
    let t'11 ← PMem.ldB ((this + 9448) + 7)
    return t'11

/-- C++ `ModeAuto::subtract_pos_offsets : void (Location &) const`, `mode_auto.cpp:1528-1533`. -/
def ModeAuto.subtract_pos_offsets.body (fp : UInt64) (this : UInt64) (target_loc : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 40)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_PosControl.get_pos_offset_NED_m t'2
  let pos_ofs_ned_m : UInt64 := t'3
  Vector3'double.operator_'2 pos_ofs_ned_m (fp + 0)
  let t'4 := (fp + 0)
  Location.offset'2 target_loc t'4
  return ()

def ModeAuto.subtract_pos_offsets (this : UInt64) (target_loc : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← ModeAuto.subtract_pos_offsets.body fp this target_loc
  PMem.leave fp
  return r

/-- C++ `ModeAuto::get_loc_from_cmd : bool (const AP_Mission::Mission_Command &, const Location &, Location &) const`, `mode_auto.cpp:1548-1575`. -/
def ModeAuto.get_loc_from_cmd.body (fp : UInt64) (this : UInt64) (cmd : UInt64) (default_loc : UInt64) (loc : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU16 (cmd + 2)
  let t'2 ← AP_Mission.cmd_has_location t'1
  if !t'2 then
    return false
  discard <| PMem.memcpy loc (cmd + 8) 16
  discard <| pure (loc)
  let t'3 ← PMem.ldI32 (loc + 8)
  let mut sc'5 := (t'3 == (0 : Int32))
  if sc'5 then
    let t'4 ← PMem.ldI32 (loc + 12)
    sc'5 := (t'4 == (0 : Int32))
  if sc'5 then
    let t'6 ← PMem.ldI32 (default_loc + 8)
    PMem.stI32 (loc + 8) t'6
    let t'7 ← PMem.ldI32 (default_loc + 12)
    PMem.stI32 (loc + 12) t'7
  let t'8 ← PMem.ldI32 (loc + 4)
  if (t'8 == (0 : Int32)) then
    let t'9 ← Location.get_alt_frame loc
    let t'10 ← Location.get_alt_m default_loc t'9 (fp + 0)
    if !t'10 then
      return false
    let t'11 ← PMem.ldF32 (fp + 0)
    let t'12 ← Location.get_alt_frame loc
    Location.set_alt_m loc t'11 t'12
  return true

def ModeAuto.get_loc_from_cmd (this : UInt64) (cmd : UInt64) (default_loc : UInt64) (loc : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← ModeAuto.get_loc_from_cmd.body fp this cmd default_loc loc
  PMem.leave fp
  return r

/-- C++ `ModeRTL::init : bool (bool)`, `mode_rtl.cpp:81-105`. -/
def ModeRTL.init.body (fp : UInt64) (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let mut ignore_checks := ignore_checks
  if !ignore_checks then
    let t'1 ← VehicleBridge.ahrs'0
    let t'2 ← VehicleBridge.AP_AHRS.home_is_set'0 t'1
    if !t'2 then
      return false
  let t'3 ← AP_ParamTBase'float_4.get (this + 116)
  let t'4 ← PMem.ldF32 t'3
  Vector3'double.Vector3 (fp + 24)
  Vector3'double.Vector3'2 (fp + 0) (fp + 24)
  let t'5 ← PMem.ldU64 (this + 24)
  let t'6 ← PMem.ldU64 t'5
  AC_WPNav.wp_and_spline_init_m t'6 t'4 (fp + 0)
  PMem.stU8 (this + 128) (0 : UInt8)
  PMem.stB (this + 129) true
  let t'7 ← PMem.ldBits ((0x86d8 : UInt64) /- &copter -/ + 9508) 75 1
  let t'8 := !((UInt64.toUInt8 (t'7)) != (0 : UInt8))
  PMem.stB (this + 204) t'8
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 19) false
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 26) false
  return true

def ModeRTL.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 48
  let r ← ModeRTL.init.body fp this ignore_checks
  PMem.leave fp
  return r

/-- C++ `ModeGuided::init : bool (bool)`, `mode_guided.cpp:36-48`. -/
def ModeGuided.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let mut ignore_checks := ignore_checks
  ModeGuided.velaccel_control_start this
  Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
  Vector3'float.zero (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
  PMem.stB (this + 116) false
  PMem.stB (this + 117) false
  return true

/-- C++ `ModeAuto::do_change_speed : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2017-2036`. -/
def ModeAuto.do_change_speed (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 ((cmd + 8) + 1)
  if (decide (t'1 > (Int32.toBinary32 ((0 : Int32))))) then
    let t'2 ← PMem.ldU8 (cmd + 8)
    let sw'3 := UInt32.toInt32 (UInt8.toUInt32 (t'2))
    if sw'3 == (2 : Int32) then
      let t'4 ← PMem.ldF32 ((cmd + 8) + 1)
      let t'5 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
      AC_WPNav.set_speed_up_ms t'5 t'4
      let t'6 ← PMem.ldF32 ((cmd + 8) + 1)
      PMem.stF32 ((this + 880) + 4) t'6
    else if sw'3 == (3 : Int32) then
      let t'7 ← PMem.ldF32 ((cmd + 8) + 1)
      let t'8 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
      AC_WPNav.set_speed_down_ms t'8 t'7
      let t'9 ← PMem.ldF32 ((cmd + 8) + 1)
      PMem.stF32 ((this + 880) + 8) t'9
    else if sw'3 == (0 : Int32) || sw'3 == (1 : Int32) then
      let t'10 ← PMem.ldF32 ((cmd + 8) + 1)
      let t'11 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
      AC_WPNav.set_speed_NE_ms t'11 t'10
      let t'12 ← PMem.ldF32 ((cmd + 8) + 1)
      PMem.stF32 (this + 880) t'12
    else
      pure ()
  return ()

/-- C++ `Mode::AutoYaw::set_roi : void (const Location &)`, `autoyaw.cpp:173-207`. -/
def Mode.AutoYaw.set_roi (this : UInt64) (roi_location : UInt64) : PMem.M Unit := do
  let t'1 ← Location.initialised roi_location
  if !t'1 then
    Mode.AutoYaw.set_mode_to_default (0xeb78 : UInt64) /- &Mode::auto_yaw -/ false
  else
    let t'2 ← Location.get_vector_from_origin_NED_m'Vector3_float roi_location (this + 8)
    if t'2 then
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (2 : Int32)
  return ()

/-- C++ `ModeAuto::do_roi : void (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:2055-2058`. -/
def ModeAuto.do_roi (this : UInt64) (cmd : UInt64) : PMem.M Unit := do
  Mode.AutoYaw.set_roi (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (cmd + 8)
  return ()

/-- C++ `Mode::throttle_hover : float () const`, `mode.cpp:969-972`. -/
def Mode.throttle_hover (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 64)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AP_MotorsMulticopter.get_throttle_hover t'2
  return t'3

/-- C++ `Copter::get_non_takeoff_throttle : float ()`, `Attitude.cpp:118-121`. -/
def Copter.get_non_takeoff_throttle.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  PMem.stI32 (fp + 0) (0 : Int32)
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_MotorsMulticopter.get_throttle_hover t'1
  PMem.stF32 (fp + 4) (t'2 / (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))))
  let t'3 ← MAX'int_float (fp + 0) (fp + 4)
  return t'3

def Copter.get_non_takeoff_throttle (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 8
  let r ← Copter.get_non_takeoff_throttle.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::set_accel_throttle_I_from_pilot_throttle : void ()`, `Attitude.cpp:124-130`. -/
def Copter.set_accel_throttle_I_from_pilot_throttle (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 11168)
  let t'2 ← AC_AttitudeControl.get_throttle_in t'1
  let t'3 ← constrain_value_line'float t'2 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((127 : Int32)))
  let mut pilot_throttle : Binary32 := t'3
  let t'4 ← PMem.ldU64 (this + 9528)
  let t'5 ← AP_MotorsMulticopter.get_throttle_hover t'4
  let t'6 ← PMem.ldU64 (this + 11184)
  let t'7 ← AC_PosControl.D_get_accel_pid t'6
  AC_PID.set_integrator t'7 (-(pilot_throttle - t'5))
  return ()

/-- C++ `Mode::get_pilot_speed_dn_ms : float () const`, `mode.cpp:1155-1158`. -/
def Mode.get_pilot_speed_dn_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Copter.get_pilot_speed_dn_ms (0x86d8 : UInt64) /- &copter -/
  return t'1

/-- C++ `ModeAltHold::init : bool (bool)`, `mode_althold.cpp:10-23`. -/
def ModeAltHold.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let mut ignore_checks := ignore_checks
  let t'1 ← PMem.ldU64 (this + 40)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_PosControl.D_is_active t'2
  if !t'3 then
    let t'4 ← PMem.ldU64 (this + 40)
    let t'5 ← PMem.ldU64 t'4
    AC_PosControl.D_init_controller t'5
  let t'6 ← Mode.get_pilot_speed_dn_ms this
  let t'7 ← Mode.get_pilot_speed_up_ms this
  let t'8 ← Mode.get_pilot_accel_D_mss this
  let t'9 ← PMem.ldU64 (this + 40)
  let t'10 ← PMem.ldU64 t'9
  AC_PosControl.D_set_max_speed_accel_m t'10 t'6 t'7 t'8
  let t'11 ← Mode.get_pilot_speed_dn_ms this
  let t'12 ← Mode.get_pilot_speed_up_ms this
  let t'13 ← Mode.get_pilot_accel_D_mss this
  let t'14 ← PMem.ldU64 (this + 40)
  let t'15 ← PMem.ldU64 t'14
  AC_PosControl.D_set_correction_speed_accel_m t'15 t'11 t'12 t'13
  return true

/-- C++ `ModeBrake::init : bool (bool)`, `mode_brake.cpp:10-31`. -/
def ModeBrake.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let mut ignore_checks := ignore_checks
  let t'1 ← PMem.ldU64 (this + 40)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_PosControl.get_vel_estimate_NED_ms t'2
  let t'4 ← Vector3'float.xy t'3
  let t'5 ← Vector2'float.length t'4
  let t'6 ← PMem.ldU64 (this + 40)
  let t'7 ← PMem.ldU64 t'6
  AC_PosControl.NE_set_max_speed_accel_m t'7 t'5 (Binary64.toBinary32 ((Binary64.ofBits 0x401e000000000000 /- 15/2 -/)))
  let t'8 ← PMem.ldU64 (this + 40)
  let t'9 ← PMem.ldU64 t'8
  let t'10 ← AC_PosControl.get_vel_estimate_NED_ms t'9
  let t'11 ← Vector3'float.xy t'10
  let t'12 ← Vector2'float.length t'11
  let t'13 ← PMem.ldU64 (this + 40)
  let t'14 ← PMem.ldU64 t'13
  AC_PosControl.NE_set_correction_speed_accel_m t'14 t'12 (Binary64.toBinary32 ((Binary64.ofBits 0x401e000000000000 /- 15/2 -/)))
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.NE_init_controller t'16
  let t'17 ← PMem.ldU64 (this + 40)
  let t'18 ← PMem.ldU64 t'17
  AC_PosControl.D_set_max_speed_accel_m t'18 (Binary64.toBinary32 ((Binary64.ofBits 0x4004000000000000 /- 5/2 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x4004000000000000 /- 5/2 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x401e000000000000 /- 15/2 -/)))
  let t'19 ← PMem.ldU64 (this + 40)
  let t'20 ← PMem.ldU64 t'19
  AC_PosControl.D_set_correction_speed_accel_m t'20 (Binary64.toBinary32 ((Binary64.ofBits 0x4004000000000000 /- 5/2 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x4004000000000000 /- 5/2 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x401e000000000000 /- 15/2 -/)))
  let t'21 ← PMem.ldU64 (this + 40)
  let t'22 ← PMem.ldU64 t'21
  let t'23 ← AC_PosControl.D_is_active t'22
  if !t'23 then
    let t'24 ← PMem.ldU64 (this + 40)
    let t'25 ← PMem.ldU64 t'24
    AC_PosControl.D_init_controller t'25
  let t'26 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 116) t'26
  return true

/-- C++ `ModeCircle::init : bool (bool)`, `mode_circle.cpp:11-43`. -/
def ModeCircle.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let mut ignore_checks := ignore_checks
  PMem.stB (this + 112) false
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_default_speed_NE_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.get_wp_acceleration_mss t'5
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.NE_set_max_speed_accel_m t'8 t'3 t'6
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_WPNav.get_default_speed_NE_ms t'10
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← PMem.ldU64 t'12
  let t'14 ← AC_WPNav.get_wp_acceleration_mss t'13
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.NE_set_correction_speed_accel_m t'16 t'11 t'14
  let t'17 ← Mode.get_pilot_speed_dn_ms this
  let t'18 ← Mode.get_pilot_speed_up_ms this
  let t'19 ← Mode.get_pilot_accel_D_mss this
  let t'20 ← PMem.ldU64 (this + 40)
  let t'21 ← PMem.ldU64 t'20
  AC_PosControl.D_set_max_speed_accel_m t'21 t'17 t'18 t'19
  let t'22 ← Mode.get_pilot_speed_dn_ms this
  let t'23 ← Mode.get_pilot_speed_up_ms this
  let t'24 ← Mode.get_pilot_accel_D_mss this
  let t'25 ← PMem.ldU64 (this + 40)
  let t'26 ← PMem.ldU64 t'25
  AC_PosControl.D_set_correction_speed_accel_m t'26 t'22 t'23 t'24
  let t'27 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  AC_Circle.init t'27
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (8 : Int32)
  return true

/-- C++ `ModeLand::init : bool (bool)`, `mode_land.cpp:62-108`. -/
def ModeLand.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let mut ignore_checks := ignore_checks
  let t'1 ← Copter.position_ok (0x86d8 : UInt64) /- &copter -/
  PMem.stB (this + 112) t'1
  let t'2 ← PMem.ldU64 (this + 24)
  let t'3 ← PMem.ldU64 t'2
  let t'4 ← AC_WPNav.get_default_speed_NE_ms t'3
  let t'5 ← PMem.ldU64 (this + 24)
  let t'6 ← PMem.ldU64 t'5
  let t'7 ← AC_WPNav.get_wp_acceleration_mss t'6
  let t'8 ← PMem.ldU64 (this + 40)
  let t'9 ← PMem.ldU64 t'8
  AC_PosControl.NE_set_max_speed_accel_m t'9 t'4 t'7
  let t'10 ← PMem.ldU64 (this + 24)
  let t'11 ← PMem.ldU64 t'10
  let t'12 ← AC_WPNav.get_default_speed_NE_ms t'11
  let t'13 ← PMem.ldU64 (this + 24)
  let t'14 ← PMem.ldU64 t'13
  let t'15 ← AC_WPNav.get_wp_acceleration_mss t'14
  let t'16 ← PMem.ldU64 (this + 40)
  let t'17 ← PMem.ldU64 t'16
  AC_PosControl.NE_set_correction_speed_accel_m t'17 t'12 t'15
  let t'18 ← PMem.ldB (this + 112)
  let mut sc'22 := t'18
  if sc'22 then
    let t'19 ← PMem.ldU64 (this + 40)
    let t'20 ← PMem.ldU64 t'19
    let t'21 ← AC_PosControl.NE_is_active t'20
    sc'22 := !t'21
  if sc'22 then
    let t'23 ← PMem.ldU64 (this + 40)
    let t'24 ← PMem.ldU64 t'23
    AC_PosControl.NE_init_controller t'24
  let t'25 ← PMem.ldU64 (this + 24)
  let t'26 ← PMem.ldU64 t'25
  let t'27 ← AC_WPNav.get_default_speed_down_ms t'26
  let t'28 ← PMem.ldU64 (this + 24)
  let t'29 ← PMem.ldU64 t'28
  let t'30 ← AC_WPNav.get_default_speed_up_ms t'29
  let t'31 ← PMem.ldU64 (this + 24)
  let t'32 ← PMem.ldU64 t'31
  let t'33 ← AC_WPNav.get_accel_D_mss t'32
  let t'34 ← PMem.ldU64 (this + 40)
  let t'35 ← PMem.ldU64 t'34
  AC_PosControl.D_set_max_speed_accel_m t'35 t'27 t'30 t'33
  let t'36 ← PMem.ldU64 (this + 24)
  let t'37 ← PMem.ldU64 t'36
  let t'38 ← AC_WPNav.get_default_speed_down_ms t'37
  let t'39 ← PMem.ldU64 (this + 24)
  let t'40 ← PMem.ldU64 t'39
  let t'41 ← AC_WPNav.get_default_speed_up_ms t'40
  let t'42 ← PMem.ldU64 (this + 24)
  let t'43 ← PMem.ldU64 t'42
  let t'44 ← AC_WPNav.get_accel_D_mss t'43
  let t'45 ← PMem.ldU64 (this + 40)
  let t'46 ← PMem.ldU64 t'45
  AC_PosControl.D_set_correction_speed_accel_m t'46 t'38 t'41 t'44
  let t'47 ← PMem.ldU64 (this + 40)
  let t'48 ← PMem.ldU64 t'47
  let t'49 ← AC_PosControl.D_is_active t'48
  if !t'49 then
    let t'50 ← PMem.ldU64 (this + 40)
    let t'51 ← PMem.ldU64 t'50
    AC_PosControl.D_init_controller t'51
  let t'52 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 128) t'52
  PMem.stB (this + 132) false
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 19) false
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 26) false
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  return true

/-- C++ `ModeLoiter::init : bool (bool)`, `mode_loiter.cpp:10-35`. -/
def ModeLoiter.init.body (fp : UInt64) (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let mut ignore_checks := ignore_checks
  let t'1 ← PMem.ldU64 (this + 32)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_Loiter.get_angle_max_rad t'2
  let t'4 ← PMem.ldU64 (this + 56)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_AttitudeControl.get_althold_lean_angle_max_rad t'5
  Mode.get_pilot_desired_lean_angles_rad this (fp + 0) (fp + 8) t'3 t'6
  let t'7 ← PMem.ldF32 (fp + 0)
  let t'8 ← PMem.ldF32 (fp + 8)
  let t'9 ← PMem.ldU64 (this + 32)
  let t'10 ← PMem.ldU64 t'9
  AC_Loiter.set_pilot_desired_acceleration_rad t'10 t'7 t'8
  let t'11 ← PMem.ldU64 (this + 32)
  let t'12 ← PMem.ldU64 t'11
  AC_Loiter.init_target t'12
  let t'13 ← PMem.ldU64 (this + 40)
  let t'14 ← PMem.ldU64 t'13
  let t'15 ← AC_PosControl.D_is_active t'14
  if !t'15 then
    let t'16 ← PMem.ldU64 (this + 40)
    let t'17 ← PMem.ldU64 t'16
    AC_PosControl.D_init_controller t'17
  let t'18 ← Mode.get_pilot_speed_dn_ms this
  let t'19 ← Mode.get_pilot_speed_up_ms this
  let t'20 ← Mode.get_pilot_accel_D_mss this
  let t'21 ← PMem.ldU64 (this + 40)
  let t'22 ← PMem.ldU64 t'21
  AC_PosControl.D_set_max_speed_accel_m t'22 t'18 t'19 t'20
  let t'23 ← Mode.get_pilot_speed_dn_ms this
  let t'24 ← Mode.get_pilot_speed_up_ms this
  let t'25 ← Mode.get_pilot_accel_D_mss this
  let t'26 ← PMem.ldU64 (this + 40)
  let t'27 ← PMem.ldU64 t'26
  AC_PosControl.D_set_correction_speed_accel_m t'27 t'23 t'24 t'25
  return true

def ModeLoiter.init (this : UInt64) (ignore_checks : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 12
  let r ← ModeLoiter.init.body fp this ignore_checks
  PMem.leave fp
  return r

/-- C++ `ModeAuto::do_guided : bool (const AP_Mission::Mission_Command &)`, `mode_auto.cpp:921-948`. -/
def ModeAuto.do_guided.body (fp : UInt64) (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'in_guided_mode'11 t'1
  if !t'2 then
    return false
  let t'3 ← PMem.ldU16 (cmd + 2)
  let sw'4 := UInt32.toInt32 (UInt16.toUInt32 (t'3))
  if sw'4 == (16 : Int32) then
    discard <| PMem.memcpy (fp + 0) (cmd + 8) 16
    let t'5 ← ModeGuided.set_destination ((0x86d8 : UInt64) /- &copter -/ + 12520) (fp + 0) false (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) false (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) false
    return t'5
    ModeAuto.do_yaw this cmd
    return true
  else if sw'4 == (115 : Int32) then
    ModeAuto.do_yaw this cmd
    return true
  else
    return false
  return true

def ModeAuto.do_guided (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← ModeAuto.do_guided.body fp this cmd
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK_Copter::handle_guided_request : bool (AP_Mission::Mission_Command &)`, `GCS_MAVLink_Copter.cpp:337-344`. -/
def GCS_MAVLINK_Copter.handle_guided_request (this : UInt64) (cmd : UInt64) : PMem.M Bool := do
  let t'1 ← ModeAuto.do_guided ((0x86d8 : UInt64) /- &copter -/ + 11368) cmd
  return t'1

/-- C++ `GCS_MAVLINK_Copter::mission_state : MISSION_STATE (const class AP_Mission &) const`, `GCS_MAVLink_Copter.cpp:328-334`. -/
def GCS_MAVLINK_Copter.mission_state (this : UInt64) (mission : UInt64) : PMem.M UInt32 := do
  let t'1 ← ModeAuto.paused ((0x86d8 : UInt64) /- &copter -/ + 11368)
  if t'1 then
    return (4 : UInt32)
  let t'2 ← GCS_MAVLINK.mission_state this mission
  return t'2

/-- C++ `GCS_MAVLINK_Copter::handle_MAV_CMD_CONDITION_YAW : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_MAVLink_Copter.cpp:614-631`. -/
def GCS_MAVLINK_Copter.handle_MAV_CMD_CONDITION_YAW (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldF32 packet
  let mut sc'3 := (decide (t'1 ≥ (Binary32.ofBits 0x00000000 /- 0 -/)))
  if sc'3 then
    let t'2 ← PMem.ldF32 packet
    sc'3 := (decide (t'2 ≤ (Binary32.ofBits 0x43b40000 /- 360 -/)))
  let mut sc'9 := sc'3
  if sc'9 then
    let t'4 ← PMem.ldF32 (packet + 12)
    let t'5 ← is_zero t'4
    let mut sc'8 := t'5
    if !sc'8 then
      let t'6 ← PMem.ldF32 (packet + 12)
      let t'7 ← is_equal'float_float t'6 (Binary32.ofBits 0x3f800000 /- 1 -/)
      sc'8 := t'7
    sc'9 := sc'8
  if sc'9 then
    let t'10 ← PMem.ldF32 packet
    let t'11 ← radians t'10
    let t'12 ← PMem.ldF32 (packet + 4)
    let t'13 ← radians t'12
    let t'14 ← PMem.ldF32 (packet + 8)
    let t'15 ← PMem.ldF32 (packet + 12)
    let t'16 ← is_positive'float t'15
    let t'17 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    Mode.AutoYaw.set_fixed_yaw_rad (0xeb78 : UInt64) /- &Mode::auto_yaw -/ t'11 t'13 (Binary32.toInt8 (t'14)) t'16
    return (0 : UInt32)
  return (4 : UInt32)

/-- C++ `ModeAuto::set_speed_NE_ms : bool (float)`, `mode_auto.cpp:743-748`. -/
def ModeAuto.set_speed_NE_ms (this : UInt64) (speed_ne_ms : Binary32) : PMem.M Bool := do
  let mut speed_ne_ms := speed_ne_ms
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  AC_WPNav.set_speed_NE_ms t'1 speed_ne_ms
  PMem.stF32 (this + 880) speed_ne_ms
  return true

/-- C++ `ModeGuided::set_speed_NE_ms : bool (float)`, `mode_guided.cpp:318-324`. -/
def ModeGuided.set_speed_NE_ms (this : UInt64) (speed_ne_ms : Binary32) : PMem.M Bool := do
  let mut speed_ne_ms := speed_ne_ms
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_wp_acceleration_mss t'2
  let t'4 ← PMem.ldU64 (this + 40)
  let t'5 ← PMem.ldU64 t'4
  AC_PosControl.NE_set_max_speed_accel_m t'5 speed_ne_ms t'3
  let t'6 ← PMem.ldU64 (this + 24)
  let t'7 ← PMem.ldU64 t'6
  let t'8 ← AC_WPNav.get_wp_acceleration_mss t'7
  let t'9 ← PMem.ldU64 (this + 40)
  let t'10 ← PMem.ldU64 t'9
  AC_PosControl.NE_set_correction_speed_accel_m t'10 speed_ne_ms t'8
  return true

/-- C++ `ModeRTL::set_speed_NE_ms : bool (float)`, `mode_rtl.cpp:649-653`. -/
def ModeRTL.set_speed_NE_ms (this : UInt64) (speed_ne_ms : Binary32) : PMem.M Bool := do
  let mut speed_ne_ms := speed_ne_ms
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  AC_WPNav.set_speed_NE_ms t'1 speed_ne_ms
  return true

/-- C++ `ModeAuto::set_speed_down_ms : bool (float)`, `mode_auto.cpp:757-762`. -/
def ModeAuto.set_speed_down_ms (this : UInt64) (speed_down_ms : Binary32) : PMem.M Bool := do
  let mut speed_down_ms := speed_down_ms
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  AC_WPNav.set_speed_down_ms t'1 speed_down_ms
  PMem.stF32 ((this + 880) + 8) speed_down_ms
  return true

/-- C++ `ModeGuided::set_speed_down_ms : bool (float)`, `mode_guided.cpp:334-340`. -/
def ModeGuided.set_speed_down_ms (this : UInt64) (speed_down_ms : Binary32) : PMem.M Bool := do
  let mut speed_down_ms := speed_down_ms
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_default_speed_up_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.get_accel_D_mss t'5
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.D_set_max_speed_accel_m t'8 speed_down_ms t'3 t'6
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_WPNav.get_default_speed_up_ms t'10
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← PMem.ldU64 t'12
  let t'14 ← AC_WPNav.get_accel_D_mss t'13
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.D_set_correction_speed_accel_m t'16 speed_down_ms t'11 t'14
  return true

/-- C++ `ModeRTL::set_speed_down_ms : bool (float)`, `mode_rtl.cpp:661-665`. -/
def ModeRTL.set_speed_down_ms (this : UInt64) (speed_down_ms : Binary32) : PMem.M Bool := do
  let mut speed_down_ms := speed_down_ms
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  AC_WPNav.set_speed_down_ms t'1 speed_down_ms
  return true

/-- C++ `ModeAuto::set_speed_up_ms : bool (float)`, `mode_auto.cpp:750-755`. -/
def ModeAuto.set_speed_up_ms (this : UInt64) (speed_up_ms : Binary32) : PMem.M Bool := do
  let mut speed_up_ms := speed_up_ms
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  AC_WPNav.set_speed_up_ms t'1 speed_up_ms
  PMem.stF32 ((this + 880) + 4) speed_up_ms
  return true

/-- C++ `ModeGuided::set_speed_up_ms : bool (float)`, `mode_guided.cpp:326-332`. -/
def ModeGuided.set_speed_up_ms (this : UInt64) (speed_up_ms : Binary32) : PMem.M Bool := do
  let mut speed_up_ms := speed_up_ms
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_default_speed_down_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.get_accel_D_mss t'5
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.D_set_max_speed_accel_m t'8 t'3 speed_up_ms t'6
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_WPNav.get_default_speed_down_ms t'10
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← PMem.ldU64 t'12
  let t'14 ← AC_WPNav.get_accel_D_mss t'13
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.D_set_correction_speed_accel_m t'16 t'11 speed_up_ms t'14
  return true

/-- C++ `ModeRTL::set_speed_up_ms : bool (float)`, `mode_rtl.cpp:655-659`. -/
def ModeRTL.set_speed_up_ms (this : UInt64) (speed_up_ms : Binary32) : PMem.M Bool := do
  let mut speed_up_ms := speed_up_ms
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  AC_WPNav.set_speed_up_ms t'1 speed_up_ms
  return true

/-- C++ `ModeGuided::do_user_takeoff_start_m : bool (float)`, `mode_guided.cpp:160-205`. -/
def ModeGuided.do_user_takeoff_start_m.body (fp : UInt64) (this : UInt64) (takeoff_alt_m : Binary32) : PMem.M Bool := do
  let mut takeoff_alt_m := takeoff_alt_m
  let mut alt_target_terrain : Bool := false
  discard <| PMem.memcpy (fp + 8) ((0x86d8 : UInt64) /- &copter -/ + 11148) 16
  Location.set_alt_m (fp + 8) takeoff_alt_m (1 : Int32)
  let t'1 ← Location.get_alt_m (fp + 8) (2 : Int32) (fp + 0)
  if !t'1 then
    return false
  PMem.stI32 (this + 112) (0 : Int32)
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  let t'2 ← PMem.ldU64 (this + 40)
  let t'3 ← PMem.ldU64 t'2
  AC_PosControl.D_init_controller t'3
  let t'4 ← PMem.ldF32 (fp + 0)
  _AutoTakeoff.start_m (0x131b0 : UInt64) /- &Mode::auto_takeoff -/ t'4 alt_target_terrain
  PMem.stB (0x131d8 : UInt64) /- &ModeGuided::takeoff_complete -/ false
  return true

def ModeGuided.do_user_takeoff_start_m (this : UInt64) (takeoff_alt_m : Binary32) : PMem.M Bool := do
  let fp ← PMem.enter 24
  let r ← ModeGuided.do_user_takeoff_start_m.body fp this takeoff_alt_m
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK_Copter::handle_command_do_set_roi : MAV_RESULT (const Location &)`, `GCS_MAVLink_Copter.cpp:410-417`. -/
def GCS_MAVLINK_Copter.handle_command_do_set_roi (this : UInt64) (roi_loc : UInt64) : PMem.M UInt32 := do
  let t'1 ← Location.check_latlng roi_loc
  if !t'1 then
    return (4 : UInt32)
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  Mode.AutoYaw.set_roi (0xeb78 : UInt64) /- &Mode::auto_yaw -/ roi_loc
  return (0 : UInt32)

/-- C++ `GCS_MAVLINK_Copter::send_wind : void () const`, `GCS_MAVLink_Copter.cpp:1259-1276`. -/
def GCS_MAVLINK_Copter.send_wind.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Vector3'float.Vector3'2 (fp + 0)
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.airspeed_vector_TAS'1 t'1 (fp + 0)
  if !t'2 then
    return ()
  Vector3'float.Vector3'2 (fp + 16)
  for _ in [0:1] do
    let t'3 ← VehicleBridge.ahrs'0
    let t'4 ← VehicleBridge.AP_AHRS.get_wind'1 t'3 (fp + 16)
    if t'4 then
      pure ()
  let t'5 ← PMem.ldU32 (this + 40)
  let t'6 ← PMem.ldF32 ((fp + 16) + 4)
  let t'7 ← PMem.ldF32 (fp + 16)
  let t'8 ← degrees (Musl.atan2f.atan2f (-t'6) (-t'7))
  let t'9 ← Vector3'float.xy (fp + 16)
  let t'10 ← Vector2'float.length t'9
  let t'11 ← PMem.ldF32 ((fp + 16) + 8)
  mavlink_msg_wind_send t'5 t'8 t'10 t'11
  return ()

def GCS_MAVLINK_Copter.send_wind (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← GCS_MAVLINK_Copter.send_wind.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_Copter::frame_type : MAV_TYPE () const`, `GCS_MAVLink_Copter.cpp:7-27`. -/
def GCS_Copter.frame_type (this : UInt64) : PMem.M UInt32 := do
  let mut mav_type_default : UInt32 := (2 : UInt32)
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  if (t'1 == (0 : UInt64)) then
    return mav_type_default
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'3 ← AP_Motors.get_frame_mav_type t'2
  let mut mav_type : UInt32 := t'3
  if ((UInt32.toInt32 (mav_type)) == (UInt32.toInt32 ((0 : UInt32)))) then
    mav_type := mav_type_default
  return mav_type

/-- C++ `GCS_MAVLINK_Copter::base_mode : uint8_t () const`, `GCS_MAVLink_Copter.cpp:29-60`. -/
def GCS_MAVLINK_Copter.base_mode (this : UInt64) : PMem.M UInt8 := do
  let mut _base_mode : UInt8 := UInt32.toUInt8 ((16 : UInt32))
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let mut sc'4 := (t'1 != (0 : UInt64))
  if sc'4 then
    let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    let t'3 ← AC_PosControl.NE_is_active t'2
    sc'4 := t'3
  if sc'4 then
    let t'5 := (_base_mode ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((8 : UInt32)))))))
    _base_mode := t'5
  let t'6 := (_base_mode ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((64 : UInt32)))))))
  _base_mode := t'6
  let t'7 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let mut sc'10 := (t'7 != (0 : UInt64))
  if sc'10 then
    let t'8 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
    let t'9 ← AP_Motors.armed t'8
    sc'10 := t'9
  if sc'10 then
    let t'11 := (_base_mode ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((128 : UInt32)))))))
    _base_mode := t'11
  let t'12 := (_base_mode ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((1 : UInt32)))))))
  _base_mode := t'12
  return _base_mode

/-- C++ `GCS_Copter::custom_mode : uint32_t () const`, `GCS_MAVLink_Copter.cpp:62-65`. -/
def GCS_Copter.custom_mode (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'mode_number'1 t'1
  return UInt8.toUInt32 (t'2)

/-- C++ `Copter::any_failsafe_triggered : bool () const`, `AP_Common.h:420-422`. -/
def Copter.any_failsafe_triggered (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldBits (this + 9508) 72 1
  let mut sc'3 := (UInt64.toUInt8 (t'1)) != (0 : UInt8)
  if !sc'3 then
    let t'2 ← AP_BattMonitor.has_failsafed (this + 9584)
    sc'3 := t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← PMem.ldBits (this + 9508) 73 1
    sc'5 := (UInt64.toUInt8 (t'4)) != (0 : UInt8)
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← PMem.ldBits (this + 9508) 74 1
    sc'7 := (UInt64.toUInt8 (t'6)) != (0 : UInt8)
  let mut sc'9 := sc'7
  if !sc'9 then
    let t'8 ← PMem.ldBits (this + 9508) 75 1
    sc'9 := (UInt64.toUInt8 (t'8)) != (0 : UInt8)
  let mut sc'11 := sc'9
  if !sc'11 then
    let t'10 ← PMem.ldBits (this + 9508) 76 1
    sc'11 := (UInt64.toUInt8 (t'10)) != (0 : UInt8)
  let mut sc'13 := sc'11
  if !sc'13 then
    let t'12 ← PMem.ldBits (this + 9508) 77 1
    sc'13 := (UInt64.toUInt8 (t'12)) != (0 : UInt8)
  return sc'13

/-- C++ `GCS_MAVLINK_Copter::vehicle_system_status : MAV_STATE () const`, `GCS_MAVLink_Copter.cpp:67-83`. -/
def GCS_MAVLINK_Copter.vehicle_system_status (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← Copter.any_failsafe_triggered (0x86d8 : UInt64) /- &copter -/
  if t'1 then
    return (5 : UInt32)
  let t'2 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  if t'2 then
    return (3 : UInt32)
  let t'3 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
  if !t'3 then
    return (1 : UInt32)
  return (4 : UInt32)

/-- C++ `ModeGuided::get_wp : bool (Location &) const`, `mode_guided.cpp:444-461`. -/
def ModeGuided.get_wp.body (fp : UInt64) (this : UInt64) (destination : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldI32 (this + 112)
  let sw'2 := t'1
  if sw'2 == (1 : Int32) then
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.get_oa_wp_destination t'4 destination
    return t'5
  else if sw'2 == (2 : Int32) then
    let t'6 ← PMem.ldB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/
    let mut c'7 : Int32 := default
    if t'6 then
      c'7 := (3 : Int32)
    else
      c'7 := (2 : Int32)
    Location.from_ekf_offset_NED_m (fp + 0) (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/ c'7
    let t'8 := (fp + 0)
    discard <| PMem.memcpy destination t'8 16
    discard <| pure (destination)
    return true
  else if sw'2 == (6 : Int32) || sw'2 == (0 : Int32) || sw'2 == (5 : Int32) || sw'2 == (4 : Int32) || sw'2 == (3 : Int32) then
    pure ()
  else
    pure ()
  return false

def ModeGuided.get_wp (this : UInt64) (destination : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← ModeGuided.get_wp.body fp this destination
  PMem.leave fp
  return r

/-- C++ `ModeRTL::get_wp : bool (Location &) const`, `mode_rtl.cpp:611-627`. -/
def ModeRTL.get_wp (this : UInt64) (destination : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 128)
  let sw'2 := t'1
  if sw'2 == (0 : UInt8) || sw'2 == (1 : UInt8) || sw'2 == (2 : UInt8) || sw'2 == (3 : UInt8) || sw'2 == (4 : UInt8) then
    let t'3 ← PMem.ldU64 (this + 24)
    let t'4 ← PMem.ldU64 t'3
    let t'5 ← AC_WPNav.get_oa_wp_destination t'4 destination
    return t'5
  else if sw'2 == (5 : UInt8) then
    return false
  else
    pure ()
  return false

/-- C++ `ModeAuto::get_wp : bool (Location &) const`, `mode_auto.cpp:961-976`. -/
def ModeAuto.get_wp (this : UInt64) (destination : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 820)
  let sw'2 := t'1
  if sw'2 == (7 : UInt8) then
    let t'3 ← ModeGuided.get_wp ((0x86d8 : UInt64) /- &copter -/ + 12520) destination
    return t'3
  else if sw'2 == (2 : UInt8) || sw'2 == (5 : UInt8) || sw'2 == (6 : UInt8) then
    let t'4 ← PMem.ldU64 (this + 24)
    let t'5 ← PMem.ldU64 t'4
    let t'6 ← AC_WPNav.get_oa_wp_destination t'5 destination
    return t'6
  else if sw'2 == (4 : UInt8) then
    let t'7 ← ModeRTL.get_wp ((0x86d8 : UInt64) /- &copter -/ + 12888) destination
    return t'7
  else
    return false

/-- C++ `Mode::is_taking_off : bool () const`, `takeoff.cpp:253-259`. -/
def Mode.is_taking_off (this : UInt64) : PMem.M Bool := do
  let t'1 ← vcall'Mode'has_user_takeoff'24 this false
  if !t'1 then
    return false
  let t'2 ← Mode._TakeOff.running (0xede8 : UInt64) /- &Mode::takeoff -/
  return t'2

/-- C++ `GCS_MAVLINK_Copter::send_attitude_target : void ()`, `GCS_MAVLink_Copter.cpp:86-107`. -/
def GCS_MAVLINK_Copter.send_attitude_target.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  AC_AttitudeControl.get_attitude_target_quat t'1 (fp + 16)
  let t'2 := (fp + 16)
  QuaternionT'float.QuaternionT'3 (fp + 0) t'2
  let t'3 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  let t'4 ← AC_AttitudeControl.get_attitude_target_ang_vel t'3
  Vector3'float.Vector3'4 (fp + 32) t'4
  let t'5 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  let t'6 ← AC_AttitudeControl.get_throttle_in t'5
  let mut thrust : Binary32 := t'6
  let t'7 ← PMem.ldF32 (fp + 0)
  PMem.stF32 ((fp + 48) + 0) t'7
  let t'8 ← PMem.ldF32 ((fp + 0) + 4)
  PMem.stF32 ((fp + 48) + 4) t'8
  let t'9 ← PMem.ldF32 ((fp + 0) + 8)
  PMem.stF32 ((fp + 48) + 8) t'9
  let t'10 ← PMem.ldF32 ((fp + 0) + 12)
  PMem.stF32 ((fp + 48) + 12) t'10
  let mut typemask : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'11 ← PMem.ldU32 (this + 40)
  let t'12 ← PMem.ldF32 (fp + 32)
  let t'13 ← PMem.ldF32 ((fp + 32) + 4)
  let t'14 ← PMem.ldF32 ((fp + 32) + 8)
  mavlink_msg_attitude_target_send t'11 (((← PMem.clock) / 1000).toUInt32) (UInt16.toUInt8 (typemask)) (fp + 48) t'12 t'13 t'14 thrust
  return ()

def GCS_MAVLINK_Copter.send_attitude_target (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← GCS_MAVLINK_Copter.send_attitude_target.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK_Copter::send_position_target_local_ned : void ()`, `GCS_MAVLink_Copter.cpp:114-176`. -/
def GCS_MAVLINK_Copter.send_position_target_local_ned.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let t'2 ← vcall'Mode'in_guided_mode'11 t'1
  if !t'2 then
    return ()
  let t'3 ← ModeGuided.submode ((0x86d8 : UInt64) /- &copter -/ + 12520)
  let mut guided_mode : Int32 := t'3
  Vector3'float.Vector3'2 (fp + 0)
  Vector3'float.Vector3'2 (fp + 16)
  Vector3'float.Vector3'2 (fp + 32)
  let mut type_mask : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let sw'4 := guided_mode
  if sw'4 == (6 : Int32) then
    return ()
  else if sw'4 == (0 : Int32) || sw'4 == (1 : Int32) || sw'4 == (2 : Int32) then
    let t'5 := Int16.toUInt16 (Int32.toInt16 (((((((((UInt32.toInt32 ((8 : UInt32))) ||| (UInt32.toInt32 ((16 : UInt32)))) ||| (UInt32.toInt32 ((32 : UInt32)))) ||| (UInt32.toInt32 ((64 : UInt32)))) ||| (UInt32.toInt32 ((128 : UInt32)))) ||| (UInt32.toInt32 ((256 : UInt32)))) ||| (UInt32.toInt32 ((1024 : UInt32)))) ||| (UInt32.toInt32 ((2048 : UInt32))))))
    type_mask := t'5
    let t'6 ← ModeGuided.get_target_pos_NED_m ((0x86d8 : UInt64) /- &copter -/ + 12520)
    Vector3'double.tofloat t'6 (fp + 48)
    let t'7 := (fp + 48)
    discard <| PMem.memcpy (fp + 0) t'7 12
    discard <| pure ((fp + 0))
  else if sw'4 == (3 : Int32) then
    let t'8 := Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 ((1024 : UInt32))) ||| (UInt32.toInt32 ((2048 : UInt32))))))
    type_mask := t'8
    let t'9 ← ModeGuided.get_target_pos_NED_m ((0x86d8 : UInt64) /- &copter -/ + 12520)
    Vector3'double.tofloat t'9 (fp + 64)
    let t'10 := (fp + 64)
    discard <| PMem.memcpy (fp + 0) t'10 12
    discard <| pure ((fp + 0))
    let t'11 ← ModeGuided.get_target_vel_NED_ms ((0x86d8 : UInt64) /- &copter -/ + 12520)
    discard <| PMem.memcpy (fp + 16) t'11 12
    discard <| pure ((fp + 16))
    let t'12 ← ModeGuided.get_target_accel_NED_mss ((0x86d8 : UInt64) /- &copter -/ + 12520)
    discard <| PMem.memcpy (fp + 32) t'12 12
    discard <| pure ((fp + 32))
  else if sw'4 == (4 : Int32) then
    let t'13 := Int16.toUInt16 (Int32.toInt16 ((((((UInt32.toInt32 ((1 : UInt32))) ||| (UInt32.toInt32 ((2 : UInt32)))) ||| (UInt32.toInt32 ((4 : UInt32)))) ||| (UInt32.toInt32 ((1024 : UInt32)))) ||| (UInt32.toInt32 ((2048 : UInt32))))))
    type_mask := t'13
    let t'14 ← ModeGuided.get_target_vel_NED_ms ((0x86d8 : UInt64) /- &copter -/ + 12520)
    discard <| PMem.memcpy (fp + 16) t'14 12
    discard <| pure ((fp + 16))
    let t'15 ← ModeGuided.get_target_accel_NED_mss ((0x86d8 : UInt64) /- &copter -/ + 12520)
    discard <| PMem.memcpy (fp + 32) t'15 12
    discard <| pure ((fp + 32))
  else if sw'4 == (5 : Int32) then
    let t'16 := Int16.toUInt16 (Int32.toInt16 (((((((((UInt32.toInt32 ((1 : UInt32))) ||| (UInt32.toInt32 ((2 : UInt32)))) ||| (UInt32.toInt32 ((4 : UInt32)))) ||| (UInt32.toInt32 ((8 : UInt32)))) ||| (UInt32.toInt32 ((16 : UInt32)))) ||| (UInt32.toInt32 ((32 : UInt32)))) ||| (UInt32.toInt32 ((1024 : UInt32)))) ||| (UInt32.toInt32 ((2048 : UInt32))))))
    type_mask := t'16
    let t'17 ← ModeGuided.get_target_accel_NED_mss ((0x86d8 : UInt64) /- &copter -/ + 12520)
    discard <| PMem.memcpy (fp + 32) t'17 12
    discard <| pure ((fp + 32))
  else
    pure ()
  let t'18 ← PMem.ldU32 (this + 40)
  let t'19 ← PMem.ldF32 (fp + 0)
  let t'20 ← PMem.ldF32 ((fp + 0) + 4)
  let t'21 ← PMem.ldF32 ((fp + 0) + 8)
  let t'22 ← PMem.ldF32 (fp + 16)
  let t'23 ← PMem.ldF32 ((fp + 16) + 4)
  let t'24 ← PMem.ldF32 ((fp + 16) + 8)
  let t'25 ← PMem.ldF32 (fp + 32)
  let t'26 ← PMem.ldF32 ((fp + 32) + 4)
  let t'27 ← PMem.ldF32 ((fp + 32) + 8)
  mavlink_msg_position_target_local_ned_send t'18 (((← PMem.clock) / 1000).toUInt32) (UInt32.toUInt8 ((1 : UInt32))) type_mask t'19 t'20 t'21 t'22 t'23 t'24 t'25 t'26 t'27 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  return ()

def GCS_MAVLINK_Copter.send_position_target_local_ned (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 76
  let r ← GCS_MAVLINK_Copter.send_position_target_local_ned.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_Copter::update_vehicle_sensor_status_flags : void ()`, `GCS_Copter.cpp:23-119`. -/
def GCS_Copter.update_vehicle_sensor_status_flags (this : UInt64) : PMem.M Unit := do
  let t'1 := (this + 16)
  let t'2 ← PMem.ldU32 t'1
  let t'3 := (t'2 ||| (((1024 : UInt32) ||| (2048 : UInt32)) ||| (4096 : UInt32)))
  PMem.stU32 t'1 t'3
  let t'4 := (this + 20)
  let t'5 ← PMem.ldU32 t'4
  let t'6 := (t'5 ||| (((1024 : UInt32) ||| (2048 : UInt32)) ||| (4096 : UInt32)))
  PMem.stU32 t'4 t'6
  let t'7 := (this + 24)
  let t'8 ← PMem.ldU32 t'7
  let t'9 := (t'8 ||| (((1024 : UInt32) ||| (2048 : UInt32)) ||| (4096 : UInt32)))
  PMem.stU32 t'7 t'9
  let t'10 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  if (t'10 != (0 : UInt64)) then
    let t'11 := (this + 16)
    let t'12 ← PMem.ldU32 t'11
    let t'13 := (t'12 ||| (8192 : UInt32))
    PMem.stU32 t'11 t'13
    let t'14 := (this + 16)
    let t'15 ← PMem.ldU32 t'14
    let t'16 := (t'15 ||| (16384 : UInt32))
    PMem.stU32 t'14 t'16
    let t'17 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    let t'18 ← AC_PosControl.NE_is_active t'17
    if t'18 then
      let t'19 := (this + 20)
      let t'20 ← PMem.ldU32 t'19
      let t'21 := (t'20 ||| (16384 : UInt32))
      PMem.stU32 t'19 t'21
      let t'22 := (this + 24)
      let t'23 ← PMem.ldU32 t'22
      let t'24 := (t'23 ||| (16384 : UInt32))
      PMem.stU32 t'22 t'24
    let t'25 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
    let t'26 ← AC_PosControl.D_is_active t'25
    if t'26 then
      let t'27 := (this + 20)
      let t'28 ← PMem.ldU32 t'27
      let t'29 := (t'28 ||| (8192 : UInt32))
      PMem.stU32 t'27 t'29
      let t'30 := (this + 24)
      let t'31 ← PMem.ldU32 t'30
      let t'32 := (t'31 ||| (8192 : UInt32))
      PMem.stU32 t'30 t'32
  let t'33 := (this + 16)
  let t'34 ← PMem.ldU32 t'33
  let t'35 := (t'34 ||| (1073741824 : UInt32))
  PMem.stU32 t'33 t'35
  let t'36 := (this + 20)
  let t'37 ← PMem.ldU32 t'36
  let t'38 := (t'37 ||| (1073741824 : UInt32))
  PMem.stU32 t'36 t'38
  let t'39 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'40 ← AP_Motors.get_thrust_boost t'39
  if !t'40 then
    let t'41 := (this + 24)
    let t'42 ← PMem.ldU32 t'41
    let t'43 := (t'42 ||| (1073741824 : UInt32))
    PMem.stU32 t'41 t'43
  return ()

/-- C++ `GCS_MAVLINK_Copter::send_pid_tuning : void ()`, `GCS_MAVLink_Copter.cpp:229-274`. -/
def GCS_MAVLINK_Copter.send_pid_tuning (this : UInt64) : PMem.M Unit := do
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((16 : UInt64) / (4 : UInt64))))) then break
    let t'4 ← AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ (((0x86d8 : UInt64) /- &copter -/ + 6776) + 60)
    let t'5 ← PMem.ldU16 t'4
    let t'6 ← PMem.ldU32 ((0x12ed8 : UInt64) /- &GCS_MAVLINK_Copter::send_pid_tuning(...)::axes -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
    if !(((UInt32.toInt32 (UInt16.toUInt32 (t'5))) &&& ((1 : Int32) <<< ((UInt32.toInt32 (t'6)) - (1 : Int32)))) != (0 : Int32)) then
      continue
    let t'7 ← PMem.ldU32 (this + 40)
    let t'8 ← comm_get_txspace t'7
    let t'9 ← PMem.ldU32 (this + 40)
    let t'10 ← GCS_MAVLINK.packet_overhead_chan t'9
    let mut c'11 : Bool := default
    if (decide ((UInt16.toUInt32 (t'8)) ≥ (Int32.toUInt32 (((UInt32.toInt32 (UInt8.toUInt32 (t'10))) + (33 : Int32)))))) then
      c'11 := true
    else
      let t'12 ← PMem.ldU32 (this + 40)
      gcs_out_of_space_to_send t'12
      c'11 := false
    if !c'11 then
      return ()
    let mut pid_info : UInt64 := (0 : UInt64)
    let t'13 ← PMem.ldU32 ((0x12ed8 : UInt64) /- &GCS_MAVLINK_Copter::send_pid_tuning(...)::axes -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
    let sw'14 := UInt32.toInt32 (t'13)
    if sw'14 == (1 : Int32) then
      let t'15 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
      let t'16 ← AC_AttitudeControl_Multi.get_rate_roll_pid t'15
      let t'17 ← AC_PID.get_pid_info t'16
      pid_info := t'17
    else if sw'14 == (2 : Int32) then
      let t'18 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
      let t'19 ← AC_AttitudeControl_Multi.get_rate_pitch_pid t'18
      let t'20 ← AC_PID.get_pid_info t'19
      pid_info := t'20
    else if sw'14 == (3 : Int32) then
      let t'21 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
      let t'22 ← AC_AttitudeControl_Multi.get_rate_yaw_pid t'21
      let t'23 ← AC_PID.get_pid_info t'22
      pid_info := t'23
    else if sw'14 == (4 : Int32) then
      let t'24 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'25 ← AC_PosControl.D_get_accel_pid t'24
      let t'26 ← AC_PID.get_pid_info t'25
      pid_info := t'26
    else
      continue
    if (pid_info != (0 : UInt64)) then
      let t'27 ← PMem.ldU32 (this + 40)
      let t'28 ← PMem.ldU32 ((0x12ed8 : UInt64) /- &GCS_MAVLINK_Copter::send_pid_tuning(...)::axes -/ + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      let t'29 ← PMem.ldF32 pid_info
      let t'30 ← PMem.ldF32 (pid_info + 4)
      let t'31 ← PMem.ldF32 (pid_info + 24)
      let t'32 ← PMem.ldF32 (pid_info + 12)
      let t'33 ← PMem.ldF32 (pid_info + 16)
      let t'34 ← PMem.ldF32 (pid_info + 20)
      let t'35 ← PMem.ldF32 (pid_info + 36)
      let t'36 ← PMem.ldF32 (pid_info + 32)
      mavlink_msg_pid_tuning_send t'27 (UInt32.toUInt8 (t'28)) t'29 t'30 t'31 t'32 t'33 t'34 t'35 t'36
  return ()

/-- C++ `GCS_MAVLINK_Copter::send_nav_controller_output : void () const`, `GCS_MAVLink_Copter.cpp:178-195`. -/
def GCS_MAVLINK_Copter.send_nav_controller_output.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 13)
  if !t'1 then
    return ()
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  let t'3 ← AC_AttitudeControl.get_att_target_euler_rad t'2
  let targets_rad : UInt64 := t'3
  let t'4 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
  let mut flightmode : UInt64 := t'4
  let t'5 ← PMem.ldU32 (this + 40)
  let t'6 ← PMem.ldF32 targets_rad
  let t'7 ← degrees t'6
  let t'8 ← PMem.ldF32 (targets_rad + 4)
  let t'9 ← degrees t'8
  let t'10 ← PMem.ldF32 (targets_rad + 8)
  let t'11 ← degrees t'10
  let t'12 ← vcall'Mode'wp_bearing_deg'12 flightmode
  let t'13 ← vcall'Mode'wp_distance_m'13 flightmode
  PMem.stF32 (fp + 0) t'13
  PMem.stI32 (fp + 4) (65535 : Int32)
  let t'14 ← MIN'float_int (fp + 0) (fp + 4)
  let t'15 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  let t'16 ← AC_PosControl.get_pos_error_D_m t'15
  let t'17 ← vcall'Mode'crosstrack_error_m'14 flightmode
  mavlink_msg_nav_controller_output_send t'5 t'7 t'9 (Binary32.toInt16 (t'11)) (Binary32.toInt16 (t'12)) (Binary32.toUInt16 (t'14)) t'16 (Int32.toBinary32 ((0 : Int32))) t'17
  return ()

def GCS_MAVLINK_Copter.send_nav_controller_output (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK_Copter.send_nav_controller_output.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK_Copter::vfr_hud_throttle : int16_t () const`, `GCS_MAVLink_Copter.cpp:218-224`. -/
def GCS_MAVLINK_Copter.vfr_hud_throttle (this : UInt64) : PMem.M Int16 := do
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  if (t'1 == (0 : UInt64)) then
    return Int32.toInt16 ((0 : Int32))
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'3 ← AP_Motors.get_throttle t'2
  return Binary32.toInt16 ((t'3 * (Int32.toBinary32 ((100 : Int32)))))

/-- C++ `GCS_MAVLINK_Copter::vfr_hud_alt : float () const`, `GCS_MAVLink_Copter.cpp:1220-1228`. -/
def GCS_MAVLINK_Copter.vfr_hud_alt (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamTBase'unsigned_int_3.get (((0x86d8 : UInt64) /- &copter -/ + 6840) + 8)
  let t'2 ← PMem.ldU32 t'1
  if (t'2 &&& (2 : UInt32)) != (0 : UInt32) then
    let t'3 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 4)
    return ((Int32.toBinary32 (t'3)) * (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/))
  let t'4 ← GCS_MAVLINK.vfr_hud_alt this
  return t'4

/-- `GCS_MAVLINK_Copter.capabilities` as a pure function of its arguments (it reads and writes no memory). -/
def GCS_MAVLINK_Copter.capabilities.pure' (this : UInt64) : Id UInt64 := do
  let t'1 ← _root_.Vehicle_lib.GCS_MAVLINK.capabilities.pure' this
  return ((Int64.toUInt64 (Int32.toInt64 ((((((((UInt32.toInt32 ((1 : UInt32))) ||| (UInt32.toInt32 ((4 : UInt32)))) ||| (UInt32.toInt32 ((8 : UInt32)))) ||| (UInt32.toInt32 ((128 : UInt32)))) ||| (UInt32.toInt32 ((256 : UInt32)))) ||| (UInt32.toInt32 ((2048 : UInt32)))) ||| (UInt32.toInt32 ((64 : UInt32))))))) ||| t'1)

/-- C++ `GCS_MAVLINK_Copter::capabilities : uint64_t () const`, `GCS_MAVLink_Copter.cpp:1230-1243`. -/
def GCS_MAVLINK_Copter.capabilities (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.GCS_MAVLINK_Copter.capabilities.pure' this)

/-- C++ `GCS_MAVLINK_Copter::send_available_mode : uint8_t (uint8_t) const`, `GCS_MAVLink_Copter.cpp:1354-1504`. -/
def GCS_MAVLINK_Copter.send_available_mode.body (fp : UInt64) (this : UInt64) (index : UInt8) : PMem.M UInt8 := do
  let mut index := index
  PMem.stU64 ((fp + 0) + 0) ((0x86d8 : UInt64) /- &copter -/ + 11368)
  PMem.stU64 ((fp + 0) + 8) ((0x86d8 : UInt64) /- &copter -/ + 11368)
  PMem.stU64 ((fp + 0) + 16) ((0x86d8 : UInt64) /- &copter -/ + 13096)
  PMem.stU64 ((fp + 0) + 24) ((0x86d8 : UInt64) /- &copter -/ + 11256)
  PMem.stU64 ((fp + 0) + 32) ((0x86d8 : UInt64) /- &copter -/ + 12400)
  PMem.stU64 ((fp + 0) + 40) ((0x86d8 : UInt64) /- &copter -/ + 12776)
  PMem.stU64 ((fp + 0) + 48) ((0x86d8 : UInt64) /- &copter -/ + 12520)
  PMem.stU64 ((fp + 0) + 56) ((0x86d8 : UInt64) /- &copter -/ + 12640)
  PMem.stU64 ((fp + 0) + 64) ((0x86d8 : UInt64) /- &copter -/ + 12888)
  PMem.stU64 ((fp + 0) + 72) ((0x86d8 : UInt64) /- &copter -/ + 12280)
  let mut base_mode_count : UInt8 := UInt64.toUInt8 (((80 : UInt64) / (8 : UInt64)))
  let mut mode_count : UInt8 := base_mode_count
  let mut index_zero : UInt8 := Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (index))) - (1 : Int32))))
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (index_zero))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (mode_count))))) then
    return mode_count
  let mut name : UInt64 := default  -- uninitialized in C
  let mut mode_number : UInt8 := default  -- uninitialized in C
  let mut enabled : Bool := default  -- uninitialized in C
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (index_zero))) < (UInt32.toInt32 (UInt8.toUInt32 (base_mode_count))))) then
    let t'1 ← PMem.ldU64 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (index_zero))) * 8).toUInt64)
    let t'2 ← vcall'Mode'name'8 t'1
    name := t'2
    let t'3 ← PMem.ldU64 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (index_zero))) * 8).toUInt64)
    let t'4 ← vcall'Mode'mode_number'1 t'3
    mode_number := t'4
    let t'5 ← PMem.ldU64 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (index_zero))) * 8).toUInt64)
    let t'6 ← vcall'Mode'enabled'18 t'5
    enabled := t'6
  else
    return mode_count
  if ((UInt32.toInt32 (UInt8.toUInt32 (index_zero))) == (0 : Int32)) then
    mode_number := (27 : UInt8)
    let t'7 := (0x14019 : UInt64) /- "Auto RTL" -/
    name := t'7
  else
    if ((UInt32.toInt32 (UInt8.toUInt32 (index_zero))) == (1 : Int32)) then
      mode_number := (3 : UInt8)
      let t'8 := (0x14022 : UInt64) /- "Auto" -/
      name := t'8
  let mut sc'10 := enabled
  if sc'10 then
    let t'9 ← Copter.gcs_mode_enabled (0x86d8 : UInt64) /- &copter -/ mode_number
    sc'10 := t'9
  let mut user_selectable : Bool := sc'10
  let t'11 ← PMem.ldU32 (this + 40)
  let mut c'12 : Int32 := default
  if user_selectable then
    c'12 := (0 : Int32)
  else
    c'12 := UInt32.toInt32 ((2 : UInt32))
  mavlink_msg_available_modes_send t'11 mode_count index (UInt32.toUInt8 ((0 : UInt32))) (UInt8.toUInt32 (mode_number)) (Int32.toUInt32 (c'12)) name
  return mode_count

def GCS_MAVLINK_Copter.send_available_mode (this : UInt64) (index : UInt8) : PMem.M UInt8 := do
  let fp ← PMem.enter 80
  let r ← GCS_MAVLINK_Copter.send_available_mode.body fp this index
  PMem.leave fp
  return r

/-- C++ `ModeRTL::convert_params : void ()`, `mode_rtl.cpp:55-71`. -/
def ModeRTL.convert_params (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.configured (this + 112)
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← AP_Param.configured (this + 116)
    sc'3 := t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← AP_Param.configured (this + 120)
    sc'5 := t'4
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← AP_Param.configured (this + 124)
    sc'7 := t'6
  if sc'7 then
    return ()
  AP_Param.convert_old_parameters_scaled (0xcb18 : UInt64) /- &ModeRTL::convert_params(...)::conversion_info -/ (UInt64.toUInt8 (((96 : UInt64) / (24 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- C++ `ModeLand::convert_params : void ()`, `mode_land.cpp:44-59`. -/
def ModeLand.convert_params (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.configured (this + 116)
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← AP_Param.configured (this + 120)
    sc'3 := t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← AP_Param.configured (this + 124)
    sc'5 := t'4
  if sc'5 then
    return ()
  AP_Param.convert_old_parameters_scaled (0xcbb8 : UInt64) /- &ModeLand::convert_params(...)::conversion_info -/ (UInt64.toUInt8 (((72 : UInt64) / (24 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- C++ `Copter::update_using_interlock : void ()`, `AP_State.cpp:83-93`. -/
def Copter.update_using_interlock (this : UInt64) : PMem.M Unit := do
  let t'1 ← rc
  let t'2 ← RC_Channels.find_channel_for_option t'1 (32 : Int32)
  let t'3 := (t'2 != (0 : UInt64))
  PMem.stB ((this + 9448) + 18) t'3
  return ()

/-- C++ `Copter::init_rc_in : void ()`, `radio.cpp:20-51`. -/
def Copter.init_rc_in (this : UInt64) : PMem.M Unit := do
  let t'1 ← rc
  let t'2 ← RC_Channels.get_roll_channel t'1
  PMem.stU64 (this + 8600) t'2
  let t'3 ← rc
  let t'4 ← RC_Channels.get_pitch_channel t'3
  PMem.stU64 (this + 8608) t'4
  let t'5 ← rc
  let t'6 ← RC_Channels.get_throttle_channel t'5
  PMem.stU64 (this + 8616) t'6
  let t'7 ← rc
  let t'8 ← RC_Channels.get_yaw_channel t'7
  PMem.stU64 (this + 8624) t'8
  let t'9 ← PMem.ldU64 (this + 8600)
  RC_Channel.set_angle t'9 (Int16.toUInt16 (Int32.toInt16 ((4500 : Int32))))
  let t'10 ← PMem.ldU64 (this + 8608)
  RC_Channel.set_angle t'10 (Int16.toUInt16 (Int32.toInt16 ((4500 : Int32))))
  let t'11 ← PMem.ldU64 (this + 8624)
  RC_Channel.set_angle t'11 (Int16.toUInt16 (Int32.toInt16 ((4500 : Int32))))
  let t'12 ← PMem.ldU64 (this + 8616)
  RC_Channel.set_range t'12 (Int16.toUInt16 (Int32.toInt16 ((1000 : Int32))))
  Copter.default_dead_zones this
  PMem.stB ((this + 9448) + 15) true
  return ()

/-- C++ `Copter::allocate_motors : void ()`, `system.cpp:357-565`. -/
def Copter.allocate_motors.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamTBase'signed_char_1.get ((this + 6840) + 12)
  let t'2 ← PMem.ldI8 t'1
  let sw'3 := UInt32.toInt32 ((Int32.toUInt32 (Int8.toInt32 (t'2))))
  if sw'3 == (1 : Int32) then
    let t'4 ← PMem.alloc 776
    let t'5 ← AP_Scheduler.get_loop_rate_hz ((0x86d8 : UInt64) /- &copter -/ + 208)
    AP_MotorsMatrix.AP_MotorsMatrix t'4 t'5
    PMem.stU64 (this + 9528) t'4
    let t'6 := (0x1b68 : UInt64) /- &AP_MotorsMulticopter::var_info -/
    PMem.stU64 (this + 9536) t'6
  else
    let t'7 ← PMem.alloc 776
    let t'8 ← AP_Scheduler.get_loop_rate_hz ((0x86d8 : UInt64) /- &copter -/ + 208)
    AP_MotorsMatrix.AP_MotorsMatrix t'7 t'8
    PMem.stU64 (this + 9528) t'7
    let t'9 := (0x1b68 : UInt64) /- &AP_MotorsMulticopter::var_info -/
    PMem.stU64 (this + 9536) t'9
  let t'10 ← PMem.ldU64 (this + 9528)
  if (t'10 == (0 : UInt64)) then
    let t'11 ← AP_ParamTBase'signed_char_1.get ((this + 6840) + 12)
    let t'12 ← PMem.ldI8 t'11
    PMem.stU64 (fp + 0) (UInt32.toUInt64 ((Int32.toUInt32 (Int8.toInt32 (t'12)))))
    AP_BoardConfig.allocation_error (0x14d5a : UInt64) /- "FRAME_CLASS=%u" -/ (fp + 0)
  let t'13 ← PMem.ldU64 (this + 9528)
  let t'14 ← PMem.ldU64 (this + 9536)
  AP_Param.load_object_from_eeprom t'13 t'14
  let t'15 ← VehicleBridge.AP_AHRS.create_view'2 (this + 4080) (0 : UInt8) (Int32.toBinary32 ((0 : Int32)))
  PMem.stU64 (this + 8760) t'15
  let t'16 ← PMem.ldU64 (this + 8760)
  if (t'16 == (0 : UInt64)) then
    AP_BoardConfig.allocation_error (0x14d69 : UInt64) /- "AP_AHRS_View" -/ (fp + 8)
  let t'17 ← PMem.alloc 1112
  let t'18 ← PMem.ldU64 (this + 8760)
  let t'19 ← PMem.ldU64 (this + 9528)
  AC_AttitudeControl_Multi.AC_AttitudeControl_Multi t'17 t'18 t'19
  PMem.stU64 (this + 11168) t'17
  let t'20 := (0x19d0 : UInt64) /- &AC_AttitudeControl_Multi::var_info -/
  PMem.stU64 (this + 11176) t'20
  let t'21 ← PMem.ldU64 (this + 11168)
  if (t'21 == (0 : UInt64)) then
    AP_BoardConfig.allocation_error (0x14d76 : UInt64) /- "AttitudeControl" -/ (fp + 16)
  let t'22 ← PMem.ldU64 (this + 11168)
  let t'23 ← PMem.ldU64 (this + 11176)
  AP_Param.load_object_from_eeprom t'22 t'23
  let t'24 ← PMem.alloc 984
  let t'25 ← PMem.ldU64 (this + 8760)
  let t'26 ← PMem.ldU64 (this + 9528)
  let t'27 ← PMem.ldU64 (this + 11168)
  AC_PosControl.AC_PosControl t'24 t'25 t'26 t'27
  PMem.stU64 (this + 11184) t'24
  let t'28 ← PMem.ldU64 (this + 11184)
  if (t'28 == (0 : UInt64)) then
    AP_BoardConfig.allocation_error (0x14d86 : UInt64) /- "PosControl" -/ (fp + 24)
  let t'29 ← PMem.ldU64 (this + 11184)
  let t'30 ← PMem.ldU64 (this + 11184)
  AP_Param.load_object_from_eeprom t'29 (0x33c8 : UInt64) /- &AC_PosControl::var_info -/
  let t'31 ← PMem.alloc 2504
  let t'32 ← PMem.ldU64 (this + 8760)
  let t'33 ← PMem.ldU64 (this + 11184)
  let t'34 ← PMem.ldU64 (this + 11168)
  AC_WPNav.AC_WPNav t'31 t'32 t'33 t'34
  PMem.stU64 (this + 11192) t'31
  let t'35 ← PMem.ldU64 (this + 11192)
  if (t'35 == (0 : UInt64)) then
    AP_BoardConfig.allocation_error (0x14d91 : UInt64) /- "WPNav" -/ (fp + 32)
  let t'36 ← PMem.ldU64 (this + 11192)
  let t'37 ← PMem.ldU64 (this + 11192)
  AP_Param.load_object_from_eeprom t'36 (0x2fe8 : UInt64) /- &AC_WPNav::var_info -/
  let t'38 ← PMem.alloc 104
  let t'39 ← PMem.ldU64 (this + 8760)
  let t'40 ← PMem.ldU64 (this + 11184)
  let t'41 ← PMem.ldU64 (this + 11168)
  AC_Loiter.AC_Loiter t'38 t'39 t'40 t'41
  PMem.stU64 (this + 11200) t'38
  let t'42 ← PMem.ldU64 (this + 11200)
  if (t'42 == (0 : UInt64)) then
    AP_BoardConfig.allocation_error (0x14d97 : UInt64) /- "LoiterNav" -/ (fp + 40)
  let t'43 ← PMem.ldU64 (this + 11200)
  let t'44 ← PMem.ldU64 (this + 11200)
  AP_Param.load_object_from_eeprom t'43 (0x31b8 : UInt64) /- &AC_Loiter::var_info -/
  let t'45 ← PMem.alloc 104
  let t'46 ← PMem.ldU64 (this + 8760)
  let t'47 ← PMem.ldU64 (this + 11184)
  AC_Circle.AC_Circle t'45 t'46 t'47
  PMem.stU64 (this + 11208) t'45
  let t'48 ← PMem.ldU64 (this + 11208)
  if (t'48 == (0 : UInt64)) then
    AP_BoardConfig.allocation_error (0x14da1 : UInt64) /- "CircleNav" -/ (fp + 48)
  let t'49 ← PMem.ldU64 (this + 11208)
  let t'50 ← PMem.ldU64 (this + 11208)
  AP_Param.load_object_from_eeprom t'49 (0x3320 : UInt64) /- &AC_Circle::var_info -/
  AP_Param.reload_defaults_file true
  let t'51 ← AP_ParamTBase'signed_char_1.get ((this + 6840) + 12)
  let t'52 ← PMem.ldI8 t'51
  let sw'53 := UInt32.toInt32 ((Int32.toUInt32 (Int8.toInt32 (t'52))))
  let t'54 ← PMem.ldU64 (this + 9528)
  let t'55 ← AP_Motors.is_brushed_pwm_type t'54
  if t'55 then
    PMem.stI16 (fp + 56) (Int32.toInt16 ((16000 : Int32)))
    AP_ParamTBase'short_2.set_default ((this + 6776) + 62) (fp + 56)
  let t'56 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
  AC_AttitudeControl.convert_parameters t'56
  let t'57 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
  AC_PosControl.convert_parameters t'57
  let t'58 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
  AC_WPNav.convert_parameters t'58
  let t'59 ← PMem.ldU64 (this + 11200)
  AC_Loiter.convert_parameters t'59
  let t'60 ← PMem.ldU64 (this + 11208)
  AC_Circle.convert_parameters t'60
  AP_Param.invalidate_count
  return ()

def Copter.allocate_motors (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 58
  let r ← Copter.allocate_motors.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::set_throttle_zero_flag : void (int16_t)`, `radio.cpp:179-195`. -/
def Copter.set_throttle_zero_flag (this : UInt64) (throttle_control : Int16) : PMem.M Unit := do
  let mut throttle_control := throttle_control
  let mut tnow_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldB ((this + 9448) + 18)
  let mut sc'3 := ((!t'1) && (decide ((Int16.toInt32 (throttle_control)) > (0 : Int32))))
  if sc'3 then
    let t'2 ← SRV_Channels.get_emergency_stop
    sc'3 := !t'2
  let mut sc'8 := sc'3
  if !sc'8 then
    let t'4 ← PMem.ldB ((this + 9448) + 18)
    let mut sc'7 := t'4
    if sc'7 then
      let t'5 ← PMem.ldU64 (this + 9528)
      let t'6 ← AP_Motors.get_interlock t'5
      sc'7 := t'6
    sc'8 := sc'7
  let mut sc'10 := sc'8
  if !sc'10 then
    let t'9 ← Copter.air_mode_active this
    sc'10 := t'9
  if sc'10 then
    PMem.stU32 (0xedb0 : UInt64) /- &Copter::set_throttle_zero_flag(...)::last_nonzero_throttle_ms -/ tnow_ms
    PMem.stB ((this + 9448) + 15) false
  else
    let t'11 ← PMem.ldU32 (0xedb0 : UInt64) /- &Copter::set_throttle_zero_flag(...)::last_nonzero_throttle_ms -/
    if (decide ((tnow_ms - t'11) > (Int32.toUInt32 ((400 : Int32))))) then
      PMem.stB ((this + 9448) + 15) true
  return ()

/-- C++ `Copter::radio_passthrough_to_motors : void ()`, `radio.cpp:198-204`. -/
def Copter.radio_passthrough_to_motors (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 8600)
  let t'2 ← RC_Channel.norm_input t'1
  let t'3 ← PMem.ldU64 (this + 8608)
  let t'4 ← RC_Channel.norm_input t'3
  let t'5 ← PMem.ldU64 (this + 8616)
  let t'6 ← RC_Channel.get_control_in_zero_dz t'5
  let t'7 ← PMem.ldU64 (this + 8624)
  let t'8 ← RC_Channel.norm_input t'7
  let t'9 ← PMem.ldU64 (this + 9528)
  AP_Motors.set_radio_passthrough t'9 t'2 t'4 (t'6 * (Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/)) t'8
  return ()

/-- C++ `Copter::run_rate_controller_main : void ()`, `Attitude.cpp:10-24`. -/
def Copter.run_rate_controller_main (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP.scheduler
  let t'2 ← AP_Scheduler.get_last_loop_time_s t'1
  let mut last_loop_time_s : Binary32 := t'2
  let t'3 ← PMem.ldU64 (this + 11184)
  AC_PosControl.set_dt_s t'3 last_loop_time_s
  let t'4 ← PMem.ldU64 (this + 11168)
  AC_AttitudeControl.set_dt_s t'4 last_loop_time_s
  let t'5 ← PMem.ldB (this + 13209)
  if !t'5 then
    let t'6 ← PMem.ldU64 (this + 9528)
    AP_Motors.set_dt_s t'6 last_loop_time_s
    let t'7 ← PMem.ldU64 (this + 11168)
    AC_AttitudeControl_Multi.rate_controller_run t'7
  let t'8 ← PMem.ldU64 (this + 11168)
  AC_AttitudeControl.rate_controller_target_reset t'8
  return ()

/-- C++ `Copter::read_inertia : void ()`, `inertia.cpp:4-41`. -/
def Copter.read_inertia.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 8852)
  let t'2 ← PMem.ldU64 (this + 11184)
  AC_PosControl.update_estimates t'2 t'1
  Location.Location (fp + 0)
  for _ in [0:1] do
    let mut __unique_name___COUNTER__ : Bool := default  -- uninitialized in C
    let t'3 ← VehicleBridge.AP_AHRS.get_location'1 (this + 4080) (fp + 0)
    __unique_name___COUNTER__ := t'3
  let t'4 ← PMem.ldI32 ((fp + 0) + 8)
  PMem.stI32 ((this + 11148) + 8) t'4
  let t'5 ← PMem.ldI32 ((fp + 0) + 12)
  PMem.stI32 ((this + 11148) + 12) t'5
  let t'6 ← VehicleBridge.ahrs'0
  let t'7 ← VehicleBridge.AP_AHRS.get_relative_position_D_origin_float'1 t'6 (fp + 16)
  if !t'7 then
    return ()
  let t'8 ← PMem.ldF32 (fp + 16)
  let mut alt_above_origin_m : Binary32 := -t'8
  Location.set_alt_m (this + 11148) alt_above_origin_m (2 : Int32)
  let t'9 ← Location.initialised (this + 11148)
  if !t'9 then
    return ()
  let t'10 ← VehicleBridge.AP_AHRS.home_is_set'0 (this + 4080)
  let mut sc'12 := !t'10
  if !sc'12 then
    let t'11 ← Location.change_alt_frame (this + 11148) (1 : Int32)
    sc'12 := !t'11
  if sc'12 then
    Location.set_alt_m (this + 11148) alt_above_origin_m (1 : Int32)
  return ()

def Copter.read_inertia (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← Copter.read_inertia.body fp this
  PMem.leave fp
  return r

/-- C++ `Mode::get_pilot_desired_climb_rate_ms : float () const`, `mode.cpp:1093-1096`. -/
def Mode.get_pilot_desired_climb_rate_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Copter.get_pilot_desired_climb_rate_ms (0x86d8 : UInt64) /- &copter -/
  return t'1

/-- C++ `Mode::_TakeOff::triggered_ms : bool (const float) const`, `mode.cpp:607-624`. -/
def Mode._TakeOff.triggered_ms (this : UInt64) (target_climb_rate_ms : Binary32) : PMem.M Bool := do
  let mut target_climb_rate_ms := target_climb_rate_ms
  let t'1 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
  if !t'1 then
    return false
  if (decide (target_climb_rate_ms ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
    return false
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'3 ← AP_Motors.get_spool_state t'2
  if (t'3 != (3 : UInt8)) then
    return false
  return true

/-- C++ `Mode::get_alt_hold_state_D_ms : Mode::AltHoldModeState (float)`, `mode.cpp:1022-1071`. -/
def Mode.get_alt_hold_state_D_ms (this : UInt64) (target_climb_rate_ms : Binary32) : PMem.M Int32 := do
  let mut target_climb_rate_ms := target_climb_rate_ms
  let t'1 ← PMem.ldU64 (this + 64)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AP_Motors.armed t'2
  if !t'3 then
    let t'4 ← PMem.ldU64 (this + 64)
    let t'5 ← PMem.ldU64 t'4
    AP_MotorsMulticopter.set_desired_spool_state t'5 (0 : UInt8)
    let t'6 ← PMem.ldU64 (this + 64)
    let t'7 ← PMem.ldU64 t'6
    let t'8 ← AP_Motors.get_spool_state t'7
    let sw'9 := t'8
    if sw'9 == (0 : UInt8) then
      return (0 : Int32)
    else if sw'9 == (1 : UInt8) then
      return (2 : Int32)
    else
      return (3 : Int32)
  else
    let t'10 ← Mode._TakeOff.running (0xede8 : UInt64) /- &Mode::takeoff -/
    let mut sc'12 := t'10
    if !sc'12 then
      let t'11 ← Mode._TakeOff.triggered_ms (0xede8 : UInt64) /- &Mode::takeoff -/ target_climb_rate_ms
      sc'12 := t'11
    if sc'12 then
      return (1 : Int32)
    else
      let t'13 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 5)
      let mut sc'15 := !t'13
      if !sc'15 then
        let t'14 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 7)
        sc'15 := t'14
      if sc'15 then
        let mut sc'17 := (decide (target_climb_rate_ms < (Binary32.ofBits 0x00000000 /- 0 -/)))
        if sc'17 then
          let t'16 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 18)
          sc'17 := !t'16
        if sc'17 then
          let t'18 ← PMem.ldU64 (this + 64)
          let t'19 ← PMem.ldU64 t'18
          AP_MotorsMulticopter.set_desired_spool_state t'19 (1 : UInt8)
        else
          let t'20 ← PMem.ldU64 (this + 64)
          let t'21 ← PMem.ldU64 t'20
          AP_MotorsMulticopter.set_desired_spool_state t'21 (2 : UInt8)
        let t'22 ← PMem.ldU64 (this + 64)
        let t'23 ← PMem.ldU64 t'22
        let t'24 ← AP_Motors.get_spool_state t'23
        if (t'24 == (1 : UInt8)) then
          return (2 : Int32)
        else
          return (3 : Int32)
      else
        let t'25 ← PMem.ldU64 (this + 64)
        let t'26 ← PMem.ldU64 t'25
        AP_MotorsMulticopter.set_desired_spool_state t'26 (2 : UInt8)
        return (4 : Int32)

/-- C++ `ModeRTL::is_complete : bool () const`, `mode_rtl.cpp:437-442`. -/
def ModeRTL.is_complete (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 129)
  let mut sc'9 := t'1
  if sc'9 then
    let t'2 ← PMem.ldU8 (this + 128)
    let mut sc'8 := (t'2 == (4 : UInt8))
    if !sc'8 then
      let t'3 ← PMem.ldU8 (this + 128)
      let mut sc'7 := (t'3 == (5 : UInt8))
      if sc'7 then
        let t'4 ← PMem.ldU64 (this + 64)
        let t'5 ← PMem.ldU64 t'4
        let t'6 ← AP_Motors.get_spool_state t'5
        sc'7 := (t'6 == (1 : UInt8))
      sc'8 := sc'7
    sc'9 := sc'8
  return sc'9

/-- C++ `ModeAuto::verify_RTL : bool ()`, `mode_auto.cpp:2259-2262`. -/
def ModeAuto.verify_RTL (this : UInt64) : PMem.M Bool := do
  let t'1 ← ModeRTL.is_complete ((0x86d8 : UInt64) /- &copter -/ + 12888)
  return t'1

/-- C++ `Mode::make_safe_ground_handling : void (bool)`, `mode.cpp:658-690`. -/
def Mode.make_safe_ground_handling (this : UInt64) (force_throttle_unlimited : Bool) : PMem.M Unit := do
  let mut force_throttle_unlimited := force_throttle_unlimited
  if force_throttle_unlimited then
    let t'1 ← PMem.ldU64 (this + 64)
    let t'2 ← PMem.ldU64 t'1
    AP_MotorsMulticopter.set_desired_spool_state t'2 (2 : UInt8)
  else
    let t'3 ← PMem.ldU64 (this + 64)
    let t'4 ← PMem.ldU64 t'3
    AP_MotorsMulticopter.set_desired_spool_state t'4 (1 : UInt8)
  let t'5 ← PMem.ldU64 (this + 56)
  let t'6 ← PMem.ldU64 t'5
  AC_AttitudeControl.reset_rate_controller_I_terms_smoothly t'6
  let t'7 ← PMem.ldU64 (this + 64)
  let t'8 ← PMem.ldU64 t'7
  let t'9 ← AP_Motors.get_spool_state t'8
  let sw'10 := t'9
  if sw'10 == (0 : UInt8) || sw'10 == (1 : UInt8) then
    let t'11 ← PMem.ldU64 (this + 56)
    let t'12 ← PMem.ldU64 t'11
    AC_AttitudeControl.reset_yaw_target_and_rate t'12 true
  else if sw'10 == (2 : UInt8) || sw'10 == (3 : UInt8) || sw'10 == (4 : UInt8) then
    pure ()
  else
    pure ()
  let t'13 ← PMem.ldU64 (this + 40)
  let t'14 ← PMem.ldU64 t'13
  AC_PosControl.NE_relax_velocity_controller t'14
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.NE_update_controller t'16
  let t'17 ← PMem.ldU64 (this + 40)
  let t'18 ← PMem.ldU64 t'17
  AC_PosControl.D_relax_controller t'18 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'19 ← PMem.ldU64 (this + 40)
  let t'20 ← PMem.ldU64 t'19
  AC_PosControl.D_update_controller t'20
  let t'21 ← PMem.ldU64 (this + 56)
  let t'22 ← PMem.ldU64 t'21
  AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad t'22 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  return ()

/-- C++ `Mode::AutoYaw::look_ahead_yaw_rad : float ()`, `autoyaw.cpp:16-27`. -/
def Mode.AutoYaw.look_ahead_yaw_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  Vector3'float.Vector3'2 (fp + 0)
  let t'1 ← Copter.position_ok (0x86d8 : UInt64) /- &copter -/
  let mut sc'4 := t'1
  if sc'4 then
    let t'2 ← VehicleBridge.ahrs'0
    let t'3 ← VehicleBridge.AP_AHRS.get_velocity_NED'1 t'2 (fp + 0)
    sc'4 := t'3
  if sc'4 then
    let t'5 ← Vector3'float.xy (fp + 0)
    let t'6 ← Vector2'float.length_squared t'5
    let mut speed_ms_sq : Binary32 := t'6
    if (decide (speed_ms_sq > (Int32.toBinary32 (((1 : Int32) * (1 : Int32)))))) then
      let t'7 ← PMem.ldF32 ((fp + 0) + 4)
      let t'8 ← PMem.ldF32 (fp + 0)
      let t'9 := (Musl.atan2f.atan2f t'7 t'8)
      PMem.stF32 (this + 32) t'9
  let t'10 ← PMem.ldF32 (this + 32)
  return t'10

def Mode.AutoYaw.look_ahead_yaw_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 12
  let r ← Mode.AutoYaw.look_ahead_yaw_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `Mode::AutoYaw::yaw_rad : float ()`, `autoyaw.cpp:234-321`. -/
def Mode.AutoYaw.yaw_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  for _ in [0:1] do
    let t'1 ← PMem.ldI32 this
    let sw'2 := t'1
    if sw'2 == (2 : Int32) then
      let t'3 ← Mode.AutoYaw.roi_yaw_rad this
      PMem.stF32 (this + 36) t'3
    else if sw'2 == (3 : Int32) then
      let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
      let t'4 ← PMem.ldU32 (this + 28)
      let mut dt : Binary32 := ((UInt32.toBinary32 ((now_ms - t'4))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f50624dd2f1a9fc /- 1/1000 -/))))
      PMem.stU32 (this + 28) now_ms
      let t'5 ← PMem.ldF32 (this + 20)
      let t'6 ← PMem.ldF32 (this + 24)
      let t'7 ← PMem.ldF32 (this + 24)
      let t'8 ← constrain_value_line'float t'5 ((-dt) * t'6) (dt * t'7) (Int32.toUInt32 ((249 : Int32)))
      let mut yaw_angle_step_rad : Binary32 := t'8
      let t'9 := (this + 20)
      let t'10 ← PMem.ldF32 t'9
      let t'11 := (t'10 - yaw_angle_step_rad)
      PMem.stF32 t'9 t'11
      let t'12 := (this + 36)
      let t'13 ← PMem.ldF32 t'12
      let t'14 := (t'13 + yaw_angle_step_rad)
      PMem.stF32 t'12 t'14
      break
      let t'15 ← Mode.AutoYaw.look_ahead_yaw_rad this
      PMem.stF32 (this + 36) t'15
    else if sw'2 == (4 : Int32) then
      let t'16 ← Mode.AutoYaw.look_ahead_yaw_rad this
      PMem.stF32 (this + 36) t'16
    else if sw'2 == (5 : Int32) then
      let t'17 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9576)
      PMem.stF32 (this + 36) t'17
    else if sw'2 == (8 : Int32) then
      let t'18 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
      let t'19 ← AC_Circle.is_active t'18
      if t'19 then
        let t'20 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
        let t'21 ← AC_Circle.get_yaw_rad t'20
        PMem.stF32 (this + 36) t'21
        break
      let t'22 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
      let t'23 ← AC_Circle.face_direction_of_travel t'22
      if !t'23 then
        let t'24 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
        let t'25 ← AC_Circle.get_center_NED_m t'24
        let t'26 ← Vector3'double.xy t'25
        let t'27 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
        let t'28 ← AC_PosControl.get_pos_desired_NED_m t'27
        let t'29 ← Vector3'double.xy t'28
        Vector2'double.operator_ t'26 (fp + 8) t'29
        let t'30 := (fp + 8)
        Vector2'double.tofloat t'30 (fp + 24)
        let t'31 := (fp + 24)
        Vector2'float.Vector2'3 (fp + 0) t'31
        let t'32 ← Vector2'float.is_zero (fp + 0)
        if !t'32 then
          let t'33 ← Vector2'float.angle (fp + 0)
          PMem.stF32 (this + 36) t'33
        break
      let t'34 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'35 ← AC_PosControl.get_vel_desired_NED_ms t'34
      let t'36 ← Vector3'float.xy t'35
      Vector2'float.Vector2'4 (fp + 32) t'36
      let t'37 ← Vector2'float.length (fp + 32)
      if (decide (t'37 > (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/))) then
        let t'38 ← Vector2'float.angle (fp + 32)
        PMem.stF32 (this + 36) t'38
    else if sw'2 == (6 : Int32) then
      let mut now_ms'2 : UInt32 := ((← PMem.clock) / 1000).toUInt32
      let t'39 ← PMem.ldU32 (this + 28)
      let mut dt'2 : Binary32 := ((UInt32.toBinary32 ((now_ms'2 - t'39))) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f50624dd2f1a9fc /- 1/1000 -/))))
      PMem.stU32 (this + 28) now_ms'2
      let t'40 := (this + 36)
      let t'41 ← PMem.ldF32 t'40
      let t'42 ← PMem.ldF32 (this + 40)
      let t'43 := (t'41 + (t'42 * dt'2))
      PMem.stF32 t'40 t'43
      break
      let t'44 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
      let t'45 ← AC_AttitudeControl.get_att_target_euler_rad t'44
      let t'46 ← PMem.ldF32 (t'45 + 8)
      PMem.stF32 (this + 36) t'46
    else if sw'2 == (0 : Int32) || sw'2 == (7 : Int32) || sw'2 == (10 : Int32) || sw'2 == (9 : Int32) then
      let t'47 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11168)
      let t'48 ← AC_AttitudeControl.get_att_target_euler_rad t'47
      let t'49 ← PMem.ldF32 (t'48 + 8)
      PMem.stF32 (this + 36) t'49
    else if sw'2 == (1 : Int32) then
      let t'50 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'51 ← AC_PosControl.get_yaw_rad t'50
      PMem.stF32 (this + 36) t'51
    else
      let t'52 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11184)
      let t'53 ← AC_PosControl.get_yaw_rad t'52
      PMem.stF32 (this + 36) t'53
  let t'54 ← PMem.ldF32 (this + 36)
  return t'54

def Mode.AutoYaw.yaw_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 40
  let r ← Mode.AutoYaw.yaw_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `Mode::AutoYaw::get_heading : AC_AttitudeControl::HeadingCommand ()`, `autoyaw.cpp:356-398`. -/
def Mode.AutoYaw.get_heading.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 44) t'1
  let t'2 ← rc
  let t'3 ← RC_Channels_Copter.has_valid_input t'2
  let mut sc'6 := t'3
  if sc'6 then
    let t'4 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'5 ← vcall'Mode'use_pilot_yaw'33 t'4
    sc'6 := t'5
  if sc'6 then
    let t'7 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'8 ← Mode.get_pilot_desired_yaw_rate_rads t'7
    PMem.stF32 (this + 44) t'8
    let t'9 ← PMem.ldF32 (this + 44)
    let t'10 ← is_zero t'9
    if !t'10 then
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (9 : Int32)
  else
    let t'11 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    if (t'11 == (9 : Int32)) then
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  AC_AttitudeControl.HeadingCommand.HeadingCommand (fp + 0)
  let t'12 ← Mode.AutoYaw.yaw_rad (0xeb78 : UInt64) /- &Mode::auto_yaw -/
  PMem.stF32 (fp + 0) t'12
  let t'13 ← Mode.AutoYaw.rate_rads (0xeb78 : UInt64) /- &Mode::auto_yaw -/
  PMem.stF32 ((fp + 0) + 4) t'13
  let t'14 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
  let sw'15 := t'14
  if sw'15 == (0 : Int32) || sw'15 == (7 : Int32) || sw'15 == (9 : Int32) || sw'15 == (10 : Int32) then
    PMem.stI32 ((fp + 0) + 8) (2 : Int32)
  else if sw'15 == (1 : Int32) || sw'15 == (2 : Int32) || sw'15 == (3 : Int32) || sw'15 == (4 : Int32) || sw'15 == (5 : Int32) || sw'15 == (6 : Int32) || sw'15 == (8 : Int32) then
    PMem.stI32 ((fp + 0) + 8) (1 : Int32)
  else
    pure ()
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 sret (fp + 0)
  return ()

def Mode.AutoYaw.get_heading (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← Mode.AutoYaw.get_heading.body fp this sret
  PMem.leave fp
  return r

/-- C++ `ModeAuto::wp_run : void ()`, `mode_auto.cpp:1134-1154`. -/
def ModeAuto.wp_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    Mode.make_safe_ground_handling this false
    return ()
  let t'2 ← PMem.ldU64 (this + 64)
  let t'3 ← PMem.ldU64 t'2
  AP_MotorsMulticopter.set_desired_spool_state t'3 (2 : UInt8)
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.update_wpnav t'5
  Copter.failsafe_terrain_set_status (0x86d8 : UInt64) /- &copter -/ t'6
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.D_update_controller t'8
  let t'9 ← PMem.ldU64 (this + 40)
  let t'10 ← PMem.ldU64 t'9
  AC_PosControl.get_thrust_vector t'10 (fp + 0)
  let t'11 := (fp + 0)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 32)
  let t'12 := (fp + 32)
  discard <| PMem.memcpy (fp + 16) t'12 12
  let t'13 ← PMem.ldU64 (this + 56)
  let t'14 ← PMem.ldU64 t'13
  AC_AttitudeControl.input_thrust_vector_heading t'14 t'11 (fp + 16)
  return ()

def ModeAuto.wp_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 44
  let r ← ModeAuto.wp_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::loiter_run : void ()`, `mode_auto.cpp:1194-1198`. -/
def ModeAuto.loiter_run (this : UInt64) : PMem.M Unit := do
  ModeAuto.wp_run this
  return ()

/-- C++ `Mode::get_alt_above_ground_m : float () const`, `mode.cpp:695-711`. -/
def Mode.get_alt_above_ground_m.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Copter.get_rangefinder_height_interpolated_m (0x86d8 : UInt64) /- &copter -/ (fp + 0)
  if t'1 then
    let t'2 ← PMem.ldF32 (fp + 0)
    return t'2
  let t'3 ← Location.initialised ((0x86d8 : UInt64) /- &copter -/ + 11148)
  if !t'3 then
    return Int32.toBinary32 ((0 : Int32))
  let t'4 ← Location.get_alt_m ((0x86d8 : UInt64) /- &copter -/ + 11148) (3 : Int32) (fp + 0)
  if t'4 then
    let t'5 ← PMem.ldF32 (fp + 0)
    return t'5
  let t'6 ← PMem.ldI32 (((0x86d8 : UInt64) /- &copter -/ + 11148) + 4)
  return ((Int32.toBinary32 (t'6)) * (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))))

def Mode.get_alt_above_ground_m (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← Mode.get_alt_above_ground_m.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeAuto::get_alt_above_ground_m : float () const`, `mode_auto.cpp:2455-2488`. -/
def ModeAuto.get_alt_above_ground_m.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU8 (this + 820)
  if (t'1 == (3 : UInt8)) then
    let t'2 ← Copter.get_rangefinder_height_interpolated_m (0x86d8 : UInt64) /- &copter -/ (fp + 0)
    if t'2 then
      let t'3 ← PMem.ldF32 (fp + 0)
      return t'3
    let t'4 ← AP_Mission.get_current_nav_cmd (this + 112)
    let cmd : UInt64 := t'4
    for _ in [0:1] do
      let t'5 ← PMem.ldU16 (cmd + 2)
      let sw'6 := UInt32.toInt32 (UInt16.toUInt32 (t'5))
      if sw'6 == (85 : Int32) || sw'6 == (21 : Int32) then
        let t'7 ← PMem.ldI32 ((cmd + 8) + 8)
        let mut sc'9 := (t'7 != (0 : Int32))
        if !sc'9 then
          let t'8 ← PMem.ldI32 ((cmd + 8) + 12)
          sc'9 := (t'8 != (0 : Int32))
        if sc'9 then
          let t'10 ← Location.get_height_above ((0x86d8 : UInt64) /- &copter -/ + 11148) (cmd + 8) (fp + 8)
          if t'10 then
            let t'11 ← PMem.ldF64 (fp + 8)
            return Binary64.toBinary32 (t'11)
        break
      else
        pure ()
  let t'12 ← Mode.get_alt_above_ground_m this
  return t'12

def ModeAuto.get_alt_above_ground_m (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← ModeAuto.get_alt_above_ground_m.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeRTL::return_start : bool ()`, `mode_rtl.cpp:247-256`. -/
def ModeRTL.return_start (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.set_wp_destination_loc t'2 ((this + 132) + 32) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let mut destination_set : Bool := t'3
  Mode.AutoYaw.set_mode_to_default (0xeb78 : UInt64) /- &Mode::auto_yaw -/ true
  return destination_set

/-- C++ `ModeRTL::descent_start : void ()`, `mode_rtl.cpp:332-344`. -/
def ModeRTL.descent_start (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 40)
  let t'2 ← PMem.ldU64 t'1
  AC_PosControl.D_init_controller_stopping_point t'2
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  return ()

/-- C++ `ModeRTL::land_start : void ()`, `mode_rtl.cpp:404-427`. -/
def ModeRTL.land_start (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_default_speed_NE_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.get_wp_acceleration_mss t'5
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.NE_set_max_speed_accel_m t'8 t'3 t'6
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_WPNav.get_default_speed_NE_ms t'10
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← PMem.ldU64 t'12
  let t'14 ← AC_WPNav.get_wp_acceleration_mss t'13
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.NE_set_correction_speed_accel_m t'16 t'11 t'14
  let t'17 ← PMem.ldU64 (this + 40)
  let t'18 ← PMem.ldU64 t'17
  let t'19 ← AC_PosControl.NE_is_active t'18
  if !t'19 then
    let t'20 ← PMem.ldU64 (this + 40)
    let t'21 ← PMem.ldU64 t'20
    AC_PosControl.NE_init_controller t'21
  let t'22 ← PMem.ldU64 (this + 40)
  let t'23 ← PMem.ldU64 t'22
  let t'24 ← AC_PosControl.D_is_active t'23
  if !t'24 then
    let t'25 ← PMem.ldU64 (this + 40)
    let t'26 ← PMem.ldU64 t'25
    AC_PosControl.D_init_controller t'26
  Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  return ()

/-- C++ `ModeRTL::run_wp_controllers : bool ()`, `mode_rtl.cpp:260-282`. -/
def ModeRTL.run_wp_controllers.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    Mode.make_safe_ground_handling this false
    return false
  let t'2 ← PMem.ldU64 (this + 64)
  let t'3 ← PMem.ldU64 t'2
  AP_MotorsMulticopter.set_desired_spool_state t'3 (2 : UInt8)
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.update_wpnav t'5
  Copter.failsafe_terrain_set_status (0x86d8 : UInt64) /- &copter -/ t'6
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.D_update_controller t'8
  let t'9 ← PMem.ldU64 (this + 40)
  let t'10 ← PMem.ldU64 t'9
  AC_PosControl.get_thrust_vector t'10 (fp + 0)
  let t'11 := (fp + 0)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 32)
  let t'12 := (fp + 32)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 16) t'12
  let t'13 ← PMem.ldU64 (this + 56)
  let t'14 ← PMem.ldU64 t'13
  AC_AttitudeControl.input_thrust_vector_heading t'14 t'11 (fp + 16)
  return true

def ModeRTL.run_wp_controllers (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 44
  let r ← ModeRTL.run_wp_controllers.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeRTL::climb_return_run : void ()`, `mode_rtl.cpp:286-294`. -/
def ModeRTL.climb_return_run (this : UInt64) : PMem.M Unit := do
  let t'1 ← ModeRTL.run_wp_controllers this
  if !t'1 then
    return ()
  let t'2 ← PMem.ldU64 (this + 24)
  let t'3 ← PMem.ldU64 t'2
  let t'4 ← AC_WPNav.reached_wp_destination t'3
  PMem.stB (this + 129) t'4
  return ()

/-- C++ `ModeRTL::hold_at_return_point_run : void ()`, `mode_rtl.cpp:309-329`. -/
def ModeRTL.hold_at_return_point_run (this : UInt64) : PMem.M Unit := do
  let t'1 ← ModeRTL.run_wp_controllers this
  if !t'1 then
    return ()
  let t'2 ← PMem.ldU32 (this + 200)
  let mut hold_elapsed_ms : UInt32 := ((((← PMem.clock) / 1000).toUInt32) - t'2)
  let t'3 ← PMem.ldU64 (this + 8)
  let t'4 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (t'3 + 16)
  let t'5 ← PMem.ldU32 t'4
  if (decide (hold_elapsed_ms ≥ t'5)) then
    let t'6 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    if (t'6 == (5 : Int32)) then
      let t'7 ← PMem.ldU64 (this + 48)
      let t'8 ← VehicleBridge.AP_AHRS.get_yaw_rad'0 t'7
      let t'9 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 9576)
      let t'10 ← wrap_PI'float (t'8 - t'9)
      let t'11 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/)))
      if (decide ((Binary32.abs t'10) ≤ t'11)) then
        PMem.stB (this + 129) true
    else
      PMem.stB (this + 129) true
  return ()

/-- C++ `ModeGuided::pause_control_run : void ()`, `mode_guided.cpp:889-915`. -/
def ModeGuided.pause_control_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    let t'2 ← Copter.is_tradheli (0x86d8 : UInt64) /- &copter -/
    let mut sc'6 := t'2
    if sc'6 then
      let t'3 ← PMem.ldU64 (this + 64)
      let t'4 ← PMem.ldU64 t'3
      let t'5 ← AP_Motors.get_interlock t'4
      sc'6 := t'5
    Mode.make_safe_ground_handling this sc'6
    return ()
  let t'7 ← PMem.ldU64 (this + 64)
  let t'8 ← PMem.ldU64 t'7
  AP_MotorsMulticopter.set_desired_spool_state t'8 (2 : UInt8)
  Vector2'float.Vector2 (fp + 0)
  Vector2'float.Vector2 (fp + 8)
  let t'9 ← PMem.ldU64 (this + 40)
  let t'10 ← PMem.ldU64 t'9
  AC_PosControl.input_vel_accel_NE_m t'10 (fp + 0) (fp + 8) false
  PMem.stF32 (fp + 16) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let t'11 ← PMem.ldU64 (this + 40)
  let t'12 ← PMem.ldU64 t'11
  AC_PosControl.input_vel_accel_D_m t'12 (fp + 16) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) false
  let t'13 ← PMem.ldU64 (this + 40)
  let t'14 ← PMem.ldU64 t'13
  AC_PosControl.NE_update_controller t'14
  let t'15 ← PMem.ldU64 (this + 40)
  let t'16 ← PMem.ldU64 t'15
  AC_PosControl.D_update_controller t'16
  let t'17 ← PMem.ldU64 (this + 40)
  let t'18 ← PMem.ldU64 t'17
  AC_PosControl.get_thrust_vector t'18 (fp + 24)
  let t'19 := (fp + 24)
  let t'20 ← PMem.ldU64 (this + 56)
  let t'21 ← PMem.ldU64 t'20
  AC_AttitudeControl.input_thrust_vector_rate_heading_rads t'21 t'19 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) true
  return ()

def ModeGuided.pause_control_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 36
  let r ← ModeGuided.pause_control_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeGuided::wp_control_run : void ()`, `mode_guided.cpp:229-249`. -/
def ModeGuided.wp_control_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    let t'2 ← Copter.is_tradheli (0x86d8 : UInt64) /- &copter -/
    let mut sc'6 := t'2
    if sc'6 then
      let t'3 ← PMem.ldU64 (this + 64)
      let t'4 ← PMem.ldU64 t'3
      let t'5 ← AP_Motors.get_interlock t'4
      sc'6 := t'5
    Mode.make_safe_ground_handling this sc'6
    return ()
  let t'7 ← PMem.ldU64 (this + 64)
  let t'8 ← PMem.ldU64 t'7
  AP_MotorsMulticopter.set_desired_spool_state t'8 (2 : UInt8)
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← PMem.ldU64 t'9
  let t'11 ← AC_WPNav.update_wpnav t'10
  Copter.failsafe_terrain_set_status (0x86d8 : UInt64) /- &copter -/ t'11
  let t'12 ← PMem.ldU64 (this + 40)
  let t'13 ← PMem.ldU64 t'12
  AC_PosControl.D_update_controller t'13
  let t'14 ← PMem.ldU64 (this + 40)
  let t'15 ← PMem.ldU64 t'14
  AC_PosControl.get_thrust_vector t'15 (fp + 0)
  let t'16 := (fp + 0)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 32)
  let t'17 := (fp + 32)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 16) t'17
  let t'18 ← PMem.ldU64 (this + 56)
  let t'19 ← PMem.ldU64 t'18
  AC_AttitudeControl.input_thrust_vector_heading t'19 t'16 (fp + 16)
  return ()

def ModeGuided.wp_control_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 44
  let r ← ModeGuided.wp_control_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeGuided::get_timeout_ms : uint32_t () const`, `mode_guided.cpp:1202-1205`. -/
def ModeGuided.get_timeout_ms.body (fp : UInt64) (this : UInt64) : PMem.M UInt32 := do
  PMem.stF32 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/)))
  let t'1 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1700) (fp + 0)
  let t'2 ← PMem.ldF32 t'1
  return Binary32.toUInt32 ((t'2 * (Int32.toBinary32 ((1000 : Int32)))))

def ModeGuided.get_timeout_ms (this : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 4
  let r ← ModeGuided.get_timeout_ms.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeGuided::accel_control_run : void ()`, `mode_guided.cpp:789-830`. -/
def ModeGuided.accel_control_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    let t'2 ← Copter.is_tradheli (0x86d8 : UInt64) /- &copter -/
    let mut sc'6 := t'2
    if sc'6 then
      let t'3 ← PMem.ldU64 (this + 64)
      let t'4 ← PMem.ldU64 t'3
      let t'5 ← AP_Motors.get_interlock t'4
      sc'6 := t'5
    Mode.make_safe_ground_handling this sc'6
    return ()
  let t'7 ← PMem.ldU64 (this + 64)
  let t'8 ← PMem.ldU64 t'7
  AP_MotorsMulticopter.set_desired_spool_state t'8 (2 : UInt8)
  let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'9 ← PMem.ldU32 (0x12e30 : UInt64) /- &update_time_ms -/
  let t'10 ← ModeGuided.get_timeout_ms this
  if (decide ((tnow - t'9) > t'10)) then
    Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
    Vector3'float.zero (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
    let t'11 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    let mut sc'13 := (t'11 == (7 : Int32))
    if !sc'13 then
      let t'12 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
      sc'13 := (t'12 == (6 : Int32))
    if sc'13 then
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
    let t'14 ← Vector3'float.xy (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
    let t'15 ← Vector3'float.xy (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
    let t'16 ← PMem.ldU64 (this + 40)
    let t'17 ← PMem.ldU64 t'16
    AC_PosControl.input_vel_accel_NE_m t'17 t'14 t'15 false
    let t'18 ← PMem.ldF32 ((0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/ + 8)
    let t'19 ← PMem.ldU64 (this + 40)
    let t'20 ← PMem.ldU64 t'19
    AC_PosControl.input_vel_accel_D_m t'20 ((0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/ + 8) t'18 false
  else
    let t'21 ← Vector3'float.xy (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
    let t'22 ← PMem.ldU64 (this + 40)
    let t'23 ← PMem.ldU64 t'22
    AC_PosControl.input_accel_NE_m t'23 t'21
    let t'24 ← ModeGuided.stabilizing_vel_NE this
    if !t'24 then
      let t'25 ← PMem.ldU64 (this + 40)
      let t'26 ← PMem.ldU64 t'25
      AC_PosControl.NE_stop_vel_stabilisation t'26
    else
      let t'27 ← ModeGuided.stabilizing_pos_NE this
      if !t'27 then
        let t'28 ← PMem.ldU64 (this + 40)
        let t'29 ← PMem.ldU64 t'28
        AC_PosControl.NE_stop_pos_stabilisation t'29
    let t'30 ← PMem.ldF32 ((0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/ + 8)
    let t'31 ← PMem.ldU64 (this + 40)
    let t'32 ← PMem.ldU64 t'31
    AC_PosControl.input_accel_D_m t'32 t'30
  let t'33 ← PMem.ldU64 (this + 40)
  let t'34 ← PMem.ldU64 t'33
  AC_PosControl.NE_update_controller t'34
  let t'35 ← PMem.ldU64 (this + 40)
  let t'36 ← PMem.ldU64 t'35
  AC_PosControl.D_update_controller t'36
  let t'37 ← PMem.ldU64 (this + 40)
  let t'38 ← PMem.ldU64 t'37
  AC_PosControl.get_thrust_vector t'38 (fp + 0)
  let t'39 := (fp + 0)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 32)
  let t'40 := (fp + 32)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 16) t'40
  let t'41 ← PMem.ldU64 (this + 56)
  let t'42 ← PMem.ldU64 t'41
  AC_AttitudeControl.input_thrust_vector_heading t'42 t'39 (fp + 16)
  return ()

def ModeGuided.accel_control_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 44
  let r ← ModeGuided.accel_control_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeGuided::velaccel_control_run : void ()`, `mode_guided.cpp:834-885`. -/
def ModeGuided.velaccel_control_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    let t'2 ← Copter.is_tradheli (0x86d8 : UInt64) /- &copter -/
    let mut sc'6 := t'2
    if sc'6 then
      let t'3 ← PMem.ldU64 (this + 64)
      let t'4 ← PMem.ldU64 t'3
      let t'5 ← AP_Motors.get_interlock t'4
      sc'6 := t'5
    Mode.make_safe_ground_handling this sc'6
    return ()
  let t'7 ← PMem.ldU64 (this + 64)
  let t'8 ← PMem.ldU64 t'7
  AP_MotorsMulticopter.set_desired_spool_state t'8 (2 : UInt8)
  let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'9 ← PMem.ldU32 (0x12e30 : UInt64) /- &update_time_ms -/
  let t'10 ← ModeGuided.get_timeout_ms this
  if (decide ((tnow - t'9) > t'10)) then
    Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
    Vector3'float.zero (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
    let t'11 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    let mut sc'13 := (t'11 == (7 : Int32))
    if !sc'13 then
      let t'12 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
      sc'13 := (t'12 == (6 : Int32))
    if sc'13 then
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  let mut do_avoid : Bool := false
  let t'14 ← ModeGuided.stabilizing_vel_NE this
  if ((!t'14) && (!do_avoid)) then
    let t'15 ← Vector3'float.xy (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
    let t'16 ← PMem.ldU64 (this + 40)
    let t'17 ← PMem.ldU64 t'16
    let t'18 ← AC_PosControl.get_vel_desired_NED_ms t'17
    let t'19 ← Vector3'float.xy t'18
    discard <| PMem.memcpy t'15 t'19 8
    discard <| pure (t'15)
  let t'20 ← Vector3'float.xy (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
  let t'21 ← Vector3'float.xy (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
  let t'22 ← PMem.ldU64 (this + 40)
  let t'23 ← PMem.ldU64 t'22
  AC_PosControl.input_vel_accel_NE_m t'23 t'20 t'21 false
  let t'24 ← ModeGuided.stabilizing_vel_NE this
  if ((!t'24) && (!do_avoid)) then
    let t'25 ← PMem.ldU64 (this + 40)
    let t'26 ← PMem.ldU64 t'25
    AC_PosControl.NE_stop_vel_stabilisation t'26
  else
    let t'27 ← ModeGuided.stabilizing_pos_NE this
    if ((!t'27) && (!do_avoid)) then
      let t'28 ← PMem.ldU64 (this + 40)
      let t'29 ← PMem.ldU64 t'28
      AC_PosControl.NE_stop_pos_stabilisation t'29
  let t'30 ← PMem.ldF32 ((0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/ + 8)
  let t'31 ← PMem.ldU64 (this + 40)
  let t'32 ← PMem.ldU64 t'31
  AC_PosControl.input_vel_accel_D_m t'32 ((0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/ + 8) t'30 false
  let t'33 ← PMem.ldU64 (this + 40)
  let t'34 ← PMem.ldU64 t'33
  AC_PosControl.NE_update_controller t'34
  let t'35 ← PMem.ldU64 (this + 40)
  let t'36 ← PMem.ldU64 t'35
  AC_PosControl.D_update_controller t'36
  let t'37 ← PMem.ldU64 (this + 40)
  let t'38 ← PMem.ldU64 t'37
  AC_PosControl.get_thrust_vector t'38 (fp + 0)
  let t'39 := (fp + 0)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 32)
  let t'40 := (fp + 32)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 16) t'40
  let t'41 ← PMem.ldU64 (this + 56)
  let t'42 ← PMem.ldU64 t'41
  AC_AttitudeControl.input_thrust_vector_heading t'42 t'39 (fp + 16)
  return ()

def ModeGuided.velaccel_control_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 44
  let r ← ModeGuided.velaccel_control_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeGuided::posvelaccel_control_run : void ()`, `mode_guided.cpp:919-974`. -/
def ModeGuided.posvelaccel_control_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  if t'1 then
    let t'2 ← Copter.is_tradheli (0x86d8 : UInt64) /- &copter -/
    let mut sc'6 := t'2
    if sc'6 then
      let t'3 ← PMem.ldU64 (this + 64)
      let t'4 ← PMem.ldU64 t'3
      let t'5 ← AP_Motors.get_interlock t'4
      sc'6 := t'5
    Mode.make_safe_ground_handling this sc'6
    return ()
  let t'7 ← PMem.ldU64 (this + 64)
  let t'8 ← PMem.ldU64 t'7
  AP_MotorsMulticopter.set_desired_spool_state t'8 (2 : UInt8)
  let mut tnow : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'9 ← PMem.ldU32 (0x12e30 : UInt64) /- &update_time_ms -/
  let t'10 ← ModeGuided.get_timeout_ms this
  if (decide ((tnow - t'9) > t'10)) then
    Vector3'float.zero (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
    Vector3'float.zero (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
    let t'11 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
    let mut sc'13 := (t'11 == (7 : Int32))
    if !sc'13 then
      let t'12 ← Mode.AutoYaw.mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/
      sc'13 := (t'12 == (6 : Int32))
    if sc'13 then
      Mode.AutoYaw.set_mode (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (0 : Int32)
  let t'14 ← ModeGuided.stabilizing_vel_NE this
  if !t'14 then
    let t'15 ← Vector3'double.xy (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/
    let t'16 ← PMem.ldU64 (this + 40)
    let t'17 ← PMem.ldU64 t'16
    let t'18 ← AC_PosControl.get_pos_desired_NED_m t'17
    let t'19 ← Vector3'double.xy t'18
    discard <| PMem.memcpy t'15 t'19 16
    discard <| pure (t'15)
    let t'20 ← Vector3'float.xy (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
    let t'21 ← PMem.ldU64 (this + 40)
    let t'22 ← PMem.ldU64 t'21
    let t'23 ← AC_PosControl.get_vel_desired_NED_ms t'22
    let t'24 ← Vector3'float.xy t'23
    discard <| PMem.memcpy t'20 t'24 8
    discard <| pure (t'20)
  else
    let t'25 ← ModeGuided.stabilizing_pos_NE this
    if !t'25 then
      let t'26 ← Vector3'double.xy (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/
      let t'27 ← PMem.ldU64 (this + 40)
      let t'28 ← PMem.ldU64 t'27
      let t'29 ← AC_PosControl.get_pos_desired_NED_m t'28
      let t'30 ← Vector3'double.xy t'29
      discard <| PMem.memcpy t'26 t'30 16
      discard <| pure (t'26)
  let t'31 ← Vector3'double.xy (0x12e38 : UInt64) /- &guided_pos_target_ned_m -/
  let t'32 ← Vector3'float.xy (0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/
  let t'33 ← Vector3'float.xy (0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/
  let t'34 ← PMem.ldU64 (this + 40)
  let t'35 ← PMem.ldU64 t'34
  AC_PosControl.input_pos_vel_accel_NE_m t'35 t'31 t'32 t'33 false
  let t'36 ← ModeGuided.stabilizing_vel_NE this
  if !t'36 then
    let t'37 ← PMem.ldU64 (this + 40)
    let t'38 ← PMem.ldU64 t'37
    AC_PosControl.NE_stop_vel_stabilisation t'38
  else
    let t'39 ← ModeGuided.stabilizing_pos_NE this
    if !t'39 then
      let t'40 ← PMem.ldU64 (this + 40)
      let t'41 ← PMem.ldU64 t'40
      AC_PosControl.NE_stop_pos_stabilisation t'41
  let t'42 ← PMem.ldB (0x12e50 : UInt64) /- &guided_is_terrain_alt -/
  if t'42 then
    pure ()
  let t'43 ← PMem.ldF64 ((0x12e38 : UInt64) /- &guided_pos_target_ned_m -/ + 16)
  PMem.stF32 (fp + 0) (Binary64.toBinary32 (t'43))
  let t'44 ← PMem.ldF32 ((0xebb8 : UInt64) /- &guided_accel_target_ned_mss -/ + 8)
  let t'45 ← PMem.ldU64 (this + 40)
  let t'46 ← PMem.ldU64 t'45
  AC_PosControl.input_pos_vel_accel_D_m t'46 (fp + 0) ((0xeba8 : UInt64) /- &guided_vel_target_ned_ms -/ + 8) t'44 false
  let t'47 ← PMem.ldF32 (fp + 0)
  let t'48 := Binary32.toBinary64 (t'47)
  PMem.stF64 ((0x12e38 : UInt64) /- &guided_pos_target_ned_m -/ + 16) t'48
  let t'49 ← PMem.ldU64 (this + 40)
  let t'50 ← PMem.ldU64 t'49
  AC_PosControl.NE_update_controller t'50
  let t'51 ← PMem.ldU64 (this + 40)
  let t'52 ← PMem.ldU64 t'51
  AC_PosControl.D_update_controller t'52
  let t'53 ← PMem.ldU64 (this + 40)
  let t'54 ← PMem.ldU64 t'53
  AC_PosControl.get_thrust_vector t'54 (fp + 8)
  let t'55 := (fp + 8)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 40)
  let t'56 := (fp + 40)
  AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (fp + 24) t'56
  let t'57 ← PMem.ldU64 (this + 56)
  let t'58 ← PMem.ldU64 t'57
  AC_AttitudeControl.input_thrust_vector_heading t'58 t'55 (fp + 24)
  return ()

def ModeGuided.posvelaccel_control_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 52
  let r ← ModeGuided.posvelaccel_control_run.body fp this
  PMem.leave fp
  return r

/-- C++ `Mode::zero_throttle_and_relax_ac : void (bool)`, `mode.cpp:634-643`. -/
def Mode.zero_throttle_and_relax_ac (this : UInt64) (spool_up : Bool) : PMem.M Unit := do
  let mut spool_up := spool_up
  if spool_up then
    let t'1 ← PMem.ldU64 (this + 64)
    let t'2 ← PMem.ldU64 t'1
    AP_MotorsMulticopter.set_desired_spool_state t'2 (2 : UInt8)
  else
    let t'3 ← PMem.ldU64 (this + 64)
    let t'4 ← PMem.ldU64 t'3
    AP_MotorsMulticopter.set_desired_spool_state t'4 (1 : UInt8)
  let t'5 ← PMem.ldU64 (this + 56)
  let t'6 ← PMem.ldU64 t'5
  AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad t'6 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'7 ← AP_ParamT'float_4.operator_const_float__'1 (((0x86d8 : UInt64) /- &copter -/ + 6776) + 4)
  let t'8 ← PMem.ldF32 t'7
  let t'9 ← PMem.ldU64 (this + 56)
  let t'10 ← PMem.ldU64 t'9
  AC_AttitudeControl_Multi.set_throttle_out t'10 (Binary32.ofBits 0x00000000 /- 0 -/) false t'8
  return ()

/-- C++ `ModeAuto::nav_attitude_time_run : void ()`, `mode_auto.cpp:1267-1294`. -/
def ModeAuto.nav_attitude_time_run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Mode.is_disarmed_or_landed this
  let mut sc'5 := t'1
  if !sc'5 then
    let t'2 ← PMem.ldU64 (this + 64)
    let t'3 ← PMem.ldU64 t'2
    let t'4 ← AP_Motors.get_interlock t'3
    sc'5 := !t'4
  if sc'5 then
    Mode.make_safe_ground_handling this false
    return ()
  let t'6 ← PMem.ldF32 ((this + 864) + 8)
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  let t'9 ← AC_PosControl.get_max_speed_down_ms t'8
  let t'10 ← PMem.ldU64 (this + 40)
  let t'11 ← PMem.ldU64 t'10
  let t'12 ← AC_PosControl.get_max_speed_up_ms t'11
  let t'13 ← constrain_value_line'float t'6 (-t'9) t'12 (Int32.toUInt32 ((1276 : Int32)))
  let mut target_climb_rate_ms : Binary32 := t'13
  let t'14 ← Mode.get_avoidance_adjusted_climbrate_ms this target_climb_rate_ms
  target_climb_rate_ms := t'14
  let t'15 ← radians (Binary32.ofBits 0x41200000 /- 10 -/)
  PMem.stF32 (fp + 0) t'15
  let t'16 ← PMem.ldU64 (this + 56)
  let t'17 ← PMem.ldU64 t'16
  let t'18 ← AC_AttitudeControl.lean_angle_max_rad t'17
  PMem.stF32 (fp + 4) t'18
  let t'19 ← PMem.ldU64 (this + 56)
  let t'20 ← PMem.ldU64 t'19
  let t'21 ← AC_AttitudeControl.get_althold_lean_angle_max_rad t'20
  PMem.stF32 (fp + 8) t'21
  let t'22 ← MIN'float_float (fp + 4) (fp + 8)
  let t'23 ← MAX'float_float (fp + 0) t'22
  let t'24 ← PMem.ldF32 t'23
  let mut angle_limit_rad : Binary32 := t'24
  let t'25 ← PMem.ldI16 (this + 864)
  let t'26 ← radians'2 (Int16.toInt32 (t'25))
  let t'27 ← PMem.ldI8 ((this + 864) + 2)
  let t'28 ← radians'2 (Int8.toInt32 (t'27))
  Vector2'float.Vector2'2 (fp + 16) t'26 t'28
  let t'29 ← Vector2'float.limit_length (fp + 16) angle_limit_rad
  discard <| pure (t'29)
  let t'30 ← PMem.ldF32 (fp + 16)
  let t'31 ← PMem.ldF32 ((fp + 16) + 4)
  let t'32 ← PMem.ldI16 ((this + 864) + 4)
  let t'33 ← radians'2 (Int16.toInt32 (t'32))
  let t'34 ← PMem.ldU64 (this + 56)
  let t'35 ← PMem.ldU64 t'34
  AC_AttitudeControl.input_euler_angle_roll_pitch_yaw_rad t'35 t'30 t'31 t'33 true
  let t'36 ← PMem.ldU64 (this + 40)
  let t'37 ← PMem.ldU64 t'36
  AC_PosControl.D_set_pos_target_from_climb_rate_ms t'37 target_climb_rate_ms false
  let t'38 ← PMem.ldU64 (this + 40)
  let t'39 ← PMem.ldU64 t'38
  AC_PosControl.D_update_controller t'39
  return ()

def ModeAuto.nav_attitude_time_run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← ModeAuto.nav_attitude_time_run.body fp this
  PMem.leave fp
  return r

/-- C++ `ModeCircle::run : void ()`, `mode_circle.cpp:47-131`. -/
def ModeCircle.run.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← PMem.ldU64 t'1
  let t'3 ← AC_WPNav.get_default_speed_NE_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← PMem.ldU64 t'4
  let t'6 ← AC_WPNav.get_wp_acceleration_mss t'5
  let t'7 ← PMem.ldU64 (this + 40)
  let t'8 ← PMem.ldU64 t'7
  AC_PosControl.NE_set_max_speed_accel_m t'8 t'3 t'6
  let t'9 ← Mode.get_pilot_speed_dn_ms this
  let t'10 ← Mode.get_pilot_speed_up_ms this
  let t'11 ← Mode.get_pilot_accel_D_mss this
  let t'12 ← PMem.ldU64 (this + 40)
  let t'13 ← PMem.ldU64 t'12
  AC_PosControl.D_set_max_speed_accel_m t'13 t'9 t'10 t'11
  let t'14 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  AC_Circle.check_param_change t'14
  let t'15 ← rc
  let t'16 ← RC_Channels_Copter.has_valid_input t'15
  let mut sc'19 := t'16
  if sc'19 then
    let t'17 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
    let t'18 ← AC_Circle.pilot_control_enabled t'17
    sc'19 := t'18
  if sc'19 then
    let t'20 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
    let t'21 ← AC_Circle.get_radius_target_m t'20
    let mut radius_current_m : Binary32 := t'21
    let t'22 ← PMem.ldU64 (this + 80)
    let t'23 ← PMem.ldU64 t'22
    let t'24 ← RC_Channel.norm_input_dz t'23
    let mut pitch_stick_norm : Binary32 := t'24
    let t'25 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11192)
    let t'26 ← AC_WPNav.get_default_speed_NE_ms t'25
    let mut nav_speed_ms : Binary32 := t'26
    let t'27 ← PMem.ldU64 (this + 104)
    let t'28 ← PMem.ldF32 t'27
    let mut radius_pilot_change_m : Binary32 := ((pitch_stick_norm * nav_speed_ms) * t'28)
    PMem.stF32 (fp + 0) (radius_current_m + radius_pilot_change_m)
    PMem.stI32 (fp + 4) (0 : Int32)
    let t'29 ← MAX'float_int (fp + 0) (fp + 4)
    let mut radius_new_m : Binary32 := t'29
    let t'30 ← is_equal'float_float radius_current_m radius_new_m
    if !t'30 then
      let t'31 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
      AC_Circle.set_radius_m t'31 radius_new_m
    let t'32 ← PMem.ldU64 (this + 72)
    let t'33 ← PMem.ldU64 t'32
    let t'34 ← RC_Channel.norm_input_dz t'33
    let mut roll_stick_norm : Binary32 := t'34
    let t'35 ← is_zero roll_stick_norm
    if t'35 then
      PMem.stB (this + 112) false
    else
      let t'36 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
      let t'37 ← AC_Circle.get_rate_degs t'36
      let mut rate_degs : Binary32 := t'37
      let t'38 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
      let t'39 ← AC_Circle.get_rate_target_degs t'38
      let mut rate_target_degs : Binary32 := t'39
      let t'40 ← PMem.ldU64 (this + 104)
      let t'41 ← PMem.ldF32 t'40
      let mut rate_pilot_change_degs : Binary32 := (roll_stick_norm * t'41)
      let mut rate_new_degs : Binary32 := rate_target_degs
      let t'42 ← is_positive'float rate_degs
      if t'42 then
        let t'43 ← constrain_value_line'float (rate_target_degs + rate_pilot_change_degs) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((90 : Int32))) (Int32.toUInt32 ((89 : Int32)))
        rate_new_degs := t'43
      else
        let t'44 ← is_negative'float rate_degs
        if t'44 then
          let t'45 ← constrain_value_line'float (rate_target_degs + rate_pilot_change_degs) (Int32.toBinary32 ((-(90 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toUInt32 ((93 : Int32)))
          rate_new_degs := t'45
        else
          let t'46 ← is_zero rate_degs
          let mut sc'48 := t'46
          if sc'48 then
            let t'47 ← PMem.ldB (this + 112)
            sc'48 := !t'47
          if sc'48 then
            rate_new_degs := rate_pilot_change_degs
      PMem.stB (this + 112) true
      let t'49 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
      AC_Circle.set_rate_degs t'49 rate_new_degs
  let t'50 ← Mode.get_pilot_desired_climb_rate_ms this
  let mut target_climb_rate_ms : Binary32 := t'50
  let t'51 ← Mode.get_avoidance_adjusted_climbrate_ms this target_climb_rate_ms
  target_climb_rate_ms := t'51
  let t'52 ← Mode.is_disarmed_or_landed this
  if t'52 then
    Mode.make_safe_ground_handling this false
    return ()
  let t'53 ← PMem.ldU64 (this + 64)
  let t'54 ← PMem.ldU64 t'53
  AP_MotorsMulticopter.set_desired_spool_state t'54 (2 : UInt8)
  let t'55 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 11208)
  let t'56 ← AC_Circle.update_ms t'55 target_climb_rate_ms
  Copter.failsafe_terrain_set_status (0x86d8 : UInt64) /- &copter -/ t'56
  let t'57 ← PMem.ldU64 (this + 40)
  let t'58 ← PMem.ldU64 t'57
  AC_PosControl.D_update_controller t'58
  let t'59 ← PMem.ldU64 (this + 40)
  let t'60 ← PMem.ldU64 t'59
  AC_PosControl.get_thrust_vector t'60 (fp + 8)
  let t'61 := (fp + 8)
  Mode.AutoYaw.get_heading (0xeb78 : UInt64) /- &Mode::auto_yaw -/ (fp + 40)
  let t'62 := (fp + 40)
  discard <| PMem.memcpy (fp + 24) t'62 12
  let t'63 ← PMem.ldU64 (this + 56)
  let t'64 ← PMem.ldU64 t'63
  AC_AttitudeControl.input_thrust_vector_heading t'64 t'61 (fp + 24)
  return ()

def ModeCircle.run (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 52
  let r ← ModeCircle.run.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::update_rangefinder_terrain_offset : void ()`, `sensors.cpp:54-68`. -/
def Copter.update_rangefinder_terrain_offset (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 ((this + 8632) + 16)
  let t'2 ← PMem.ldF32 ((this + 8632) + 32)
  let mut terrain_u_m : Binary32 := (t'1 - t'2)
  let t'3 := ((this + 8632) + 44)
  let t'4 ← PMem.ldF32 t'3
  let t'5 ← PMem.ldF32 ((this + 8632) + 44)
  let t'6 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 376)
  let t'7 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1708) ((0x86d8 : UInt64) /- &copter -/ + 376)
  let t'8 ← PMem.ldF32 t'7
  let t'9 := (t'4 + ((terrain_u_m - t'5) * (t'6 / t'8)))
  PMem.stF32 t'3 t'9
  let t'10 ← PMem.ldF32 ((this + 8696) + 16)
  let t'11 ← PMem.ldF32 ((this + 8696) + 32)
  let t'12 := (t'10 + t'11)
  terrain_u_m := t'12
  let t'13 := ((this + 8696) + 44)
  let t'14 ← PMem.ldF32 t'13
  let t'15 ← PMem.ldF32 ((this + 8696) + 44)
  let t'16 ← PMem.ldF32 ((0x86d8 : UInt64) /- &copter -/ + 376)
  let t'17 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (((0x86d8 : UInt64) /- &copter -/ + 6840) + 1708) ((0x86d8 : UInt64) /- &copter -/ + 376)
  let t'18 ← PMem.ldF32 t'17
  let t'19 := (t'14 + ((terrain_u_m - t'15) * (t'16 / t'18)))
  PMem.stF32 t'13 t'19
  let t'20 ← PMem.ldB ((this + 8632) + 9)
  let mut sc'22 := t'20
  if !sc'22 then
    let t'21 ← AP_SurfaceDistance.data_stale (this + 8632)
    sc'22 := t'21
  if sc'22 then
    let t'23 ← PMem.ldB ((this + 8632) + 8)
    let t'24 ← PMem.ldB ((this + 8632) + 9)
    let t'25 ← PMem.ldF32 ((this + 8632) + 44)
    let t'26 ← PMem.ldU64 (this + 11192)
    AC_WPNav.set_rangefinder_terrain_U_m t'26 t'23 t'24 t'25
    let t'27 ← PMem.ldB ((this + 8632) + 8)
    let mut sc'30 := t'27
    if sc'30 then
      let t'28 ← PMem.ldU64 (this + 11192)
      let t'29 ← AC_WPNav.rangefinder_used t'28
      sc'30 := t'29
    let t'31 ← PMem.ldB ((this + 8632) + 9)
    let t'32 ← PMem.ldF32 ((this + 8632) + 44)
    let t'33 ← PMem.ldU64 (this + 11208)
    AC_Circle.set_rangefinder_terrain_U_m t'33 sc'30 t'31 t'32
  return ()

/-- C++ `Copter::update_throttle_mix : void ()`, `land_detector.cpp:281-324`. -/
def Copter.update_throttle_mix (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.armed t'1
  let mut sc'4 := !t'2
  if !sc'4 then
    let t'3 ← PMem.ldB ((this + 9448) + 7)
    sc'4 := t'3
  if sc'4 then
    let t'5 ← PMem.ldU64 (this + 11168)
    AC_AttitudeControl_Multi.set_throttle_mix_min t'5
    return ()
  let t'6 ← PMem.ldU64 (this + 9488)
  let t'7 ← vcall'Mode'has_manual_throttle'3 t'6
  if t'7 then
    let t'8 ← PMem.ldU64 (this + 8616)
    let t'9 ← RC_Channel.get_control_in t'8
    let mut sc'11 := (decide ((Int16.toInt32 (t'9)) ≤ (0 : Int32)))
    if sc'11 then
      let t'10 ← Copter.air_mode_active this
      sc'11 := !t'10
    if sc'11 then
      let t'12 ← PMem.ldU64 (this + 11168)
      AC_AttitudeControl_Multi.set_throttle_mix_min t'12
    else
      let t'13 ← PMem.ldU64 (this + 11168)
      AC_AttitudeControl_Multi.set_throttle_mix_man t'13
  else
    let t'14 ← PMem.ldU64 (this + 11168)
    let t'15 ← AC_AttitudeControl.get_att_target_euler_rad t'14
    let angle_target_rad : UInt64 := t'15
    let t'16 ← Vector3'float.xy angle_target_rad
    let t'17 ← Vector2'float.length_squared t'16
    let t'18 ← radians (Binary32.ofBits 0x41700000 /- 15 -/)
    let t'19 ← sq t'18
    let mut large_angle_request : Bool := (decide (t'17 > t'19))
    let t'20 ← PMem.ldU64 (this + 11168)
    let t'21 ← AC_AttitudeControl.get_att_error_angle_deg t'20
    let mut angle_error : Binary32 := t'21
    let mut large_angle_error : Bool := (decide (angle_error > (Binary32.ofBits 0x41f00000 /- 30 -/)))
    let t'22 ← DigitalLPF'Vector3_float.get (this + 11116)
    let t'23 ← Vector3'float.length t'22
    let mut accel_moving : Bool := (decide (t'23 > (Binary32.ofBits 0x40400000 /- 3 -/)))
    let t'24 ← PMem.ldU64 (this + 11184)
    let t'25 ← AC_PosControl.get_vel_desired_U_ms t'24
    let mut descent_not_demanded : Bool := (decide (t'25 ≥ (Binary32.ofBits 0x00000000 /- 0 -/)))
    let t'26 ← PMem.ldU64 (this + 9488)
    let t'27 ← vcall'Mode'is_landing'15 t'26
    let mut landing : Bool := t'27
    let mut sc'29 := large_angle_request
    if !sc'29 then
      let t'28 ← Copter.get_force_flying this
      sc'29 := t'28
    if ((((sc'29 && (!landing)) || large_angle_error) || accel_moving) || descent_not_demanded) then
      let t'30 ← PMem.ldU64 (this + 11184)
      let t'31 ← AC_PosControl.get_vel_D_control_ratio t'30
      let t'32 ← PMem.ldU64 (this + 11168)
      AC_AttitudeControl_Multi.set_throttle_mix_max t'32 t'31
    else
      let t'33 ← PMem.ldU64 (this + 11168)
      AC_AttitudeControl_Multi.set_throttle_mix_min t'33
  return ()

/-- C++ `Copter::update_auto_armed : void ()`, `system.cpp:312-342`. -/
def Copter.update_auto_armed (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB ((this + 9448) + 5)
  if t'1 then
    let t'2 ← PMem.ldU64 (this + 9528)
    let t'3 ← AP_Motors.armed t'2
    if !t'3 then
      Copter.set_auto_armed this false
      return ()
    let t'4 ← PMem.ldU64 (this + 9488)
    let t'5 ← vcall'Mode'has_manual_throttle'3 t'4
    let mut sc'7 := t'5
    if sc'7 then
      let t'6 ← PMem.ldB ((this + 9448) + 15)
      sc'7 := t'6
    let mut sc'10 := sc'7
    if sc'10 then
      let t'8 ← rc
      let t'9 ← RC_Channels_Copter.has_valid_input t'8
      sc'10 := t'9
    if sc'10 then
      Copter.set_auto_armed this false
  else
    let t'11 ← PMem.ldU64 (this + 9528)
    let t'12 ← AP_Motors.armed t'11
    let mut sc'14 := t'12
    if sc'14 then
      let t'13 ← PMem.ldB ((this + 9448) + 18)
      sc'14 := t'13
    if sc'14 then
      let t'15 ← PMem.ldB ((this + 9448) + 15)
      let mut sc'18 := !t'15
      if sc'18 then
        let t'16 ← PMem.ldU64 (this + 9528)
        let t'17 ← AP_Motors.get_spool_state t'16
        sc'18 := (t'17 == (3 : UInt8))
      if sc'18 then
        Copter.set_auto_armed this true
    else
      let t'19 ← PMem.ldU64 (this + 9528)
      let t'20 ← AP_Motors.armed t'19
      let mut sc'22 := t'20
      if sc'22 then
        let t'21 ← PMem.ldB ((this + 9448) + 18)
        sc'22 := !t'21
      if sc'22 then
        let t'23 ← PMem.ldB ((this + 9448) + 15)
        let mut sc'26 := !t'23
        if !sc'26 then
          let t'24 ← PMem.ldU64 (this + 9488)
          let t'25 ← vcall'Mode'mode_number'1 t'24
          sc'26 := (t'25 == (18 : UInt8))
        if sc'26 then
          Copter.set_auto_armed this true
  return ()

/-- C++ `Copter::run_nav_updates : void ()`, `navigation.cpp:6-9`. -/
def Copter.run_nav_updates (this : UInt64) : PMem.M Unit := do
  Copter.update_super_simple_bearing this false
  return ()

/-- C++ `Copter::update_throttle_hover : void ()`, `Attitude.cpp:32-67`. -/
def Copter.update_throttle_hover.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 9528)
  let t'2 ← AP_Motors.armed t'1
  let mut sc'4 := !t'2
  if !sc'4 then
    let t'3 ← PMem.ldB ((this + 9448) + 7)
    sc'4 := t'3
  let mut sc'6 := sc'4
  if !sc'6 then
    let t'5 ← PMem.ldB (this + 11229)
    sc'6 := t'5
  if sc'6 then
    return ()
  let t'7 ← PMem.ldU64 (this + 9488)
  let t'8 ← vcall'Mode'has_manual_throttle'3 t'7
  let mut sc'11 := t'8
  if !sc'11 then
    let t'9 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9488)
    let t'10 ← vcall'Mode'mode_number'1 t'9
    sc'11 := (t'10 == (11 : UInt8))
  if sc'11 then
    return ()
  let t'12 ← PMem.ldU64 (this + 11184)
  let t'13 ← AC_PosControl.get_vel_desired_U_ms t'12
  let t'14 ← is_zero t'13
  if !t'14 then
    return ()
  let t'15 ← PMem.ldB (this + 8852)
  let t'16 ← VehicleBridge.ahrs'0
  let t'17 ← VehicleBridge.AP_AHRS.get_velocity_D'2 t'16 (fp + 0) t'15
  if !t'17 then
    return ()
  let t'18 ← PMem.ldU64 (this + 9528)
  let t'19 ← AP_Motors.get_throttle t'18
  let mut throttle : Binary32 := t'19
  let mut sc'21 := (decide (throttle > (Binary32.ofBits 0x00000000 /- 0 -/)))
  if sc'21 then
    let t'20 ← PMem.ldF32 (fp + 0)
    sc'21 := (decide ((Binary32.abs t'20) < (Binary64.toBinary32 ((Binary64.ofBits 0x3fe3333333333333 /- 29999999999999999/50000000000000000 -/)))))
  let mut sc'26 := sc'21
  if sc'26 then
    let t'22 ← VehicleBridge.AP_AHRS.get_roll_rad'0 (this + 4080)
    let t'23 ← PMem.ldU64 (this + 11168)
    let t'24 ← AC_AttitudeControl.get_roll_trim_rad t'23
    let t'25 ← radians'2 (5 : Int32)
    sc'26 := (decide ((Binary32.abs (t'22 - t'24)) < t'25))
  let mut sc'29 := sc'26
  if sc'29 then
    let t'27 ← VehicleBridge.AP_AHRS.get_pitch_rad'0 (this + 4080)
    let t'28 ← radians'2 (5 : Int32)
    sc'29 := (decide ((Binary32.abs t'27) < t'28))
  if sc'29 then
    let t'30 ← PMem.ldU64 (this + 9528)
    AP_MotorsMulticopter.update_throttle_hover t'30 (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/)
  return ()

def Copter.update_throttle_hover (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← Copter.update_throttle_hover.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::ekf_over_threshold : bool ()`, `ekf_check.cpp:114-162`. -/
def Copter.ekf_over_threshold.body (fp : UInt64) (this : UInt64) : PMem.M Bool := do
  Vector3'float.Vector3'2 (fp + 32)
  let t'1 ← VehicleBridge.AP_AHRS.get_variances_for_configured_backend'5 (this + 4080) (fp + 8) (fp + 0) (fp + 16) (fp + 32) (fp + 24)
  PMem.stB (this + 8888) t'1
  let t'2 ← PMem.ldB (this + 8888)
  if !t'2 then
    return false
  let mut now_us : UInt32 := (← PMem.clock).toUInt32
  let t'3 ← PMem.ldU32 (this + 8892)
  PMem.stF32 (fp + 48) ((UInt32.toBinary32 ((now_us - t'3))) * (Binary32.ofBits 0x358637bd /- 999999997/1000000000000000 -/))
  let t'4 ← LowPassFilter'float.apply (this + 8864) (fp + 0) (fp + 48)
  PMem.stF32 (fp + 0) t'4
  let t'5 ← LowPassFilter'float.apply (this + 8876) (fp + 8) (fp + 48)
  PMem.stF32 (fp + 8) t'5
  PMem.stU32 (this + 8892) now_us
  let t'6 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6776) + 56)
  let t'7 ← PMem.ldF32 t'6
  if (decide (t'7 ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
    return false
  let t'8 ← PMem.ldF32 (fp + 32)
  let t'9 ← PMem.ldF32 ((fp + 32) + 4)
  let t'10 ← PMem.ldF32 ((fp + 32) + 8)
  let mut mag_max : Binary32 := (Binary32.fmax (Binary32.fmax t'8 t'9) t'10)
  let mut over_thresh_count : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let t'11 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6776) + 56)
  let t'12 ← PMem.ldF32 t'11
  if (decide (mag_max ≥ t'12)) then
    let t'13 := over_thresh_count
    let t'14 := (t'13 + 1)
    over_thresh_count := t'14
  let mut optflow_healthy : Bool := false
  let mut sc'18 := !optflow_healthy
  if sc'18 then
    let t'15 ← PMem.ldF32 (fp + 8)
    let t'16 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6776) + 56)
    let t'17 ← PMem.ldF32 t'16
    sc'18 := (decide (t'15 ≥ ((Binary32.ofBits 0x40000000 /- 2 -/) * t'17)))
  if sc'18 then
    let t'19 := (over_thresh_count + (Int8.toUInt8 (Int32.toInt8 ((2 : Int32)))))
    over_thresh_count := t'19
  else
    let t'20 ← PMem.ldF32 (fp + 8)
    let t'21 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6776) + 56)
    let t'22 ← PMem.ldF32 t'21
    if (decide (t'20 ≥ t'22)) then
      let t'23 := over_thresh_count
      let t'24 := (t'23 + 1)
      over_thresh_count := t'24
  let t'25 ← PMem.ldF32 (fp + 0)
  let t'26 ← AP_ParamT'float_4.operator_const_float__'1 ((this + 6776) + 56)
  let t'27 ← PMem.ldF32 t'26
  if (((decide (t'25 ≥ t'27)) && (decide ((UInt32.toInt32 (UInt8.toUInt32 (over_thresh_count))) ≥ (1 : Int32)))) || (decide ((UInt32.toInt32 (UInt8.toUInt32 (over_thresh_count))) ≥ (2 : Int32)))) then
    return true
  return false

def Copter.ekf_over_threshold (this : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 52
  let r ← Copter.ekf_over_threshold.body fp this
  PMem.leave fp
  return r

/-- C++ `Copter::get_available_mode_enabled_mask : uint32_t () const`, `mode.cpp:220-311`. -/
def Copter.get_available_mode_enabled_mask.body (fp : UInt64) (this : UInt64) : PMem.M UInt32 := do
  PMem.stU64 ((fp + 0) + 0) ((0x86d8 : UInt64) /- &copter -/ + 11368)
  PMem.stU64 ((fp + 0) + 8) ((0x86d8 : UInt64) /- &copter -/ + 13096)
  PMem.stU64 ((fp + 0) + 16) ((0x86d8 : UInt64) /- &copter -/ + 11256)
  PMem.stU64 ((fp + 0) + 24) ((0x86d8 : UInt64) /- &copter -/ + 12400)
  PMem.stU64 ((fp + 0) + 32) ((0x86d8 : UInt64) /- &copter -/ + 12776)
  PMem.stU64 ((fp + 0) + 40) ((0x86d8 : UInt64) /- &copter -/ + 12520)
  PMem.stU64 ((fp + 0) + 48) ((0x86d8 : UInt64) /- &copter -/ + 12640)
  PMem.stU64 ((fp + 0) + 56) ((0x86d8 : UInt64) /- &copter -/ + 12888)
  PMem.stU64 ((fp + 0) + 64) ((0x86d8 : UInt64) /- &copter -/ + 12280)
  let mut mask : UInt32 := Int32.toUInt32 ((0 : Int32))
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((72 : UInt64) / (8 : UInt64))))) then break
    let t'4 ← PMem.ldU64 ((fp + 0) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    let mut mode : UInt64 := t'4
    let t'5 ← vcall'Mode'enabled'18 mode
    let mut sc'8 := t'5
    if sc'8 then
      let t'6 ← vcall'Mode'mode_number'1 mode
      let t'7 ← Copter.gcs_mode_enabled (0x86d8 : UInt64) /- &copter -/ t'6
      sc'8 := t'7
    let mut user_selectable : Bool := sc'8
    if user_selectable then
      let t'9 := (mask ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i)))))))
      mask := t'9
  return mask

def Copter.get_available_mode_enabled_mask (this : UInt64) : PMem.M UInt32 := do
  let fp ← PMem.enter 72
  let r ← Copter.get_available_mode_enabled_mask.body fp this
  PMem.leave fp
  return r

/-- C++ `ParametersG2::ParametersG2 : void ()`, `Parameters.cpp:1203-1269`. -/
def ParametersG2.ParametersG2 (this : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  PMem.stU8 (this + 4) (Int8.toUInt8 (Int32.toInt8 ((17 : Int32))))
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  RC_Channels_Copter.RC_Channels_Copter (this + 16)
  SRV_Channels.SRV_Channels (this + 960)
  AP_Param.AP_Param'2 (this + 1632)
  AP_Param.AP_Param'2 (this + 1636)
  AP_Param.AP_Param'2 (this + 1640)
  AP_Param.AP_Param'2 (this + 1644)
  AP_Param.AP_Param'2 (this + 1648)
  AP_Param.AP_Param'2 (this + 1652)
  AC_CommandModel.AC_CommandModel (this + 1656) (Binary64.toBinary32 ((Binary64.ofBits 0x4069500000000000 /- 405/2 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary32.ofBits 0x00000000 /- 0 -/)
  AP_Param.AP_Param'2 (this + 1680)
  AP_Param.AP_Param'2 (this + 1684)
  AP_Param.AP_Param'2 (this + 1688)
  AP_Param.AP_Param'2 (this + 1692)
  AP_Param.AP_Param'2 (this + 1696)
  AP_Param.AP_Param'2 (this + 1700)
  AP_Param.AP_Param'2 (this + 1704)
  AP_Param.AP_Param'2 (this + 1705)
  AP_Param.AP_Param'2 (this + 1706)
  AP_Param.AP_Param'2 (this + 1708)
  AP_SurfaceDistance.SurfDistParameters.SurfDistParameters (this + 1712)
  AP_Param.AP_Param'2 (this + 1720)
  AP_Param.AP_Param'2 (this + 1724)
  AP_Param.AP_Param'2 (this + 1728)
  AP_Param.AP_Param'2 (this + 1732)
  AP_Param.AP_Param'2 (this + 1733)
  PMem.stU64 (this + 1736) ((0x86d8 : UInt64) /- &copter -/ + 12888)
  PMem.stU64 (this + 1744) ((0x86d8 : UInt64) /- &copter -/ + 12640)
  AP_Param.setup_object_defaults this (0x53c0 : UInt64) /- &ParametersG2::var_info -/
  AP_Param.setup_object_defaults this (0x7708 : UInt64) /- &ParametersG2::var_info2 -/
  return ()

/-- C++ `GCS_Copter::GCS_Copter : void () noexcept(false)`, `AP_Common.h:?-?`. -/
def GCS_Copter.GCS_Copter (this : UInt64) : PMem.M Unit := do
  GCS.GCS this
  return ()

/-- C++ `ModeRTL::ModeRTL : void ()`, `mode_rtl.cpp:48-52`. -/
def ModeRTL.ModeRTL (this : UInt64) : PMem.M Unit := do
  Mode.Mode this
  AP_Param.AP_Param'2 (this + 112)
  AP_Param.AP_Param'2 (this + 116)
  AP_Param.AP_Param'2 (this + 120)
  AP_Param.AP_Param'2 (this + 124)
  PMem.stU8 (this + 128) (0 : UInt8)
  PMem.stB (this + 129) false
  Location.Location (this + 132)
  Location.Location ((this + 132) + 16)
  Location.Location ((this + 132) + 32)
  Location.Location ((this + 132) + 48)
  AP_Param.setup_object_defaults this (0x82a0 : UInt64) /- &ModeRTL::var_info -/
  return ()

end Vehicle_lib
