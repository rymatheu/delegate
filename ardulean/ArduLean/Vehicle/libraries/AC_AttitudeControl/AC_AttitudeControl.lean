import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_PID.AC_PID

/-!
ArduPilot `libraries/AC_AttitudeControl`, part 1 of 2. Sources: `libraries/AC_AttitudeControl/AC_PosControl.cpp`, `libraries/AC_AttitudeControl/AC_AttitudeControl.cpp`, `libraries/AC_AttitudeControl/AC_AttitudeControl.h`, `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.cpp`, `libraries/AC_AttitudeControl/AC_AttitudeControl_Multi.h`, `libraries/AC_AttitudeControl/AC_CommandModel.h`, `libraries/AC_AttitudeControl/AC_CommandModel.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AC_CommandModel::AC_CommandModel : void (float, float, float)`, `AC_CommandModel.cpp:42-48`. -/
def AC_CommandModel.AC_CommandModel (this : UInt64) (initial_rate : Binary32) (initial_expo : Binary32) (initial_tc : Binary32) : PMem.M Unit := do
  let mut initial_rate := initial_rate
  let mut initial_expo := initial_expo
  let mut initial_tc := initial_tc
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 8)
  PMem.stF32 (this + 12) initial_tc
  PMem.stF32 (this + 16) initial_rate
  PMem.stF32 (this + 20) initial_expo
  AP_Param.setup_object_defaults this (0x7668 : UInt64) /- &AC_CommandModel::var_info -/
  return ()

/-- C++ `AC_PosControl::init_terrain : void ()`, `AC_PosControl.cpp:1220-1231`. -/
def AC_PosControl.init_terrain (this : UInt64) : PMem.M Unit := do
  let t'1 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 848) t'1
  let t'2 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 852) t'2
  let t'3 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 856) t'3
  let t'4 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 860) t'4
  return ()

/-- C++ `AC_PosControl::D_init_offsets : void ()`, `AC_PosControl.cpp:1275-1293`. -/
def AC_PosControl.D_init_offsets (this : UInt64) : PMem.M Unit := do
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldU32 (this + 964)
  if (decide ((now_ms - t'1) > (Int32.toUInt32 ((3000 : Int32))))) then
    let t'2 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
    PMem.stF64 ((this + 864) + 16) t'2
    let t'3 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 ((this + 912) + 8) t'3
    let t'4 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 ((this + 936) + 8) t'4
  let t'5 ← PMem.ldF64 ((this + 864) + 16)
  PMem.stF64 ((this + 888) + 16) t'5
  let t'6 ← PMem.ldF32 ((this + 912) + 8)
  PMem.stF32 ((this + 924) + 8) t'6
  let t'7 ← PMem.ldF32 ((this + 936) + 8)
  PMem.stF32 ((this + 948) + 8) t'7
  return ()

/-- C++ `AC_PosControl::get_estimated_accel_D_mss : float () const`, `<scratch space>:607-?`. -/
def AC_PosControl.get_estimated_accel_D_mss.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 this
  VehicleBridge.AP_AHRS_View.get_accel_ef'0 t'1 (fp + 0)
  let t'2 := (fp + 0)
  let t'3 ← PMem.ldF32 (t'2 + 8)
  return (t'3 + (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))

def AC_PosControl.get_estimated_accel_D_mss (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 12
  let r ← AC_PosControl.get_estimated_accel_D_mss.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::get_throttle_in : float () const`, `<scratch space>:408-?`. -/
def AC_AttitudeControl.get_throttle_in (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 240)
  return t'1

/-- C++ `AC_PosControl::D_init_ekf_reset : void ()`, `AC_PosControl.cpp:1729-1732`. -/
def AC_PosControl.D_init_ekf_reset (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← VehicleBridge.AP_AHRS_View.get_position_D_reset_count'0 t'1
  PMem.stU16 (this + 970) t'2
  return ()

/-- C++ `AC_AttitudeControl::get_ang_vel_roll_max_rads : float () const`, `AC_AttitudeControl.h:118-?`. -/
def AC_AttitudeControl.get_ang_vel_roll_max_rads (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← radians t'2
  return t'3

/-- C++ `AC_AttitudeControl::get_ang_vel_pitch_max_rads : float () const`, `AC_AttitudeControl.h:124-?`. -/
def AC_AttitudeControl.get_ang_vel_pitch_max_rads (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← radians t'2
  return t'3

/-- C++ `AC_AttitudeControl::get_accel_roll_max_radss : float () const`, `AC_AttitudeControl.h:91-?`. -/
def AC_AttitudeControl.get_accel_roll_max_radss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 24)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← radians t'2
  return t'3

/-- C++ `AC_AttitudeControl::get_accel_pitch_max_radss : float () const`, `AC_AttitudeControl.h:100-?`. -/
def AC_AttitudeControl.get_accel_pitch_max_radss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 28)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← radians t'2
  return t'3

/-- C++ `AC_AttitudeControl::get_bf_feedforward : bool ()`, `<scratch space>:396-?`. -/
def AC_AttitudeControl.get_bf_feedforward (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 36)
  let t'2 ← PMem.ldI8 t'1
  return t'2 != (0 : Int8)

/-- C++ `AC_PosControl::NE_set_max_speed_accel_m : void (float, float)`, `AC_PosControl.cpp:458-479`. -/
def AC_PosControl.NE_set_max_speed_accel_m.body (fp : UInt64) (this : UInt64) (speed_ne_ms : Binary32) (accel_ne_mss : Binary32) : PMem.M Unit := do
  let mut speed_ne_ms := speed_ne_ms
  let mut accel_ne_mss := accel_ne_mss
  let t'1 := (Binary32.abs speed_ne_ms)
  PMem.stF32 (this + 636) t'1
  let t'2 := (Binary32.abs accel_ne_mss)
  PMem.stF32 (this + 648) t'2
  let t'3 ← PMem.ldU64 (this + 16)
  let t'4 ← AC_AttitudeControl.get_ang_vel_roll_max_rads t'3
  PMem.stF32 (fp + 4) t'4
  let t'5 ← PMem.ldU64 (this + 16)
  let t'6 ← AC_AttitudeControl.get_ang_vel_pitch_max_rads t'5
  PMem.stF32 (fp + 8) t'6
  let t'7 ← MIN'float_float (fp + 4) (fp + 8)
  let t'8 ← PMem.ldF32 t'7
  PMem.stF32 (fp + 0) (t'8 * (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))
  let t'9 ← PMem.ldU64 (this + 16)
  let t'10 ← AC_AttitudeControl.get_accel_roll_max_radss t'9
  PMem.stF32 (fp + 12) t'10
  let t'11 ← PMem.ldU64 (this + 16)
  let t'12 ← AC_AttitudeControl.get_accel_pitch_max_radss t'11
  PMem.stF32 (fp + 16) t'12
  let t'13 ← MIN'float_float (fp + 12) (fp + 16)
  let t'14 ← PMem.ldF32 t'13
  let mut snap_max_mssss : Binary32 := (t'14 * (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))
  let t'15 ← AP_ParamT'float_4.operator_const_float__'1 (this + 28)
  let t'16 ← PMem.ldF32 t'15
  PMem.stF32 (this + 656) t'16
  let t'17 ← PMem.ldF32 (fp + 0)
  let t'18 ← is_positive'float t'17
  let mut sc'21 := t'18
  if sc'21 then
    let t'19 ← PMem.ldU64 (this + 16)
    let t'20 ← AC_AttitudeControl.get_bf_feedforward t'19
    sc'21 := t'20
  if sc'21 then
    let t'22 ← MIN'float_float (this + 656) (fp + 0)
    let t'23 ← PMem.ldF32 t'22
    PMem.stF32 (this + 656) t'23
  let t'24 ← is_positive'float snap_max_mssss
  let mut sc'27 := t'24
  if sc'27 then
    let t'25 ← PMem.ldU64 (this + 16)
    let t'26 ← AC_AttitudeControl.get_bf_feedforward t'25
    sc'27 := t'26
  if sc'27 then
    let t'28 ← PMem.ldF32 (this + 648)
    let t'29 ← safe_sqrt'float (t'28 * snap_max_mssss)
    PMem.stF32 (fp + 20) ((Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) * t'29)
    let t'30 ← MIN'float_float (fp + 20) (this + 656)
    let t'31 ← PMem.ldF32 t'30
    PMem.stF32 (this + 656) t'31
  return ()

def AC_PosControl.NE_set_max_speed_accel_m (this : UInt64) (speed_ne_ms : Binary32) (accel_ne_mss : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AC_PosControl.NE_set_max_speed_accel_m.body fp this speed_ne_ms accel_ne_mss
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::get_althold_lean_angle_max_rad : float () const`, `AC_AttitudeControl.cpp:1407-1410`. -/
def AC_AttitudeControl.get_althold_lean_angle_max_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4024000000000000 /- 10 -/)))
  PMem.stF32 (fp + 0) t'1
  let t'2 ← MAX'float_float (this + 252) (fp + 0)
  let t'3 ← PMem.ldF32 t'2
  return t'3

def AC_AttitudeControl.get_althold_lean_angle_max_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← AC_AttitudeControl.get_althold_lean_angle_max_rad.body fp this
  PMem.leave fp
  return r

/-- `AC_AttitudeControl.get_att_target_euler_rad` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl.get_att_target_euler_rad.pure' (this : UInt64) : Id UInt64 := do
  return (this + 116)

/-- C++ `AC_AttitudeControl::get_att_target_euler_rad : const Vector3f &() const`, `<scratch space>:331-?`. -/
def AC_AttitudeControl.get_att_target_euler_rad (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl.get_att_target_euler_rad.pure' this)

/-- C++ `AC_PosControl::NE_init_offsets : void ()`, `AC_PosControl.cpp:1254-1272`. -/
def AC_PosControl.NE_init_offsets (this : UInt64) : PMem.M Unit := do
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldU32 (this + 960)
  if (decide ((now_ms - t'1) > (Int32.toUInt32 ((3000 : Int32))))) then
    let t'2 ← Vector3'double.xy (this + 864)
    Vector2'double.zero t'2
    let t'3 ← Vector3'float.xy (this + 912)
    Vector2'float.zero t'3
    let t'4 ← Vector3'float.xy (this + 936)
    Vector2'float.zero t'4
  let t'5 ← Vector3'double.xy (this + 888)
  let t'6 ← Vector3'double.xy (this + 864)
  discard <| PMem.memcpy t'5 t'6 16
  discard <| pure (t'5)
  let t'7 ← Vector3'float.xy (this + 924)
  let t'8 ← Vector3'float.xy (this + 912)
  discard <| PMem.memcpy t'7 t'8 8
  discard <| pure (t'7)
  let t'9 ← Vector3'float.xy (this + 948)
  let t'10 ← Vector3'float.xy (this + 936)
  discard <| PMem.memcpy t'9 t'10 8
  discard <| pure (t'9)
  return ()

/-- C++ `AC_PosControl::lean_angles_rad_to_accel_NED_mss : Vector3f (const Vector3f &) const`, `AC_PosControl.cpp:1200-1215`. -/
def AC_PosControl.lean_angles_rad_to_accel_NED_mss.body (fp : UInt64) (this : UInt64) (sret : UInt64) (att_target_euler_rad : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 att_target_euler_rad
  let mut sin_roll : Binary32 := (Musl.sinf.sinf t'1)
  let t'2 ← PMem.ldF32 att_target_euler_rad
  let mut cos_roll : Binary32 := (Musl.cosf.cosf t'2)
  let t'3 ← PMem.ldF32 (att_target_euler_rad + 4)
  let mut sin_pitch : Binary32 := (Musl.sinf.sinf t'3)
  let t'4 ← PMem.ldF32 (att_target_euler_rad + 4)
  let mut cos_pitch : Binary32 := (Musl.cosf.cosf t'4)
  let t'5 ← PMem.ldF32 (att_target_euler_rad + 8)
  let mut sin_yaw : Binary32 := (Musl.sinf.sinf t'5)
  let t'6 ← PMem.ldF32 (att_target_euler_rad + 8)
  let mut cos_yaw : Binary32 := (Musl.cosf.cosf t'6)
  PMem.stF32 (fp + 12) (cos_roll * cos_pitch)
  PMem.stF32 (fp + 16) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/)
  let t'7 ← MAX'float_float (fp + 12) (fp + 16)
  let t'8 ← PMem.ldF32 t'7
  PMem.stF32 (fp + 20) (cos_roll * cos_pitch)
  PMem.stF32 (fp + 24) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/)
  let t'9 ← MAX'float_float (fp + 20) (fp + 24)
  let t'10 ← PMem.ldF32 t'9
  Vector3'float.Vector3 (fp + 0) (((Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/) * ((((-cos_yaw) * sin_pitch) * cos_roll) - (sin_yaw * sin_roll))) / t'8) (((Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/) * ((((-sin_yaw) * sin_pitch) * cos_roll) + (cos_yaw * sin_roll))) / t'10) (-(Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def AC_PosControl.lean_angles_rad_to_accel_NED_mss (this : UInt64) (sret : UInt64) (att_target_euler_rad : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← AC_PosControl.lean_angles_rad_to_accel_NED_mss.body fp this sret att_target_euler_rad
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::lean_angles_to_accel_NE_mss : void (float &, float &) const`, `AC_PosControl.cpp:1628-1637`. -/
def AC_PosControl.lean_angles_to_accel_NE_mss.body (fp : UInt64) (this : UInt64) (accel_n_mss : UInt64) (accel_e_mss : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 16)
  let t'2 ← AC_AttitudeControl.get_att_target_euler_rad t'1
  Vector3'float.Vector3'4 (fp + 0) t'2
  let t'3 ← PMem.ldU64 this
  let t'4 ← VehicleBridge.AP_AHRS_View.yaw'field t'3
  PMem.stF32 ((fp + 0) + 8) t'4
  AC_PosControl.lean_angles_rad_to_accel_NED_mss this (fp + 32) (fp + 0)
  let t'5 := (fp + 32)
  Vector3'float.Vector3'3 (fp + 16) t'5
  let t'6 ← PMem.ldF32 (fp + 16)
  PMem.stF32 accel_n_mss t'6
  let t'7 ← PMem.ldF32 ((fp + 16) + 4)
  PMem.stF32 accel_e_mss t'7
  return ()

def AC_PosControl.lean_angles_to_accel_NE_mss (this : UInt64) (accel_n_mss : UInt64) (accel_e_mss : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 44
  let r ← AC_PosControl.lean_angles_to_accel_NE_mss.body fp this accel_n_mss accel_e_mss
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::lean_angle_max_rad : float () const`, `AC_AttitudeControl.cpp:1419-1422`. -/
def AC_AttitudeControl.lean_angle_max_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 84)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← constrain_value_line'float t'2 (Binary64.toBinary32 ((Binary64.ofBits 0x4024000000000000 /- 10 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x4054000000000000 /- 80 -/))) (Int32.toUInt32 ((1421 : Int32)))
  let t'4 ← radians t'3
  return t'4

/-- C++ `AC_PosControl::NE_init_ekf_reset : void ()`, `AC_PosControl.cpp:1690-1693`. -/
def AC_PosControl.NE_init_ekf_reset (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← VehicleBridge.AP_AHRS_View.get_position_NE_reset_count'0 t'1
  PMem.stU16 (this + 968) t'2
  return ()

/-- C++ `AC_PosControl::get_stopping_point_NE_m : void (Vector2p &) const`, `AC_PosControl.cpp:1382-1410`. -/
def AC_PosControl.get_stopping_point_NE_m.body (fp : UInt64) (this : UInt64) (stopping_point_ne_m : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'double.xy (this + 704)
  discard <| PMem.memcpy stopping_point_ne_m t'1 16
  discard <| pure (stopping_point_ne_m)
  let t'2 ← Vector3'double.xy (this + 888)
  let t'3 ← Vector2'double.operator__ stopping_point_ne_m t'2
  discard <| pure (t'3)
  let t'4 ← Vector3'float.xy (this + 776)
  Vector2'float.Vector2'4 (fp + 0) t'4
  let t'5 ← Vector3'float.xy (this + 924)
  let t'6 ← Vector2'float.operator__'2 (fp + 0) t'5
  discard <| pure (t'6)
  let t'7 ← Vector2'float.length (fp + 0)
  let mut speed_ne_ms : Binary32 := t'7
  let t'8 ← is_positive'float speed_ne_ms
  if !t'8 then
    return ()
  let t'9 ← AC_P_2D.kP (this + 36)
  let t'10 ← AP_ParamT'float_4.operator_const_float__'1 t'9
  let t'11 ← PMem.ldF32 t'10
  let mut kP : Binary32 := t'11
  let t'12 ← PMem.ldF32 (this + 636)
  let t'13 ← constrain_value_line'float speed_ne_ms (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'12 (Int32.toUInt32 ((1401 : Int32)))
  let t'14 ← PMem.ldF32 (this + 648)
  let t'15 ← stopping_distance t'13 kP t'14
  let mut stopping_dist_m : Binary32 := t'15
  let t'16 ← is_positive'float stopping_dist_m
  if !t'16 then
    return ()
  let mut stopping_time_s : Binary32 := (stopping_dist_m / speed_ne_ms)
  Vector2'float.operator_'2 (fp + 0) (fp + 8) stopping_time_s
  let t'17 := (fp + 8)
  Vector2'float.todouble t'17 (fp + 16)
  let t'18 := (fp + 16)
  let t'19 ← Vector2'double.operator__'2 stopping_point_ne_m t'18
  discard <| pure (t'19)
  return ()

def AC_PosControl.get_stopping_point_NE_m (this : UInt64) (stopping_point_ne_m : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← AC_PosControl.get_stopping_point_NE_m.body fp this stopping_point_ne_m
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::get_input_tc : float () const`, `AC_AttitudeControl.h:139-?`. -/
def AC_AttitudeControl.get_input_tc (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- `AC_PosControl.get_vel_desired_NED_ms` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.get_vel_desired_NED_ms.pure' (this : UInt64) : Id UInt64 := do
  return (this + 788)

/-- C++ `AC_PosControl::get_vel_desired_NED_ms : const Vector3f &() const`, `AP_Common.h:397-?`. -/
def AC_PosControl.get_vel_desired_NED_ms (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.get_vel_desired_NED_ms.pure' this)

/-- C++ `AC_PosControl::NE_get_max_speed_ms : float () const`, `AP_Common.h:112-?`. -/
def AC_PosControl.NE_get_max_speed_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 636)
  return t'1

/-- C++ `AC_PosControl::get_vel_offset_D_ms : float () const`, `AP_Common.h:500-?`. -/
def AC_PosControl.get_vel_offset_D_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 ((this + 924) + 8)
  return t'1

/-- C++ `AC_PosControl::init_pos_terrain_D_m : void (float)`, `AC_PosControl.cpp:1243-1248`. -/
def AC_PosControl.init_pos_terrain_D_m (this : UInt64) (pos_terrain_d_m : Binary32) : PMem.M Unit := do
  let mut pos_terrain_d_m := pos_terrain_d_m
  let t'1 := ((this + 728) + 16)
  let t'2 ← PMem.ldF64 t'1
  let t'3 ← PMem.ldF32 (this + 852)
  let t'4 := (t'2 - (Binary32.toBinary64 ((pos_terrain_d_m - t'3))))
  PMem.stF64 t'1 t'4
  PMem.stF32 (this + 848) pos_terrain_d_m
  PMem.stF32 (this + 852) pos_terrain_d_m
  return ()

/-- C++ `AC_PosControl::get_max_speed_up_ms : float () const`, `AP_Common.h:227-?`. -/
def AC_PosControl.get_max_speed_up_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 640)
  return t'1

/-- C++ `AC_PosControl::get_max_speed_down_ms : float () const`, `AP_Common.h:230-?`. -/
def AC_PosControl.get_max_speed_down_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 644)
  return t'1

/-- C++ `AC_AttitudeControl::set_yaw_rate_tc : void (float)`, `<scratch space>:507-?`. -/
def AC_AttitudeControl.set_yaw_rate_tc (this : UInt64) (input_tc : Binary32) : PMem.M Unit := do
  let mut input_tc := input_tc
  PMem.stF32 (this + 272) input_tc
  return ()

/-- C++ `AC_CommandModel::get_rate_tc : float () const`, `AC_CommandModel.h:17-?`. -/
def AC_CommandModel.get_rate_tc (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_AttitudeControl::bf_feedforward : void (bool)`, `<scratch space>:390-?`. -/
def AC_AttitudeControl.bf_feedforward.body (fp : UInt64) (this : UInt64) (enable_or_disable : Bool) : PMem.M Unit := do
  let mut enable_or_disable := enable_or_disable
  PMem.stI8 (fp + 0) (if enable_or_disable then (1 : Int8) else (0 : Int8))
  AP_ParamTBase'signed_char_1.set (this + 36) (fp + 0)
  return ()

def AC_AttitudeControl.bf_feedforward (this : UInt64) (enable_or_disable : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 1
  let r ← AC_AttitudeControl.bf_feedforward.body fp this enable_or_disable
  PMem.leave fp
  return r

/-- `AC_PosControl.D_get_accel_pid` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.D_get_accel_pid.pure' (this : UInt64) : Id UInt64 := do
  return (this + 384)

/-- C++ `AC_PosControl::D_get_accel_pid : AC_PID &()`, `AP_Common.h:564-?`. -/
def AC_PosControl.D_get_accel_pid (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.D_get_accel_pid.pure' this)

/-- `AC_PosControl.NE_get_pos_p` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.NE_get_pos_p.pure' (this : UInt64) : Id UInt64 := do
  return (this + 36)

/-- C++ `AC_PosControl::NE_get_pos_p : AC_P_2D &()`, `AP_Common.h:552-?`. -/
def AC_PosControl.NE_get_pos_p (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.NE_get_pos_p.pure' this)

/-- `AC_PosControl.D_get_pos_p` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.D_get_pos_p.pure' (this : UInt64) : Id UInt64 := do
  return (this + 60)

/-- C++ `AC_PosControl::D_get_pos_p : AC_P_1D &()`, `AP_Common.h:555-?`. -/
def AC_PosControl.D_get_pos_p (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.D_get_pos_p.pure' this)

/-- `AC_PosControl.D_get_vel_pid` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.D_get_vel_pid.pure' (this : UInt64) : Id UInt64 := do
  return (this + 264)

/-- C++ `AC_PosControl::D_get_vel_pid : AC_PID_Basic &()`, `AP_Common.h:561-?`. -/
def AC_PosControl.D_get_vel_pid (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.D_get_vel_pid.pure' this)

/-- `AC_AttitudeControl_Multi.get_rate_roll_pid` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl_Multi.get_rate_roll_pid.pure' (this : UInt64) : Id UInt64 := do
  return (this + 376)

/-- C++ `AC_AttitudeControl_Multi::get_rate_roll_pid : AC_PID &()`, `AC_AttitudeControl_Multi.h:50-?`. -/
def AC_AttitudeControl_Multi.get_rate_roll_pid (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl_Multi.get_rate_roll_pid.pure' this)

/-- `AC_AttitudeControl_Multi.get_rate_pitch_pid` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl_Multi.get_rate_pitch_pid.pure' (this : UInt64) : Id UInt64 := do
  return (this + 616)

/-- C++ `AC_AttitudeControl_Multi::get_rate_pitch_pid : AC_PID &()`, `AC_AttitudeControl_Multi.h:51-?`. -/
def AC_AttitudeControl_Multi.get_rate_pitch_pid (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl_Multi.get_rate_pitch_pid.pure' this)

/-- `AC_AttitudeControl_Multi.get_rate_yaw_pid` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl_Multi.get_rate_yaw_pid.pure' (this : UInt64) : Id UInt64 := do
  return (this + 856)

/-- C++ `AC_AttitudeControl_Multi::get_rate_yaw_pid : AC_PID &()`, `AC_AttitudeControl_Multi.h:52-?`. -/
def AC_AttitudeControl_Multi.get_rate_yaw_pid (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl_Multi.get_rate_yaw_pid.pure' this)

/-- `AC_AttitudeControl.get_angle_pitch_p` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl.get_angle_pitch_p.pure' (this : UInt64) : Id UInt64 := do
  return (this + 48)

/-- C++ `AC_AttitudeControl::get_angle_pitch_p : AC_P &()`, `AC_AttitudeControl.h:81-?`. -/
def AC_AttitudeControl.get_angle_pitch_p (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl.get_angle_pitch_p.pure' this)

/-- `AC_AttitudeControl.get_angle_roll_p` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl.get_angle_roll_p.pure' (this : UInt64) : Id UInt64 := do
  return (this + 40)

/-- C++ `AC_AttitudeControl::get_angle_roll_p : AC_P &()`, `AC_AttitudeControl.h:80-?`. -/
def AC_AttitudeControl.get_angle_roll_p (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl.get_angle_roll_p.pure' this)

/-- `AC_AttitudeControl.get_angle_yaw_p` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl.get_angle_yaw_p.pure' (this : UInt64) : Id UInt64 := do
  return (this + 56)

/-- C++ `AC_AttitudeControl::get_angle_yaw_p : AC_P &()`, `AC_AttitudeControl.h:82-?`. -/
def AC_AttitudeControl.get_angle_yaw_p (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl.get_angle_yaw_p.pure' this)

/-- C++ `AC_PosControl::get_vel_terrain_D_ms : float () const`, `AP_Common.h:453-?`. -/
def AC_PosControl.get_vel_terrain_D_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 856)
  return t'1

/-- C++ `AC_PosControl::get_pos_estimate_U_m : float () const`, `AP_Common.h:316-?`. -/
def AC_PosControl.get_pos_estimate_U_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF64 ((this + 704) + 16)
  return Binary64.toBinary32 ((-t'1))

/-- `AC_PosControl.get_pos_offset_NED_m` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.get_pos_offset_NED_m.pure' (this : UInt64) : Id UInt64 := do
  return (this + 888)

/-- C++ `AC_PosControl::get_pos_offset_NED_m : const Vector3p &() const`, `AP_Common.h:485-?`. -/
def AC_PosControl.get_pos_offset_NED_m (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.get_pos_offset_NED_m.pure' this)

/-- C++ `AC_PosControl::D_get_max_accel_mss : float () const`, `AP_Common.h:214-?`. -/
def AC_PosControl.D_get_max_accel_mss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 652)
  return t'1

/-- C++ `AC_PosControl::NE_get_max_accel_mss : float () const`, `AP_Common.h:115-?`. -/
def AC_PosControl.NE_get_max_accel_mss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 648)
  return t'1

/-- `AC_PosControl.get_pos_estimate_NED_m` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.get_pos_estimate_NED_m.pure' (this : UInt64) : Id UInt64 := do
  return (this + 704)

/-- C++ `AC_PosControl::get_pos_estimate_NED_m : const Vector3p &() const`, `AP_Common.h:313-?`. -/
def AC_PosControl.get_pos_estimate_NED_m (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.get_pos_estimate_NED_m.pure' this)

/-- `AC_PosControl.get_vel_estimate_NED_ms` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.get_vel_estimate_NED_ms.pure' (this : UInt64) : Id UInt64 := do
  return (this + 776)

/-- C++ `AC_PosControl::get_vel_estimate_NED_ms : const Vector3f &() const`, `AP_Common.h:377-?`. -/
def AC_PosControl.get_vel_estimate_NED_ms (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.get_vel_estimate_NED_ms.pure' this)

/-- `AC_PosControl.get_pos_desired_NED_m` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.get_pos_desired_NED_m.pure' (this : UInt64) : Id UInt64 := do
  return (this + 728)

/-- C++ `AC_PosControl::get_pos_desired_NED_m : const Vector3p &() const`, `AP_Common.h:325-?`. -/
def AC_PosControl.get_pos_desired_NED_m (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.get_pos_desired_NED_m.pure' this)

/-- C++ `AC_AttitudeControl::get_dt_s : float () const`, `AC_AttitudeControl.h:77-?`. -/
def AC_AttitudeControl.get_dt_s (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 112)
  return t'1

/-- C++ `AC_AttitudeControl::attitude_command_model : void (float, float, float &, float &, float, float, float, float) const`, `AC_AttitudeControl.cpp:1108-1130`. -/
def AC_AttitudeControl.attitude_command_model (this : UInt64) (error_angle : Binary32) (desired_ang_vel : Binary32) (target_ang_vel : UInt64) (target_ang_accel : UInt64) (max_ang_vel : Binary32) (accel_max : Binary32) (input_tc : Binary32) (dt : Binary32) : PMem.M Unit := do
  let mut error_angle := error_angle
  let mut desired_ang_vel := desired_ang_vel
  let mut max_ang_vel := max_ang_vel
  let mut accel_max := accel_max
  let mut input_tc := input_tc
  let mut dt := dt
  let t'1 ← is_positive'float dt
  if !t'1 then
    return ()
  let t'2 ← is_positive'float accel_max
  if !t'2 then
    let t'3 ← radians'2 (1800 : Int32)
    accel_max := t'3
  let t'4 ← is_positive'float input_tc
  if !t'4 then
    let t'5 := (dt * (Binary64.toBinary32 ((Binary64.ofBits 0x4024000000000000 /- 10 -/))))
    input_tc := t'5
  let t'6 ← PMem.ldF32 target_ang_vel
  shape_angle_vel_accel error_angle desired_ang_vel (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'6 target_ang_accel (-max_ang_vel) max_ang_vel accel_max (accel_max / input_tc) dt true
  let t'7 ← PMem.ldF32 target_ang_vel
  let t'8 ← PMem.ldF32 target_ang_accel
  let t'9 := (t'7 + (t'8 * dt))
  PMem.stF32 target_ang_vel t'9
  return ()

/-- C++ `AC_AttitudeControl::ang_vel_limit : void (Vector3f &, float, float, float) const`, `AC_AttitudeControl.cpp:1206-1226`. -/
def AC_AttitudeControl.ang_vel_limit.body (fp : UInt64) (this : UInt64) (euler_rad : UInt64) (ang_vel_roll_max_rads : Binary32) (ang_vel_pitch_max_rads : Binary32) (ang_vel_yaw_max_rads : Binary32) : PMem.M Unit := do
  let mut ang_vel_roll_max_rads := ang_vel_roll_max_rads
  let mut ang_vel_pitch_max_rads := ang_vel_pitch_max_rads
  let mut ang_vel_yaw_max_rads := ang_vel_yaw_max_rads
  let t'1 ← is_zero ang_vel_roll_max_rads
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← is_zero ang_vel_pitch_max_rads
    sc'3 := t'2
  if sc'3 then
    let t'4 ← is_zero ang_vel_roll_max_rads
    if !t'4 then
      let t'5 ← PMem.ldF32 euler_rad
      let t'6 ← constrain_value_line'float t'5 (-ang_vel_roll_max_rads) ang_vel_roll_max_rads (Int32.toUInt32 ((1210 : Int32)))
      PMem.stF32 euler_rad t'6
    let t'7 ← is_zero ang_vel_pitch_max_rads
    if !t'7 then
      let t'8 ← PMem.ldF32 (euler_rad + 4)
      let t'9 ← constrain_value_line'float t'8 (-ang_vel_pitch_max_rads) ang_vel_pitch_max_rads (Int32.toUInt32 ((1213 : Int32)))
      PMem.stF32 (euler_rad + 4) t'9
  else
    let t'10 ← PMem.ldF32 euler_rad
    let t'11 ← PMem.ldF32 (euler_rad + 4)
    Vector2'float.Vector2'2 (fp + 0) (t'10 / ang_vel_roll_max_rads) (t'11 / ang_vel_pitch_max_rads)
    let t'12 ← Vector2'float.length (fp + 0)
    let mut thrust_vector_length : Binary32 := t'12
    if (decide (thrust_vector_length > (Binary32.ofBits 0x3f800000 /- 1 -/))) then
      let t'13 ← PMem.ldF32 (fp + 0)
      let t'14 := ((t'13 * ang_vel_roll_max_rads) / thrust_vector_length)
      PMem.stF32 euler_rad t'14
      let t'15 ← PMem.ldF32 ((fp + 0) + 4)
      let t'16 := ((t'15 * ang_vel_pitch_max_rads) / thrust_vector_length)
      PMem.stF32 (euler_rad + 4) t'16
  let t'17 ← is_zero ang_vel_yaw_max_rads
  if !t'17 then
    let t'18 ← PMem.ldF32 (euler_rad + 8)
    let t'19 ← constrain_value_line'float t'18 (-ang_vel_yaw_max_rads) ang_vel_yaw_max_rads (Int32.toUInt32 ((1224 : Int32)))
    PMem.stF32 (euler_rad + 8) t'19
  return ()

def AC_AttitudeControl.ang_vel_limit (this : UInt64) (euler_rad : UInt64) (ang_vel_roll_max_rads : Binary32) (ang_vel_pitch_max_rads : Binary32) (ang_vel_yaw_max_rads : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AC_AttitudeControl.ang_vel_limit.body fp this euler_rad ang_vel_roll_max_rads ang_vel_pitch_max_rads ang_vel_yaw_max_rads
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::command_model_rate_predictor : void (const Vector2f &, Vector2f &, Vector2f &, float) const`, `AC_AttitudeControl.cpp:1134-1152`. -/
def AC_AttitudeControl.command_model_rate_predictor.body (fp : UInt64) (this : UInt64) (error_angle_rad : UInt64) (target_ang_vel_rads : UInt64) (target_ang_accel_rads : UInt64) (dt : Binary32) : PMem.M Unit := do
  let mut dt := dt
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 36)
  let t'2 ← PMem.ldI8 t'1
  if t'2 != (0 : Int8) then
    let t'3 ← PMem.ldF32 error_angle_rad
    let t'4 ← wrap_PI'float t'3
    let t'5 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
    let t'6 ← PMem.ldF32 t'5
    let t'7 ← radians t'6
    let t'8 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'9 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'10 ← PMem.ldF32 t'9
    let t'11 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'4 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) target_ang_vel_rads target_ang_accel_rads t'7 t'8 t'10 t'11
    let t'12 ← PMem.ldF32 (error_angle_rad + 4)
    let t'13 ← wrap_PI'float t'12
    let t'14 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'15 ← PMem.ldF32 t'14
    let t'16 ← radians t'15
    let t'17 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'18 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'19 ← PMem.ldF32 t'18
    let t'20 ← PMem.ldF32 (this + 112)
    AC_AttitudeControl.attitude_command_model this t'13 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (target_ang_vel_rads + 4) (target_ang_accel_rads + 4) t'16 t'17 t'19 t'20
  else
    let t'21 ← AC_P.kP (this + 40)
    let t'22 ← AP_ParamT'float_4.operator_const_float__'1 t'21
    let t'23 ← PMem.ldF32 t'22
    let t'24 ← PMem.ldF32 (this + 276)
    let mut angleP_roll : Binary32 := (t'23 * t'24)
    let t'25 ← AC_P.kP (this + 48)
    let t'26 ← AP_ParamT'float_4.operator_const_float__'1 t'25
    let t'27 ← PMem.ldF32 t'26
    let t'28 ← PMem.ldF32 ((this + 276) + 4)
    let mut angleP_pitch : Binary32 := (t'27 * t'28)
    let t'29 ← PMem.ldF32 error_angle_rad
    let t'30 ← wrap_PI'float t'29
    let t'31 := (angleP_roll * t'30)
    PMem.stF32 target_ang_vel_rads t'31
    let t'32 ← PMem.ldF32 (error_angle_rad + 4)
    let t'33 ← wrap_PI'float t'32
    let t'34 := (angleP_pitch * t'33)
    PMem.stF32 (target_ang_vel_rads + 4) t'34
  let t'35 ← PMem.ldF32 target_ang_vel_rads
  let t'36 ← PMem.ldF32 (target_ang_vel_rads + 4)
  Vector3'float.Vector3 (fp + 0) t'35 t'36 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'37 ← AP_ParamT'float_4.operator_const_float__'1 (this + 12)
  let t'38 ← PMem.ldF32 t'37
  let t'39 ← radians t'38
  let t'40 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'41 ← PMem.ldF32 t'40
  let t'42 ← radians t'41
  AC_AttitudeControl.ang_vel_limit this (fp + 0) t'39 t'42 (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'43 ← PMem.ldF32 (fp + 0)
  PMem.stF32 target_ang_vel_rads t'43
  let t'44 ← PMem.ldF32 ((fp + 0) + 4)
  PMem.stF32 (target_ang_vel_rads + 4) t'44
  return ()

def AC_AttitudeControl.command_model_rate_predictor (this : UInt64) (error_angle_rad : UInt64) (target_ang_vel_rads : UInt64) (target_ang_accel_rads : UInt64) (dt : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_AttitudeControl.command_model_rate_predictor.body fp this error_angle_rad target_ang_vel_rads target_ang_accel_rads dt
  PMem.leave fp
  return r

/-- `AC_AttitudeControl.get_attitude_target_ang_vel` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl.get_attitude_target_ang_vel.pure' (this : UInt64) : Id UInt64 := do
  return (this + 156)

/-- C++ `AC_AttitudeControl::get_attitude_target_ang_vel : const Vector3f &() const`, `<scratch space>:338-?`. -/
def AC_AttitudeControl.get_attitude_target_ang_vel (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl.get_attitude_target_ang_vel.pure' this)

/-- C++ `AC_PosControl::NE_set_pos_error_max_m : void (float)`, `AP_Common.h:119-?`. -/
def AC_PosControl.NE_set_pos_error_max_m (this : UInt64) (error_max_m : Binary32) : PMem.M Unit := do
  let mut error_max_m := error_max_m
  AC_P_2D.set_error_max (this + 36) error_max_m
  return ()

/-- `AC_PosControl.get_accel_target_NED_mss` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.get_accel_target_NED_mss.pure' (this : UInt64) : Id UInt64 := do
  return (this + 824)

/-- C++ `AC_PosControl::get_accel_target_NED_mss : const Vector3f &() const`, `AP_Common.h:426-?`. -/
def AC_PosControl.get_accel_target_NED_mss (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.get_accel_target_NED_mss.pure' this)

/-- C++ `AC_PosControl::get_roll_rad : float () const`, `AP_Common.h:508-?`. -/
def AC_PosControl.get_roll_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 688)
  return t'1

/-- C++ `AC_PosControl::get_pitch_rad : float () const`, `AP_Common.h:511-?`. -/
def AC_PosControl.get_pitch_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 692)
  return t'1

/-- C++ `AC_AttitudeControl::get_attitude_target_quat : Quaternion () const`, `<scratch space>:335-?`. -/
def AC_AttitudeControl.get_attitude_target_quat (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  QuaternionT'float.QuaternionT'4 sret (this + 140)
  return ()

/-- C++ `AC_PosControl::get_pos_error_D_m : float () const`, `AP_Common.h:371-?`. -/
def AC_PosControl.get_pos_error_D_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AC_P_1D.get_error (this + 60)
  return t'1

/-- C++ `AC_PosControl::crosstrack_error_m : float () const`, `AC_PosControl.cpp:1553-1568`. -/
def AC_PosControl.crosstrack_error_m.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Vector3'double.xy (this + 752)
  let t'2 ← Vector3'double.xy (this + 704)
  Vector2'double.operator_ t'1 (fp + 8) t'2
  let t'3 := (fp + 8)
  Vector2'double.tofloat t'3 (fp + 24)
  let t'4 := (fp + 24)
  Vector2'float.Vector2'3 (fp + 0) t'4
  let t'5 ← Vector3'float.xy (this + 788)
  let t'6 ← Vector2'float.length_squared t'5
  let t'7 ← is_zero t'6
  if t'7 then
    let t'8 ← Vector2'float.length (fp + 0)
    return t'8
  else
    let t'9 ← Vector3'float.xy (this + 788)
    Vector2'float.normalized t'9 (fp + 40)
    let t'10 := (fp + 40)
    Vector2'float.Vector2'3 (fp + 32) t'10
    let t'11 ← Vector2'float.operator_'4 (fp + 0) (fp + 32)
    let mut dot_error : Binary32 := t'11
    let t'12 ← Vector2'float.length_squared (fp + 0)
    let t'13 ← sq dot_error
    PMem.stF32 (fp + 48) (t'12 - t'13)
    PMem.stF32 (fp + 52) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    let t'14 ← MAX'float_float (fp + 48) (fp + 52)
    let t'15 ← PMem.ldF32 t'14
    let t'16 ← safe_sqrt'float t'15
    return t'16

def AC_PosControl.crosstrack_error_m (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 56
  let r ← AC_PosControl.crosstrack_error_m.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::get_bearing_to_target_rad : float () const`, `AC_PosControl.cpp:1433-1436`. -/
def AC_PosControl.get_bearing_to_target_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Vector3'double.xy (this + 752)
  let t'2 ← Vector3'double.xy (this + 704)
  Vector2'double.operator_ t'1 (fp + 0) t'2
  let t'3 := (fp + 0)
  let t'4 ← Vector2'double.angle t'3
  return Binary64.toBinary32 (t'4)

def AC_PosControl.get_bearing_to_target_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← AC_PosControl.get_bearing_to_target_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::get_pos_error_NE_m : float () const`, `AP_Common.h:364-?`. -/
def AC_PosControl.get_pos_error_NE_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AC_P_2D.get_error (this + 36)
  let t'2 ← Vector2'float.length t'1
  return t'2

/-- C++ `AC_AttitudeControl::AC_AttitudeControl : void (AP_AHRS_View &, AP_Motors &)`, `AC_AttitudeControl.h:49-63`. -/
def AC_AttitudeControl.AC_AttitudeControl.body (fp : UInt64) (this : UInt64) (ahrs : UInt64) (motors : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 (this + 28)
  AP_Param.AP_Param'2 (this + 32)
  AP_Param.AP_Param'2 (this + 36)
  AP_Param.AP_Param'2 (this + 37)
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x40900000 /- 9/2 -/)
  AC_P.AC_P (this + 40) (fp + 0)
  PMem.stF32 (fp + 4) (Binary32.ofBits 0x40900000 /- 9/2 -/)
  AC_P.AC_P (this + 48) (fp + 4)
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x40900000 /- 9/2 -/)
  AC_P.AC_P (this + 56) (fp + 8)
  AP_Param.AP_Param'2 (this + 64)
  AP_Param.AP_Param'2 (this + 68)
  AP_Param.AP_Param'2 (this + 72)
  AP_Param.AP_Param'2 (this + 76)
  AP_Param.AP_Param'2 (this + 80)
  AP_Param.AP_Param'2 (this + 84)
  Vector3'float.Vector3'2 (this + 88)
  Vector3'float.Vector3'2 (this + 116)
  Vector3'float.Vector3'2 (this + 128)
  QuaternionT'float.QuaternionT (this + 140)
  Vector3'float.Vector3'2 (this + 156)
  Vector3'float.Vector3'2 (this + 168)
  Vector3'float.Vector3'2 (this + 180)
  Vector3'float.Vector3'2 (this + 192)
  Vector3'float.Vector3'2 (this + 204)
  QuaternionT'float.QuaternionT (this + 216)
  PMem.stF32 (this + 240) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 244) (Int32.toBinary32 ((0 : Int32)))
  PMem.stB (this + 248) true
  PMem.stF32 (this + 252) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 256) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
  PMem.stF32 (this + 260) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
  PMem.stF32 (this + 264) (Binary32.ofBits 0x3f800000 /- 1 -/)
  Vector3'float.Vector3 (this + 276) (Int32.toBinary32 ((1 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int32.toBinary32 ((1 : Int32)))
  Vector3'float.Vector3'2 (this + 288)
  Vector3'float.Vector3 (this + 300) (Int32.toBinary32 ((1 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int32.toBinary32 ((1 : Int32)))
  Vector3'float.Vector3'2 (this + 312)
  Vector3'float.Vector3 (this + 324) (Int32.toBinary32 ((1 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int32.toBinary32 ((1 : Int32)))
  Vector3'float.Vector3'2 (this + 336)
  PMem.stU64 (this + 352) ahrs
  PMem.stU64 (this + 360) motors
  PMem.stU64 (0xbf90 : UInt64) /- &AC_AttitudeControl::_singleton -/ this
  AP_Param.setup_object_defaults this (0x5b38 : UInt64) /- &AC_AttitudeControl::var_info -/
  return ()

def AC_AttitudeControl.AC_AttitudeControl (this : UInt64) (ahrs : UInt64) (motors : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_AttitudeControl.AC_AttitudeControl.body fp this ahrs motors
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl_Multi::AC_AttitudeControl_Multi : void (AP_AHRS_View &, AP_MotorsMulticopter &)`, `AC_AttitudeControl_Multi.cpp:337-346`. -/
def AC_AttitudeControl_Multi.AC_AttitudeControl_Multi.body (fp : UInt64) (this : UInt64) (ahrs : UInt64) (motors : UInt64) : PMem.M Unit := do
  AC_AttitudeControl.AC_AttitudeControl this ahrs motors
  PMem.stU64 (this + 368) motors
  PMem.stF32 ((fp + 0) + 0) (Binary32.ofBits 0x3e0a3d71 /- 27000001/200000000 -/)
  PMem.stF32 ((fp + 0) + 4) (Binary32.ofBits 0x3e0a3d71 /- 27000001/200000000 -/)
  PMem.stF32 ((fp + 0) + 8) (Binary32.ofBits 0x3b6bedfa /- 179999997/50000000000 -/)
  PMem.stF32 ((fp + 0) + 12) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((fp + 0) + 16) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
  PMem.stF32 ((fp + 0) + 20) (Binary32.ofBits 0x41a00000 /- 20 -/)
  PMem.stF32 ((fp + 0) + 24) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((fp + 0) + 28) (Binary32.ofBits 0x41a00000 /- 20 -/)
  PMem.stF32 ((fp + 0) + 32) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 ((fp + 0) + 36) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  discard <| PMem.memset ((fp + 0) + 40) 0 4
  AC_PID.AC_PID (this + 376) (fp + 0)
  PMem.stF32 ((fp + 48) + 0) (Binary32.ofBits 0x3e0a3d71 /- 27000001/200000000 -/)
  PMem.stF32 ((fp + 48) + 4) (Binary32.ofBits 0x3e0a3d71 /- 27000001/200000000 -/)
  PMem.stF32 ((fp + 48) + 8) (Binary32.ofBits 0x3b6bedfa /- 179999997/50000000000 -/)
  PMem.stF32 ((fp + 48) + 12) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((fp + 48) + 16) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
  PMem.stF32 ((fp + 48) + 20) (Binary32.ofBits 0x41a00000 /- 20 -/)
  PMem.stF32 ((fp + 48) + 24) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((fp + 48) + 28) (Binary32.ofBits 0x41a00000 /- 20 -/)
  PMem.stF32 ((fp + 48) + 32) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 ((fp + 48) + 36) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  discard <| PMem.memset ((fp + 48) + 40) 0 4
  AC_PID.AC_PID (this + 616) (fp + 48)
  PMem.stF32 ((fp + 96) + 0) (Binary32.ofBits 0x3e3851ec /- 180000007/1000000000 -/)
  PMem.stF32 ((fp + 96) + 4) (Binary32.ofBits 0x3c9374bc /- 22499999/1250000000 -/)
  PMem.stF32 ((fp + 96) + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((fp + 96) + 12) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 ((fp + 96) + 16) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
  PMem.stF32 ((fp + 96) + 20) (Binary32.ofBits 0x41a00000 /- 20 -/)
  PMem.stF32 ((fp + 96) + 24) (Binary32.ofBits 0x40200000 /- 5/2 -/)
  PMem.stF32 ((fp + 96) + 28) (Binary32.ofBits 0x41a00000 /- 20 -/)
  PMem.stF32 ((fp + 96) + 32) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 ((fp + 96) + 36) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  discard <| PMem.memset ((fp + 96) + 40) 0 4
  AC_PID.AC_PID (this + 856) (fp + 96)
  AP_Param.AP_Param'2 (this + 1096)
  AP_Param.AP_Param'2 (this + 1100)
  AP_Param.AP_Param'2 (this + 1104)
  AP_Param.AP_Param'2 (this + 1108)
  AP_Param.setup_object_defaults this (0x19d0 : UInt64) /- &AC_AttitudeControl_Multi::var_info -/
  return ()

def AC_AttitudeControl_Multi.AC_AttitudeControl_Multi (this : UInt64) (ahrs : UInt64) (motors : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 140
  let r ← AC_AttitudeControl_Multi.AC_AttitudeControl_Multi.body fp this ahrs motors
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::AC_PosControl : void (AP_AHRS_View &, const AP_Motors &, AC_AttitudeControl &)`, `AC_PosControl.cpp:353-373`. -/
def AC_PosControl.AC_PosControl (this : UInt64) (ahrs : UInt64) (motors : UInt64) (attitude_control : UInt64) : PMem.M Unit := do
  PMem.stU64 (this + 0) ahrs
  PMem.stU64 (this + 8) motors
  PMem.stU64 (this + 16) attitude_control
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 (this + 28)
  AP_Param.AP_Param'2 (this + 32)
  AC_P_2D.AC_P_2D (this + 36) (Binary32.ofBits 0x3f800000 /- 1 -/)
  AC_P_1D.AC_P_1D (this + 60) (Binary32.ofBits 0x3f800000 /- 1 -/)
  AC_PID_2D.AC_PID_2D (this + 84) (Binary32.ofBits 0x40000000 /- 2 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Binary32.ofBits 0x3e800000 /- 1/4 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x41200000 /- 10 -/) (Binary32.ofBits 0x40a00000 /- 5 -/) (Binary32.ofBits 0x40a00000 /- 5 -/)
  AC_PID_Basic.AC_PID_Basic (this + 264) (Binary32.ofBits 0x40a00000 /- 5 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x41200000 /- 10 -/) (Binary32.ofBits 0x40a00000 /- 5 -/) (Binary32.ofBits 0x40a00000 /- 5 -/)
  AC_PID.AC_PID'2 (this + 384) (Binary32.ofBits 0x3d4ccccd /- 500000007/10000000000 -/) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f4ccccd /- 800000011/1000000000 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x41a00000 /- 20 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Int32.toBinary32 ((0 : Int32))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toBinary32 ((0 : Int32)))
  PMem.stF32 (this + 636) (Binary32.ofBits 0x40a00000 /- 5 -/)
  PMem.stF32 (this + 640) (Binary32.ofBits 0x40200000 /- 5/2 -/)
  PMem.stF32 (this + 644) (Binary32.ofBits 0x3fc00000 /- 3/2 -/)
  PMem.stF32 (this + 648) (Binary32.ofBits 0x3f800000 /- 1 -/)
  PMem.stF32 (this + 652) (Binary32.ofBits 0x40200000 /- 5/2 -/)
  PMem.stF32 (this + 656) (Binary32.ofBits 0x40a00000 /- 5 -/)
  PMem.stF32 (this + 660) (Binary32.ofBits 0x40a00000 /- 5 -/)
  PMem.stF32 (this + 664) (Binary32.ofBits 0x40000000 /- 2 -/)
  Vector2'float.Vector2 (this + 668)
  Vector2'float.Vector2 (this + 676)
  PMem.stF32 (this + 684) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  Vector3'double.Vector3 (this + 704)
  Vector3'double.Vector3 (this + 728)
  Vector3'double.Vector3 (this + 752)
  Vector3'float.Vector3'2 (this + 776)
  Vector3'float.Vector3'2 (this + 788)
  Vector3'float.Vector3'2 (this + 800)
  Vector3'float.Vector3'2 (this + 812)
  Vector3'float.Vector3'2 (this + 824)
  Vector3'float.Vector3'2 (this + 836)
  Vector3'double.Vector3 (this + 864)
  Vector3'double.Vector3 (this + 888)
  Vector3'float.Vector3'2 (this + 912)
  Vector3'float.Vector3'2 (this + 924)
  Vector3'float.Vector3'2 (this + 936)
  Vector3'float.Vector3'2 (this + 948)
  PMem.stU8 (this + 972) (0 : UInt8)
  AP_Param.setup_object_defaults this (0x33c8 : UInt64) /- &AC_PosControl::var_info -/
  PMem.stU64 (0xbf18 : UInt64) /- &AC_PosControl::_singleton -/ this
  return ()

/-- C++ `AC_PosControl::set_dt_s : void (float)`, `AP_Common.h:50-?`. -/
def AC_PosControl.set_dt_s (this : UInt64) (dt : Binary32) : PMem.M Unit := do
  let mut dt := dt
  PMem.stF32 (this + 624) dt
  return ()

/-- C++ `AC_AttitudeControl::set_dt_s : void (float)`, `AC_AttitudeControl.h:74-?`. -/
def AC_AttitudeControl.set_dt_s (this : UInt64) (dt_s : Binary32) : PMem.M Unit := do
  let mut dt_s := dt_s
  PMem.stF32 (this + 112) dt_s
  return ()

/-- C++ `AC_AttitudeControl::set_PD_scale_mult : void (const Vector3f &)`, `<scratch space>:526-?`. -/
def AC_AttitudeControl.set_PD_scale_mult (this : UInt64) (pd_scale : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'float.operator__'4 (this + 300) pd_scale
  discard <| pure (t'1)
  return ()

/-- C++ `AC_AttitudeControl::set_angle_P_scale_mult : void (const Vector3f &)`, `<scratch space>:517-?`. -/
def AC_AttitudeControl.set_angle_P_scale_mult (this : UInt64) (angle_P_scale : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'float.operator__'4 (this + 276) angle_P_scale
  discard <| pure (t'1)
  return ()

/-- C++ `AC_AttitudeControl::rate_controller_target_reset : void ()`, `AC_AttitudeControl.cpp:289-296`. -/
def AC_AttitudeControl.rate_controller_target_reset (this : UInt64) : PMem.M Unit := do
  Vector3'float.zero (this + 192)
  Vector3'float.zero (this + 204)
  discard <| PMem.memcpy (this + 300) (0x135d0 : UInt64) /- &AC_AttitudeControl::VECTORF_111 -/ 12
  discard <| pure ((this + 300))
  discard <| PMem.memcpy (this + 324) (0x135d0 : UInt64) /- &AC_AttitudeControl::VECTORF_111 -/ 12
  discard <| pure ((this + 324))
  discard <| PMem.memcpy (this + 276) (0x135d0 : UInt64) /- &AC_AttitudeControl::VECTORF_111 -/ 12
  discard <| pure ((this + 276))
  return ()

/-- C++ `AC_PosControl::update_estimates : void (bool)`, `AC_PosControl.cpp:1446-1465`. -/
def AC_PosControl.update_estimates.body (fp : UInt64) (this : UInt64) (high_vibes : Bool) : PMem.M Unit := do
  let mut high_vibes := high_vibes
  Vector3'double.Vector3 (fp + 0)
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_relative_position_NED_origin'1 t'1 (fp + 0)
  if !t'2 then
    let t'3 ← VehicleBridge.ahrs'0
    let t'4 ← VehicleBridge.AP_AHRS.get_relative_position_D_origin_float'1 t'3 (fp + 24)
    if t'4 then
      let t'5 ← PMem.ldF32 (fp + 24)
      let t'6 := Binary32.toBinary64 (t'5)
      PMem.stF64 ((fp + 0) + 16) t'6
  discard <| PMem.memcpy (this + 704) (fp + 0) 24
  discard <| pure ((this + 704))
  Vector3'float.Vector3'2 (fp + 32)
  let t'7 ← VehicleBridge.ahrs'0
  let t'8 ← VehicleBridge.AP_AHRS.get_velocity_NED'1 t'7 (fp + 32)
  if ((!t'8) || high_vibes) then
    let t'9 ← VehicleBridge.ahrs'0
    let t'10 ← VehicleBridge.AP_AHRS.get_vert_pos_rate_D'1 t'9 (fp + 48)
    if t'10 then
      let t'11 ← PMem.ldF32 (fp + 48)
      PMem.stF32 ((fp + 32) + 8) t'11
  discard <| PMem.memcpy (this + 776) (fp + 32) 12
  discard <| pure ((this + 776))
  return ()

def AC_PosControl.update_estimates (this : UInt64) (high_vibes : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 52
  let r ← AC_PosControl.update_estimates.body fp this high_vibes
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::inertial_frame_reset : void ()`, `AC_AttitudeControl.cpp:1286-1297`. -/
def AC_AttitudeControl.inertial_frame_reset.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  QuaternionT'float.QuaternionT (fp + 0)
  let t'1 ← PMem.ldU64 (this + 352)
  VehicleBridge.AP_AHRS_View.get_quat_body_to_ned'1 t'1 (fp + 0)
  QuaternionT'float.operator_ (fp + 0) (fp + 16) (this + 216)
  let t'2 := (fp + 16)
  discard <| PMem.memcpy (this + 140) t'2 16
  discard <| pure ((this + 140))
  QuaternionT'float.to_euler'2 (this + 140) (this + 116)
  return ()

def AC_AttitudeControl.inertial_frame_reset (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← AC_AttitudeControl.inertial_frame_reset.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::set_reset_handling_method : void (EKFResetMethod)`, `AP_Common.h:591-?`. -/
def AC_PosControl.set_reset_handling_method (this : UInt64) (reset_method : UInt8) : PMem.M Unit := do
  let mut reset_method := reset_method
  PMem.stU8 (this + 972) reset_method
  return ()

/-- C++ `AC_AttitudeControl::reset_rate_controller_I_terms : void ()`, `AC_AttitudeControl.cpp:273-278`. -/
def AC_AttitudeControl.reset_rate_controller_I_terms (this : UInt64) : PMem.M Unit := do
  let t'1 ← AC_AttitudeControl_Multi.get_rate_roll_pid this
  AC_PID.reset_I t'1
  let t'2 ← AC_AttitudeControl_Multi.get_rate_pitch_pid this
  AC_PID.reset_I t'2
  let t'3 ← AC_AttitudeControl_Multi.get_rate_yaw_pid this
  AC_PID.reset_I t'3
  return ()

/-- C++ `AC_AttitudeControl::euler_derivative_to_body : void (const Quaternion &, const Vector3f &, Vector3f &)`, `AC_AttitudeControl.cpp:1303-1316`. -/
def AC_AttitudeControl.euler_derivative_to_body (this : UInt64) (att : UInt64) (euler_derivative_rads : UInt64) (body_derivative_rads : UInt64) : PMem.M Unit := do
  let t'1 ← QuaternionT'float.get_euler_pitch att
  let mut theta : Binary32 := t'1
  let t'2 ← QuaternionT'float.get_euler_roll att
  let mut phi : Binary32 := t'2
  let mut sin_theta : Binary32 := (Musl.sinf.sinf theta)
  let mut cos_theta : Binary32 := (Musl.cosf.cosf theta)
  let mut sin_phi : Binary32 := (Musl.sinf.sinf phi)
  let mut cos_phi : Binary32 := (Musl.cosf.cosf phi)
  let t'3 ← PMem.ldF32 euler_derivative_rads
  let t'4 ← PMem.ldF32 (euler_derivative_rads + 8)
  let t'5 := (t'3 - (sin_theta * t'4))
  PMem.stF32 body_derivative_rads t'5
  let t'6 ← PMem.ldF32 (euler_derivative_rads + 4)
  let t'7 ← PMem.ldF32 (euler_derivative_rads + 8)
  let t'8 := ((cos_phi * t'6) + ((sin_phi * cos_theta) * t'7))
  PMem.stF32 (body_derivative_rads + 4) t'8
  let t'9 ← PMem.ldF32 (euler_derivative_rads + 4)
  let t'10 ← PMem.ldF32 (euler_derivative_rads + 8)
  let t'11 := (((-sin_phi) * t'9) + ((cos_theta * cos_phi) * t'10))
  PMem.stF32 (body_derivative_rads + 8) t'11
  return ()

/-- C++ `AC_AttitudeControl::reset_yaw_target_and_rate : void (bool)`, `AC_AttitudeControl.cpp:1267-1283`. -/
def AC_AttitudeControl.reset_yaw_target_and_rate.body (fp : UInt64) (this : UInt64) (reset_rate : Bool) : PMem.M Unit := do
  let mut reset_rate := reset_rate
  let t'1 ← PMem.ldU64 (this + 352)
  let t'2 ← VehicleBridge.AP_AHRS_View.yaw'field t'1
  let t'3 ← PMem.ldF32 ((this + 116) + 8)
  let mut yaw_shift : Binary32 := (t'2 - t'3)
  QuaternionT'float.QuaternionT (fp + 0)
  Vector3'float.Vector3 (fp + 32) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) yaw_shift
  Vector3'float.Vector3'3 (fp + 16) (fp + 32)
  QuaternionT'float.from_axis_angle (fp + 0) (fp + 16)
  QuaternionT'float.operator_ (fp + 0) (fp + 48) (this + 140)
  let t'4 := (fp + 48)
  discard <| PMem.memcpy (this + 140) t'4 16
  discard <| pure ((this + 140))
  if reset_rate then
    let t'5 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((this + 128) + 8) t'5
    let t'6 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 ((this + 168) + 8) t'6
    AC_AttitudeControl.euler_derivative_to_body this (this + 140) (this + 128) (this + 156)
  return ()

def AC_AttitudeControl.reset_yaw_target_and_rate (this : UInt64) (reset_rate : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← AC_AttitudeControl.reset_yaw_target_and_rate.body fp this reset_rate
  PMem.leave fp
  return r

/-- C++ `AC_CommandModel::get_rate : float () const`, `AC_CommandModel.h:18-?`. -/
def AC_CommandModel.get_rate (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 4)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_CommandModel::get_expo : float () const`, `AC_CommandModel.h:19-?`. -/
def AC_CommandModel.get_expo (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 8)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_AttitudeControl::reset_rate_controller_I_terms_smoothly : void ()`, `AC_AttitudeControl.cpp:281-286`. -/
def AC_AttitudeControl.reset_rate_controller_I_terms_smoothly (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 112)
  let t'2 ← AC_AttitudeControl_Multi.get_rate_roll_pid this
  AC_PID.relax_integrator t'2 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'1 (Binary32.ofBits 0x3e23d70a /- 39999999/250000000 -/)
  let t'3 ← PMem.ldF32 (this + 112)
  let t'4 ← AC_AttitudeControl_Multi.get_rate_pitch_pid this
  AC_PID.relax_integrator t'4 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'3 (Binary32.ofBits 0x3e23d70a /- 39999999/250000000 -/)
  let t'5 ← PMem.ldF32 (this + 112)
  let t'6 ← AC_AttitudeControl_Multi.get_rate_yaw_pid this
  AC_PID.relax_integrator t'6 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'5 (Binary32.ofBits 0x3e23d70a /- 39999999/250000000 -/)
  return ()

/-- C++ `AC_AttitudeControl_Multi::get_throttle_boosted : float (float)`, `AC_AttitudeControl_Multi.cpp:388-405`. -/
def AC_AttitudeControl_Multi.get_throttle_boosted (this : UInt64) (throttle_in : Binary32) : PMem.M Binary32 := do
  let mut throttle_in := throttle_in
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 37)
  let t'2 ← PMem.ldI8 t'1
  if !(t'2 != (0 : Int8)) then
    let t'3 := Int32.toBinary32 ((0 : Int32))
    PMem.stF32 (this + 244) t'3
    return throttle_in
  let t'4 ← PMem.ldU64 (this + 352)
  let t'5 ← VehicleBridge.AP_AHRS_View.cos_pitch'0 t'4
  let t'6 ← PMem.ldU64 (this + 352)
  let t'7 ← VehicleBridge.AP_AHRS_View.cos_roll'0 t'6
  let mut cos_tilt : Binary32 := (t'5 * t'7)
  let t'8 ← constrain_value_line'float ((Binary32.ofBits 0x41200000 /- 10 -/) * cos_tilt) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((398 : Int32)))
  let mut inverted_factor : Binary32 := t'8
  let t'9 ← PMem.ldF32 (this + 232)
  let mut cos_tilt_target : Binary32 := (Musl.cosf.cosf t'9)
  let t'10 ← constrain_value_line'float cos_tilt_target (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((400 : Int32)))
  let mut boost_factor : Binary32 := ((Binary32.ofBits 0x3f800000 /- 1 -/) / t'10)
  let mut throttle_out : Binary32 := ((throttle_in * inverted_factor) * boost_factor)
  let t'11 ← constrain_value_line'float (throttle_out - throttle_in) (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((403 : Int32)))
  PMem.stF32 (this + 244) t'11
  return throttle_out

/-- C++ `AC_PosControl::get_estimated_accel_U_mss : float () const`, `definitions.h:611-?`. -/
def AC_PosControl.get_estimated_accel_U_mss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AC_PosControl.get_estimated_accel_D_mss this
  return -t'1

/-- C++ `AC_PosControl::get_vel_estimate_U_ms : float () const`, `AP_Common.h:380-?`. -/
def AC_PosControl.get_vel_estimate_U_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 ((this + 776) + 8)
  return -t'1

/-- C++ `AC_PosControl::calculate_overspeed_gain : float ()`, `AC_PosControl.cpp:1673-1687`. -/
def AC_PosControl.calculate_overspeed_gain (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 ((this + 788) + 8)
  let t'2 ← PMem.ldF32 (this + 644)
  let mut sc'5 := (decide (t'1 > t'2))
  if sc'5 then
    let t'3 ← PMem.ldF32 (this + 644)
    let t'4 ← is_zero t'3
    sc'5 := !t'4
  if sc'5 then
    let t'6 ← PMem.ldF32 ((this + 788) + 8)
    let t'7 ← PMem.ldF32 (this + 644)
    return (((Binary32.ofBits 0x40000000 /- 2 -/) * t'6) / t'7)
  let t'8 ← PMem.ldF32 ((this + 788) + 8)
  let t'9 ← PMem.ldF32 (this + 640)
  let mut sc'12 := (decide (t'8 < (-t'9)))
  if sc'12 then
    let t'10 ← PMem.ldF32 (this + 640)
    let t'11 ← is_zero t'10
    sc'12 := !t'11
  if sc'12 then
    let t'13 ← PMem.ldF32 ((this + 788) + 8)
    let t'14 ← PMem.ldF32 (this + 640)
    return (((-(Binary32.ofBits 0x40000000 /- 2 -/)) * t'13) / t'14)
  return Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))

/-- C++ `AC_PosControl::input_pos_vel_accel_D_m : void (float &, float &, float, bool)`, `AC_PosControl.cpp:1002-1021`. -/
def AC_PosControl.input_pos_vel_accel_D_m.body (fp : UInt64) (this : UInt64) (pos_d_m : UInt64) (vel_d_ms : UInt64) (accel_d_mss : Binary32) (limit_output : Bool) : PMem.M Unit := do
  let mut accel_d_mss := accel_d_mss
  let mut limit_output := limit_output
  let t'1 ← AC_PosControl.calculate_overspeed_gain this
  let mut overspeed_gain : Binary32 := t'1
  let t'2 ← PMem.ldF32 (this + 652)
  let mut accel_max_d_mss : Binary32 := (t'2 * overspeed_gain)
  let t'3 ← PMem.ldF32 (this + 660)
  let mut jerk_max_d_msss : Binary32 := (t'3 * overspeed_gain)
  let t'4 ← PMem.ldF32 ((this + 812) + 8)
  let t'5 ← PMem.ldF32 (this + 624)
  let t'6 ← PMem.ldF32 ((this + 836) + 8)
  let t'7 ← AC_P_1D.get_error (this + 60)
  let t'8 ← AC_PID_Basic.get_error (this + 264)
  update_pos_vel_accel ((this + 728) + 16) ((this + 788) + 8) t'4 t'5 t'6 t'7 t'8
  let t'9 ← PMem.ldF32 pos_d_m
  let t'10 ← PMem.ldF32 vel_d_ms
  let t'11 ← PMem.ldF64 ((this + 728) + 16)
  let t'12 ← PMem.ldF32 ((this + 788) + 8)
  let t'13 ← PMem.ldF32 (this + 640)
  let t'14 ← PMem.ldF32 (this + 644)
  let t'15 ← constrain_value_line'float accel_max_d_mss (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x401e000000000000 /- 15/2 -/))) (Int32.toUInt32 ((1015 : Int32)))
  let t'16 ← PMem.ldF32 (this + 624)
  shape_pos_vel_accel (Binary32.toBinary64 (t'9)) t'10 accel_d_mss t'11 t'12 ((this + 812) + 8) (-t'13) t'14 (-accel_max_d_mss) t'15 jerk_max_d_msss t'16 limit_output
  let t'17 ← PMem.ldF32 pos_d_m
  PMem.stF64 (fp + 0) (Binary32.toBinary64 (t'17))
  let t'18 ← PMem.ldF32 (this + 624)
  update_pos_vel_accel (fp + 0) vel_d_ms accel_d_mss t'18 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let t'19 ← PMem.ldF64 (fp + 0)
  let t'20 := Binary64.toBinary32 (t'19)
  PMem.stF32 pos_d_m t'20
  return ()

def AC_PosControl.input_pos_vel_accel_D_m (this : UInt64) (pos_d_m : UInt64) (vel_d_ms : UInt64) (accel_d_mss : Binary32) (limit_output : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AC_PosControl.input_pos_vel_accel_D_m.body fp this pos_d_m vel_d_ms accel_d_mss limit_output
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::get_pos_desired_U_m : float () const`, `AP_Common.h:346-?`. -/
def AC_PosControl.get_pos_desired_U_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF64 ((this + 728) + 16)
  return Binary64.toBinary32 ((-t'1))

/-- C++ `AC_PosControl::input_vel_accel_D_m : void (float &, float, bool)`, `AC_PosControl.cpp:948-964`. -/
def AC_PosControl.input_vel_accel_D_m (this : UInt64) (vel_d_ms : UInt64) (accel_d_mss : Binary32) (limit_output : Bool) : PMem.M Unit := do
  let mut accel_d_mss := accel_d_mss
  let mut limit_output := limit_output
  let t'1 ← AC_PosControl.calculate_overspeed_gain this
  let mut overspeed_gain : Binary32 := t'1
  let t'2 ← PMem.ldF32 (this + 652)
  let mut accel_max_d_mss : Binary32 := (t'2 * overspeed_gain)
  let t'3 ← PMem.ldF32 (this + 660)
  let mut jerk_max_d_msss : Binary32 := (t'3 * overspeed_gain)
  let t'4 ← PMem.ldF32 ((this + 812) + 8)
  let t'5 ← PMem.ldF32 (this + 624)
  let t'6 ← PMem.ldF32 ((this + 836) + 8)
  let t'7 ← AC_P_1D.get_error (this + 60)
  let t'8 ← AC_PID_Basic.get_error (this + 264)
  update_pos_vel_accel ((this + 728) + 16) ((this + 788) + 8) t'4 t'5 t'6 t'7 t'8
  let t'9 ← PMem.ldF32 vel_d_ms
  let t'10 ← PMem.ldF32 ((this + 788) + 8)
  let t'11 ← constrain_value_line'float accel_max_d_mss (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x401e000000000000 /- 15/2 -/))) (Int32.toUInt32 ((960 : Int32)))
  let t'12 ← PMem.ldF32 (this + 624)
  shape_vel_accel t'9 accel_d_mss t'10 ((this + 812) + 8) (-accel_max_d_mss) t'11 jerk_max_d_msss t'12 limit_output
  let t'13 ← PMem.ldF32 (this + 624)
  update_vel_accel vel_d_ms accel_d_mss t'13 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  return ()

/-- C++ `AC_PosControl::D_set_pos_target_from_climb_rate_ms : void (float, bool)`, `AC_PosControl.cpp:976-985`. -/
def AC_PosControl.D_set_pos_target_from_climb_rate_ms.body (fp : UInt64) (this : UInt64) (climb_rate_ms : Binary32) (ignore_descent_limit : Bool) : PMem.M Unit := do
  let mut climb_rate_ms := climb_rate_ms
  let mut ignore_descent_limit := ignore_descent_limit
  if ignore_descent_limit then
    PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'1 ← MIN'float_float ((this + 836) + 8) (fp + 0)
    let t'2 ← PMem.ldF32 t'1
    PMem.stF32 ((this + 836) + 8) t'2
  PMem.stF32 (fp + 8) (-climb_rate_ms)
  AC_PosControl.input_vel_accel_D_m this (fp + 8) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) true
  return ()

def AC_PosControl.D_set_pos_target_from_climb_rate_ms (this : UInt64) (climb_rate_ms : Binary32) (ignore_descent_limit : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_PosControl.D_set_pos_target_from_climb_rate_ms.body fp this climb_rate_ms ignore_descent_limit
  PMem.leave fp
  return r

/-- `AC_AttitudeControl.get_roll_trim_cd` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl.get_roll_trim_cd.pure' (this : UInt64) : Id Binary32 := do
  return Int32.toBinary32 ((0 : Int32))

/-- C++ `AC_AttitudeControl::get_roll_trim_cd : float ()`, `<scratch space>:483-?`. -/
def AC_AttitudeControl.get_roll_trim_cd (this : UInt64) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl.get_roll_trim_cd.pure' this)

/-- `AC_AttitudeControl.get_roll_trim_rad` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl.get_roll_trim_rad.pure' (this : UInt64) : Id Binary32 := do
  let t'1 ← _root_.Vehicle_lib.AC_AttitudeControl.get_roll_trim_cd.pure' this
  let t'2 ← _root_.Vehicle_lib.cd_to_rad.pure' t'1
  return t'2

/-- C++ `AC_AttitudeControl::get_roll_trim_rad : float ()`, `<scratch space>:487-?`. -/
def AC_AttitudeControl.get_roll_trim_rad (this : UInt64) : PMem.M Binary32 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl.get_roll_trim_rad.pure' this)

/-- C++ `AC_AttitudeControl::update_attitude_target : void ()`, `AC_AttitudeControl.cpp:979-986`. -/
def AC_AttitudeControl.update_attitude_target.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  QuaternionT'float.QuaternionT (fp + 0)
  let t'1 ← PMem.ldF32 (this + 112)
  Vector3'float.operator_ (this + 156) (fp + 32) t'1
  let t'2 := (fp + 32)
  Vector3'float.Vector3'3 (fp + 16) t'2
  QuaternionT'float.from_axis_angle (fp + 0) (fp + 16)
  let t'3 ← QuaternionT'float.operator__ (this + 140) (fp + 0)
  discard <| pure (t'3)
  QuaternionT'float.normalize (this + 140)
  return ()

def AC_AttitudeControl.update_attitude_target (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 44
  let r ← AC_AttitudeControl.update_attitude_target.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::body_to_euler_limit : Vector3f (const Quaternion &, const Vector3f &)`, `AC_AttitudeControl.cpp:1229-1248`. -/
def AC_AttitudeControl.body_to_euler_limit.body (fp : UInt64) (this : UInt64) (sret : UInt64) (att : UInt64) (body_limit : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 body_limit
  let t'2 ← is_positive'float t'1
  let mut sc'5 := !t'2
  if !sc'5 then
    let t'3 ← PMem.ldF32 (body_limit + 4)
    let t'4 ← is_positive'float t'3
    sc'5 := !t'4
  let mut sc'8 := sc'5
  if !sc'8 then
    let t'6 ← PMem.ldF32 (body_limit + 8)
    let t'7 ← is_positive'float t'6
    sc'8 := !t'7
  if sc'8 then
    Vector3'float.Vector3'4 (fp + 0) body_limit
    Vector3'float.Vector3'3 sret (fp + 0)
    return ()
  let t'9 ← QuaternionT'float.get_euler_roll att
  let mut phi : Binary32 := t'9
  let t'10 ← QuaternionT'float.get_euler_pitch att
  let mut theta : Binary32 := t'10
  let t'11 ← constrain_value_line'float (Binary32.abs (Musl.sinf.sinf phi)) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((1238 : Int32)))
  let mut sin_phi : Binary32 := t'11
  let t'12 ← constrain_value_line'float (Binary32.abs (Musl.cosf.cosf phi)) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((1239 : Int32)))
  let mut cos_phi : Binary32 := t'12
  let t'13 ← constrain_value_line'float (Binary32.abs (Musl.sinf.sinf theta)) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((1240 : Int32)))
  let mut sin_theta : Binary32 := t'13
  let t'14 ← constrain_value_line'float (Binary32.abs (Musl.cosf.cosf theta)) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((1241 : Int32)))
  let mut cos_theta : Binary32 := t'14
  let t'15 ← PMem.ldF32 body_limit
  let t'16 ← PMem.ldF32 (body_limit + 4)
  PMem.stF32 (fp + 28) (t'16 / cos_phi)
  let t'17 ← PMem.ldF32 (body_limit + 8)
  PMem.stF32 (fp + 32) (t'17 / sin_phi)
  let t'18 ← MIN'float_float (fp + 28) (fp + 32)
  let t'19 ← PMem.ldF32 t'18
  let t'20 ← PMem.ldF32 body_limit
  PMem.stF32 (fp + 36) (t'20 / sin_theta)
  let t'21 ← PMem.ldF32 (body_limit + 4)
  PMem.stF32 (fp + 40) (t'21 / (sin_phi * cos_theta))
  let t'22 ← MIN'float_float (fp + 36) (fp + 40)
  let t'23 ← PMem.ldF32 (body_limit + 8)
  PMem.stF32 (fp + 44) (t'23 / (cos_phi * cos_theta))
  let t'24 ← MIN'float_float t'22 (fp + 44)
  let t'25 ← PMem.ldF32 t'24
  Vector3'float.Vector3 (fp + 16) t'15 t'19 t'25
  Vector3'float.Vector3'3 sret (fp + 16)
  return ()

def AC_AttitudeControl.body_to_euler_limit (this : UInt64) (sret : UInt64) (att : UInt64) (body_limit : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 48
  let r ← AC_AttitudeControl.body_to_euler_limit.body fp this sret att body_limit
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::get_accel_yaw_max_radss : float () const`, `AC_AttitudeControl.h:109-?`. -/
def AC_AttitudeControl.get_accel_yaw_max_radss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 32)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← radians t'2
  return t'3

/-- C++ `AC_AttitudeControl::body_to_euler_derivative : bool (const Quaternion &, const Vector3f &, Vector3f &)`, `AC_AttitudeControl.cpp:1323-1342`. -/
def AC_AttitudeControl.body_to_euler_derivative (this : UInt64) (att : UInt64) (body_derivative_rads : UInt64) (euler_derivative_rads : UInt64) : PMem.M Bool := do
  let t'1 ← QuaternionT'float.get_euler_pitch att
  let mut theta : Binary32 := t'1
  let t'2 ← QuaternionT'float.get_euler_roll att
  let mut phi : Binary32 := t'2
  let mut sin_theta : Binary32 := (Musl.sinf.sinf theta)
  let mut cos_theta : Binary32 := (Musl.cosf.cosf theta)
  let mut sin_phi : Binary32 := (Musl.sinf.sinf phi)
  let mut cos_phi : Binary32 := (Musl.cosf.cosf phi)
  let t'3 ← is_zero cos_theta
  if t'3 then
    return false
  let t'4 ← PMem.ldF32 body_derivative_rads
  let t'5 ← PMem.ldF32 (body_derivative_rads + 4)
  let t'6 ← PMem.ldF32 (body_derivative_rads + 8)
  let t'7 := ((t'4 + ((sin_phi * (sin_theta / cos_theta)) * t'5)) + ((cos_phi * (sin_theta / cos_theta)) * t'6))
  PMem.stF32 euler_derivative_rads t'7
  let t'8 ← PMem.ldF32 (body_derivative_rads + 4)
  let t'9 ← PMem.ldF32 (body_derivative_rads + 8)
  let t'10 := ((cos_phi * t'8) - (sin_phi * t'9))
  PMem.stF32 (euler_derivative_rads + 4) t'10
  let t'11 ← PMem.ldF32 (body_derivative_rads + 4)
  let t'12 ← PMem.ldF32 (body_derivative_rads + 8)
  let t'13 := (((sin_phi / cos_theta) * t'11) + ((cos_phi / cos_theta) * t'12))
  PMem.stF32 (euler_derivative_rads + 8) t'13
  return true

/-- C++ `AC_AttitudeControl::thrust_vector_rotation_angles : void (const Quaternion &, const Quaternion &, Quaternion &, Vector3f &, float &, float &) const`, `AC_AttitudeControl.cpp:1056-1104`. -/
def AC_AttitudeControl.thrust_vector_rotation_angles.body (fp : UInt64) (this : UInt64) (attitude_target : UInt64) (attitude_body : UInt64) (thrust_vector_correction : UInt64) (attitude_error_rad : UInt64) (thrust_angle_rad : UInt64) (thrust_error_angle_rad : UInt64) : PMem.M Unit := do
  Vector3'float.Vector3 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (-(Binary32.ofBits 0x3f800000 /- 1 -/))
  QuaternionT'float.operator_'2 attitude_target (fp + 32) (fp + 0)
  let t'1 := (fp + 32)
  Vector3'float.Vector3'3 (fp + 16) t'1
  QuaternionT'float.operator_'2 attitude_body (fp + 64) (fp + 0)
  let t'2 := (fp + 64)
  Vector3'float.Vector3'3 (fp + 48) t'2
  let t'3 ← Vector3'float.operator_'4 (fp + 0) (fp + 48)
  let t'4 ← constrain_value_line'float t'3 (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((1070 : Int32)))
  let t'5 := (Musl.acosf.acosf t'4)
  PMem.stF32 thrust_angle_rad t'5
  Vector3'float.operator_'6 (fp + 48) (fp + 96) (fp + 16)
  let t'6 := (fp + 96)
  Vector3'float.Vector3'3 (fp + 80) t'6
  let t'7 ← Vector3'float.operator_'4 (fp + 48) (fp + 16)
  let t'8 ← constrain_value_line'float t'7 (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((1076 : Int32)))
  let t'9 := (Musl.acosf.acosf t'8)
  PMem.stF32 thrust_error_angle_rad t'9
  let t'10 ← Vector3'float.length (fp + 80)
  let mut thrust_vector_length : Binary32 := t'10
  let t'11 ← is_zero thrust_vector_length
  let mut sc'14 := t'11
  if !sc'14 then
    let t'12 ← PMem.ldF32 thrust_error_angle_rad
    let t'13 ← is_zero t'12
    sc'14 := t'13
  if sc'14 then
    discard <| PMem.memcpy (fp + 80) (fp + 0) 12
    discard <| pure ((fp + 80))
  else
    let t'15 ← Vector3'float.operator__'5 (fp + 80) thrust_vector_length
    discard <| pure (t'15)
  QuaternionT'float.inverse attitude_body (fp + 112)
  let t'16 := (fp + 112)
  QuaternionT'float.operator_'2 t'16 (fp + 128) (fp + 80)
  let t'17 := (fp + 128)
  discard <| PMem.memcpy (fp + 80) t'17 12
  discard <| pure ((fp + 80))
  let t'18 ← PMem.ldF32 thrust_error_angle_rad
  QuaternionT'float.from_axis_angle'2 thrust_vector_correction (fp + 80) t'18
  Vector3'float.Vector3'2 (fp + 144)
  QuaternionT'float.to_axis_angle thrust_vector_correction (fp + 144)
  let t'19 ← PMem.ldF32 (fp + 144)
  PMem.stF32 attitude_error_rad t'19
  let t'20 ← PMem.ldF32 ((fp + 144) + 4)
  PMem.stF32 (attitude_error_rad + 4) t'20
  QuaternionT'float.inverse thrust_vector_correction (fp + 176)
  let t'21 := (fp + 176)
  QuaternionT'float.inverse attitude_body (fp + 192)
  let t'22 := (fp + 192)
  QuaternionT'float.operator_ t'21 (fp + 208) t'22
  let t'23 := (fp + 208)
  QuaternionT'float.operator_ t'23 (fp + 224) attitude_target
  let t'24 := (fp + 224)
  QuaternionT'float.QuaternionT'3 (fp + 160) t'24
  QuaternionT'float.to_axis_angle (fp + 160) (fp + 144)
  let t'25 ← PMem.ldF32 ((fp + 144) + 8)
  PMem.stF32 (attitude_error_rad + 8) t'25
  return ()

def AC_AttitudeControl.thrust_vector_rotation_angles (this : UInt64) (attitude_target : UInt64) (attitude_body : UInt64) (thrust_vector_correction : UInt64) (attitude_error_rad : UInt64) (thrust_angle_rad : UInt64) (thrust_error_angle_rad : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 240
  let r ← AC_AttitudeControl.thrust_vector_rotation_angles.body fp this attitude_target attitude_body thrust_vector_correction attitude_error_rad thrust_angle_rad thrust_error_angle_rad
  PMem.leave fp
  return r

/-- `AC_AttitudeControl_Multi.get_rate_yaw_pid'2` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl_Multi.get_rate_yaw_pid'2.pure' (this : UInt64) : Id UInt64 := do
  return (this + 856)

/-- C++ `AC_AttitudeControl_Multi::get_rate_yaw_pid : const AC_PID &() const`, `AC_AttitudeControl_Multi.h:55-?`. -/
def AC_AttitudeControl_Multi.get_rate_yaw_pid'2 (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl_Multi.get_rate_yaw_pid'2.pure' this)

/-- C++ `AC_AttitudeControl::update_ang_vel_target_from_att_error : Vector3f (const Vector3f &)`, `AC_AttitudeControl.cpp:1345-1374`. -/
def AC_AttitudeControl.update_ang_vel_target_from_att_error.body (fp : UInt64) (this : UInt64) (sret : UInt64) (attitude_error_rot_vec_rad : UInt64) : PMem.M Unit := do
  Vector3'float.Vector3'2 (fp + 0)
  let t'1 ← AC_P.kP (this + 40)
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 t'1
  let t'3 ← PMem.ldF32 t'2
  let t'4 ← PMem.ldF32 (this + 276)
  let mut angleP_roll : Binary32 := (t'3 * t'4)
  let t'5 ← PMem.ldB (this + 248)
  let mut sc'8 := t'5
  if sc'8 then
    let t'6 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'7 ← is_zero t'6
    sc'8 := !t'7
  if sc'8 then
    let t'9 ← PMem.ldF32 attitude_error_rot_vec_rad
    let t'10 ← AC_AttitudeControl.get_accel_roll_max_radss this
    let t'11 ← radians (Binary32.ofBits 0x42200000 /- 40 -/)
    let t'12 ← radians (Binary32.ofBits 0x44340000 /- 720 -/)
    let t'13 ← constrain_value_line'float (t'10 / (Binary32.ofBits 0x40000000 /- 2 -/)) t'11 t'12 (Int32.toUInt32 ((1352 : Int32)))
    let t'14 ← PMem.ldF32 (this + 112)
    let t'15 ← sqrt_controller t'9 angleP_roll t'13 t'14
    PMem.stF32 (fp + 0) t'15
  else
    let t'16 ← PMem.ldF32 attitude_error_rot_vec_rad
    let t'17 := (angleP_roll * t'16)
    PMem.stF32 (fp + 0) t'17
  let t'18 ← AC_P.kP (this + 48)
  let t'19 ← AP_ParamT'float_4.operator_const_float__'1 t'18
  let t'20 ← PMem.ldF32 t'19
  let t'21 ← PMem.ldF32 ((this + 276) + 4)
  let mut angleP_pitch : Binary32 := (t'20 * t'21)
  let t'22 ← PMem.ldB (this + 248)
  let mut sc'25 := t'22
  if sc'25 then
    let t'23 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'24 ← is_zero t'23
    sc'25 := !t'24
  if sc'25 then
    let t'26 ← PMem.ldF32 (attitude_error_rot_vec_rad + 4)
    let t'27 ← AC_AttitudeControl.get_accel_pitch_max_radss this
    let t'28 ← radians (Binary32.ofBits 0x42200000 /- 40 -/)
    let t'29 ← radians (Binary32.ofBits 0x44340000 /- 720 -/)
    let t'30 ← constrain_value_line'float (t'27 / (Binary32.ofBits 0x40000000 /- 2 -/)) t'28 t'29 (Int32.toUInt32 ((1360 : Int32)))
    let t'31 ← PMem.ldF32 (this + 112)
    let t'32 ← sqrt_controller t'26 angleP_pitch t'30 t'31
    PMem.stF32 ((fp + 0) + 4) t'32
  else
    let t'33 ← PMem.ldF32 (attitude_error_rot_vec_rad + 4)
    let t'34 := (angleP_pitch * t'33)
    PMem.stF32 ((fp + 0) + 4) t'34
  let t'35 ← AC_P.kP (this + 56)
  let t'36 ← AP_ParamT'float_4.operator_const_float__'1 t'35
  let t'37 ← PMem.ldF32 t'36
  let t'38 ← PMem.ldF32 ((this + 276) + 8)
  let mut angleP_yaw : Binary32 := (t'37 * t'38)
  let t'39 ← PMem.ldB (this + 248)
  let mut sc'42 := t'39
  if sc'42 then
    let t'40 ← AC_AttitudeControl.get_accel_yaw_max_radss this
    let t'41 ← is_zero t'40
    sc'42 := !t'41
  if sc'42 then
    let t'43 ← PMem.ldF32 (attitude_error_rot_vec_rad + 8)
    let t'44 ← AC_AttitudeControl.get_accel_yaw_max_radss this
    let t'45 ← radians (Binary32.ofBits 0x41200000 /- 10 -/)
    let t'46 ← radians (Binary32.ofBits 0x42f00000 /- 120 -/)
    let t'47 ← constrain_value_line'float (t'44 / (Binary32.ofBits 0x40000000 /- 2 -/)) t'45 t'46 (Int32.toUInt32 ((1368 : Int32)))
    let t'48 ← PMem.ldF32 (this + 112)
    let t'49 ← sqrt_controller t'43 angleP_yaw t'47 t'48
    PMem.stF32 ((fp + 0) + 8) t'49
  else
    let t'50 ← PMem.ldF32 (attitude_error_rot_vec_rad + 8)
    let t'51 := (angleP_yaw * t'50)
    PMem.stF32 ((fp + 0) + 8) t'51
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def AC_AttitudeControl.update_ang_vel_target_from_att_error (this : UInt64) (sret : UInt64) (attitude_error_rot_vec_rad : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_AttitudeControl.update_ang_vel_target_from_att_error.body fp this sret attitude_error_rot_vec_rad
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::get_latest_gyro : const Vector3f () const`, `AC_AttitudeControl.cpp:233-243`. -/
def AC_AttitudeControl.get_latest_gyro (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  Vector3'float.Vector3'4 sret (this + 88)
  return ()

/-- C++ `AC_PosControl::D_handle_ekf_reset : void ()`, `AC_PosControl.cpp:1735-1764`. -/
def AC_PosControl.D_handle_ekf_reset (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← VehicleBridge.AP_AHRS_View.get_position_D_reset_count'0 t'1
  let mut reset_count : UInt16 := t'2
  let t'3 ← PMem.ldU16 (this + 970)
  if ((UInt32.toInt32 (UInt16.toUInt32 (reset_count))) != (UInt32.toInt32 (UInt16.toUInt32 (t'3)))) then
    let t'4 ← AC_P_1D.get_error (this + 60)
    let t'5 ← PMem.ldF64 ((this + 752) + 16)
    let t'6 ← PMem.ldF64 ((this + 704) + 16)
    let mut delta_pos_estimate_d_m : Binary64 := ((Binary32.toBinary64 (t'4)) - (t'5 - t'6))
    let t'7 := ((this + 752) + 16)
    let t'8 ← PMem.ldF64 t'7
    let t'9 := (t'8 + delta_pos_estimate_d_m)
    PMem.stF64 t'7 t'9
    let t'10 ← AC_PID_Basic.get_error (this + 264)
    let t'11 ← PMem.ldF32 ((this + 800) + 8)
    let t'12 ← PMem.ldF32 ((this + 776) + 8)
    let mut delta_vel_estimate_d_ms : Binary32 := (t'10 - (t'11 - t'12))
    let t'13 := ((this + 800) + 8)
    let t'14 ← PMem.ldF32 t'13
    let t'15 := (t'14 + delta_vel_estimate_d_ms)
    PMem.stF32 t'13 t'15
    let t'16 ← PMem.ldU8 (this + 972)
    let sw'17 := t'16
    if sw'17 == (0 : UInt8) then
      let t'18 := ((this + 728) + 16)
      let t'19 ← PMem.ldF64 t'18
      let t'20 := (t'19 + delta_pos_estimate_d_m)
      PMem.stF64 t'18 t'20
      let t'21 := ((this + 788) + 8)
      let t'22 ← PMem.ldF32 t'21
      let t'23 := (t'22 + delta_vel_estimate_d_ms)
      PMem.stF32 t'21 t'23
    else if sw'17 == (1 : UInt8) then
      let t'24 := ((this + 888) + 16)
      let t'25 ← PMem.ldF64 t'24
      let t'26 := (t'25 + delta_pos_estimate_d_m)
      PMem.stF64 t'24 t'26
      let t'27 := ((this + 924) + 8)
      let t'28 ← PMem.ldF32 t'27
      let t'29 := (t'28 + delta_vel_estimate_d_ms)
      PMem.stF32 t'27 t'29
    else
      pure ()
    PMem.stU16 (this + 970) reset_count
  return ()

/-- C++ `AC_PosControl::has_good_timing : bool () const`, `AC_PosControl.cpp:1797-1807`. -/
def AC_PosControl.has_good_timing (this : UInt64) : PMem.M Bool := do
  let t'1 ← VehicleBridge.sitl'0
  let mut sitl : UInt64 := t'1
  if (sitl != 0) then
    let t'2 ← PMem.ldB (sitl + 216)
    return t'2
  return true

/-- C++ `AC_PosControl::D_update_offsets : void ()`, `AC_PosControl.cpp:1039-1066`. -/
def AC_PosControl.D_update_offsets.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldU32 (this + 964)
  if (decide ((now_ms - t'1) > (Int32.toUInt32 ((3000 : Int32))))) then
    let t'2 := (Binary64.ofBits 0x0000000000000000 /- 0 -/)
    PMem.stF64 ((this + 864) + 16) t'2
    let t'3 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 ((this + 912) + 8) t'3
    let t'4 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 ((this + 936) + 8) t'4
  let t'5 ← PMem.ldF64 ((this + 888) + 16)
  PMem.stF64 (fp + 0) t'5
  let t'6 ← PMem.ldF32 ((this + 948) + 8)
  let t'7 ← PMem.ldF32 (this + 624)
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'8 ← MIN'float_float ((this + 836) + 8) (fp + 8)
  let t'9 ← PMem.ldF32 t'8
  let t'10 ← AC_P_1D.get_error (this + 60)
  let t'11 ← AC_PID_Basic.get_error (this + 264)
  update_pos_vel_accel (fp + 0) ((this + 924) + 8) t'6 t'7 t'9 t'10 t'11
  let t'12 ← PMem.ldF64 (fp + 0)
  PMem.stF64 ((this + 888) + 16) t'12
  let t'13 ← PMem.ldF64 ((this + 864) + 16)
  let t'14 ← PMem.ldF32 ((this + 912) + 8)
  let t'15 ← PMem.ldF32 ((this + 936) + 8)
  let t'16 ← PMem.ldF64 ((this + 888) + 16)
  let t'17 ← PMem.ldF32 ((this + 924) + 8)
  let t'18 ← AC_PosControl.get_max_speed_up_ms this
  let t'19 ← AC_PosControl.get_max_speed_down_ms this
  let t'20 ← AC_PosControl.D_get_max_accel_mss this
  let t'21 ← AC_PosControl.D_get_max_accel_mss this
  let t'22 ← PMem.ldF32 (this + 660)
  let t'23 ← PMem.ldF32 (this + 624)
  shape_pos_vel_accel t'13 t'14 t'15 t'16 t'17 ((this + 948) + 8) (-t'18) t'19 (-t'20) t'21 t'22 t'23 false
  let t'24 ← PMem.ldF64 ((this + 864) + 16)
  PMem.stF64 (fp + 0) t'24
  let t'25 ← PMem.ldF32 ((this + 936) + 8)
  let t'26 ← PMem.ldF32 (this + 624)
  update_pos_vel_accel (fp + 0) ((this + 912) + 8) t'25 t'26 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  let t'27 ← PMem.ldF64 (fp + 0)
  PMem.stF64 ((this + 864) + 16) t'27
  return ()

def AC_PosControl.D_update_offsets (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_PosControl.D_update_offsets.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::update_terrain : void ()`, `AC_PosControl.cpp:1596-1612`. -/
def AC_PosControl.update_terrain.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 852)
  PMem.stF64 (fp + 0) (Binary32.toBinary64 (t'1))
  let t'2 ← PMem.ldF32 (this + 860)
  let t'3 ← PMem.ldF32 (this + 624)
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'4 ← MIN'float_float ((this + 836) + 8) (fp + 8)
  let t'5 ← PMem.ldF32 t'4
  let t'6 ← AC_P_1D.get_error (this + 60)
  let t'7 ← AC_PID_Basic.get_error (this + 264)
  update_pos_vel_accel (fp + 0) (this + 856) t'2 t'3 t'5 t'6 t'7
  let t'8 ← PMem.ldF64 (fp + 0)
  let t'9 := Binary64.toBinary32 (t'8)
  PMem.stF32 (this + 852) t'9
  let t'10 ← PMem.ldF32 (this + 848)
  let t'11 ← PMem.ldF32 (this + 852)
  let t'12 ← PMem.ldF32 (this + 856)
  let t'13 ← AC_PosControl.get_max_speed_up_ms this
  let t'14 ← AC_PosControl.get_max_speed_down_ms this
  let t'15 ← AC_PosControl.D_get_max_accel_mss this
  let t'16 ← AC_PosControl.D_get_max_accel_mss this
  let t'17 ← PMem.ldF32 (this + 660)
  let t'18 ← PMem.ldF32 (this + 624)
  shape_pos_vel_accel (Binary32.toBinary64 (t'10)) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary32.toBinary64 (t'11)) t'12 (this + 860) (-t'13) t'14 (-t'15) t'16 t'17 t'18 false
  return ()

def AC_PosControl.update_terrain (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_PosControl.update_terrain.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::NE_handle_ekf_reset : void ()`, `AC_PosControl.cpp:1696-1726`. -/
def AC_PosControl.NE_handle_ekf_reset.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 this
  let t'2 ← VehicleBridge.AP_AHRS_View.get_position_NE_reset_count'0 t'1
  let mut reset_count : UInt16 := t'2
  let t'3 ← PMem.ldU16 (this + 968)
  if ((UInt32.toInt32 (UInt16.toUInt32 (reset_count))) != (UInt32.toInt32 (UInt16.toUInt32 (t'3)))) then
    let t'4 ← AC_P_2D.get_error (this + 36)
    Vector2'float.todouble t'4 (fp + 16)
    let t'5 := (fp + 16)
    let t'6 ← Vector3'double.xy (this + 752)
    let t'7 ← Vector3'double.xy (this + 704)
    Vector2'double.operator_ t'6 (fp + 32) t'7
    let t'8 := (fp + 32)
    Vector2'double.operator_ t'5 (fp + 48) t'8
    let t'9 := (fp + 48)
    Vector2'double.Vector2 (fp + 0) t'9
    let t'10 ← Vector3'double.xy (this + 752)
    let t'11 ← Vector2'double.operator__'2 t'10 (fp + 0)
    discard <| pure (t'11)
    let t'12 ← AC_PID_2D.get_error (this + 84)
    let t'13 ← Vector3'float.xy (this + 800)
    let t'14 ← Vector3'float.xy (this + 776)
    Vector2'float.operator_ t'13 (fp + 72) t'14
    let t'15 := (fp + 72)
    Vector2'float.operator_ t'12 (fp + 80) t'15
    let t'16 := (fp + 80)
    Vector2'float.Vector2'3 (fp + 64) t'16
    let t'17 ← Vector3'float.xy (this + 800)
    let t'18 ← Vector2'float.operator__ t'17 (fp + 64)
    discard <| pure (t'18)
    let t'19 ← PMem.ldU8 (this + 972)
    let sw'20 := t'19
    if sw'20 == (0 : UInt8) then
      let t'21 ← Vector3'double.xy (this + 728)
      let t'22 ← Vector2'double.operator__'2 t'21 (fp + 0)
      discard <| pure (t'22)
      let t'23 ← Vector3'float.xy (this + 788)
      let t'24 ← Vector2'float.operator__ t'23 (fp + 64)
      discard <| pure (t'24)
    else if sw'20 == (1 : UInt8) then
      let t'25 ← Vector3'double.xy (this + 888)
      let t'26 ← Vector2'double.operator__'2 t'25 (fp + 0)
      discard <| pure (t'26)
      let t'27 ← Vector3'float.xy (this + 924)
      let t'28 ← Vector2'float.operator__ t'27 (fp + 64)
      discard <| pure (t'28)
    else
      pure ()
    PMem.stU16 (this + 968) reset_count
  return ()

def AC_PosControl.NE_handle_ekf_reset (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 88
  let r ← AC_PosControl.NE_handle_ekf_reset.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::NE_update_offsets : void ()`, `AC_PosControl.cpp:644-663`. -/
def AC_PosControl.NE_update_offsets.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let t'1 ← PMem.ldU32 (this + 960)
  if (decide ((now_ms - t'1) > (Int32.toUInt32 ((3000 : Int32))))) then
    let t'2 ← Vector3'double.xy (this + 864)
    Vector2'double.zero t'2
    let t'3 ← Vector3'float.xy (this + 912)
    Vector2'float.zero t'3
    let t'4 ← Vector3'float.xy (this + 936)
    Vector2'float.zero t'4
  let t'5 ← Vector3'double.xy (this + 864)
  let t'6 ← Vector3'float.xy (this + 912)
  let t'7 ← Vector3'float.xy (this + 936)
  let t'8 ← PMem.ldF32 (this + 624)
  Vector2'float.Vector2 (fp + 0)
  Vector2'float.Vector2 (fp + 8)
  Vector2'float.Vector2 (fp + 16)
  update_pos_vel_accel_xy t'5 t'6 t'7 t'8 (fp + 0) (fp + 8) (fp + 16)
  let t'9 ← Vector3'double.xy (this + 888)
  let t'10 ← Vector3'float.xy (this + 924)
  let t'11 ← Vector3'float.xy (this + 948)
  let t'12 ← PMem.ldF32 (this + 624)
  let t'13 ← Vector3'float.xy (this + 836)
  let t'14 ← AC_P_2D.get_error (this + 36)
  let t'15 ← AC_PID_2D.get_error (this + 84)
  update_pos_vel_accel_xy t'9 t'10 t'11 t'12 t'13 t'14 t'15
  let t'16 ← Vector3'double.xy (this + 864)
  let t'17 ← Vector3'float.xy (this + 912)
  let t'18 ← Vector3'float.xy (this + 936)
  let t'19 ← Vector3'double.xy (this + 888)
  let t'20 ← Vector3'float.xy (this + 924)
  let t'21 ← Vector3'float.xy (this + 948)
  let t'22 ← PMem.ldF32 (this + 636)
  let t'23 ← PMem.ldF32 (this + 648)
  let t'24 ← PMem.ldF32 (this + 656)
  let t'25 ← PMem.ldF32 (this + 624)
  shape_pos_vel_accel_xy t'16 t'17 t'18 t'19 t'20 t'21 t'22 t'23 t'24 t'25 false
  return ()

def AC_PosControl.NE_update_offsets (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AC_PosControl.NE_update_offsets.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::accel_NE_mss_to_lean_angles_rad : void (float, float, float &, float &) const`, `AC_PosControl.cpp:1615-1625`. -/
def AC_PosControl.accel_NE_mss_to_lean_angles_rad (this : UInt64) (accel_n_mss : Binary32) (accel_e_mss : Binary32) (roll_target_rad : UInt64) (pitch_target_rad : UInt64) : PMem.M Unit := do
  let mut accel_n_mss := accel_n_mss
  let mut accel_e_mss := accel_e_mss
  let t'1 ← PMem.ldU64 this
  let t'2 ← VehicleBridge.AP_AHRS_View.cos_yaw'0 t'1
  let t'3 ← PMem.ldU64 this
  let t'4 ← VehicleBridge.AP_AHRS_View.sin_yaw'0 t'3
  let mut accel_forward_mss : Binary32 := ((accel_n_mss * t'2) + (accel_e_mss * t'4))
  let t'5 ← PMem.ldU64 this
  let t'6 ← VehicleBridge.AP_AHRS_View.sin_yaw'0 t'5
  let t'7 ← PMem.ldU64 this
  let t'8 ← VehicleBridge.AP_AHRS_View.cos_yaw'0 t'7
  let mut accel_right_mss : Binary32 := (((-accel_n_mss) * t'6) + (accel_e_mss * t'8))
  let t'9 ← accel_mss_to_angle_rad (-accel_forward_mss)
  PMem.stF32 pitch_target_rad t'9
  let t'10 ← PMem.ldF32 pitch_target_rad
  let mut cos_pitch_target : Binary32 := (Musl.cosf.cosf t'10)
  let t'11 ← accel_mss_to_angle_rad (accel_right_mss * cos_pitch_target)
  PMem.stF32 roll_target_rad t'11
  return ()

/-- C++ `AC_PosControl::calculate_yaw_and_rate_yaw : void ()`, `AC_PosControl.cpp:1641-1670`. -/
def AC_PosControl.calculate_yaw_and_rate_yaw.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut turn_rate_rads : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← Vector3'float.xy (this + 788)
  let t'2 ← Vector2'float.length t'1
  let mut vel_desired_length_ne_ms : Binary32 := t'2
  let t'3 ← is_positive'float vel_desired_length_ne_ms
  if t'3 then
    let t'4 ← PMem.ldF32 (this + 812)
    let t'5 ← PMem.ldF32 (this + 788)
    let t'6 ← PMem.ldF32 ((this + 812) + 4)
    let t'7 ← PMem.ldF32 ((this + 788) + 4)
    let mut accel_forward_mss : Binary32 := (((t'4 * t'5) + (t'6 * t'7)) / vel_desired_length_ne_ms)
    let t'8 ← Vector3'float.xy (this + 812)
    let t'9 ← Vector3'float.xy (this + 788)
    Vector2'float.operator_'2 t'9 (fp + 8) accel_forward_mss
    let t'10 := (fp + 8)
    Vector2'float.operator_'5 t'10 (fp + 16) vel_desired_length_ne_ms
    let t'11 := (fp + 16)
    Vector2'float.operator_ t'8 (fp + 24) t'11
    let t'12 := (fp + 24)
    Vector2'float.Vector2'3 (fp + 0) t'12
    let t'13 ← Vector2'float.length (fp + 0)
    let mut accel_turn_length_ne_mss : Binary32 := t'13
    let t'14 := (accel_turn_length_ne_mss / vel_desired_length_ne_ms)
    turn_rate_rads := t'14
    let t'15 ← PMem.ldF32 ((fp + 0) + 4)
    let t'16 ← PMem.ldF32 (this + 788)
    let t'17 ← PMem.ldF32 (fp + 0)
    let t'18 ← PMem.ldF32 ((this + 788) + 4)
    if (decide (((t'15 * t'16) - (t'17 * t'18)) < (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))))) then
      let t'19 := -turn_rate_rads
      turn_rate_rads := t'19
  let t'20 ← PMem.ldF32 (this + 636)
  if (decide (vel_desired_length_ne_ms > (t'20 * (Binary32.ofBits 0x3d4ccccd /- 500000007/10000000000 -/)))) then
    let t'21 ← Vector3'float.xy (this + 788)
    let t'22 ← Vector2'float.angle t'21
    PMem.stF32 (this + 696) t'22
    PMem.stF32 (this + 700) turn_rate_rads
    return ()
  let t'23 ← PMem.ldU64 (this + 16)
  let t'24 ← AC_AttitudeControl.get_att_target_euler_rad t'23
  let t'25 ← PMem.ldF32 (t'24 + 8)
  PMem.stF32 (this + 696) t'25
  let t'26 := Int32.toBinary32 ((0 : Int32))
  PMem.stF32 (this + 700) t'26
  return ()

def AC_PosControl.calculate_yaw_and_rate_yaw (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← AC_PosControl.calculate_yaw_and_rate_yaw.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::get_thrust_vector : Vector3f () const`, `AC_PosControl.cpp:1374-1379`. -/
def AC_PosControl.get_thrust_vector.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← AC_PosControl.get_accel_target_NED_mss this
  Vector3'float.Vector3'4 (fp + 0) t'1
  let t'2 := -(Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/)
  PMem.stF32 ((fp + 0) + 8) t'2
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def AC_PosControl.get_thrust_vector (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_PosControl.get_thrust_vector.body fp this sret
  PMem.leave fp
  return r

/-- C++ `AC_AttitudeControl::attitude_from_thrust_vector : Quaternion (Vector3f, float) const`, `AC_AttitudeControl.cpp:947-976`. -/
def AC_AttitudeControl.attitude_from_thrust_vector.body (fp : UInt64) (this : UInt64) (sret : UInt64) (thrust_vector : UInt64) (heading_angle_rad : Binary32) : PMem.M Unit := do
  let mut heading_angle_rad := heading_angle_rad
  Vector3'float.Vector3 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (-(Binary32.ofBits 0x3f800000 /- 1 -/))
  let t'1 ← Vector3'float.length_squared thrust_vector
  let t'2 ← is_zero t'1
  if t'2 then
    discard <| PMem.memcpy thrust_vector (fp + 0) 12
    discard <| pure (thrust_vector)
  else
    Vector3'float.normalize thrust_vector
  Vector3'float.operator_'6 (fp + 0) (fp + 32) thrust_vector
  let t'3 := (fp + 32)
  Vector3'float.Vector3'3 (fp + 16) t'3
  let t'4 ← Vector3'float.operator_'4 (fp + 0) thrust_vector
  let t'5 ← constrain_value_line'float t'4 (-(Binary32.ofBits 0x3f800000 /- 1 -/)) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((961 : Int32)))
  let mut thrust_vector_angle : Binary32 := (Musl.acosf.acosf t'5)
  let t'6 ← Vector3'float.length (fp + 16)
  let mut thrust_vector_length : Binary32 := t'6
  let t'7 ← is_zero thrust_vector_length
  let mut sc'9 := t'7
  if !sc'9 then
    let t'8 ← is_zero thrust_vector_angle
    sc'9 := t'8
  if sc'9 then
    discard <| PMem.memcpy (fp + 16) (fp + 0) 12
    discard <| pure ((fp + 16))
  else
    let t'10 ← Vector3'float.operator__'5 (fp + 16) thrust_vector_length
    discard <| pure (t'10)
  QuaternionT'float.QuaternionT (fp + 48)
  QuaternionT'float.from_axis_angle'2 (fp + 48) (fp + 16) thrust_vector_angle
  QuaternionT'float.QuaternionT (fp + 64)
  Vector3'float.Vector3 (fp + 80) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/)
  QuaternionT'float.from_axis_angle'2 (fp + 64) (fp + 80) heading_angle_rad
  QuaternionT'float.operator_ (fp + 48) (fp + 96) (fp + 64)
  let t'11 := (fp + 96)
  QuaternionT'float.QuaternionT'3 sret t'11
  return ()

def AC_AttitudeControl.attitude_from_thrust_vector (this : UInt64) (sret : UInt64) (thrust_vector : UInt64) (heading_angle_rad : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 112
  let r ← AC_AttitudeControl.attitude_from_thrust_vector.body fp this sret thrust_vector heading_angle_rad
  PMem.leave fp
  return r

/-- `AC_AttitudeControl.HeadingCommand.HeadingCommand` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl.HeadingCommand.HeadingCommand.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AC_AttitudeControl::HeadingCommand::HeadingCommand : void () noexcept`, `AC_AttitudeControl.h:716-?`. -/
def AC_AttitudeControl.HeadingCommand.HeadingCommand (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl.HeadingCommand.HeadingCommand.pure' this)

/-- C++ `AC_PosControl::get_yaw_rad : float () const`, `AP_Common.h:514-?`. -/
def AC_PosControl.get_yaw_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 696)
  return t'1

/-- C++ `AC_PosControl::get_yaw_rate_rads : float () const`, `AP_Common.h:517-?`. -/
def AC_PosControl.get_yaw_rate_rads (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 700)
  return t'1

/-- C++ `AC_AttitudeControl::HeadingCommand::HeadingCommand : void (HeadingCommand &&) noexcept`, `AC_AttitudeControl.h:?-?`. -/
def AC_AttitudeControl.HeadingCommand.HeadingCommand'2 (this : UInt64) (arg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 arg
  PMem.stF32 (this + 0) t'1
  let t'2 ← PMem.ldF32 (arg + 4)
  PMem.stF32 (this + 4) t'2
  let t'3 ← PMem.ldI32 (arg + 8)
  PMem.stI32 (this + 8) t'3
  return ()

/-- C++ `AC_PosControl::get_dt_s : float () const`, `AP_Common.h:53-?`. -/
def AC_PosControl.get_dt_s (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 624)
  return t'1

/-- C++ `AC_PosControl::terrain_scaler_D_m : float (float, float) const`, `AC_PosControl.cpp:433-440`. -/
def AC_PosControl.terrain_scaler_D_m (this : UInt64) (pos_terrain_d_m : Binary32) (terrain_margin_m : Binary32) : PMem.M Binary32 := do
  let mut pos_terrain_d_m := pos_terrain_d_m
  let mut terrain_margin_m := terrain_margin_m
  let t'1 ← is_zero terrain_margin_m
  if t'1 then
    return Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'2 ← PMem.ldF64 ((this + 704) + 16)
  let t'3 ← PMem.ldF64 ((this + 752) + 16)
  let t'4 ← PMem.ldF32 (this + 852)
  let mut pos_offset_error_d_m : Binary32 := Binary64.toBinary32 ((t'2 - (t'3 + (Binary32.toBinary64 ((pos_terrain_d_m - t'4))))))
  let t'5 ← constrain_value_line'float ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - (((Binary32.abs pos_offset_error_d_m) - ((Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) * terrain_margin_m)) / ((Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) * terrain_margin_m))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((439 : Int32)))
  return t'5

/-- C++ `AC_PosControl::set_pos_terrain_target_D_m : void (float)`, `AP_Common.h:438-?`. -/
def AC_PosControl.set_pos_terrain_target_D_m (this : UInt64) (pos_terrain_target_d_m : Binary32) : PMem.M Unit := do
  let mut pos_terrain_target_d_m := pos_terrain_target_d_m
  PMem.stF32 (this + 848) pos_terrain_target_d_m
  return ()

/-- C++ `AC_PosControl::get_pos_error_NED_m : const Vector3f () const`, `AP_Common.h:361-?`. -/
def AC_PosControl.get_pos_error_NED_m.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← AC_P_2D.get_error (this + 36)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← AC_P_2D.get_error (this + 36)
  let t'4 ← PMem.ldF32 (t'3 + 4)
  let t'5 ← AC_P_1D.get_error (this + 60)
  Vector3'float.Vector3 (fp + 0) t'2 t'4 t'5
  Vector3'float.Vector3'3 sret (fp + 0)
  return ()

def AC_PosControl.get_pos_error_NED_m (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_PosControl.get_pos_error_NED_m.body fp this sret
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::get_shaping_jerk_NE_msss : float () const`, `AP_Common.h:62-?`. -/
def AC_PosControl.get_shaping_jerk_NE_msss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 28)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_PosControl::set_pos_vel_accel_NED_m : void (const Vector3p &, const Vector3f &, const Vector3f &)`, `AC_PosControl.cpp:1183-1188`. -/
def AC_PosControl.set_pos_vel_accel_NED_m (this : UInt64) (pos_ned_m : UInt64) (vel_ned_ms : UInt64) (accel_ned_mss : UInt64) : PMem.M Unit := do
  discard <| PMem.memcpy (this + 728) pos_ned_m 24
  discard <| pure ((this + 728))
  discard <| PMem.memcpy (this + 788) vel_ned_ms 12
  discard <| pure ((this + 788))
  discard <| PMem.memcpy (this + 812) accel_ned_mss 12
  discard <| pure ((this + 812))
  return ()

/-- C++ `AC_PosControl::get_vel_desired_U_ms : float () const`, `AP_Common.h:400-?`. -/
def AC_PosControl.get_vel_desired_U_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 ((this + 788) + 8)
  return -t'1

/-- C++ `AC_PosControl::input_vel_accel_NE_m : void (Vector2f &, const Vector2f &, bool)`, `AC_PosControl.cpp:609-617`. -/
def AC_PosControl.input_vel_accel_NE_m.body (fp : UInt64) (this : UInt64) (vel_ne_ms : UInt64) (accel_ne_mss : UInt64) (limit_output : Bool) : PMem.M Unit := do
  let mut limit_output := limit_output
  let t'1 ← Vector3'double.xy (this + 728)
  let t'2 ← Vector3'float.xy (this + 788)
  let t'3 ← Vector3'float.xy (this + 812)
  let t'4 ← PMem.ldF32 (this + 624)
  let t'5 ← Vector3'float.xy (this + 836)
  let t'6 ← AC_P_2D.get_error (this + 36)
  let t'7 ← AC_PID_2D.get_error (this + 84)
  update_pos_vel_accel_xy t'1 t'2 t'3 t'4 t'5 t'6 t'7
  let t'8 ← Vector3'float.xy (this + 788)
  let t'9 ← Vector3'float.xy (this + 812)
  let t'10 ← PMem.ldF32 (this + 648)
  let t'11 ← PMem.ldF32 (this + 656)
  let t'12 ← PMem.ldF32 (this + 624)
  shape_vel_accel_xy vel_ne_ms accel_ne_mss t'8 t'9 t'10 t'11 t'12 limit_output
  let t'13 ← PMem.ldF32 (this + 624)
  Vector2'float.Vector2 (fp + 0)
  Vector2'float.Vector2 (fp + 8)
  update_vel_accel_xy vel_ne_ms accel_ne_mss t'13 (fp + 0) (fp + 8)
  return ()

def AC_PosControl.input_vel_accel_NE_m (this : UInt64) (vel_ne_ms : UInt64) (accel_ne_mss : UInt64) (limit_output : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← AC_PosControl.input_vel_accel_NE_m.body fp this vel_ne_ms accel_ne_mss limit_output
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::NE_set_externally_limited : void ()`, `AP_Common.h:568-?`. -/
def AC_PosControl.NE_set_externally_limited (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 824)
  PMem.stF32 (this + 836) t'1
  let t'2 ← PMem.ldF32 ((this + 824) + 4)
  PMem.stF32 ((this + 836) + 4) t'2
  return ()

/-- C++ `AC_PosControl::NE_soften_for_landing : void ()`, `AC_PosControl.cpp:528-539`. -/
def AC_PosControl.NE_soften_for_landing.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 624)
  let t'2 ← is_positive'float t'1
  if t'2 then
    let t'3 ← Vector3'double.xy (this + 752)
    let t'4 ← Vector3'double.xy (this + 704)
    let t'5 ← Vector3'double.xy (this + 752)
    Vector2'double.operator_ t'4 (fp + 0) t'5
    let t'6 := (fp + 0)
    let t'7 ← PMem.ldF32 (this + 624)
    let t'8 ← PMem.ldF32 (this + 624)
    Vector2'double.operator_'3 t'6 (fp + 16) (Binary32.toBinary64 ((t'7 / (t'8 + (Binary32.ofBits 0x3e23d70a /- 39999999/250000000 -/)))))
    let t'9 := (fp + 16)
    let t'10 ← Vector2'double.operator__'2 t'3 t'9
    discard <| pure (t'10)
    let t'11 ← Vector3'double.xy (this + 728)
    let t'12 ← Vector3'double.xy (this + 752)
    let t'13 ← Vector3'double.xy (this + 888)
    Vector2'double.operator_ t'12 (fp + 32) t'13
    let t'14 := (fp + 32)
    discard <| PMem.memcpy t'11 t'14 16
    discard <| pure (t'11)
  AC_PosControl.NE_set_externally_limited this
  return ()

def AC_PosControl.NE_soften_for_landing (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 48
  let r ← AC_PosControl.NE_soften_for_landing.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::get_pos_offset_U_m : float () const`, `AP_Common.h:497-?`. -/
def AC_PosControl.get_pos_offset_U_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF64 ((this + 888) + 16)
  return Binary64.toBinary32 ((-t'1))

/-- C++ `AC_PosControl::D_set_alt_target_with_slew_m : void (float)`, `AC_PosControl.cpp:1031-1036`. -/
def AC_PosControl.D_set_alt_target_with_slew_m.body (fp : UInt64) (this : UInt64) (pos_u_m : Binary32) : PMem.M Unit := do
  let mut pos_u_m := pos_u_m
  PMem.stF32 (fp + 0) (-pos_u_m)
  PMem.stF32 (fp + 8) (Int32.toBinary32 ((0 : Int32)))
  AC_PosControl.input_pos_vel_accel_D_m this (fp + 0) (fp + 8) (Int32.toBinary32 ((0 : Int32))) true
  return ()

def AC_PosControl.D_set_alt_target_with_slew_m (this : UInt64) (pos_u_m : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_PosControl.D_set_alt_target_with_slew_m.body fp this pos_u_m
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::input_pos_NED_m : void (const Vector3p &, float, float)`, `AC_PosControl.cpp:386-429`. -/
def AC_PosControl.input_pos_NED_m.body (fp : UInt64) (this : UInt64) (pos_ned_m : UInt64) (pos_terrain_target_d_m : Binary32) (terrain_margin_m : Binary32) : PMem.M Unit := do
  let mut pos_terrain_target_d_m := pos_terrain_target_d_m
  let mut terrain_margin_m := terrain_margin_m
  let t'1 ← AC_PosControl.terrain_scaler_D_m this pos_terrain_target_d_m terrain_margin_m
  let mut offset_d_scalar : Binary32 := t'1
  AC_PosControl.set_pos_terrain_target_D_m this pos_terrain_target_d_m
  let t'2 ← AC_PosControl.calculate_overspeed_gain this
  let mut overspeed_gain : Binary32 := t'2
  let t'3 ← PMem.ldF32 (this + 652)
  let mut accel_max_d_mss : Binary32 := (t'3 * overspeed_gain)
  let t'4 ← PMem.ldF32 (this + 660)
  let mut jerk_max_d_msss : Binary32 := (t'4 * overspeed_gain)
  let t'5 ← Vector3'double.xy (this + 728)
  let t'6 ← Vector3'float.xy (this + 788)
  let t'7 ← Vector3'float.xy (this + 812)
  let t'8 ← PMem.ldF32 (this + 624)
  let t'9 ← Vector3'float.xy (this + 836)
  let t'10 ← AC_P_2D.get_error (this + 36)
  let t'11 ← AC_PID_2D.get_error (this + 84)
  update_pos_vel_accel_xy t'5 t'6 t'7 t'8 t'9 t'10 t'11
  let t'12 ← PMem.ldF32 ((this + 812) + 8)
  let t'13 ← PMem.ldF32 (this + 624)
  let t'14 ← PMem.ldF32 ((this + 836) + 8)
  let t'15 ← AC_P_1D.get_error (this + 60)
  let t'16 ← AC_PID_Basic.get_error (this + 264)
  update_pos_vel_accel ((this + 728) + 16) ((this + 788) + 8) t'12 t'13 t'14 t'15 t'16
  let mut vel_max_ne_ms : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut vel_max_d_ms : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  Vector3'double.operator_ pos_ned_m (fp + 16) (this + 728)
  let t'17 := (fp + 16)
  Vector3'double.tofloat t'17 (fp + 40)
  let t'18 := (fp + 40)
  Vector3'float.Vector3'3 (fp + 0) t'18
  let t'19 ← Vector3'float.length_squared (fp + 0)
  let t'20 ← is_positive'float t'19
  if t'20 then
    Vector3'float.normalize (fp + 0)
    let t'21 ← Vector3'float.xy (fp + 0)
    let t'22 ← Vector2'float.length t'21
    let mut travel_dir_unit_ne_length : Binary32 := t'22
    Vector3'float.Vector3'4 (fp + 56) (fp + 0)
    let t'23 ← PMem.ldF32 (this + 636)
    let t'24 ← PMem.ldF32 (this + 640)
    let t'25 ← PMem.ldF32 (this + 644)
    let t'26 ← kinematic_limit'2 (fp + 56) t'23 t'24 t'25
    let mut vel_max_ms : Binary32 := t'26
    let t'27 := (vel_max_ms * travel_dir_unit_ne_length)
    vel_max_ne_ms := t'27
    let t'28 ← PMem.ldF32 ((fp + 0) + 8)
    let t'29 := (Binary32.abs (vel_max_ms * t'28))
    vel_max_d_ms := t'29
  let t'30 := (vel_max_ne_ms * offset_d_scalar)
  vel_max_ne_ms := t'30
  Vector2'float.Vector2 (fp + 72)
  Vector2'float.Vector2 (fp + 80)
  let t'31 ← Vector3'double.xy pos_ned_m
  let t'32 ← Vector3'double.xy (this + 728)
  let t'33 ← Vector3'float.xy (this + 788)
  let t'34 ← Vector3'float.xy (this + 812)
  let t'35 ← PMem.ldF32 (this + 648)
  let t'36 ← PMem.ldF32 (this + 656)
  let t'37 ← PMem.ldF32 (this + 624)
  shape_pos_vel_accel_xy t'31 (fp + 72) (fp + 80) t'32 t'33 t'34 vel_max_ne_ms t'35 t'36 t'37 false
  let t'38 ← PMem.ldF64 (pos_ned_m + 16)
  let mut pos_d_m : Binary32 := Binary64.toBinary32 (t'38)
  let t'39 ← PMem.ldF64 ((this + 728) + 16)
  let t'40 ← PMem.ldF32 ((this + 788) + 8)
  let t'41 ← constrain_value_line'float accel_max_d_mss (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x401e000000000000 /- 15/2 -/))) (Int32.toUInt32 ((427 : Int32)))
  let t'42 ← PMem.ldF32 (this + 624)
  shape_pos_vel_accel (Binary32.toBinary64 (pos_d_m)) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((0 : Int32))) t'39 t'40 ((this + 812) + 8) (-vel_max_d_ms) vel_max_d_ms (-accel_max_d_mss) t'41 jerk_max_d_msss t'42 false
  return ()

def AC_PosControl.input_pos_NED_m (this : UInt64) (pos_ned_m : UInt64) (pos_terrain_target_d_m : Binary32) (terrain_margin_m : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 88
  let r ← AC_PosControl.input_pos_NED_m.body fp this pos_ned_m pos_terrain_target_d_m terrain_margin_m
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::input_accel_NE_m : void (const Vector2f &)`, `AC_PosControl.cpp:591-595`. -/
def AC_PosControl.input_accel_NE_m (this : UInt64) (accel_ne_mss : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'double.xy (this + 728)
  let t'2 ← Vector3'float.xy (this + 788)
  let t'3 ← Vector3'float.xy (this + 812)
  let t'4 ← PMem.ldF32 (this + 624)
  let t'5 ← Vector3'float.xy (this + 836)
  let t'6 ← AC_P_2D.get_error (this + 36)
  let t'7 ← AC_PID_2D.get_error (this + 84)
  update_pos_vel_accel_xy t'1 t'2 t'3 t'4 t'5 t'6 t'7
  let t'8 ← Vector3'float.xy (this + 812)
  let t'9 ← PMem.ldF32 (this + 656)
  let t'10 ← PMem.ldF32 (this + 624)
  shape_accel_xy accel_ne_mss t'8 t'9 t'10
  return ()

/-- C++ `AC_PosControl::NE_stop_vel_stabilisation : void ()`, `AC_PosControl.cpp:675-686`. -/
def AC_PosControl.NE_stop_vel_stabilisation.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'double.xy (this + 752)
  let t'2 ← Vector3'double.xy (this + 704)
  discard <| PMem.memcpy t'1 t'2 16
  discard <| pure (t'1)
  let t'3 ← Vector3'double.xy (this + 728)
  let t'4 ← Vector3'double.xy (this + 752)
  let t'5 ← Vector3'double.xy (this + 888)
  Vector2'double.operator_ t'4 (fp + 0) t'5
  let t'6 := (fp + 0)
  discard <| PMem.memcpy t'3 t'6 16
  discard <| pure (t'3)
  let t'7 ← Vector3'float.xy (this + 800)
  let t'8 ← Vector3'float.xy (this + 776)
  discard <| PMem.memcpy t'7 t'8 8
  discard <| pure (t'7)
  let t'9 ← Vector3'float.xy (this + 788)
  let t'10 ← Vector3'float.xy (this + 800)
  let t'11 ← Vector3'float.xy (this + 924)
  Vector2'float.operator_ t'10 (fp + 16) t'11
  let t'12 := (fp + 16)
  discard <| PMem.memcpy t'9 t'12 8
  discard <| pure (t'9)
  AC_PID_2D.reset_filter (this + 84)
  AC_PID_2D.reset_I (this + 84)
  return ()

def AC_PosControl.NE_stop_vel_stabilisation (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AC_PosControl.NE_stop_vel_stabilisation.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::NE_stop_pos_stabilisation : void ()`, `AC_PosControl.cpp:667-671`. -/
def AC_PosControl.NE_stop_pos_stabilisation.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'double.xy (this + 752)
  let t'2 ← Vector3'double.xy (this + 704)
  discard <| PMem.memcpy t'1 t'2 16
  discard <| pure (t'1)
  let t'3 ← Vector3'double.xy (this + 728)
  let t'4 ← Vector3'double.xy (this + 752)
  let t'5 ← Vector3'double.xy (this + 888)
  Vector2'double.operator_ t'4 (fp + 0) t'5
  let t'6 := (fp + 0)
  discard <| PMem.memcpy t'3 t'6 16
  discard <| pure (t'3)
  return ()

def AC_PosControl.NE_stop_pos_stabilisation (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← AC_PosControl.NE_stop_pos_stabilisation.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_PosControl::input_accel_D_m : void (float)`, `AC_PosControl.cpp:934-943`. -/
def AC_PosControl.input_accel_D_m (this : UInt64) (accel_d_mss : Binary32) : PMem.M Unit := do
  let mut accel_d_mss := accel_d_mss
  let t'1 ← PMem.ldF32 (this + 660)
  let t'2 ← AC_PosControl.calculate_overspeed_gain this
  let mut jerk_max_d_msss : Binary32 := (t'1 * t'2)
  let t'3 ← PMem.ldF32 ((this + 812) + 8)
  let t'4 ← PMem.ldF32 (this + 624)
  let t'5 ← PMem.ldF32 ((this + 836) + 8)
  let t'6 ← AC_P_1D.get_error (this + 60)
  let t'7 ← AC_PID_Basic.get_error (this + 264)
  update_pos_vel_accel ((this + 728) + 16) ((this + 788) + 8) t'3 t'4 t'5 t'6 t'7
  let t'8 ← PMem.ldF32 (this + 624)
  shape_accel accel_d_mss ((this + 812) + 8) jerk_max_d_msss t'8
  return ()

/-- C++ `AC_PosControl::input_pos_vel_accel_NE_m : void (Vector2p &, Vector2f &, const Vector2f &, bool)`, `AC_PosControl.cpp:633-641`. -/
def AC_PosControl.input_pos_vel_accel_NE_m.body (fp : UInt64) (this : UInt64) (pos_ne_m : UInt64) (vel_ne_ms : UInt64) (accel_ne_mss : UInt64) (limit_output : Bool) : PMem.M Unit := do
  let mut limit_output := limit_output
  let t'1 ← Vector3'double.xy (this + 728)
  let t'2 ← Vector3'float.xy (this + 788)
  let t'3 ← Vector3'float.xy (this + 812)
  let t'4 ← PMem.ldF32 (this + 624)
  let t'5 ← Vector3'float.xy (this + 836)
  let t'6 ← AC_P_2D.get_error (this + 36)
  let t'7 ← AC_PID_2D.get_error (this + 84)
  update_pos_vel_accel_xy t'1 t'2 t'3 t'4 t'5 t'6 t'7
  let t'8 ← Vector3'double.xy (this + 728)
  let t'9 ← Vector3'float.xy (this + 788)
  let t'10 ← Vector3'float.xy (this + 812)
  let t'11 ← PMem.ldF32 (this + 636)
  let t'12 ← PMem.ldF32 (this + 648)
  let t'13 ← PMem.ldF32 (this + 656)
  let t'14 ← PMem.ldF32 (this + 624)
  shape_pos_vel_accel_xy pos_ne_m vel_ne_ms accel_ne_mss t'8 t'9 t'10 t'11 t'12 t'13 t'14 limit_output
  let t'15 ← PMem.ldF32 (this + 624)
  Vector2'float.Vector2 (fp + 0)
  Vector2'float.Vector2 (fp + 8)
  Vector2'float.Vector2 (fp + 16)
  update_pos_vel_accel_xy pos_ne_m vel_ne_ms accel_ne_mss t'15 (fp + 0) (fp + 8) (fp + 16)
  return ()

def AC_PosControl.input_pos_vel_accel_NE_m (this : UInt64) (pos_ne_m : UInt64) (vel_ne_ms : UInt64) (accel_ne_mss : UInt64) (limit_output : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AC_PosControl.input_pos_vel_accel_NE_m.body fp this pos_ne_m vel_ne_ms accel_ne_mss limit_output
  PMem.leave fp
  return r

/-- `AC_PosControl.NE_get_vel_pid` as a pure function of its arguments (it reads and writes no memory). -/
def AC_PosControl.NE_get_vel_pid.pure' (this : UInt64) : Id UInt64 := do
  return (this + 84)

/-- C++ `AC_PosControl::NE_get_vel_pid : AC_PID_2D &()`, `AP_Common.h:558-?`. -/
def AC_PosControl.NE_get_vel_pid (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_PosControl.NE_get_vel_pid.pure' this)

/-- C++ `AC_PosControl::set_pos_vel_accel_NE_m : void (const Vector2p &, const Vector2f &, const Vector2f &)`, `AC_PosControl.cpp:1192-1197`. -/
def AC_PosControl.set_pos_vel_accel_NE_m (this : UInt64) (pos_ne_m : UInt64) (vel_ne_ms : UInt64) (accel_ne_mss : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'double.xy (this + 728)
  discard <| PMem.memcpy t'1 pos_ne_m 16
  discard <| pure (t'1)
  let t'2 ← Vector3'float.xy (this + 788)
  discard <| PMem.memcpy t'2 vel_ne_ms 8
  discard <| pure (t'2)
  let t'3 ← Vector3'float.xy (this + 812)
  discard <| PMem.memcpy t'3 accel_ne_mss 8
  discard <| pure (t'3)
  return ()

/-- C++ `AC_AttitudeControl_Multi::is_throttle_mix_min : bool () const`, `AC_AttitudeControl_Multi.h:76-?`. -/
def AC_AttitudeControl_Multi.is_throttle_mix_min (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldF32 (this + 260)
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1100)
  let t'3 ← PMem.ldF32 t'2
  return (decide (t'1 < ((Binary32.ofBits 0x3fa00000 /- 5/4 -/) * t'3)))

/-- C++ `AC_AttitudeControl::get_att_error_angle_deg : float () const`, `<scratch space>:341-?`. -/
def AC_AttitudeControl.get_att_error_angle_deg (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 236)
  let t'2 ← degrees t'1
  return t'2

/-- C++ `AC_AttitudeControl_Multi::set_throttle_mix_min : void ()`, `AC_AttitudeControl_Multi.h:69-?`. -/
def AC_AttitudeControl_Multi.set_throttle_mix_min (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1100)
  let t'2 ← PMem.ldF32 t'1
  PMem.stF32 (this + 256) t'2
  return ()

/-- C++ `AC_AttitudeControl_Multi::set_throttle_mix_man : void ()`, `AC_AttitudeControl_Multi.h:70-?`. -/
def AC_AttitudeControl_Multi.set_throttle_mix_man (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1096)
  let t'2 ← PMem.ldF32 t'1
  PMem.stF32 (this + 256) t'2
  return ()

/-- C++ `AC_AttitudeControl_Multi::set_throttle_mix_max : void (float)`, `AC_AttitudeControl_Multi.cpp:380-384`. -/
def AC_AttitudeControl_Multi.set_throttle_mix_max (this : UInt64) (ratio : Binary32) : PMem.M Unit := do
  let mut ratio := ratio
  let t'1 ← constrain_value_line'float ratio (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((382 : Int32)))
  ratio := t'1
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1100)
  let t'3 ← PMem.ldF32 t'2
  let t'4 ← AP_ParamT'float_4.operator_const_float__'1 (this + 1104)
  let t'5 ← PMem.ldF32 t'4
  let t'6 := ((((Binary32.ofBits 0x3f800000 /- 1 -/) - ratio) * t'3) + (ratio * t'5))
  PMem.stF32 (this + 256) t'6
  return ()

/-- C++ `AC_PosControl::get_vel_D_control_ratio : float () const`, `AP_Common.h:595-?`. -/
def AC_PosControl.get_vel_D_control_ratio (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 664)
  let t'2 ← constrain_value_line'float t'1 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((595 : Int32)))
  return t'2

/-- `AC_AttitudeControl_Multi.set_notch_sample_rate` as a pure function of its arguments (it reads and writes no memory). -/
def AC_AttitudeControl_Multi.set_notch_sample_rate.pure' (this : UInt64) (sample_rate : Binary32) : Id Unit := do
  let mut sample_rate := sample_rate
  return ()

/-- C++ `AC_AttitudeControl_Multi::set_notch_sample_rate : void (float)`, `AC_AttitudeControl_Multi.cpp:516-523`. -/
def AC_AttitudeControl_Multi.set_notch_sample_rate (this : UInt64) (sample_rate : Binary32) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AC_AttitudeControl_Multi.set_notch_sample_rate.pure' this sample_rate)

/-- C++ `AC_PosControl::set_vibe_comp : void (bool)`, `AP_Common.h:584-?`. -/
def AC_PosControl.set_vibe_comp (this : UInt64) (on_off : Bool) : PMem.M Unit := do
  let mut on_off := on_off
  PMem.stB (this + 973) on_off
  return ()

/-- C++ `AC_PosControl::NED_standby_reset : void ()`, `AC_PosControl.cpp:1489-1502`. -/
def AC_PosControl.NED_standby_reset (this : UInt64) : PMem.M Unit := do
  AC_PID.set_integrator (this + 384) (Binary32.ofBits 0x00000000 /- 0 -/)
  discard <| PMem.memcpy (this + 752) (this + 704) 24
  discard <| pure ((this + 752))
  AC_PID_2D.reset_filter (this + 84)
  AC_PosControl.NE_init_ekf_reset this
  return ()

end Vehicle_lib
