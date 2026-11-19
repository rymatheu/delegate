import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl

/-!
ArduPilot `libraries/AC_WPNav`, part 1 of 2. Sources: `libraries/AC_WPNav/AC_WPNav.cpp`, `libraries/AC_WPNav/AC_Circle.cpp`, `libraries/AC_WPNav/AC_Loiter.cpp`, `libraries/AC_WPNav/AC_WPNav.h`, `libraries/AC_WPNav/AC_Circle.h`, `libraries/AC_WPNav/AC_Loiter.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AC_WPNav::get_default_speed_down_ms : float () const`, `AC_WPNav.h:124-?`. -/
def AC_WPNav.get_default_speed_down_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 48)
  let t'2 ← PMem.ldF32 t'1
  return (Binary32.abs t'2)

/-- C++ `AC_WPNav::get_default_speed_up_ms : float () const`, `AC_WPNav.h:116-?`. -/
def AC_WPNav.get_default_speed_up_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 44)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_WPNav::get_default_speed_NE_ms : float () const`, `AC_WPNav.h:108-?`. -/
def AC_WPNav.get_default_speed_NE_ms (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 40)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_WPNav::get_accel_D_mss : float () const`, `AC_WPNav.h:132-?`. -/
def AC_WPNav.get_accel_D_mss (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 64)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_WPNav::is_active : bool () const`, `AC_WPNav.cpp:751-755`. -/
def AC_WPNav.is_active (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (this + 2396)
  return (decide (((((← PMem.clock) / 1000).toUInt32) - t'1) < (Int32.toUInt32 ((200 : Int32)))))

/-- C++ `AC_WPNav::get_terrain_source : AC_WPNav::TerrainSource () const`, `AC_WPNav.cpp:186-205`. -/
def AC_WPNav.get_terrain_source (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldB (this + 2494)
  let mut sc'4 := t'1
  if sc'4 then
    let t'2 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 2495)
    let t'3 ← PMem.ldI8 t'2
    sc'4 := t'3 != (0 : Int8)
  if sc'4 then
    return (1 : Int32)
  return (0 : Int32)

/-- C++ `AC_WPNav::get_terrain_U_m : bool (float &)`, `AC_WPNav.cpp:784-815`. -/
def AC_WPNav.get_terrain_U_m (this : UInt64) (terrain_u_m : UInt64) : PMem.M Bool := do
  let t'1 ← AC_WPNav.get_terrain_source this
  let sw'2 := t'1
  if sw'2 == (0 : Int32) then
    return false
  else if sw'2 == (1 : Int32) then
    let t'3 ← PMem.ldB (this + 2496)
    if t'3 then
      let t'4 ← PMem.ldF32 (this + 2500)
      PMem.stF32 terrain_u_m t'4
      return true
    return false
  else if sw'2 == (2 : Int32) then
    return false
  else
    pure ()
  return false

/-- C++ `AC_WPNav::get_terrain_D_m : bool (float &)`, `AC_WPNav.cpp:840-847`. -/
def AC_WPNav.get_terrain_D_m (this : UInt64) (terrain_d_m : UInt64) : PMem.M Bool := do
  let t'1 ← AC_WPNav.get_terrain_U_m this terrain_d_m
  if !t'1 then
    return false
  let t'2 ← PMem.ldF32 terrain_d_m
  let t'3 := (t'2 * (-(Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))))
  PMem.stF32 terrain_d_m t'3
  return true

/-- C++ `AC_WPNav::convert_origin_to_alt_frame : bool (bool)`, `AC_WPNav.cpp:820-838`. -/
def AC_WPNav.convert_origin_to_alt_frame.body (fp : UInt64) (this : UInt64) (is_terrain_alt : Bool) : PMem.M Bool := do
  let mut is_terrain_alt := is_terrain_alt
  let t'1 ← AC_WPNav.get_terrain_D_m this (fp + 0)
  if !t'1 then
    return false
  if is_terrain_alt then
    let t'2 := ((this + 2408) + 16)
    let t'3 ← PMem.ldF64 t'2
    let t'4 ← PMem.ldF32 (fp + 0)
    let t'5 := (t'3 - (Binary32.toBinary64 (t'4)))
    PMem.stF64 t'2 t'5
    let t'6 ← PMem.ldF32 (fp + 0)
    let t'7 ← PMem.ldU64 (this + 24)
    AC_PosControl.init_pos_terrain_D_m t'7 t'6
  else
    let t'8 := ((this + 2408) + 16)
    let t'9 ← PMem.ldF64 t'8
    let t'10 ← PMem.ldF32 (fp + 0)
    let t'11 := (t'9 + (Binary32.toBinary64 (t'10)))
    PMem.stF64 t'8 t'11
    let t'12 ← PMem.ldU64 (this + 24)
    AC_PosControl.init_pos_terrain_D_m t'12 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  return true

def AC_WPNav.convert_origin_to_alt_frame (this : UInt64) (is_terrain_alt : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← AC_WPNav.convert_origin_to_alt_frame.body fp this is_terrain_alt
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::reached_wp_destination : bool () const`, `AC_WPNav.h:256-?`. -/
def AC_WPNav.reached_wp_destination (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldBits (this + 8) 0 1
  return (UInt64.toUInt8 (t'1)) != (0 : UInt8)

/-- C++ `AC_WPNav::set_pause : void ()`, `AC_WPNav.h:86-?`. -/
def AC_WPNav.set_pause (this : UInt64) : PMem.M Unit := do
  PMem.stB (this + 2492) true
  return ()

/-- C++ `AC_WPNav::set_resume : void ()`, `AC_WPNav.h:89-?`. -/
def AC_WPNav.set_resume (this : UInt64) : PMem.M Unit := do
  PMem.stB (this + 2492) false
  return ()

/-- `AC_WPNav.get_wp_destination_NED_m` as a pure function of its arguments (it reads and writes no memory). -/
def AC_WPNav.get_wp_destination_NED_m.pure' (this : UInt64) : Id UInt64 := do
  return (this + 2432)

/-- C++ `AC_WPNav::get_wp_destination_NED_m : const Vector3p &() const`, `AC_WPNav.h:152-?`. -/
def AC_WPNav.get_wp_destination_NED_m (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_WPNav.get_wp_destination_NED_m.pure' this)

/-- C++ `AC_WPNav::set_spline_destination_next_NED_m : bool (const Vector3p &, bool, const Vector3p &, bool, bool)`, `AC_WPNav.cpp:983-1031`. -/
def AC_WPNav.set_spline_destination_next_NED_m.body (fp : UInt64) (this : UInt64) (next_destination_ned_m : UInt64) (next_is_terrain_alt : Bool) (next_next_destination_ned_m : UInt64) (next_next_is_terrain_alt : Bool) (next_next_is_spline : Bool) : PMem.M Bool := do
  let mut next_is_terrain_alt := next_is_terrain_alt
  let mut next_next_is_terrain_alt := next_next_is_terrain_alt
  let mut next_next_is_spline := next_next_is_spline
  let t'1 ← PMem.ldB (this + 2493)
  if ((if next_is_terrain_alt then (1 : Int32) else (0 : Int32)) != (if t'1 then (1 : Int32) else (0 : Int32))) then
    return true
  Vector3'float.Vector3'2 (fp + 0)
  let t'2 ← PMem.ldB (this + 2392)
  if t'2 then
    let t'3 ← SplineCurve.get_destination_vel (this + 1976)
    discard <| PMem.memcpy (fp + 0) t'3 12
    discard <| pure ((fp + 0))
  else
    Vector3'double.operator_ (this + 2432) (fp + 16) (this + 2408)
    let t'4 := (fp + 16)
    Vector3'double.tofloat t'4 (fp + 40)
    let t'5 := (fp + 40)
    discard <| PMem.memcpy (fp + 0) t'5 12
    discard <| pure ((fp + 0))
  Vector3'float.Vector3'2 (fp + 56)
  if ((if next_is_terrain_alt then (1 : Int32) else (0 : Int32)) == (if next_next_is_terrain_alt then (1 : Int32) else (0 : Int32))) then
    if next_next_is_spline then
      Vector3'double.operator_ next_next_destination_ned_m (fp + 72) (this + 2432)
      let t'6 := (fp + 72)
      Vector3'double.tofloat t'6 (fp + 96)
      let t'7 := (fp + 96)
      discard <| PMem.memcpy (fp + 56) t'7 12
      discard <| pure ((fp + 56))
    else
      Vector3'double.operator_ next_next_destination_ned_m (fp + 112) next_destination_ned_m
      let t'8 := (fp + 112)
      Vector3'double.tofloat t'8 (fp + 136)
      let t'9 := (fp + 136)
      discard <| PMem.memcpy (fp + 56) t'9 12
      discard <| pure ((fp + 56))
  let t'10 ← PMem.ldU64 (this + 24)
  let t'11 ← AC_PosControl.NE_get_max_speed_ms t'10
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← AC_PosControl.get_max_speed_up_ms t'12
  let t'14 ← PMem.ldU64 (this + 24)
  let t'15 ← AC_PosControl.get_max_speed_down_ms t'14
  let t'16 ← PMem.ldU64 (this + 24)
  let t'17 ← AC_PosControl.NE_get_max_accel_mss t'16
  let t'18 ← PMem.ldU64 (this + 24)
  let t'19 ← AC_PosControl.D_get_max_accel_mss t'18
  SplineCurve.set_speed_accel (this + 2184) t'11 t'13 t'15 t'17 t'19
  SplineCurve.set_origin_and_destination (this + 2184) (this + 2432) next_destination_ned_m (fp + 0) (fp + 56)
  PMem.stB (this + 2393) true
  let t'20 := if true then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 1 1 (UInt8.toUInt64 (t'20))
  let t'21 ← PMem.ldB (this + 2392)
  if !t'21 then
    let t'22 ← SplineCurve.get_origin_speed_max (this + 2184)
    SCurve.set_destination_speed_max (this + 716) t'22
  else
    let t'23 ← SplineCurve.get_origin_speed_max (this + 2184)
    SplineCurve.set_destination_speed_max (this + 1976) t'23
  return true

def AC_WPNav.set_spline_destination_next_NED_m (this : UInt64) (next_destination_ned_m : UInt64) (next_is_terrain_alt : Bool) (next_next_destination_ned_m : UInt64) (next_next_is_terrain_alt : Bool) (next_next_is_spline : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 148
  let r ← AC_WPNav.set_spline_destination_next_NED_m.body fp this next_destination_ned_m next_is_terrain_alt next_next_destination_ned_m next_next_is_terrain_alt next_next_is_spline
  PMem.leave fp
  return r

/-- C++ `AC_Circle::set_radius_m : void (float)`, `AC_Circle.cpp:181-185`. -/
def AC_Circle.set_radius_m (this : UInt64) (radius_m : Binary32) : PMem.M Unit := do
  let mut radius_m := radius_m
  let t'1 ← constrain_value_line'float radius_m (Int32.toBinary32 ((0 : Int32))) (Binary64.toBinary32 ((Binary64.ofBits 0x409f400000000000 /- 2000 -/))) (Int32.toUInt32 ((184 : Int32)))
  PMem.stF32 (this + 56) t'1
  return ()

/-- `AC_Circle.get_center_NED_m` as a pure function of its arguments (it reads and writes no memory). -/
def AC_Circle.get_center_NED_m.pure' (this : UInt64) : Id UInt64 := do
  return (this + 32)

/-- C++ `AC_Circle::get_center_NED_m : const Vector3p &() const`, `AC_Circle.h:47-?`. -/
def AC_Circle.get_center_NED_m (this : UInt64) : PMem.M UInt64 :=
  pure (_root_.Vehicle_lib.AC_Circle.get_center_NED_m.pure' this)

/-- C++ `AC_Circle::set_center_NED_m : void (const Vector3p &, bool)`, `AC_Circle.h:39-?`. -/
def AC_Circle.set_center_NED_m (this : UInt64) (center_ned_m : UInt64) (is_terrain_alt : Bool) : PMem.M Unit := do
  let mut is_terrain_alt := is_terrain_alt
  discard <| PMem.memcpy (this + 32) center_ned_m 24
  discard <| pure ((this + 32))
  PMem.stB (this + 96) is_terrain_alt
  return ()

/-- C++ `AC_Circle::get_radius_m : float () const`, `AC_Circle.h:58-?`. -/
def AC_Circle.get_radius_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 56)
  let t'2 ← is_positive'float t'1
  let mut c'3 : Binary32 := default
  if t'2 then
    let t'4 ← PMem.ldF32 (this + 56)
    c'3 := t'4
  else
    let t'5 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'6 ← PMem.ldF32 t'5
    c'3 := t'6
  return c'3

/-- C++ `AC_Circle::center_is_terrain_alt : bool () const`, `AC_Circle.h:50-?`. -/
def AC_Circle.center_is_terrain_alt (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 96)
  return t'1

/-- C++ `AC_Circle::calc_velocities : void (bool)`, `AC_Circle.cpp:345-369`. -/
def AC_Circle.calc_velocities.body (fp : UInt64) (this : UInt64) (init_velocity : Bool) : PMem.M Unit := do
  let mut init_velocity := init_velocity
  let t'1 ← PMem.ldF32 (this + 56)
  if (decide (t'1 ≤ (Int32.toBinary32 ((0 : Int32))))) then
    let t'2 ← PMem.ldF32 (this + 60)
    PMem.stF32 (this + 80) t'2
    let t'3 ← PMem.ldF32 (this + 80)
    PMem.stF32 (fp + 0) (Binary32.abs t'3)
    let t'4 ← radians (Binary32.ofBits 0x40000000 /- 2 -/)
    PMem.stF32 (fp + 4) t'4
    let t'5 ← MAX'float_float (fp + 0) (fp + 4)
    let t'6 ← PMem.ldF32 t'5
    PMem.stF32 (this + 84) t'6
  else
    let t'7 ← PMem.ldU64 (this + 8)
    let t'8 ← AC_PosControl.NE_get_max_speed_ms t'7
    PMem.stF32 (fp + 8) t'8
    let t'9 ← PMem.ldU64 (this + 8)
    let t'10 ← AC_PosControl.NE_get_max_accel_mss t'9
    let t'11 ← PMem.ldF32 (this + 56)
    let t'12 ← safe_sqrt'float (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'10) * t'11)
    PMem.stF32 (fp + 12) t'12
    let t'13 ← MIN'float_float (fp + 8) (fp + 12)
    let t'14 ← PMem.ldF32 t'13
    let mut vel_max_ms : Binary32 := t'14
    let t'15 ← PMem.ldF32 (this + 56)
    let t'16 := (vel_max_ms / t'15)
    PMem.stF32 (this + 80) t'16
    let t'17 ← PMem.ldF32 (this + 60)
    let t'18 ← PMem.ldF32 (this + 80)
    let t'19 ← PMem.ldF32 (this + 80)
    let t'20 ← constrain_value_line'float t'17 (-t'18) t'19 (Int32.toUInt32 ((359 : Int32)))
    PMem.stF32 (this + 80) t'20
    let t'21 ← PMem.ldU64 (this + 8)
    let t'22 ← AC_PosControl.NE_get_max_accel_mss t'21
    let t'23 ← PMem.ldF32 (this + 56)
    PMem.stF32 (fp + 16) (t'22 / t'23)
    let t'24 ← radians (Binary32.ofBits 0x40000000 /- 2 -/)
    PMem.stF32 (fp + 20) t'24
    let t'25 ← MAX'float_float (fp + 16) (fp + 20)
    let t'26 ← PMem.ldF32 t'25
    PMem.stF32 (this + 84) t'26
  if init_velocity then
    let t'27 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    PMem.stF32 (this + 76) t'27
  return ()

def AC_Circle.calc_velocities (this : UInt64) (init_velocity : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AC_Circle.calc_velocities.body fp this init_velocity
  PMem.leave fp
  return r

/-- C++ `AC_Circle::init_start_angle : void (bool)`, `AC_Circle.cpp:374-400`. -/
def AC_Circle.init_start_angle (this : UInt64) (use_heading : Bool) : PMem.M Unit := do
  let mut use_heading := use_heading
  let t'1 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 72) t'1
  let t'2 ← PMem.ldF32 (this + 56)
  if (decide (t'2 ≤ (Int32.toBinary32 ((0 : Int32))))) then
    let t'3 ← PMem.ldU64 this
    let t'4 ← VehicleBridge.AP_AHRS_View.yaw'field t'3
    PMem.stF32 (this + 68) t'4
    return ()
  if use_heading then
    let t'5 ← PMem.ldU64 this
    let t'6 ← VehicleBridge.AP_AHRS_View.yaw'field t'5
    let t'7 ← wrap_PI'float (t'6 - (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))))
    PMem.stF32 (this + 68) t'7
  else
    let t'8 ← PMem.ldU64 (this + 8)
    let t'9 ← AC_PosControl.get_pos_desired_NED_m t'8
    let curr_pos_desired_ned_m : UInt64 := t'9
    let t'10 ← PMem.ldF64 curr_pos_desired_ned_m
    let t'11 ← PMem.ldF64 (this + 32)
    let t'12 ← is_equal'double_double t'10 t'11
    let mut sc'16 := t'12
    if sc'16 then
      let t'13 ← PMem.ldF64 (curr_pos_desired_ned_m + 8)
      let t'14 ← PMem.ldF64 ((this + 32) + 8)
      let t'15 ← is_equal'double_double t'13 t'14
      sc'16 := t'15
    if sc'16 then
      let t'17 ← PMem.ldU64 this
      let t'18 ← VehicleBridge.AP_AHRS_View.yaw'field t'17
      let t'19 ← wrap_PI'float (t'18 - (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))))
      PMem.stF32 (this + 68) t'19
    else
      let t'20 ← PMem.ldF64 (curr_pos_desired_ned_m + 8)
      let t'21 ← PMem.ldF64 ((this + 32) + 8)
      let t'22 ← PMem.ldF64 curr_pos_desired_ned_m
      let t'23 ← PMem.ldF64 (this + 32)
      let mut bearing_rad : Binary32 := (Musl.atan2f.atan2f (Binary64.toBinary32 ((t'20 - t'21))) (Binary64.toBinary32 ((t'22 - t'23))))
      let t'24 ← wrap_PI'float bearing_rad
      PMem.stF32 (this + 68) t'24
  return ()

/-- C++ `AC_Loiter::loiter_option_is_set : bool (LoiterOption) const`, `AC_Loiter.cpp:312-314`. -/
def AC_Loiter.loiter_option_is_set (this : UInt64) (option : Int32) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ (this + 48)
  let t'2 ← PMem.ldU8 t'1
  return (((UInt32.toInt32 (UInt8.toUInt32 (t'2))) &&& (Int8.toInt32 ((Int32.toInt8 (option))))) != (0 : Int32))

/-- C++ `AC_Loiter::set_pilot_desired_acceleration_rad : void (float, float)`, `AC_Loiter.cpp:174-209`. -/
def AC_Loiter.set_pilot_desired_acceleration_rad.body (fp : UInt64) (this : UInt64) (euler_roll_angle_rad : Binary32) (euler_pitch_angle_rad : Binary32) : PMem.M Unit := do
  let mut euler_roll_angle_rad := euler_roll_angle_rad
  let mut euler_pitch_angle_rad := euler_pitch_angle_rad
  let t'1 ← PMem.ldU64 (this + 16)
  let t'2 ← AC_AttitudeControl.get_dt_s t'1
  let mut dt_s : Binary32 := t'2
  let t'3 ← PMem.ldU64 this
  let t'4 ← VehicleBridge.AP_AHRS_View.yaw'field t'3
  Vector3'float.Vector3 (fp + 0) euler_roll_angle_rad euler_pitch_angle_rad t'4
  let t'5 ← PMem.ldU64 (this + 8)
  AC_PosControl.lean_angles_rad_to_accel_NED_mss t'5 (fp + 16) (fp + 0)
  let t'6 := (fp + 16)
  let t'7 ← Vector3'float.xy t'6
  discard <| PMem.memcpy (this + 52) t'7 8
  discard <| pure ((this + 52))
  let t'8 ← Vector2'float.is_zero (this + 52)
  if !t'8 then
    let t'9 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 92) t'9
  let t'10 ← PMem.ldF32 (this + 68)
  let t'11 ← wrap_PI'float (euler_roll_angle_rad - t'10)
  let t'12 ← PMem.ldF32 ((this + 68) + 4)
  let t'13 ← wrap_PI'float (euler_pitch_angle_rad - t'12)
  Vector2'float.Vector2'2 (fp + 32) t'11 t'13
  let t'14 ← PMem.ldU64 (this + 16)
  AC_AttitudeControl.command_model_rate_predictor t'14 (fp + 32) (this + 76) (this + 84) dt_s
  Vector2'float.operator_'2 (this + 76) (fp + 40) dt_s
  let t'15 := (fp + 40)
  let t'16 ← Vector2'float.operator__ (this + 68) t'15
  discard <| pure (t'16)
  let t'17 ← PMem.ldF32 (this + 68)
  let t'18 ← PMem.ldF32 ((this + 68) + 4)
  let t'19 ← PMem.ldU64 this
  let t'20 ← VehicleBridge.AP_AHRS_View.yaw'field t'19
  Vector3'float.Vector3 (fp + 48) t'17 t'18 t'20
  let t'21 ← PMem.ldU64 (this + 8)
  AC_PosControl.lean_angles_rad_to_accel_NED_mss t'21 (fp + 80) (fp + 48)
  let t'22 := (fp + 80)
  Vector3'float.Vector3'3 (fp + 64) t'22
  let t'23 ← Vector3'float.xy (fp + 64)
  discard <| PMem.memcpy (this + 60) t'23 8
  discard <| pure ((this + 60))
  let t'24 ← AC_Loiter.loiter_option_is_set this (1 : Int32)
  if t'24 then
    let t'25 ← PMem.ldU64 (this + 16)
    let t'26 ← AC_AttitudeControl.get_attitude_target_ang_vel t'25
    Vector3'float.Vector3'4 (fp + 96) t'26
    let t'27 ← PMem.ldU64 (this + 8)
    let t'28 ← AC_PosControl.get_vel_desired_NED_ms t'27
    Vector3'float.Vector3'4 (fp + 112) t'28
    let t'29 ← PMem.ldF32 ((fp + 112) + 4)
    let t'30 ← PMem.ldF32 ((fp + 96) + 8)
    let t'31 ← PMem.ldF32 (fp + 112)
    let t'32 ← PMem.ldF32 ((fp + 96) + 8)
    Vector2'float.Vector2'2 (fp + 136) ((-t'29) * t'30) (t'31 * t'32)
    Vector2'float.Vector2'3 (fp + 128) (fp + 136)
    let t'33 ← Vector2'float.operator__ (this + 52) (fp + 128)
    discard <| pure (t'33)
    let t'34 ← Vector2'float.operator__ (this + 60) (fp + 128)
    discard <| pure (t'34)
  return ()

def AC_Loiter.set_pilot_desired_acceleration_rad (this : UInt64) (euler_roll_angle_rad : Binary32) (euler_pitch_angle_rad : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 144
  let r ← AC_Loiter.set_pilot_desired_acceleration_rad.body fp this euler_roll_angle_rad euler_pitch_angle_rad
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::paused : bool ()`, `AC_WPNav.h:92-?`. -/
def AC_WPNav.paused (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 2492)
  return t'1

/-- C++ `AC_WPNav::crosstrack_error_m : float () const`, `AC_WPNav.h:356-?`. -/
def AC_WPNav.crosstrack_error_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← AC_PosControl.crosstrack_error_m t'1
  return t'2

/-- C++ `AC_WPNav::get_wp_bearing_to_destination_rad : float () const`, `AC_WPNav.cpp:704-708`. -/
def AC_WPNav.get_wp_bearing_to_destination_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← AC_PosControl.get_pos_estimate_NED_m t'1
  let t'3 ← Vector3'double.xy t'2
  Vector2'double.tofloat t'3 (fp + 0)
  let t'4 := (fp + 0)
  let t'5 ← Vector3'double.xy (this + 2432)
  Vector2'double.tofloat t'5 (fp + 8)
  let t'6 := (fp + 8)
  let t'7 ← get_bearing_rad t'4 t'6
  return t'7

def AC_WPNav.get_wp_bearing_to_destination_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← AC_WPNav.get_wp_bearing_to_destination_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_Circle::get_bearing_to_target_rad : float () const`, `AP_Common.h:137-?`. -/
def AC_Circle.get_bearing_to_target_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AC_PosControl.get_bearing_to_target_rad t'1
  return t'2

/-- C++ `AC_Loiter::get_bearing_to_target_rad : float () const`, `AC_Loiter.h:59-?`. -/
def AC_Loiter.get_bearing_to_target_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AC_PosControl.get_bearing_to_target_rad t'1
  return t'2

/-- C++ `AC_WPNav::get_wp_distance_to_destination_m : float () const`, `AC_WPNav.cpp:688-692`. -/
def AC_WPNav.get_wp_distance_to_destination_m.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← AC_PosControl.get_pos_estimate_NED_m t'1
  let t'3 ← Vector3'double.xy t'2
  Vector2'double.tofloat t'3 (fp + 0)
  let t'4 := (fp + 0)
  let t'5 ← Vector3'double.xy (this + 2432)
  Vector2'double.tofloat t'5 (fp + 8)
  let t'6 := (fp + 8)
  let t'7 ← get_horizontal_distance'float t'4 t'6
  return t'7

def AC_WPNav.get_wp_distance_to_destination_m (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 16
  let r ← AC_WPNav.get_wp_distance_to_destination_m.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_Circle::get_distance_to_target_m : float () const`, `AP_Common.h:133-?`. -/
def AC_Circle.get_distance_to_target_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AC_PosControl.get_pos_error_NE_m t'1
  return t'2

/-- C++ `AC_Loiter::get_distance_to_target_m : float () const`, `AC_Loiter.h:55-?`. -/
def AC_Loiter.get_distance_to_target_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AC_PosControl.get_pos_error_NE_m t'1
  return t'2

/-- `AC_WPNav.wpnav_flags.wpnav_flags` as a pure function of its arguments (it reads and writes no memory). -/
def AC_WPNav.wpnav_flags.wpnav_flags.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AC_WPNav::wpnav_flags::wpnav_flags : void () noexcept`, `AC_WPNav.h:?-?`. -/
def AC_WPNav.wpnav_flags.wpnav_flags (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AC_WPNav.wpnav_flags.wpnav_flags.pure' this)

/-- C++ `AC_WPNav::AC_WPNav : void (const AP_AHRS_View &, AC_PosControl &, const AC_AttitudeControl &)`, `AC_WPNav.cpp:167-182`. -/
def AC_WPNav.AC_WPNav (this : UInt64) (ahrs : UInt64) (pos_control : UInt64) (attitude_control : UInt64) : PMem.M Unit := do
  AC_WPNav.wpnav_flags.wpnav_flags (this + 8)
  PMem.stU64 (this + 16) ahrs
  PMem.stU64 (this + 24) pos_control
  PMem.stU64 (this + 32) attitude_control
  AP_Param.AP_Param'2 (this + 40)
  AP_Param.AP_Param'2 (this + 44)
  AP_Param.AP_Param'2 (this + 48)
  AP_Param.AP_Param'2 (this + 52)
  AP_Param.AP_Param'2 (this + 56)
  AP_Param.AP_Param'2 (this + 60)
  AP_Param.AP_Param'2 (this + 64)
  AP_Param.AP_Param'2 (this + 68)
  AP_Param.AP_Param'2 (this + 72)
  SCurve.SCurve (this + 92)
  SCurve.SCurve (this + 716)
  SCurve.SCurve (this + 1340)
  Vector3'double.Vector3 (this + 1976)
  Vector3'double.Vector3 ((this + 1976) + 24)
  Vector3'float.Vector3'2 ((this + 1976) + 48)
  Vector3'float.Vector3'2 ((this + 1976) + 60)
  Vector3'double.Vector3 ((this + 1976) + 72)
  Vector3'double.Vector3 ((this + 1976) + 96)
  Vector3'double.Vector3 ((this + 1976) + 120)
  Vector3'double.Vector3 ((this + 1976) + 144)
  Vector3'double.Vector3 (this + 2184)
  Vector3'double.Vector3 ((this + 2184) + 24)
  Vector3'float.Vector3'2 ((this + 2184) + 48)
  Vector3'float.Vector3'2 ((this + 2184) + 60)
  Vector3'double.Vector3 ((this + 2184) + 72)
  Vector3'double.Vector3 ((this + 2184) + 96)
  Vector3'double.Vector3 ((this + 2184) + 120)
  Vector3'double.Vector3 ((this + 2184) + 144)
  Vector3'double.Vector3 (this + 2408)
  Vector3'double.Vector3 (this + 2432)
  Vector3'double.Vector3 (this + 2456)
  AP_Param.AP_Param'2 (this + 2495)
  AP_Param.setup_object_defaults this (0x2fe8 : UInt64) /- &AC_WPNav::var_info -/
  let t'1 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 0 1 (UInt8.toUInt64 (t'1))
  let t'2 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 1 1 (UInt8.toUInt64 (t'2))
  let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 40)
  let t'4 ← PMem.ldF32 t'3
  PMem.stF32 (this + 80) t'4
  let t'5 ← AP_ParamT'float_4.operator_const_float__'1 (this + 44)
  let t'6 ← PMem.ldF32 t'5
  PMem.stF32 (this + 84) t'6
  let t'7 ← AC_WPNav.get_default_speed_down_ms this
  PMem.stF32 (this + 88) t'7
  return ()

/-- C++ `AC_Loiter::AC_Loiter : void (const AP_AHRS_View &, AC_PosControl &, const AC_AttitudeControl &)`, `AC_Loiter.cpp:102-108`. -/
def AC_Loiter.AC_Loiter (this : UInt64) (ahrs : UInt64) (pos_control : UInt64) (attitude_control : UInt64) : PMem.M Unit := do
  PMem.stU64 (this + 0) ahrs
  PMem.stU64 (this + 8) pos_control
  PMem.stU64 (this + 16) attitude_control
  AP_Param.AP_Param'2 (this + 24)
  AP_Param.AP_Param'2 (this + 28)
  AP_Param.AP_Param'2 (this + 32)
  AP_Param.AP_Param'2 (this + 36)
  AP_Param.AP_Param'2 (this + 40)
  AP_Param.AP_Param'2 (this + 44)
  AP_Param.AP_Param'2 (this + 48)
  Vector2'float.Vector2 (this + 52)
  Vector2'float.Vector2 (this + 60)
  Vector2'float.Vector2 (this + 68)
  Vector2'float.Vector2 (this + 76)
  Vector2'float.Vector2 (this + 84)
  AP_Param.setup_object_defaults this (0x31b8 : UInt64) /- &AC_Loiter::var_info -/
  return ()

/-- C++ `AC_Circle::AC_Circle : void (const AP_AHRS_View &, AC_PosControl &)`, `AC_Circle.cpp:50-57`. -/
def AC_Circle.AC_Circle (this : UInt64) (ahrs : UInt64) (pos_control : UInt64) : PMem.M Unit := do
  PMem.stU64 (this + 0) ahrs
  PMem.stU64 (this + 8) pos_control
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  AP_Param.AP_Param'2 (this + 24)
  Vector3'double.Vector3 (this + 32)
  AP_Param.setup_object_defaults this (0x3320 : UInt64) /- &AC_Circle::var_info -/
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← radians t'2
  PMem.stF32 (this + 60) t'3
  return ()

/-- C++ `AC_Circle::get_rate_degs : float () const`, `AC_Circle.h:73-?`. -/
def AC_Circle.get_rate_degs (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AC_WPNav::get_circle_angle_covered_rad : float () const`, `AC_WPNav.h:221-?`. -/
def AC_WPNav.get_circle_angle_covered_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldB (this + 2394)
  let mut c'2 : Binary32 := default
  if t'1 then
    let t'3 ← SCurve.get_arc_angle_covered_rad (this + 716)
    c'2 := t'3
  else
    c'2 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  return c'2

/-- C++ `AC_Circle::is_active : bool () const`, `AC_Circle.cpp:189-193`. -/
def AC_Circle.is_active (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU32 (this + 88)
  return (decide (((((← PMem.clock) / 1000).toUInt32) - t'1) < (Int32.toUInt32 ((200 : Int32)))))

/-- C++ `AC_Circle::get_yaw_rad : float () const`, `AP_Common.h:110-?`. -/
def AC_Circle.get_yaw_rad (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 64)
  return t'1

/-- C++ `AC_Circle::face_direction_of_travel : bool () const`, `AP_Common.h:149-?`. -/
def AC_Circle.face_direction_of_travel (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamTBase'unsigned_short_2.get (this + 24)
  let t'2 ← PMem.ldU16 t'1
  return (((UInt32.toInt32 (UInt16.toUInt32 (t'2))) &&& (UInt32.toInt32 ((2 : UInt32)))) != (0 : Int32))

/-- C++ `AC_WPNav::reached_wp_destination_NE : bool () const`, `AC_WPNav.h:260-262`. -/
def AC_WPNav.reached_wp_destination_NE (this : UInt64) : PMem.M Bool := do
  let t'1 ← AC_WPNav.get_wp_distance_to_destination_m this
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 52)
  let t'3 ← PMem.ldF32 t'2
  return (decide (t'1 < t'3))

/-- C++ `AC_Circle::check_param_change : void ()`, `AC_Circle.cpp:459-467`. -/
def AC_Circle.check_param_change (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 92)
  let t'2 ← AP_ParamTBase'float_4.get (this + 16)
  let t'3 ← PMem.ldF32 t'2
  let t'4 ← is_equal'float_float t'1 t'3
  if !t'4 then
    let t'5 ← AP_ParamTBase'float_4.get (this + 16)
    let t'6 ← PMem.ldF32 t'5
    PMem.stF32 (this + 56) t'6
    let t'7 ← PMem.ldF32 (this + 56)
    PMem.stF32 (this + 92) t'7
  return ()

/-- C++ `AC_Circle::pilot_control_enabled : bool () const`, `AP_Common.h:141-?`. -/
def AC_Circle.pilot_control_enabled (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamTBase'unsigned_short_2.get (this + 24)
  let t'2 ← PMem.ldU16 t'1
  return (((UInt32.toInt32 (UInt16.toUInt32 (t'2))) &&& (UInt32.toInt32 ((1 : UInt32)))) != (0 : Int32))

/-- C++ `AC_Circle::get_radius_target_m : float () const`, `AC_Circle.h:62-?`. -/
def AC_Circle.get_radius_target_m (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 56)
  return t'1

/-- C++ `AC_Circle::get_rate_target_degs : float () const`, `AC_Circle.h:78-?`. -/
def AC_Circle.get_rate_target_degs (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 60)
  let t'2 ← degrees t'1
  return t'2

/-- C++ `AC_Circle::set_rate_degs : void (float)`, `AC_Circle.cpp:165-169`. -/
def AC_Circle.set_rate_degs (this : UInt64) (rate_degs : Binary32) : PMem.M Unit := do
  let mut rate_degs := rate_degs
  let t'1 ← radians rate_degs
  PMem.stF32 (this + 60) t'1
  return ()

/-- C++ `AC_Circle::get_terrain_source : AC_Circle::TerrainSource () const`, `AC_Circle.cpp:404-422`. -/
def AC_Circle.get_terrain_source (this : UInt64) : PMem.M Int32 := do
  let t'1 ← PMem.ldB (this + 97)
  if t'1 then
    return (1 : Int32)
  return (0 : Int32)

/-- C++ `AC_Circle::get_terrain_U_m : bool (float &)`, `AC_Circle.cpp:427-455`. -/
def AC_Circle.get_terrain_U_m (this : UInt64) (terrain_u_m : UInt64) : PMem.M Bool := do
  let t'1 ← AC_Circle.get_terrain_source this
  let sw'2 := t'1
  if sw'2 == (0 : Int32) then
    return false
  else if sw'2 == (1 : Int32) then
    let t'3 ← PMem.ldB (this + 98)
    if t'3 then
      let t'4 ← PMem.ldF32 (this + 100)
      PMem.stF32 terrain_u_m t'4
      return true
    return false
  else if sw'2 == (2 : Int32) then
    return false
  else
    pure ()
  return false

/-- C++ `AC_Loiter::soften_for_landing : void ()`, `AC_Loiter.cpp:158-161`. -/
def AC_Loiter.soften_for_landing (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 8)
  AC_PosControl.NE_soften_for_landing t'1
  return ()

/-- C++ `AC_Loiter::get_thrust_vector : Vector3f () const`, `AC_Loiter.h:91-?`. -/
def AC_Loiter.get_thrust_vector.body (fp : UInt64) (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 8)
  AC_PosControl.get_thrust_vector t'1 (fp + 0)
  let t'2 := (fp + 0)
  Vector3'float.Vector3'3 sret t'2
  return ()

def AC_Loiter.get_thrust_vector (this : UInt64) (sret : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AC_Loiter.get_thrust_vector.body fp this sret
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::set_rangefinder_terrain_U_m : void (bool, bool, float)`, `AC_WPNav.h:30-?`. -/
def AC_WPNav.set_rangefinder_terrain_U_m (this : UInt64) (use : Bool) (healthy : Bool) (terrain_u_m : Binary32) : PMem.M Unit := do
  let mut use := use
  let mut healthy := healthy
  let mut terrain_u_m := terrain_u_m
  PMem.stB (this + 2494) use
  PMem.stB (this + 2496) healthy
  PMem.stF32 (this + 2500) terrain_u_m
  return ()

/-- C++ `AC_Circle::set_rangefinder_terrain_U_m : void (bool, bool, float)`, `AP_Common.h:157-?`. -/
def AC_Circle.set_rangefinder_terrain_U_m (this : UInt64) (use : Bool) (healthy : Bool) (terrain_u_m : Binary32) : PMem.M Unit := do
  let mut use := use
  let mut healthy := healthy
  let mut terrain_u_m := terrain_u_m
  PMem.stB (this + 97) use
  PMem.stB (this + 98) healthy
  PMem.stF32 (this + 100) terrain_u_m
  return ()

/-- C++ `AC_WPNav::rangefinder_used : bool () const`, `AC_WPNav.h:33-?`. -/
def AC_WPNav.rangefinder_used (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 2495)
  let t'2 ← PMem.ldI8 t'1
  return t'2 != (0 : Int8)

end Vehicle_lib
