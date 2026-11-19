import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AC_PID.AC_PID
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl
import ArduLean.Vehicle.libraries.AC_WPNav.AC_WPNav
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2
import ArduLean.Vehicle.libraries.AC_AttitudeControl.AC_AttitudeControl_2

/-!
ArduPilot `libraries/AC_WPNav`, part 2 of 2. Sources: `libraries/AC_WPNav/AC_WPNav.cpp`, `libraries/AC_WPNav/AC_Circle.cpp`, `libraries/AC_WPNav/AC_Loiter.cpp`, `libraries/AC_WPNav/AC_WPNav.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AC_WPNav::get_wp_acceleration_mss : float () const`, `AC_WPNav.h:140-?`. -/
def AC_WPNav.get_wp_acceleration_mss.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  discard <| PMem.memcpy (fp + 0) (this + 56) 4
  let t'1 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  let mut c'2 : Binary32 := default
  if t'1 then
    let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 56)
    let t'4 ← PMem.ldF32 t'3
    c'2 := t'4
  else
    c'2 := Binary64.toBinary32 ((Binary64.ofBits 0x4004000000000000 /- 5/2 -/))
  return c'2

def AC_WPNav.get_wp_acceleration_mss (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← AC_WPNav.get_wp_acceleration_mss.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::calc_scurve_jerk_and_snap : void ()`, `AC_WPNav.cpp:1070-1092`. -/
def AC_WPNav.calc_scurve_jerk_and_snap.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 32)
  let t'2 ← AC_AttitudeControl.get_ang_vel_roll_max_rads t'1
  PMem.stF32 (fp + 0) (t'2 * (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))
  let t'3 ← PMem.ldU64 (this + 32)
  let t'4 ← AC_AttitudeControl.get_ang_vel_pitch_max_rads t'3
  PMem.stF32 (fp + 4) (t'4 * (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))
  let t'5 ← MIN'float_float (fp + 0) (fp + 4)
  let t'6 ← PMem.ldF32 t'5
  PMem.stF32 (this + 1964) t'6
  let t'7 ← PMem.ldF32 (this + 1964)
  let t'8 ← is_zero t'7
  if t'8 then
    let t'9 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'10 ← PMem.ldF32 t'9
    PMem.stF32 (this + 1964) t'10
  else
    let t'11 ← MIN'float_AP_ParamT_float_AP_PARAM_FLOAT (this + 1964) (this + 68)
    let t'12 ← PMem.ldF32 t'11
    PMem.stF32 (this + 1964) t'12
  let t'13 ← PMem.ldF32 (this + 1964)
  let t'14 ← PMem.ldU64 (this + 32)
  let t'15 ← AC_AttitudeControl.get_input_tc t'14
  PMem.stF32 (fp + 8) t'15
  PMem.stF32 (fp + 12) (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/)
  let t'16 ← MAX'float_float (fp + 8) (fp + 12)
  let t'17 ← PMem.ldF32 t'16
  let t'18 := ((t'13 * (Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/)))) / ((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * t'17))
  PMem.stF32 (this + 1968) t'18
  let t'19 ← PMem.ldU64 (this + 32)
  let t'20 ← AC_AttitudeControl.get_accel_roll_max_radss t'19
  PMem.stF32 (fp + 20) t'20
  let t'21 ← PMem.ldU64 (this + 32)
  let t'22 ← AC_AttitudeControl.get_accel_pitch_max_radss t'21
  PMem.stF32 (fp + 24) t'22
  let t'23 ← MIN'float_float (fp + 20) (fp + 24)
  let t'24 ← PMem.ldF32 t'23
  PMem.stF32 (fp + 16) (t'24 * (Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/))
  let t'25 ← PMem.ldF32 (fp + 16)
  let t'26 ← is_positive'float t'25
  if t'26 then
    let t'27 ← MIN'float_float (this + 1968) (fp + 16)
    let t'28 ← PMem.ldF32 t'27
    PMem.stF32 (this + 1968) t'28
  let t'29 := (this + 1968)
  let t'30 ← PMem.ldF32 t'29
  let t'31 := (t'30 * (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))))
  PMem.stF32 t'29 t'31
  return ()

def AC_WPNav.calc_scurve_jerk_and_snap (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 28
  let r ← AC_WPNav.calc_scurve_jerk_and_snap.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::get_wp_stopping_point_NED_m : void (Vector3p &) const`, `AC_WPNav.cpp:546-552`. -/
def AC_WPNav.get_wp_stopping_point_NED_m (this : UInt64) (stopping_point_ned_m : UInt64) : PMem.M Unit := do
  let t'1 ← Vector3'double.xy stopping_point_ned_m
  let t'2 ← PMem.ldU64 (this + 24)
  AC_PosControl.get_stopping_point_NE_m t'2 t'1
  let t'3 ← PMem.ldU64 (this + 24)
  AC_PosControl.get_stopping_point_D_m t'3 (stopping_point_ned_m + 16)
  return ()

/-- C++ `AC_WPNav::wp_and_spline_init_m : void (float, Vector3p)`, `AC_WPNav.cpp:214-267`. -/
def AC_WPNav.wp_and_spline_init_m.body (fp : UInt64) (this : UInt64) (speed_ms : Binary32) (stopping_point_ned_m : UInt64) : PMem.M Unit := do
  let mut speed_ms := speed_ms
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x3d4ccccd /- 500000007/10000000000 -/)
  let t'1 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 52) (fp + 0)
  AP_ParamTBase'float_4.set_and_save_ifchanged (this + 52) t'1
  PMem.stF32 (fp + 4) (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/)
  let t'2 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 40) (fp + 4)
  AP_ParamTBase'float_4.set_and_save_ifchanged (this + 40) t'2
  let t'3 ← PMem.ldU64 (this + 24)
  AC_PosControl.D_init_controller_stopping_point t'3
  let t'4 ← PMem.ldU64 (this + 24)
  AC_PosControl.NE_init_controller_stopping_point t'4
  let t'5 ← is_positive'float speed_ms
  let t'6 := !t'5
  PMem.stB (this + 76) t'6
  let t'7 ← is_positive'float speed_ms
  let mut c'8 : Binary32 := default
  if t'7 then
    c'8 := speed_ms
  else
    let t'9 ← AC_WPNav.get_default_speed_NE_ms this
    c'8 := t'9
  PMem.stF32 (this + 2400) c'8
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/)
  let t'10 ← MAX'float_float (this + 2400) (fp + 8)
  let t'11 ← PMem.ldF32 t'10
  PMem.stF32 (this + 2400) t'11
  let t'12 ← PMem.ldF32 (this + 2400)
  let t'13 ← AC_WPNav.get_wp_acceleration_mss this
  let t'14 ← PMem.ldU64 (this + 24)
  AC_PosControl.NE_set_max_speed_accel_m t'14 t'12 t'13
  let t'15 ← PMem.ldF32 (this + 2400)
  let t'16 ← AC_WPNav.get_wp_acceleration_mss this
  let t'17 ← PMem.ldU64 (this + 24)
  AC_PosControl.NE_set_correction_speed_accel_m t'17 t'15 t'16
  let t'18 ← AC_WPNav.get_default_speed_down_ms this
  let t'19 ← AC_WPNav.get_default_speed_up_ms this
  let t'20 ← AC_WPNav.get_accel_D_mss this
  let t'21 ← PMem.ldU64 (this + 24)
  AC_PosControl.D_set_max_speed_accel_m t'21 t'18 t'19 t'20
  let t'22 ← AC_WPNav.get_default_speed_down_ms this
  let t'23 ← AC_WPNav.get_default_speed_up_ms this
  let t'24 ← AC_WPNav.get_accel_D_mss this
  let t'25 ← PMem.ldU64 (this + 24)
  AC_PosControl.D_set_correction_speed_accel_m t'25 t'22 t'23 t'24
  discard <| PMem.memcpy (fp + 16) (this + 68) 4
  let t'26 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 16)
  if !t'26 then
    let t'27 ← AC_WPNav.get_wp_acceleration_mss this
    PMem.stF32 (fp + 20) t'27
    AP_ParamTBase'float_4.set (this + 68) (fp + 20)
  AC_WPNav.calc_scurve_jerk_and_snap this
  SCurve.init (this + 92)
  SCurve.init (this + 716)
  SCurve.init (this + 1340)
  let t'28 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  PMem.stF32 (this + 2480) t'28
  let t'29 := if true then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 0 1 (UInt8.toUInt64 (t'29))
  let t'30 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 1 1 (UInt8.toUInt64 (t'30))
  let t'31 ← Vector3'double.is_zero stopping_point_ned_m
  if t'31 then
    AC_WPNav.get_wp_stopping_point_NED_m this stopping_point_ned_m
  discard <| PMem.memcpy (this + 2432) stopping_point_ned_m 24
  let t'32 := (this + 2432)
  discard <| PMem.memcpy (this + 2408) t'32 24
  discard <| pure ((this + 2408))
  PMem.stB (this + 2493) false
  PMem.stB (this + 2392) false
  PMem.stB (this + 2394) false
  let t'33 ← PMem.ldF32 (this + 2400)
  PMem.stF32 (this + 2484) t'33
  let t'34 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
  PMem.stF32 (this + 2488) t'34
  PMem.stB (this + 2492) false
  let t'35 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 2396) t'35
  return ()

def AC_WPNav.wp_and_spline_init_m (this : UInt64) (speed_ms : Binary32) (stopping_point_ned_m : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AC_WPNav.wp_and_spline_init_m.body fp this speed_ms stopping_point_ned_m
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::get_corner_acceleration_mss : float () const`, `AC_WPNav.h:144-?`. -/
def AC_WPNav.get_corner_acceleration_mss.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  discard <| PMem.memcpy (fp + 0) (this + 60) 4
  let t'1 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  let mut c'2 : Binary32 := default
  if t'1 then
    let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 60)
    let t'4 ← PMem.ldF32 t'3
    c'2 := t'4
  else
    let t'5 ← AC_WPNav.get_wp_acceleration_mss this
    c'2 := ((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * t'5)
  return c'2

def AC_WPNav.get_corner_acceleration_mss (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← AC_WPNav.get_corner_acceleration_mss.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::set_wp_destination_NED_m : bool (const Vector3p &, bool, float)`, `AC_WPNav.cpp:383-437`. -/
def AC_WPNav.set_wp_destination_NED_m.body (fp : UInt64) (this : UInt64) (destination_ned_m : UInt64) (is_terrain_alt : Bool) (arc_rad : Binary32) : PMem.M Bool := do
  let mut is_terrain_alt := is_terrain_alt
  let mut arc_rad := arc_rad
  let t'1 ← AC_WPNav.is_active this
  let mut sc'3 := !t'1
  if !sc'3 then
    let t'2 ← PMem.ldBits (this + 8) 0 1
    sc'3 := !((UInt64.toUInt8 (t'2)) != (0 : UInt8))
  if sc'3 then
    let t'4 ← PMem.ldF32 (this + 2400)
    Vector3'double.Vector3 (fp + 24)
    Vector3'double.Vector3'2 (fp + 0) (fp + 24)
    AC_WPNav.wp_and_spline_init_m this t'4 (fp + 0)
  SCurve.init (this + 92)
  let mut origin_speed_m : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  discard <| PMem.memcpy (this + 2408) (this + 2432) 24
  discard <| pure ((this + 2408))
  let t'5 ← PMem.ldB (this + 2493)
  if ((if is_terrain_alt then (1 : Int32) else (0 : Int32)) == (if t'5 then (1 : Int32) else (0 : Int32))) then
    let t'6 ← PMem.ldB (this + 2392)
    if t'6 then
      let t'7 ← PMem.ldU64 (this + 24)
      let t'8 ← AC_PosControl.get_vel_desired_NED_ms t'7
      Vector3'float.Vector3'4 (fp + 48) t'8
      let t'9 := ((fp + 48) + 8)
      let t'10 ← PMem.ldF32 t'9
      let t'11 ← PMem.ldU64 (this + 24)
      let t'12 ← AC_PosControl.get_vel_offset_D_ms t'11
      let t'13 := (t'10 - t'12)
      PMem.stF32 t'9 t'13
      let t'14 ← Vector3'float.length (fp + 48)
      origin_speed_m := t'14
    else
      discard <| PMem.memcpy (this + 92) (this + 716) 624
      discard <| pure ((this + 92))
  else
    let t'15 ← AC_WPNav.convert_origin_to_alt_frame this is_terrain_alt
    if !t'15 then
      return false
  discard <| PMem.memcpy (this + 2432) destination_ned_m 24
  discard <| pure ((this + 2432))
  PMem.stB (this + 2493) is_terrain_alt
  let t'16 ← PMem.ldBits (this + 8) 1 1
  let mut sc'18 := (UInt64.toUInt8 (t'16)) != (0 : UInt8)
  if sc'18 then
    let t'17 ← PMem.ldB (this + 2392)
    sc'18 := !t'17
  let mut sc'20 := sc'18
  if sc'20 then
    let t'19 ← PMem.ldB (this + 2393)
    sc'20 := !t'19
  let mut sc'22 := sc'20
  if sc'22 then
    let t'21 ← SCurve.finished (this + 1340)
    sc'22 := !t'21
  if sc'22 then
    discard <| PMem.memcpy (this + 716) (this + 1340) 624
    discard <| pure ((this + 716))
  else
    let t'23 ← PMem.ldU64 (this + 24)
    let t'24 ← AC_PosControl.NE_get_max_speed_ms t'23
    let t'25 ← PMem.ldU64 (this + 24)
    let t'26 ← AC_PosControl.get_max_speed_up_ms t'25
    let t'27 ← PMem.ldU64 (this + 24)
    let t'28 ← AC_PosControl.get_max_speed_down_ms t'27
    let t'29 ← AC_WPNav.get_wp_acceleration_mss this
    let t'30 ← AC_WPNav.get_accel_D_mss this
    let t'31 ← AC_WPNav.get_corner_acceleration_mss this
    let t'32 ← PMem.ldF32 (this + 1968)
    let t'33 ← PMem.ldF32 (this + 1964)
    SCurve.calculate_track (this + 716) (this + 2408) (this + 2432) arc_rad t'24 t'26 t'28 t'29 t'30 t'31 t'32 t'33
    let t'34 ← is_zero origin_speed_m
    if !t'34 then
      let t'35 ← SCurve.set_origin_speed_max (this + 716) origin_speed_m
      discard <| pure (t'35)
  PMem.stB (this + 2392) false
  PMem.stB (this + 2394) false
  SCurve.init (this + 1340)
  Vector3'double.zero (this + 2456)
  let t'36 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 1 1 (UInt8.toUInt64 (t'36))
  let t'37 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 0 1 (UInt8.toUInt64 (t'37))
  return true

def AC_WPNav.set_wp_destination_NED_m (this : UInt64) (destination_ned_m : UInt64) (is_terrain_alt : Bool) (arc_rad : Binary32) : PMem.M Bool := do
  let fp ← PMem.enter 60
  let r ← AC_WPNav.set_wp_destination_NED_m.body fp this destination_ned_m is_terrain_alt arc_rad
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::get_vector_NED_m : bool (const Location &, Vector3p &, bool &)`, `AC_WPNav.cpp:1036-1066`. -/
def AC_WPNav.get_vector_NED_m.body (fp : UInt64) (this : UInt64) (loc : UInt64) (pos_from_origin_ned_m : UInt64) (is_terrain_alt : UInt64) : PMem.M Bool := do
  Vector2'double.Vector2'3 (fp + 0)
  let t'1 ← Location.get_vector_xy_from_origin_NE_m'Vector2_double loc (fp + 0)
  if !t'1 then
    return false
  let t'2 ← Location.get_alt_frame loc
  if (t'2 == (3 : Int32)) then
    let t'3 ← Location.get_alt_m loc (3 : Int32) (fp + 16)
    if !t'3 then
      return false
    let t'4 ← PMem.ldF32 (fp + 16)
    let t'5 := Binary32.toBinary64 ((-t'4))
    PMem.stF64 (pos_from_origin_ned_m + 16) t'5
    PMem.stB is_terrain_alt true
  else
    PMem.stB is_terrain_alt false
    let t'6 ← Location.get_alt_m loc (2 : Int32) (fp + 24)
    if !t'6 then
      return false
    let t'7 ← PMem.ldF32 (fp + 24)
    let t'8 := Binary32.toBinary64 ((-t'7))
    PMem.stF64 (pos_from_origin_ned_m + 16) t'8
    PMem.stB is_terrain_alt false
  let t'9 ← Vector3'double.xy pos_from_origin_ned_m
  discard <| PMem.memcpy t'9 (fp + 0) 16
  discard <| pure (t'9)
  return true

def AC_WPNav.get_vector_NED_m (this : UInt64) (loc : UInt64) (pos_from_origin_ned_m : UInt64) (is_terrain_alt : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 28
  let r ← AC_WPNav.get_vector_NED_m.body fp this loc pos_from_origin_ned_m is_terrain_alt
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::set_wp_destination_loc : bool (const Location &, float)`, `AC_WPNav.cpp:323-335`. -/
def AC_WPNav.set_wp_destination_loc.body (fp : UInt64) (this : UInt64) (destination : UInt64) (arc_rad : Binary32) : PMem.M Bool := do
  let mut arc_rad := arc_rad
  Vector3'double.Vector3 (fp + 8)
  let t'1 ← AC_WPNav.get_vector_NED_m this destination (fp + 8) (fp + 0)
  if !t'1 then
    return false
  let t'2 ← PMem.ldB (fp + 0)
  let t'3 ← AC_WPNav.set_wp_destination_NED_m this (fp + 8) t'2 arc_rad
  return t'3

def AC_WPNav.set_wp_destination_loc (this : UInt64) (destination : UInt64) (arc_rad : Binary32) : PMem.M Bool := do
  let fp ← PMem.enter 32
  let r ← AC_WPNav.set_wp_destination_loc.body fp this destination arc_rad
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::get_wp_destination_loc : bool (Location &) const`, `AC_WPNav.cpp:358-368`. -/
def AC_WPNav.get_wp_destination_loc.body (fp : UInt64) (this : UInt64) (destination : UInt64) : PMem.M Bool := do
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_origin'1 t'1 destination
  if !t'2 then
    return false
  let t'3 ← AC_WPNav.get_wp_destination_NED_m this
  let t'4 ← PMem.ldB (this + 2493)
  let mut c'5 : Int32 := default
  if t'4 then
    c'5 := (3 : Int32)
  else
    c'5 := (2 : Int32)
  Location.from_ekf_offset_NED_m (fp + 0) t'3 c'5
  let t'6 := (fp + 0)
  discard <| PMem.memcpy destination t'6 16
  discard <| pure (destination)
  return true

def AC_WPNav.get_wp_destination_loc (this : UInt64) (destination : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← AC_WPNav.get_wp_destination_loc.body fp this destination
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::update_track_with_speed_accel_limits : void ()`, `AC_WPNav.cpp:660-677`. -/
def AC_WPNav.update_track_with_speed_accel_limits (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 2392)
  if t'1 then
    let t'2 ← PMem.ldU64 (this + 24)
    let t'3 ← AC_PosControl.NE_get_max_speed_ms t'2
    let t'4 ← PMem.ldU64 (this + 24)
    let t'5 ← AC_PosControl.get_max_speed_up_ms t'4
    let t'6 ← PMem.ldU64 (this + 24)
    let t'7 ← AC_PosControl.get_max_speed_down_ms t'6
    let t'8 ← AC_WPNav.get_wp_acceleration_mss this
    let t'9 ← AC_WPNav.get_accel_D_mss this
    SplineCurve.set_speed_accel (this + 1976) t'3 t'5 t'7 t'8 t'9
  else
    let t'10 ← PMem.ldU64 (this + 24)
    let t'11 ← AC_PosControl.NE_get_max_speed_ms t'10
    let t'12 ← PMem.ldU64 (this + 24)
    let t'13 ← AC_PosControl.get_max_speed_up_ms t'12
    let t'14 ← PMem.ldU64 (this + 24)
    let t'15 ← AC_PosControl.get_max_speed_down_ms t'14
    SCurve.set_speed_max (this + 716) t'11 t'13 t'15
  let t'16 ← PMem.ldB (this + 2393)
  if t'16 then
    let t'17 ← PMem.ldU64 (this + 24)
    let t'18 ← AC_PosControl.NE_get_max_speed_ms t'17
    let t'19 ← PMem.ldU64 (this + 24)
    let t'20 ← AC_PosControl.get_max_speed_up_ms t'19
    let t'21 ← PMem.ldU64 (this + 24)
    let t'22 ← AC_PosControl.get_max_speed_down_ms t'21
    let t'23 ← AC_WPNav.get_wp_acceleration_mss this
    let t'24 ← AC_WPNav.get_accel_D_mss this
    SplineCurve.set_speed_accel (this + 2184) t'18 t'20 t'22 t'23 t'24
  else
    let t'25 ← PMem.ldU64 (this + 24)
    let t'26 ← AC_PosControl.NE_get_max_speed_ms t'25
    let t'27 ← PMem.ldU64 (this + 24)
    let t'28 ← AC_PosControl.get_max_speed_up_ms t'27
    let t'29 ← PMem.ldU64 (this + 24)
    let t'30 ← AC_PosControl.get_max_speed_down_ms t'29
    SCurve.set_speed_max (this + 1340) t'26 t'28 t'30
  return ()

/-- C++ `AC_WPNav::set_speed_up_ms : void (float)`, `AC_WPNav.cpp:299-306`. -/
def AC_WPNav.set_speed_up_ms (this : UInt64) (speed_up_ms : Binary32) : PMem.M Unit := do
  let mut speed_up_ms := speed_up_ms
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← AC_PosControl.get_max_speed_down_ms t'1
  let t'3 ← PMem.ldU64 (this + 24)
  let t'4 ← AC_PosControl.D_get_max_accel_mss t'3
  let t'5 ← PMem.ldU64 (this + 24)
  AC_PosControl.D_set_max_speed_accel_m t'5 t'2 speed_up_ms t'4
  AC_WPNav.update_track_with_speed_accel_limits this
  return ()

/-- C++ `AC_WPNav::set_speed_down_ms : void (float)`, `AC_WPNav.cpp:310-317`. -/
def AC_WPNav.set_speed_down_ms (this : UInt64) (speed_down_ms : Binary32) : PMem.M Unit := do
  let mut speed_down_ms := speed_down_ms
  let t'1 ← PMem.ldU64 (this + 24)
  let t'2 ← AC_PosControl.get_max_speed_up_ms t'1
  let t'3 ← PMem.ldU64 (this + 24)
  let t'4 ← AC_PosControl.D_get_max_accel_mss t'3
  let t'5 ← PMem.ldU64 (this + 24)
  AC_PosControl.D_set_max_speed_accel_m t'5 speed_down_ms t'2 t'4
  AC_WPNav.update_track_with_speed_accel_limits this
  return ()

/-- C++ `AC_WPNav::set_wp_destination_next_NED_m : bool (const Vector3p &, bool, float)`, `AC_WPNav.cpp:487-514`. -/
def AC_WPNav.set_wp_destination_next_NED_m (this : UInt64) (destination_ned_m : UInt64) (is_terrain_alt : Bool) (arc_rad : Binary32) : PMem.M Bool := do
  let mut is_terrain_alt := is_terrain_alt
  let mut arc_rad := arc_rad
  let t'1 ← PMem.ldB (this + 2493)
  if ((if is_terrain_alt then (1 : Int32) else (0 : Int32)) != (if t'1 then (1 : Int32) else (0 : Int32))) then
    return true
  let t'2 ← PMem.ldU64 (this + 24)
  let t'3 ← AC_PosControl.NE_get_max_speed_ms t'2
  let t'4 ← PMem.ldU64 (this + 24)
  let t'5 ← AC_PosControl.get_max_speed_up_ms t'4
  let t'6 ← PMem.ldU64 (this + 24)
  let t'7 ← AC_PosControl.get_max_speed_down_ms t'6
  let t'8 ← AC_WPNav.get_wp_acceleration_mss this
  let t'9 ← AC_WPNav.get_accel_D_mss this
  let t'10 ← AC_WPNav.get_corner_acceleration_mss this
  let t'11 ← PMem.ldF32 (this + 1968)
  let t'12 ← PMem.ldF32 (this + 1964)
  SCurve.calculate_track (this + 1340) (this + 2432) destination_ned_m arc_rad t'3 t'5 t'7 t'8 t'9 t'10 t'11 t'12
  let t'13 ← PMem.ldB (this + 2392)
  if t'13 then
    let t'14 ← SplineCurve.get_destination_speed_max (this + 1976)
    let mut this_leg_dest_speed_max_ms : Binary32 := t'14
    let t'15 ← SCurve.set_origin_speed_max (this + 1340) this_leg_dest_speed_max_ms
    let mut next_leg_origin_speed_max_ms : Binary32 := t'15
    SplineCurve.set_destination_speed_max (this + 1976) next_leg_origin_speed_max_ms
  PMem.stB (this + 2393) false
  let t'16 := if true then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 1 1 (UInt8.toUInt64 (t'16))
  discard <| PMem.memcpy (this + 2456) destination_ned_m 24
  discard <| pure ((this + 2456))
  return true

/-- C++ `AC_WPNav::set_wp_destination_next_loc : bool (const Location &, float)`, `AC_WPNav.cpp:341-353`. -/
def AC_WPNav.set_wp_destination_next_loc.body (fp : UInt64) (this : UInt64) (destination : UInt64) (arc_rad : Binary32) : PMem.M Bool := do
  let mut arc_rad := arc_rad
  Vector3'double.Vector3 (fp + 8)
  let t'1 ← AC_WPNav.get_vector_NED_m this destination (fp + 8) (fp + 0)
  if !t'1 then
    return false
  let t'2 ← PMem.ldB (fp + 0)
  let t'3 ← AC_WPNav.set_wp_destination_next_NED_m this (fp + 8) t'2 arc_rad
  return t'3

def AC_WPNav.set_wp_destination_next_loc (this : UInt64) (destination : UInt64) (arc_rad : Binary32) : PMem.M Bool := do
  let fp ← PMem.enter 32
  let r ← AC_WPNav.set_wp_destination_next_loc.body fp this destination arc_rad
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::set_spline_destination_next_loc : bool (const Location &, const Location &, bool)`, `AC_WPNav.cpp:879-897`. -/
def AC_WPNav.set_spline_destination_next_loc.body (fp : UInt64) (this : UInt64) (next_destination : UInt64) (next_next_destination : UInt64) (next_next_is_spline : Bool) : PMem.M Bool := do
  let mut next_next_is_spline := next_next_is_spline
  Vector3'double.Vector3 (fp + 0)
  let t'1 ← AC_WPNav.get_vector_NED_m this next_destination (fp + 0) (fp + 24)
  if !t'1 then
    return false
  Vector3'double.Vector3 (fp + 32)
  let t'2 ← AC_WPNav.get_vector_NED_m this next_next_destination (fp + 32) (fp + 56)
  if !t'2 then
    return false
  let t'3 ← PMem.ldB (fp + 24)
  let t'4 ← PMem.ldB (fp + 56)
  let t'5 ← AC_WPNav.set_spline_destination_next_NED_m this (fp + 0) t'3 (fp + 32) t'4 next_next_is_spline
  return t'5

def AC_WPNav.set_spline_destination_next_loc (this : UInt64) (next_destination : UInt64) (next_next_destination : UInt64) (next_next_is_spline : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 57
  let r ← AC_WPNav.set_spline_destination_next_loc.body fp this next_destination next_next_destination next_next_is_spline
  PMem.leave fp
  return r

/-- C++ `AC_Circle::set_center : void (const Location &)`, `AC_Circle.cpp:133-161`. -/
def AC_Circle.set_center.body (fp : UInt64) (this : UInt64) (center : UInt64) : PMem.M Unit := do
  let t'1 ← Location.get_alt_frame center
  if (t'1 == (3 : Int32)) then
    Vector2'double.Vector2'3 (fp + 0)
    let t'2 ← Location.get_vector_xy_from_origin_NE_m'Vector2_double center (fp + 0)
    let mut sc'4 := t'2
    if sc'4 then
      let t'3 ← Location.get_alt_m center (3 : Int32) (fp + 16)
      sc'4 := t'3
    if sc'4 then
      let t'5 ← PMem.ldF64 (fp + 0)
      let t'6 ← PMem.ldF64 ((fp + 0) + 8)
      let t'7 ← PMem.ldF32 (fp + 16)
      Vector3'double.Vector3'3 (fp + 24) t'5 t'6 (Binary32.toBinary64 ((-t'7)))
      AC_Circle.set_center_NED_m this (fp + 24) true
    else
      let t'8 ← PMem.ldU64 (this + 8)
      let t'9 ← AC_PosControl.get_pos_estimate_NED_m t'8
      AC_Circle.set_center_NED_m this t'9 false
  else
    Vector3'double.Vector3 (fp + 48)
    let t'10 ← Location.get_vector_from_origin_NED_m'Vector3_double center (fp + 48)
    if !t'10 then
      let t'11 ← PMem.ldU64 (this + 8)
      let t'12 ← AC_PosControl.get_pos_estimate_NED_m t'11
      discard <| PMem.memcpy (fp + 48) t'12 24
      discard <| pure ((fp + 48))
    AC_Circle.set_center_NED_m this (fp + 48) false
  return ()

def AC_Circle.set_center (this : UInt64) (center : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 72
  let r ← AC_Circle.set_center.body fp this center
  PMem.leave fp
  return r

/-- C++ `AC_Circle::get_closest_point_on_circle_NED_m : void (Vector3p &, float &) const`, `AC_Circle.cpp:308-340`. -/
def AC_Circle.get_closest_point_on_circle_NED_m.body (fp : UInt64) (this : UInt64) (result_ned_m : UInt64) (dist_to_edge_m : UInt64) : PMem.M Unit := do
  Vector3'double.Vector3 (fp + 0)
  let t'1 ← Vector3'double.xy (fp + 0)
  let t'2 ← PMem.ldU64 (this + 8)
  AC_PosControl.get_stopping_point_NE_m t'2 t'1
  let t'3 ← PMem.ldU64 (this + 8)
  AC_PosControl.get_stopping_point_D_m t'3 ((fp + 0) + 16)
  Vector3'double.operator_ (fp + 0) (fp + 40) (this + 32)
  let t'4 := (fp + 40)
  Vector3'double.tofloat t'4 (fp + 64)
  let t'5 := (fp + 64)
  Vector3'float.Vector3'3 (fp + 24) t'5
  let t'6 ← PMem.ldF32 (this + 56)
  let t'7 ← is_positive'float t'6
  if !t'7 then
    discard <| PMem.memcpy result_ned_m (this + 32) 24
    discard <| pure (result_ned_m)
    let t'8 := Int32.toBinary32 ((0 : Int32))
    PMem.stF32 dist_to_edge_m t'8
    return ()
  let t'9 ← Vector3'float.length_squared (fp + 24)
  let mut dist_to_center_m_sq : Binary32 := t'9
  let t'10 ← sq (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/)))
  if (decide (dist_to_center_m_sq < t'10)) then
    let t'11 ← PMem.ldF64 (this + 32)
    let t'12 ← PMem.ldF32 (this + 56)
    let t'13 ← PMem.ldU64 this
    let t'14 ← VehicleBridge.AP_AHRS_View.cos_yaw'0 t'13
    let t'15 := (t'11 - (Binary32.toBinary64 ((t'12 * t'14))))
    PMem.stF64 result_ned_m t'15
    let t'16 ← PMem.ldF64 ((this + 32) + 8)
    let t'17 ← PMem.ldF32 (this + 56)
    let t'18 ← PMem.ldU64 this
    let t'19 ← VehicleBridge.AP_AHRS_View.sin_yaw'0 t'18
    let t'20 := (t'16 - (Binary32.toBinary64 ((t'17 * t'19))))
    PMem.stF64 (result_ned_m + 8) t'20
    let t'21 ← PMem.ldF64 ((this + 32) + 16)
    PMem.stF64 (result_ned_m + 16) t'21
    Vector3'double.operator_ (fp + 0) (fp + 80) result_ned_m
    let t'22 := (fp + 80)
    let t'23 ← Vector3'double.length t'22
    let t'24 := Binary64.toBinary32 (t'23)
    PMem.stF32 dist_to_edge_m t'24
    return ()
  let t'25 ← Vector3'float.xy (fp + 24)
  let t'26 ← Vector2'float.length t'25
  let mut dist_to_center_m_xy : Binary32 := t'26
  let t'27 ← PMem.ldF64 (this + 32)
  let t'28 ← PMem.ldF32 (fp + 24)
  let t'29 ← PMem.ldF32 (this + 56)
  let t'30 := (t'27 + (Binary32.toBinary64 (((t'28 / dist_to_center_m_xy) * t'29))))
  PMem.stF64 result_ned_m t'30
  let t'31 ← PMem.ldF64 ((this + 32) + 8)
  let t'32 ← PMem.ldF32 ((fp + 24) + 4)
  let t'33 ← PMem.ldF32 (this + 56)
  let t'34 := (t'31 + (Binary32.toBinary64 (((t'32 / dist_to_center_m_xy) * t'33))))
  PMem.stF64 (result_ned_m + 8) t'34
  let t'35 ← PMem.ldF64 ((this + 32) + 16)
  PMem.stF64 (result_ned_m + 16) t'35
  Vector3'double.operator_ (fp + 0) (fp + 104) result_ned_m
  let t'36 := (fp + 104)
  let t'37 ← Vector3'double.length t'36
  let t'38 := Binary64.toBinary32 (t'37)
  PMem.stF32 dist_to_edge_m t'38
  return ()

def AC_Circle.get_closest_point_on_circle_NED_m (this : UInt64) (result_ned_m : UInt64) (dist_to_edge_m : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 128
  let r ← AC_Circle.get_closest_point_on_circle_NED_m.body fp this result_ned_m dist_to_edge_m
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::set_spline_destination_NED_m : bool (const Vector3p &, bool, const Vector3p &, bool, bool)`, `AC_WPNav.cpp:903-977`. -/
def AC_WPNav.set_spline_destination_NED_m.body (fp : UInt64) (this : UInt64) (destination_ned_m : UInt64) (is_terrain_alt : Bool) (next_destination_ned_m : UInt64) (next_is_terrain_alt : Bool) (next_is_spline : Bool) : PMem.M Bool := do
  let mut is_terrain_alt := is_terrain_alt
  let mut next_is_terrain_alt := next_is_terrain_alt
  let mut next_is_spline := next_is_spline
  let t'1 ← AC_WPNav.is_active this
  let mut sc'3 := !t'1
  if !sc'3 then
    let t'2 ← PMem.ldBits (this + 8) 0 1
    sc'3 := !((UInt64.toUInt8 (t'2)) != (0 : UInt8))
  if sc'3 then
    let t'4 ← PMem.ldF32 (this + 2400)
    Vector3'double.Vector3 (fp + 24)
    Vector3'double.Vector3'2 (fp + 0) (fp + 24)
    AC_WPNav.wp_and_spline_init_m this t'4 (fp + 0)
  let t'5 ← PMem.ldU64 (this + 24)
  let t'6 ← AC_PosControl.NE_get_max_speed_ms t'5
  let t'7 ← PMem.ldU64 (this + 24)
  let t'8 ← AC_PosControl.get_max_speed_up_ms t'7
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← AC_PosControl.get_max_speed_down_ms t'9
  let t'11 ← PMem.ldU64 (this + 24)
  let t'12 ← AC_PosControl.NE_get_max_accel_mss t'11
  let t'13 ← PMem.ldU64 (this + 24)
  let t'14 ← AC_PosControl.D_get_max_accel_mss t'13
  SplineCurve.set_speed_accel (this + 1976) t'6 t'8 t'10 t'12 t'14
  Vector3'float.Vector3'2 (fp + 48)
  let t'15 ← PMem.ldB (this + 2493)
  if ((if is_terrain_alt then (1 : Int32) else (0 : Int32)) == (if t'15 then (1 : Int32) else (0 : Int32))) then
    let t'16 ← PMem.ldBits (this + 8) 1 1
    if (UInt64.toUInt8 (t'16)) != (0 : UInt8) then
      let t'17 ← PMem.ldB (this + 2392)
      if t'17 then
        let t'18 ← SplineCurve.get_destination_vel (this + 1976)
        discard <| PMem.memcpy (fp + 48) t'18 12
        discard <| pure ((fp + 48))
      else
        Vector3'double.operator_ (this + 2432) (fp + 64) (this + 2408)
        let t'19 := (fp + 64)
        Vector3'double.tofloat t'19 (fp + 88)
        let t'20 := (fp + 88)
        discard <| PMem.memcpy (fp + 48) t'20 12
        discard <| pure ((fp + 48))
    discard <| PMem.memcpy (this + 2408) (this + 2432) 24
    discard <| pure ((this + 2408))
  else
    discard <| PMem.memcpy (this + 2408) (this + 2432) 24
    discard <| pure ((this + 2408))
    let t'21 ← AC_WPNav.get_terrain_D_m this (fp + 104)
    if !t'21 then
      return false
    if is_terrain_alt then
      let t'22 := ((this + 2408) + 16)
      let t'23 ← PMem.ldF64 t'22
      let t'24 ← PMem.ldF32 (fp + 104)
      let t'25 := (t'23 - (Binary32.toBinary64 (t'24)))
      PMem.stF64 t'22 t'25
      let t'26 ← PMem.ldF32 (fp + 104)
      let t'27 ← PMem.ldU64 (this + 24)
      AC_PosControl.init_pos_terrain_D_m t'27 t'26
    else
      let t'28 := ((this + 2408) + 16)
      let t'29 ← PMem.ldF64 t'28
      let t'30 ← PMem.ldF32 (fp + 104)
      let t'31 := (t'29 + (Binary32.toBinary64 (t'30)))
      PMem.stF64 t'28 t'31
      let t'32 ← PMem.ldU64 (this + 24)
      AC_PosControl.init_pos_terrain_D_m t'32 (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
  discard <| PMem.memcpy (this + 2432) destination_ned_m 24
  discard <| pure ((this + 2432))
  PMem.stB (this + 2493) is_terrain_alt
  Vector3'float.Vector3'2 (fp + 112)
  if ((if is_terrain_alt then (1 : Int32) else (0 : Int32)) == (if next_is_terrain_alt then (1 : Int32) else (0 : Int32))) then
    if next_is_spline then
      Vector3'double.operator_ next_destination_ned_m (fp + 128) (this + 2408)
      let t'33 := (fp + 128)
      Vector3'double.tofloat t'33 (fp + 152)
      let t'34 := (fp + 152)
      discard <| PMem.memcpy (fp + 112) t'34 12
      discard <| pure ((fp + 112))
    else
      Vector3'double.operator_ next_destination_ned_m (fp + 168) (this + 2432)
      let t'35 := (fp + 168)
      Vector3'double.tofloat t'35 (fp + 192)
      let t'36 := (fp + 192)
      discard <| PMem.memcpy (fp + 112) t'36 12
      discard <| pure ((fp + 112))
  let t'37 ← Vector3'float.is_zero (fp + 112)
  let t'38 := if (!t'37) then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 1 1 (UInt8.toUInt64 (t'38))
  SplineCurve.set_origin_and_destination (this + 1976) (this + 2408) (this + 2432) (fp + 48) (fp + 112)
  PMem.stB (this + 2392) true
  PMem.stB (this + 2394) false
  let t'39 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 0 1 (UInt8.toUInt64 (t'39))
  return true

def AC_WPNav.set_spline_destination_NED_m (this : UInt64) (destination_ned_m : UInt64) (is_terrain_alt : Bool) (next_destination_ned_m : UInt64) (next_is_terrain_alt : Bool) (next_is_spline : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 204
  let r ← AC_WPNav.set_spline_destination_NED_m.body fp this destination_ned_m is_terrain_alt next_destination_ned_m next_is_terrain_alt next_is_spline
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::set_spline_destination_loc : bool (const Location &, const Location &, bool)`, `AC_WPNav.cpp:856-874`. -/
def AC_WPNav.set_spline_destination_loc.body (fp : UInt64) (this : UInt64) (destination : UInt64) (next_destination : UInt64) (next_is_spline : Bool) : PMem.M Bool := do
  let mut next_is_spline := next_is_spline
  Vector3'double.Vector3 (fp + 0)
  let t'1 ← AC_WPNav.get_vector_NED_m this destination (fp + 0) (fp + 24)
  if !t'1 then
    return false
  Vector3'double.Vector3 (fp + 32)
  let t'2 ← AC_WPNav.get_vector_NED_m this next_destination (fp + 32) (fp + 56)
  if !t'2 then
    return false
  let t'3 ← PMem.ldB (fp + 24)
  let t'4 ← PMem.ldB (fp + 56)
  let t'5 ← AC_WPNav.set_spline_destination_NED_m this (fp + 0) t'3 (fp + 32) t'4 next_is_spline
  return t'5

def AC_WPNav.set_spline_destination_loc (this : UInt64) (destination : UInt64) (next_destination : UInt64) (next_is_spline : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 57
  let r ← AC_WPNav.set_spline_destination_loc.body fp this destination next_destination next_is_spline
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::set_speed_NE_ms : void (float)`, `AC_WPNav.cpp:278-295`. -/
def AC_WPNav.set_speed_NE_ms (this : UInt64) (speed_ms : Binary32) : PMem.M Unit := do
  let mut speed_ms := speed_ms
  let mut sc'3 := (decide (speed_ms ≥ (Binary32.ofBits 0x3c23d70a /- 999999977/100000000000 -/)))
  if sc'3 then
    let t'1 ← PMem.ldF32 (this + 2400)
    let t'2 ← is_positive'float t'1
    sc'3 := t'2
  if sc'3 then
    let t'4 ← PMem.ldF32 (this + 2484)
    let t'5 ← PMem.ldF32 (this + 2400)
    let t'6 := ((speed_ms * t'4) / t'5)
    PMem.stF32 (this + 2484) t'6
    PMem.stF32 (this + 2400) speed_ms
    let t'7 ← PMem.ldF32 (this + 2400)
    let t'8 ← AC_WPNav.get_wp_acceleration_mss this
    let t'9 ← PMem.ldU64 (this + 24)
    AC_PosControl.NE_set_max_speed_accel_m t'9 t'7 t'8
    let t'10 ← PMem.ldF32 (this + 2400)
    let t'11 ← AC_WPNav.get_wp_acceleration_mss this
    let t'12 ← PMem.ldU64 (this + 24)
    AC_PosControl.NE_set_correction_speed_accel_m t'12 t'10 t'11
    AC_WPNav.update_track_with_speed_accel_limits this
  return ()

/-- C++ `AC_Circle::init : void ()`, `AC_Circle.cpp:97-128`. -/
def AC_Circle.init (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 16)
  let t'2 ← PMem.ldF32 t'1
  PMem.stF32 (this + 56) t'2
  let t'3 ← PMem.ldF32 (this + 56)
  PMem.stF32 (this + 92) t'3
  let t'4 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'5 ← PMem.ldF32 t'4
  let t'6 ← radians t'5
  PMem.stF32 (this + 60) t'6
  let t'7 ← PMem.ldU64 (this + 8)
  AC_PosControl.NE_init_controller_stopping_point t'7
  let t'8 ← PMem.ldU64 (this + 8)
  AC_PosControl.D_init_controller_stopping_point t'8
  let t'9 ← PMem.ldU64 (this + 8)
  let t'10 ← AC_PosControl.get_pos_desired_NED_m t'9
  let stopping_point_ned_m : UInt64 := t'10
  discard <| PMem.memcpy (this + 32) stopping_point_ned_m 24
  discard <| pure ((this + 32))
  let t'11 ← AP_ParamTBase'unsigned_short_2.get (this + 24)
  let t'12 ← PMem.ldU16 t'11
  if (((UInt32.toInt32 (UInt16.toUInt32 (t'12))) &&& (UInt32.toInt32 ((4 : UInt32)))) == (0 : Int32)) then
    let t'13 := (this + 32)
    let t'14 ← PMem.ldF64 t'13
    let t'15 ← PMem.ldF32 (this + 56)
    let t'16 ← PMem.ldU64 this
    let t'17 ← VehicleBridge.AP_AHRS_View.cos_yaw'0 t'16
    let t'18 := (t'14 + (Binary32.toBinary64 ((t'15 * t'17))))
    PMem.stF64 t'13 t'18
    let t'19 := ((this + 32) + 8)
    let t'20 ← PMem.ldF64 t'19
    let t'21 ← PMem.ldF32 (this + 56)
    let t'22 ← PMem.ldU64 this
    let t'23 ← VehicleBridge.AP_AHRS_View.sin_yaw'0 t'22
    let t'24 := (t'20 + (Binary32.toBinary64 ((t'21 * t'23))))
    PMem.stF64 t'19 t'24
  PMem.stB (this + 96) false
  AC_Circle.calc_velocities this true
  AC_Circle.init_start_angle this true
  return ()

/-- C++ `AC_Loiter::get_angle_max_rad : float () const`, `AC_Loiter.cpp:235-243`. -/
def AC_Loiter.get_angle_max_rad.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  discard <| PMem.memcpy (fp + 0) (this + 24) 4
  let t'1 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if !t'1 then
    let t'2 ← PMem.ldU64 (this + 16)
    let t'3 ← AC_AttitudeControl.lean_angle_max_rad t'2
    PMem.stF32 (fp + 4) t'3
    let t'4 ← PMem.ldU64 (this + 8)
    let t'5 ← AC_PosControl.get_lean_angle_max_rad t'4
    PMem.stF32 (fp + 8) t'5
    let t'6 ← MIN'float_float (fp + 4) (fp + 8)
    let t'7 ← PMem.ldF32 t'6
    return (t'7 * ((Binary32.ofBits 0x40000000 /- 2 -/) / (Binary32.ofBits 0x40400000 /- 3 -/)))
  let t'8 ← AP_ParamT'float_4.operator_const_float__'1 (this + 24)
  let t'9 ← PMem.ldF32 t'8
  let t'10 ← radians t'9
  PMem.stF32 (fp + 12) t'10
  let t'11 ← PMem.ldU64 (this + 8)
  let t'12 ← AC_PosControl.get_lean_angle_max_rad t'11
  PMem.stF32 (fp + 16) t'12
  let t'13 ← MIN'float_float (fp + 12) (fp + 16)
  let t'14 ← PMem.ldF32 t'13
  return t'14

def AC_Loiter.get_angle_max_rad (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 20
  let r ← AC_Loiter.get_angle_max_rad.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_Loiter::sanity_check_params : void ()`, `AC_Loiter.cpp:303-310`. -/
def AC_Loiter.sanity_check_params.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stF32 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x3fc999999999999a /- 20000000000000001/100000000000000000 -/)))
  let t'1 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 28) (fp + 0)
  AP_ParamTBase'float_4.set (this + 28) t'1
  let t'2 ← PMem.ldU64 (this + 16)
  let t'3 ← AC_AttitudeControl.lean_angle_max_rad t'2
  PMem.stF32 (fp + 4) ((Binary32.ofBits 0x411ce80a /- 122583127/12500000 -/) * (Musl.tanf.tanf t'3))
  let t'4 ← MIN'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 32) (fp + 4)
  AP_ParamTBase'float_4.set (this + 32) t'4
  return ()

def AC_Loiter.sanity_check_params (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← AC_Loiter.sanity_check_params.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_Loiter::init_target : void ()`, `AC_Loiter.cpp:136-154`. -/
def AC_Loiter.init_target (this : UInt64) : PMem.M Unit := do
  AC_Loiter.sanity_check_params this
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 32)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← PMem.ldU64 (this + 8)
  AC_PosControl.NE_set_correction_speed_accel_m t'3 (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) t'2
  let t'4 ← PMem.ldU64 (this + 8)
  AC_PosControl.NE_set_pos_error_max_m t'4 (Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/)))
  let t'5 ← PMem.ldU64 (this + 8)
  AC_PosControl.NE_relax_velocity_controller t'5
  let t'6 ← PMem.ldU64 (this + 8)
  let t'7 ← AC_PosControl.get_accel_target_NED_mss t'6
  let t'8 ← Vector3'float.xy t'7
  discard <| PMem.memcpy (this + 60) t'8 8
  discard <| pure ((this + 60))
  let t'9 ← PMem.ldU64 (this + 8)
  let t'10 ← AC_PosControl.get_roll_rad t'9
  PMem.stF32 (this + 68) t'10
  let t'11 ← PMem.ldU64 (this + 8)
  let t'12 ← AC_PosControl.get_pitch_rad t'11
  PMem.stF32 ((this + 68) + 4) t'12
  Vector2'float.zero (this + 76)
  Vector2'float.zero (this + 84)
  let t'13 := (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (this + 96) t'13
  return ()

/-- C++ `AC_WPNav::get_oa_wp_destination : bool (Location &) const`, `AC_WPNav.h:186-?`. -/
def AC_WPNav.get_oa_wp_destination (this : UInt64) (destination : UInt64) : PMem.M Bool := do
  let t'1 ← AC_WPNav.get_wp_destination_loc this destination
  return t'1

/-- C++ `AC_WPNav::convert_parameters : void ()`, `AC_WPNav.cpp:116-163`. -/
def AC_WPNav.convert_parameters (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.configured (this + 40)
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← AP_Param.configured (this + 52)
    sc'3 := t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← AP_Param.configured (this + 44)
    sc'5 := t'4
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← AP_Param.configured (this + 48)
    sc'7 := t'6
  let mut sc'9 := sc'7
  if !sc'9 then
    let t'8 ← AP_Param.configured (this + 56)
    sc'9 := t'8
  let mut sc'11 := sc'9
  if !sc'11 then
    let t'10 ← AP_Param.configured (this + 64)
    sc'11 := t'10
  let mut sc'13 := sc'11
  if !sc'13 then
    let t'12 ← AP_Param.configured (this + 60)
    sc'13 := t'12
  if sc'13 then
    return ()
  AP_Param.convert_old_parameters_scaled (0xe358 : UInt64) /- &AC_WPNav::convert_parameters(...)::conversion_info -/ (UInt64.toUInt8 (((168 : UInt64) / (24 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- C++ `AC_Loiter::convert_parameters : void ()`, `AC_Loiter.cpp:263-299`. -/
def AC_Loiter.convert_parameters (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.configured (this + 28)
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← AP_Param.configured (this + 32)
    sc'3 := t'2
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← AP_Param.configured (this + 36)
    sc'5 := t'4
  let mut sc'7 := sc'5
  if !sc'7 then
    let t'6 ← AP_Param.configured (this + 40)
    sc'7 := t'6
  if sc'7 then
    return ()
  AP_Param.convert_old_parameters_scaled (0xe460 : UInt64) /- &AC_Loiter::convert_parameters(...)::conversion_info -/ (UInt64.toUInt8 (((96 : UInt64) / (24 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- C++ `AC_Circle::convert_parameters : void ()`, `AC_Circle.cpp:470-488`. -/
def AC_Circle.convert_parameters (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_Param.configured (this + 16)
  if t'1 then
    return ()
  AP_Param.convert_old_parameters_scaled (0xe500 : UInt64) /- &AC_Circle::convert_parameters(...)::conversion_info -/ (UInt64.toUInt8 (((24 : UInt64) / (24 : UInt64)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3f847ae147ae147b /- 1/100 -/))) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  return ()

/-- C++ `AC_WPNav::set_circle_destination_NED_m : bool (const Vector2f &, float, float, bool)`, `AC_WPNav.cpp:442-480`. -/
def AC_WPNav.set_circle_destination_NED_m.body (fp : UInt64) (this : UInt64) (center_ne_m : UInt64) (turns_signed : Binary32) (dest_d_m : Binary32) (is_terrain_alt : Bool) : PMem.M Bool := do
  let mut turns_signed := turns_signed
  let mut dest_d_m := dest_d_m
  let mut is_terrain_alt := is_terrain_alt
  let t'1 ← AC_WPNav.is_active this
  let mut sc'3 := !t'1
  if !sc'3 then
    let t'2 ← PMem.ldBits (this + 8) 0 1
    sc'3 := !((UInt64.toUInt8 (t'2)) != (0 : UInt8))
  if sc'3 then
    let t'4 ← PMem.ldF32 (this + 2400)
    Vector3'double.Vector3 (fp + 24)
    Vector3'double.Vector3'2 (fp + 0) (fp + 24)
    AC_WPNav.wp_and_spline_init_m this t'4 (fp + 0)
  SCurve.init (this + 92)
  discard <| PMem.memcpy (this + 2408) (this + 2432) 24
  discard <| pure ((this + 2408))
  let t'5 ← PMem.ldB (this + 2493)
  let mut sc'7 := ((if is_terrain_alt then (1 : Int32) else (0 : Int32)) != (if t'5 then (1 : Int32) else (0 : Int32)))
  if sc'7 then
    let t'6 ← AC_WPNav.convert_origin_to_alt_frame this is_terrain_alt
    sc'7 := !t'6
  if sc'7 then
    return false
  let mut total_angle_rad : Binary32 := (turns_signed * ((Binary64.toBinary32 ((Binary64.ofBits 0x400921fb54442d18 /- 31415926535897931/10000000000000000 -/))) * (Int32.toBinary32 ((2 : Int32)))))
  let t'8 ← PMem.ldF64 ((this + 2408) + 16)
  let mut climb_d_m : Binary32 := Binary64.toBinary32 (((Binary32.toBinary64 (dest_d_m)) - t'8))
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← AC_PosControl.NE_get_max_speed_ms t'9
  let t'11 ← PMem.ldU64 (this + 24)
  let t'12 ← AC_PosControl.get_max_speed_up_ms t'11
  let t'13 ← PMem.ldU64 (this + 24)
  let t'14 ← AC_PosControl.get_max_speed_down_ms t'13
  let t'15 ← AC_WPNav.get_wp_acceleration_mss this
  let t'16 ← AC_WPNav.get_accel_D_mss this
  let t'17 ← AC_WPNav.get_corner_acceleration_mss this
  let t'18 ← PMem.ldF32 (this + 1968)
  let t'19 ← PMem.ldF32 (this + 1964)
  SCurve.calculate_circle_track (this + 716) (this + 2408) center_ne_m total_angle_rad climb_d_m t'10 t'12 t'14 t'15 t'16 t'17 t'18 t'19
  let t'20 ← SCurve.get_origin_to_destination (this + 716)
  Vector3'float.todouble t'20 (fp + 48)
  let t'21 := (fp + 48)
  Vector3'double.operator_'4 (this + 2408) (fp + 72) t'21
  let t'22 := (fp + 72)
  discard <| PMem.memcpy (this + 2432) t'22 24
  discard <| pure ((this + 2432))
  PMem.stB (this + 2493) is_terrain_alt
  PMem.stB (this + 2392) false
  PMem.stB (this + 2394) true
  SCurve.init (this + 1340)
  Vector3'double.zero (this + 2456)
  let t'23 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 1 1 (UInt8.toUInt64 (t'23))
  let t'24 := if false then (1 : UInt8) else (0 : UInt8)
  PMem.stBits (this + 8) 0 1 (UInt8.toUInt64 (t'24))
  return true

def AC_WPNav.set_circle_destination_NED_m (this : UInt64) (center_ne_m : UInt64) (turns_signed : Binary32) (dest_d_m : Binary32) (is_terrain_alt : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 96
  let r ← AC_WPNav.set_circle_destination_NED_m.body fp this center_ne_m turns_signed dest_d_m is_terrain_alt
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::get_terrain_margin_m : float () const`, `AC_WPNav.h:61-?`. -/
def AC_WPNav.get_terrain_margin_m.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  PMem.stF32 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/)))
  let t'1 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 72) (fp + 0)
  let t'2 ← PMem.ldF32 t'1
  return t'2

def AC_WPNav.get_terrain_margin_m (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 4
  let r ← AC_WPNav.get_terrain_margin_m.body fp this
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::advance_wp_target_along_track : bool (float)`, `AC_WPNav.cpp:557-656`. -/
def AC_WPNav.advance_wp_target_along_track.body (fp : UInt64) (this : UInt64) (dt : Binary32) : PMem.M Bool := do
  let mut dt := dt
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'1 ← PMem.ldB (this + 2493)
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← AC_WPNav.get_terrain_D_m this (fp + 0)
    sc'3 := !t'2
  if sc'3 then
    return false
  let t'4 ← PMem.ldF32 (fp + 0)
  let t'5 ← AC_WPNav.get_terrain_margin_m this
  let t'6 ← PMem.ldU64 (this + 24)
  let t'7 ← AC_PosControl.terrain_scaler_D_m t'6 t'4 t'5
  let mut offset_d_scalar : Binary32 := t'7
  let t'8 ← PMem.ldF32 (fp + 0)
  let t'9 ← PMem.ldU64 (this + 24)
  AC_PosControl.set_pos_terrain_target_D_m t'9 t'8
  let t'10 ← PMem.ldU64 (this + 24)
  let t'11 ← AC_PosControl.get_pos_offset_NED_m t'10
  let psc_pos_offset_ned_m : UInt64 := t'11
  let t'12 ← PMem.ldU64 (this + 24)
  let t'13 ← AC_PosControl.get_pos_estimate_NED_m t'12
  Vector3'double.operator_ t'13 (fp + 32) psc_pos_offset_ned_m
  let t'14 := (fp + 32)
  Vector3'double.Vector3'2 (fp + 8) t'14
  let t'15 := ((fp + 8) + 16)
  let t'16 ← PMem.ldF64 t'15
  let t'17 ← PMem.ldF32 (fp + 0)
  let t'18 := (t'16 - (Binary32.toBinary64 (t'17)))
  PMem.stF64 t'15 t'18
  let t'19 ← PMem.ldU64 (this + 24)
  let t'20 ← AC_PosControl.get_vel_desired_NED_ms t'19
  Vector3'float.Vector3'4 (fp + 56) t'20
  let t'21 := ((fp + 56) + 8)
  let t'22 ← PMem.ldF32 t'21
  let t'23 ← PMem.ldU64 (this + 24)
  let t'24 ← AC_PosControl.get_vel_offset_D_ms t'23
  let t'25 := (t'22 - t'24)
  PMem.stF32 t'21 t'25
  let mut track_dt_scalar : Binary32 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  let t'26 ← Vector3'float.length_squared (fp + 56)
  let t'27 ← is_positive'float t'26
  if t'27 then
    Vector3'float.normalized (fp + 56) (fp + 88)
    let t'28 := (fp + 88)
    Vector3'float.Vector3'3 (fp + 72) t'28
    let t'29 ← PMem.ldU64 (this + 24)
    AC_PosControl.get_pos_error_NED_m t'29 (fp + 104)
    let t'30 := (fp + 104)
    let t'31 ← Vector3'float.dot t'30 (fp + 72)
    let mut track_error_ned_m : Binary32 := t'31
    let t'32 ← PMem.ldU64 (this + 24)
    let t'33 ← AC_PosControl.get_vel_estimate_NED_ms t'32
    let t'34 ← Vector3'float.dot t'33 (fp + 72)
    let mut track_velocity_ned_ms : Binary32 := t'34
    let t'35 ← PMem.ldU64 (this + 24)
    let t'36 ← AC_PosControl.NE_get_pos_p t'35
    let t'37 ← AC_P_2D.kP t'36
    let t'38 ← AP_ParamT'float_4.operator_const_float__'1 t'37
    let t'39 ← PMem.ldF32 t'38
    let t'40 ← Vector3'float.length (fp + 56)
    let t'41 ← constrain_value_line'float ((Binary32.ofBits 0x3d4ccccd /- 500000007/10000000000 -/) + ((track_velocity_ned_ms - (t'39 * track_error_ned_m)) / t'40)) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((589 : Int32)))
    track_dt_scalar := t'41
  let mut vel_dt_scalar : Binary32 := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'42 ← PMem.ldF32 (this + 2400)
  let t'43 ← is_positive'float t'42
  if t'43 then
    let t'44 ← PMem.ldF32 (this + 2488)
    update_vel_accel (this + 2484) t'44 dt (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
    let t'45 ← PMem.ldB (this + 2492)
    let mut c'46 : Binary32 := default
    if !t'45 then
      let t'47 ← PMem.ldF32 (this + 2400)
      c'46 := (t'47 * offset_d_scalar)
    else
      c'46 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
    let mut vel_input_ms : Binary32 := c'46
    let t'48 ← PMem.ldF32 (this + 2484)
    let t'49 ← AC_WPNav.get_wp_acceleration_mss this
    let t'50 ← AC_WPNav.get_wp_acceleration_mss this
    let t'51 ← PMem.ldU64 (this + 24)
    let t'52 ← AC_PosControl.get_shaping_jerk_NE_msss t'51
    shape_vel_accel vel_input_ms (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) t'48 (this + 2488) (-t'49) t'50 t'52 dt true
    let t'53 ← PMem.ldF32 (this + 2484)
    let t'54 ← PMem.ldF32 (this + 2400)
    let t'55 := (t'53 / t'54)
    vel_dt_scalar := t'55
  let mut track_dt_scalar_tc : Binary32 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  discard <| PMem.memcpy (fp + 120) (this + 68) 4
  let t'56 ← is_zero'AP_ParamT_float_AP_PARAM_FLOAT (fp + 120)
  if !t'56 then
    let t'57 ← AC_WPNav.get_wp_acceleration_mss this
    let t'58 ← AP_ParamT'float_4.operator_const_float__'1 (this + 68)
    let t'59 ← PMem.ldF32 t'58
    let t'60 := (t'57 / t'59)
    track_dt_scalar_tc := t'60
  let t'61 := (this + 2480)
  let t'62 ← PMem.ldF32 t'61
  let t'63 ← PMem.ldF32 (this + 2480)
  let t'64 := (t'62 + ((track_dt_scalar - t'63) * (dt / track_dt_scalar_tc)))
  PMem.stF32 t'61 t'64
  Vector3'double.Vector3 (fp + 128)
  Vector3'float.Vector3'2 (fp + 152)
  Vector3'float.Vector3'2 (fp + 168)
  let mut s_finished : Bool := default  -- uninitialized in C
  let t'65 ← PMem.ldB (this + 2392)
  if !t'65 then
    discard <| PMem.memcpy (fp + 128) (this + 2408) 24
    discard <| pure ((fp + 128))
    let t'66 ← AP_ParamT'float_4.operator_const_float__'1 (this + 52)
    let t'67 ← PMem.ldF32 t'66
    let t'68 ← AC_WPNav.get_corner_acceleration_mss this
    let t'69 ← PMem.ldBits (this + 8) 1 1
    let t'70 ← PMem.ldF32 (this + 2480)
    let t'71 ← SCurve.advance_target_along_track (this + 716) (this + 92) (this + 1340) t'67 t'68 ((UInt64.toUInt8 (t'69)) != (0 : UInt8)) ((t'70 * vel_dt_scalar) * dt) (fp + 128) (fp + 152) (fp + 168)
    s_finished := t'71
  else
    discard <| PMem.memcpy (fp + 152) (fp + 56) 12
    discard <| pure ((fp + 152))
    let t'72 ← PMem.ldF32 (this + 2480)
    SplineCurve.advance_target_along_track (this + 1976) ((t'72 * vel_dt_scalar) * dt) (fp + 128) (fp + 152)
    let t'73 ← SplineCurve.reached_destination (this + 1976)
    s_finished := t'73
  Vector3'float.Vector3'2 (fp + 184)
  let t'74 ← Vector3'float.length_squared (fp + 152)
  let t'75 ← is_positive'float t'74
  if t'75 then
    Vector3'float.normalized (fp + 152) (fp + 216)
    let t'76 := (fp + 216)
    Vector3'float.Vector3'3 (fp + 200) t'76
    let t'77 ← PMem.ldF32 (this + 2488)
    Vector3'float.operator_ (fp + 200) (fp + 232) t'77
    let t'78 := (fp + 232)
    let t'79 ← Vector3'float.length (fp + 152)
    Vector3'float.operator_ t'78 (fp + 248) t'79
    let t'80 := (fp + 248)
    let t'81 ← PMem.ldF32 (this + 2400)
    Vector3'float.operator_'3 t'80 (fp + 264) t'81
    let t'82 := (fp + 264)
    discard <| PMem.memcpy (fp + 184) t'82 12
    discard <| pure ((fp + 184))
  let t'83 ← Vector3'float.operator__'2 (fp + 152) vel_dt_scalar
  discard <| pure (t'83)
  let t'84 ← sq vel_dt_scalar
  let t'85 ← Vector3'float.operator__'2 (fp + 168) t'84
  discard <| pure (t'85)
  let t'86 ← Vector3'float.operator__'3 (fp + 168) (fp + 184)
  discard <| pure (t'86)
  let t'87 ← PMem.ldU64 (this + 24)
  AC_PosControl.set_pos_vel_accel_NED_m t'87 (fp + 128) (fp + 152) (fp + 168)
  let t'88 ← PMem.ldBits (this + 8) 0 1
  if !((UInt64.toUInt8 (t'88)) != (0 : UInt8)) then
    if s_finished then
      let t'89 ← PMem.ldBits (this + 8) 1 1
      if (UInt64.toUInt8 (t'89)) != (0 : UInt8) then
        let t'90 := if true then (1 : UInt8) else (0 : UInt8)
        PMem.stBits (this + 8) 0 1 (UInt8.toUInt64 (t'90))
      else
        Vector3'double.operator_ (fp + 8) (fp + 296) (this + 2432)
        let t'91 := (fp + 296)
        Vector3'double.tofloat t'91 (fp + 320)
        let t'92 := (fp + 320)
        Vector3'float.Vector3'3 (fp + 280) t'92
        let t'93 ← Vector3'float.length_squared (fp + 280)
        discard <| PMem.memcpy (fp + 336) (this + 52) 4
        let t'94 ← sq'AP_ParamT_float_AP_PARAM_FLOAT (fp + 336)
        if (decide ((Binary32.toBinary64 (t'93)) ≤ t'94)) then
          let t'95 := if true then (1 : UInt8) else (0 : UInt8)
          PMem.stBits (this + 8) 0 1 (UInt8.toUInt64 (t'95))
  return true

def AC_WPNav.advance_wp_target_along_track (this : UInt64) (dt : Binary32) : PMem.M Bool := do
  let fp ← PMem.enter 340
  let r ← AC_WPNav.advance_wp_target_along_track.body fp this dt
  PMem.leave fp
  return r

/-- C++ `AC_WPNav::update_wpnav : bool ()`, `AC_WPNav.cpp:713-747`. -/
def AC_WPNav.update_wpnav (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 76)
  if t'1 then
    let t'2 ← AP_ParamTBase'float_4.get (this + 40)
    let t'3 ← PMem.ldF32 t'2
    let t'4 ← PMem.ldF32 (this + 80)
    let t'5 ← is_equal'float_float t'3 t'4
    if !t'5 then
      let t'6 ← AC_WPNav.get_default_speed_NE_ms this
      AC_WPNav.set_speed_NE_ms this t'6
      let t'7 ← AP_ParamT'float_4.operator_const_float__'1 (this + 40)
      let t'8 ← PMem.ldF32 t'7
      PMem.stF32 (this + 80) t'8
  let t'9 ← AP_ParamTBase'float_4.get (this + 44)
  let t'10 ← PMem.ldF32 t'9
  let t'11 ← PMem.ldF32 (this + 84)
  let t'12 ← is_equal'float_float t'10 t'11
  if !t'12 then
    let t'13 ← AC_WPNav.get_default_speed_up_ms this
    AC_WPNav.set_speed_up_ms this t'13
    let t'14 ← AP_ParamT'float_4.operator_const_float__'1 (this + 44)
    let t'15 ← PMem.ldF32 t'14
    PMem.stF32 (this + 84) t'15
  let t'16 ← AP_ParamTBase'float_4.get (this + 48)
  let t'17 ← PMem.ldF32 t'16
  let t'18 ← PMem.ldF32 (this + 88)
  let t'19 ← is_equal'float_float t'17 t'18
  if !t'19 then
    let t'20 ← AC_WPNav.get_default_speed_down_ms this
    AC_WPNav.set_speed_down_ms this t'20
    let t'21 ← AP_ParamT'float_4.operator_const_float__'1 (this + 48)
    let t'22 ← PMem.ldF32 t'21
    PMem.stF32 (this + 88) t'22
  let mut ret : Bool := true
  let t'23 ← PMem.ldU64 (this + 24)
  let t'24 ← AC_PosControl.get_dt_s t'23
  let t'25 ← AC_WPNav.advance_wp_target_along_track this t'24
  if !t'25 then
    ret := false
  let t'26 ← PMem.ldU64 (this + 24)
  AC_PosControl.NE_update_controller t'26
  let t'27 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 2396) t'27
  return ret

/-- C++ `AC_Circle::update_ms : bool (float)`, `AC_Circle.cpp:206-286`. -/
def AC_Circle.update_ms.body (fp : UInt64) (this : UInt64) (climb_rate_ms : Binary32) : PMem.M Bool := do
  let mut climb_rate_ms := climb_rate_ms
  AC_Circle.calc_velocities this false
  let t'1 ← PMem.ldU64 (this + 8)
  let t'2 ← AC_PosControl.get_dt_s t'1
  let mut dt : Binary32 := t'2
  let t'3 ← PMem.ldF32 (this + 76)
  let t'4 ← PMem.ldF32 (this + 80)
  if (decide (t'3 < t'4)) then
    let t'5 := (this + 76)
    let t'6 ← PMem.ldF32 t'5
    let t'7 ← PMem.ldF32 (this + 84)
    let t'8 := (t'6 + ((Binary32.abs t'7) * dt))
    PMem.stF32 t'5 t'8
    let t'9 ← MIN'float_float (this + 76) (this + 80)
    let t'10 ← PMem.ldF32 t'9
    PMem.stF32 (this + 76) t'10
  let t'11 ← PMem.ldF32 (this + 76)
  let t'12 ← PMem.ldF32 (this + 80)
  if (decide (t'11 > t'12)) then
    let t'13 := (this + 76)
    let t'14 ← PMem.ldF32 t'13
    let t'15 ← PMem.ldF32 (this + 84)
    let t'16 := (t'14 - ((Binary32.abs t'15) * dt))
    PMem.stF32 t'13 t'16
    let t'17 ← MAX'float_float (this + 76) (this + 80)
    let t'18 ← PMem.ldF32 t'17
    PMem.stF32 (this + 76) t'18
  let t'19 ← PMem.ldF32 (this + 76)
  let mut angle_change_rad : Binary32 := (t'19 * dt)
  let t'20 := (this + 68)
  let t'21 ← PMem.ldF32 t'20
  let t'22 := (t'21 + angle_change_rad)
  PMem.stF32 t'20 t'22
  let t'23 ← PMem.ldF32 (this + 68)
  let t'24 ← wrap_PI'float t'23
  PMem.stF32 (this + 68) t'24
  let t'25 := (this + 72)
  let t'26 ← PMem.ldF32 t'25
  let t'27 := (t'26 + angle_change_rad)
  PMem.stF32 t'25 t'27
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  let t'28 ← PMem.ldB (this + 96)
  let mut sc'30 := t'28
  if sc'30 then
    let t'29 ← AC_Circle.get_terrain_U_m this (fp + 0)
    sc'30 := !t'29
  if sc'30 then
    return false
  let mut target_d_m : Binary32 := default  -- uninitialized in C
  let t'31 ← PMem.ldB (this + 96)
  if t'31 then
    let t'32 ← PMem.ldF64 ((this + 32) + 16)
    let t'33 ← PMem.ldF32 (fp + 0)
    let t'34 := Binary64.toBinary32 ((t'32 - (Binary32.toBinary64 (t'33))))
    target_d_m := t'34
  else
    let t'35 ← PMem.ldU64 (this + 8)
    let t'36 ← AC_PosControl.get_pos_desired_U_m t'35
    let t'37 := -t'36
    target_d_m := t'37
  let t'38 ← PMem.ldF64 (this + 32)
  let t'39 ← PMem.ldF64 ((this + 32) + 8)
  Vector3'double.Vector3'3 (fp + 8) t'38 t'39 (Binary32.toBinary64 (target_d_m))
  let t'40 ← PMem.ldF32 (this + 56)
  let t'41 ← is_zero t'40
  if !t'41 then
    let t'42 ← PMem.ldF64 (fp + 8)
    let t'43 ← PMem.ldF32 (this + 56)
    let t'44 ← PMem.ldF32 (this + 68)
    let t'45 := (t'42 + (Binary32.toBinary64 ((t'43 * (Musl.cosf.cosf (-t'44))))))
    PMem.stF64 (fp + 8) t'45
    let t'46 := ((fp + 8) + 8)
    let t'47 ← PMem.ldF64 t'46
    let t'48 ← PMem.ldF32 (this + 56)
    let t'49 ← PMem.ldF32 (this + 68)
    let t'50 := (t'47 + (Binary32.toBinary64 (((-t'48) * (Musl.sinf.sinf (-t'49))))))
    PMem.stF64 t'46 t'50
    let t'51 ← PMem.ldU64 (this + 8)
    let t'52 ← AC_PosControl.get_pos_desired_NED_m t'51
    let t'53 ← Vector3'double.xy t'52
    Vector2'double.tofloat t'53 (fp + 32)
    let t'54 := (fp + 32)
    let t'55 ← Vector3'double.xy (this + 32)
    Vector2'double.tofloat t'55 (fp + 40)
    let t'56 := (fp + 40)
    let t'57 ← get_bearing_rad t'54 t'56
    PMem.stF32 (this + 64) t'57
    let t'58 ← AP_ParamTBase'unsigned_short_2.get (this + 24)
    let t'59 ← PMem.ldU16 t'58
    if (((UInt32.toInt32 (UInt16.toUInt32 (t'59))) &&& (UInt32.toInt32 ((2 : UInt32)))) != (0 : Int32)) then
      let t'60 := (this + 64)
      let t'61 ← PMem.ldF32 t'60
      let t'62 ← PMem.ldF32 (this + 60)
      let t'63 ← is_positive'float t'62
      let mut c'64 : Binary32 := default
      if t'63 then
        let t'65 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4056800000000000 /- 90 -/)))
        c'64 := -t'65
      else
        let t'66 ← radians (Binary64.toBinary32 ((Binary64.ofBits 0x4056800000000000 /- 90 -/)))
        c'64 := t'66
      let t'67 := (t'61 + c'64)
      PMem.stF32 t'60 t'67
      let t'68 ← PMem.ldF32 (this + 64)
      let t'69 ← wrap_2PI t'68
      PMem.stF32 (this + 64) t'69
  else
    let t'70 ← PMem.ldF32 (this + 68)
    PMem.stF32 (this + 64) t'70
  Vector2'float.Vector2 (fp + 48)
  let t'71 ← Vector3'double.xy (fp + 8)
  let t'72 ← PMem.ldU64 (this + 8)
  AC_PosControl.input_pos_vel_accel_NE_m t'72 t'71 (fp + 48) (fp + 48) true
  let t'73 ← PMem.ldB (this + 96)
  if t'73 then
    PMem.stF32 (fp + 56) (Int32.toBinary32 ((0 : Int32)))
    let t'74 ← PMem.ldF64 ((fp + 8) + 16)
    PMem.stF32 (fp + 64) (Binary64.toBinary32 (t'74))
    let t'75 ← PMem.ldU64 (this + 8)
    AC_PosControl.input_pos_vel_accel_D_m t'75 (fp + 64) (fp + 56) (Int32.toBinary32 ((0 : Int32))) true
  else
    let t'76 ← PMem.ldU64 (this + 8)
    AC_PosControl.D_set_pos_target_from_climb_rate_ms t'76 climb_rate_ms false
  let t'77 ← PMem.ldU64 (this + 8)
  AC_PosControl.NE_update_controller t'77
  let t'78 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 88) t'78
  return true

def AC_Circle.update_ms (this : UInt64) (climb_rate_ms : Binary32) : PMem.M Bool := do
  let fp ← PMem.enter 68
  let r ← AC_Circle.update_ms.body fp this climb_rate_ms
  PMem.leave fp
  return r

/-- C++ `AC_Loiter::calc_desired_velocity : void (bool)`, `AC_Loiter.cpp:320-400`. -/
def AC_Loiter.calc_desired_velocity.body (fp : UInt64) (this : UInt64) (avoidance_on : Bool) : PMem.M Unit := do
  let mut avoidance_on := avoidance_on
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.get_control_ground_speed_limit_ms'0 t'1
  PMem.stF32 (fp + 0) t'2
  let t'3 ← PMem.ldU64 (this + 8)
  let t'4 ← AC_PosControl.get_dt_s t'3
  PMem.stF32 (fp + 8) t'4
  let t'5 ← MIN'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 28) (fp + 0)
  let t'6 ← PMem.ldF32 t'5
  PMem.stF32 (fp + 16) t'6
  PMem.stF32 (fp + 20) (Binary64.toBinary32 ((Binary64.ofBits 0x3fc999999999999a /- 20000000000000001/100000000000000000 -/)))
  let t'7 ← MAX'float_float (fp + 16) (fp + 20)
  let t'8 ← PMem.ldF32 t'7
  PMem.stF32 (fp + 16) t'8
  let t'9 ← PMem.ldF32 (fp + 16)
  let t'10 ← AP_ParamT'float_4.operator_const_float__'1 (this + 28)
  let t'11 ← PMem.ldF32 t'10
  let t'12 ← AC_Loiter.get_angle_max_rad this
  let t'13 ← angle_rad_to_accel_mss t'12
  let mut pilot_acceleration_max_mss : Binary32 := ((t'9 / t'11) * t'13)
  let t'14 ← PMem.ldF32 (fp + 8)
  let t'15 ← is_negative'float t'14
  if t'15 then
    return ()
  let t'16 ← PMem.ldU64 (this + 8)
  let t'17 ← AC_PosControl.get_vel_desired_NED_ms t'16
  let t'18 ← Vector3'float.xy t'17
  Vector2'float.Vector2'4 (fp + 24) t'18
  let t'19 ← PMem.ldF32 (fp + 8)
  Vector2'float.operator_'2 (this + 60) (fp + 32) t'19
  let t'20 := (fp + 32)
  let t'21 ← Vector2'float.operator__ (fp + 24) t'20
  discard <| pure (t'21)
  Vector2'float.Vector2 (fp + 40)
  let t'22 ← Vector2'float.length (fp + 24)
  let mut desired_speed_ms : Binary32 := t'22
  let t'23 ← is_zero desired_speed_ms
  if !t'23 then
    Vector2'float.operator_'5 (fp + 24) (fp + 56) desired_speed_ms
    let t'24 := (fp + 56)
    Vector2'float.Vector2'3 (fp + 48) t'24
    let t'25 ← PMem.ldF32 (fp + 16)
    let mut drag_decel_mss : Binary32 := ((pilot_acceleration_max_mss * desired_speed_ms) / t'25)
    let mut loiter_brake_accel_mss : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'26 ← PMem.ldU32 (this + 92)
    let t'27 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 44) (fp + 8)
    let t'28 ← PMem.ldF32 t'27
    if (decide ((UInt32.toBinary32 (((((← PMem.clock) / 1000).toUInt32) - t'26))) > (t'28 * (Binary64.toBinary32 ((Binary64.ofBits 0x408f400000000000 /- 1000 -/)))))) then
      let t'29 ← PMem.ldU64 (this + 8)
      let t'30 ← AC_PosControl.NE_get_vel_pid t'29
      let t'31 ← AC_PID_2D.kP t'30
      let t'32 ← AP_ParamT'float_4.operator_const_float__'1 t'31
      let t'33 ← PMem.ldF32 t'32
      let mut brake_gain : Binary32 := (t'33 * (Binary32.ofBits 0x3f000000 /- 1/2 -/))
      let t'34 ← AP_ParamT'float_4.operator_const_float__'1 (this + 40)
      let t'35 ← PMem.ldF32 t'34
      let t'36 ← PMem.ldF32 (fp + 8)
      let t'37 ← sqrt_controller desired_speed_ms brake_gain t'35 t'36
      let t'38 ← AP_ParamT'float_4.operator_const_float__'1 (this + 36)
      let t'39 ← PMem.ldF32 t'38
      let t'40 ← constrain_value_line'float t'37 (Binary32.ofBits 0x00000000 /- 0 -/) t'39 (Int32.toUInt32 ((358 : Int32)))
      loiter_brake_accel_mss := t'40
    let t'41 := (this + 96)
    let t'42 ← PMem.ldF32 t'41
    let t'43 ← PMem.ldF32 (this + 96)
    let t'44 ← AP_ParamT'float_4.operator_'3 (this + 40)
    let t'45 ← PMem.ldF32 (fp + 8)
    let t'46 ← AP_ParamT'float_4.operator_const_float__'1 (this + 40)
    let t'47 ← PMem.ldF32 t'46
    let t'48 ← PMem.ldF32 (fp + 8)
    let t'49 ← constrain_value_line'float (loiter_brake_accel_mss - t'43) (t'44 * t'45) (t'47 * t'48) (Int32.toUInt32 ((362 : Int32)))
    let t'50 := (t'42 + t'49)
    PMem.stF32 t'41 t'50
    let t'51 ← PMem.ldF32 (this + 96)
    Vector2'float.operator_'2 (fp + 48) (fp + 64) t'51
    let t'52 := (fp + 64)
    discard <| PMem.memcpy (fp + 40) t'52 8
    discard <| pure ((fp + 40))
    let t'53 ← PMem.ldF32 (this + 96)
    let t'54 ← PMem.ldF32 (fp + 8)
    PMem.stF32 (fp + 72) (desired_speed_ms - ((drag_decel_mss + t'53) * t'54))
    PMem.stF32 (fp + 76) (Binary32.ofBits 0x00000000 /- 0 -/)
    let t'55 ← MAX'float_float (fp + 72) (fp + 76)
    let t'56 ← PMem.ldF32 t'55
    desired_speed_ms := t'56
    Vector2'float.operator_'2 (fp + 48) (fp + 80) desired_speed_ms
    let t'57 := (fp + 80)
    discard <| PMem.memcpy (fp + 24) t'57 8
    discard <| pure ((fp + 24))
  let t'58 ← Vector2'float.operator__'2 (this + 52) (fp + 40)
  discard <| pure (t'58)
  let t'59 ← Vector2'float.length (fp + 24)
  let mut desired_vel_ms : Binary32 := t'59
  let t'60 ← PMem.ldF32 (fp + 16)
  if (decide (desired_vel_ms > t'60)) then
    let t'61 ← PMem.ldF32 (fp + 16)
    Vector2'float.operator_'2 (fp + 24) (fp + 88) t'61
    let t'62 := (fp + 88)
    Vector2'float.operator_'5 t'62 (fp + 96) desired_vel_ms
    let t'63 := (fp + 96)
    discard <| PMem.memcpy (fp + 24) t'63 8
    discard <| pure ((fp + 24))
  let t'64 ← PMem.ldU64 (this + 8)
  let t'65 ← AC_PosControl.get_pos_desired_NED_m t'64
  let t'66 ← Vector3'double.xy t'65
  Vector2'double.Vector2'4 (fp + 104) t'66
  let t'67 ← PMem.ldF32 (fp + 8)
  Vector2'float.operator_'2 (fp + 24) (fp + 120) t'67
  let t'68 := (fp + 120)
  Vector2'float.todouble t'68 (fp + 128)
  let t'69 := (fp + 128)
  let t'70 ← Vector2'double.operator__'2 (fp + 104) t'69
  discard <| pure (t'70)
  let t'71 ← PMem.ldU64 (this + 8)
  AC_PosControl.set_pos_vel_accel_NE_m t'71 (fp + 104) (fp + 24) (this + 52)
  return ()

def AC_Loiter.calc_desired_velocity (this : UInt64) (avoidance_on : Bool) : PMem.M Unit := do
  let fp ← PMem.enter 144
  let r ← AC_Loiter.calc_desired_velocity.body fp this avoidance_on
  PMem.leave fp
  return r

/-- C++ `AC_Loiter::update : void (bool)`, `AC_Loiter.cpp:247-254`. -/
def AC_Loiter.update (this : UInt64) (avoidance_on : Bool) : PMem.M Unit := do
  let mut avoidance_on := avoidance_on
  AC_Loiter.calc_desired_velocity this avoidance_on
  let t'1 ← PMem.ldU64 (this + 8)
  AC_PosControl.NE_update_controller t'1
  return ()

end Vehicle_lib
