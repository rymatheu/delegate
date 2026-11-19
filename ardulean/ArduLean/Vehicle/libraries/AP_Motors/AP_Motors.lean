import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param

/-!
ArduPilot `libraries/AP_Motors`, part 1 of 2. Sources: `libraries/AP_Motors/AP_MotorsMatrix.cpp`, `libraries/AP_Motors/AP_Motors_Class.h`, `libraries/AP_Motors/AP_MotorsMulticopter.cpp`, `libraries/AP_Motors/AP_Motors_Thrust_Linearization.cpp`, `libraries/AP_Motors/AP_Motors_Class.cpp`, `libraries/AP_Motors/AP_Motors_Thrust_Linearization.h`, `libraries/AP_Motors/AP_MotorsMatrix.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_MotorsMulticopter::get_throttle_hover : float () const`, `AP_Motors_Class.h:55-?`. -/
def AP_MotorsMulticopter.get_throttle_hover (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 312)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← constrain_value_line'float t'2 (Binary32.ofBits 0x3e000000 /- 1/8 -/) (Binary32.ofBits 0x3f300000 /- 11/16 -/) (Int32.toUInt32 ((55 : Int32)))
  return t'3

/-- C++ `AP_MotorsMatrix::_get_frame_string : const char *() const`, `AP_Motors_Class.h:136-?`. -/
def AP_MotorsMatrix._get_frame_string (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (this + 760)
  return t'1

/-- C++ `AP_Motors::get_frame_string : const char *() const`, `AP_Motors_Class.cpp:259-267`. -/
def AP_Motors.get_frame_string (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← AP_MotorsMatrix._get_frame_string this
  return t'1

/-- C++ `AP_MotorsMatrix::get_type_string : const char *() const`, `AP_Motors_Class.h:137-?`. -/
def AP_MotorsMatrix.get_type_string (this : UInt64) : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (this + 768)
  return t'1

/-- C++ `AP_Motors::armed : bool () const`, `AP_Motors_Class.h:178-?`. -/
def AP_Motors.armed (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 220)
  return t'1

/-- C++ `AP_Motors::get_interlock : bool () const`, `AP_Motors_Class.h:185-?`. -/
def AP_Motors.get_interlock (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 221)
  return t'1

/-- C++ `AP_MotorsMulticopter::set_desired_spool_state : void (DesiredSpoolState)`, `AP_MotorsMulticopter.cpp:570-581`. -/
def AP_MotorsMulticopter.set_desired_spool_state (this : UInt64) (desired : UInt8) : PMem.M Unit := do
  let mut desired := desired
  let t'1 ← AP_Motors.armed this
  let mut sc'3 := !t'1
  if !sc'3 then
    let t'2 ← AP_Motors.get_interlock this
    sc'3 := !t'2
  if sc'3 then
    PMem.stU8 (this + 172) (0 : UInt8)
    return ()
  PMem.stU8 (this + 172) desired
  return ()

/-- C++ `AP_Motors::has_option : bool (MotorOptions)`, `<scratch space>:354-?`. -/
def AP_Motors.has_option (this : UInt64) (option : UInt8) : PMem.M Bool := do
  let mut option := option
  let t'1 ← AP_ParamTBase'unsigned_short_2.get (this + 212)
  let t'2 ← PMem.ldU16 t'1
  return ((UInt32.toInt32 (UInt16.toUInt32 (t'2))) &&& (UInt32.toInt32 (UInt8.toUInt32 (option)))) != (0 : Int32)

/-- C++ `AP_Motors::get_dt_s : float () const`, `<scratch space>:260-?`. -/
def AP_Motors.get_dt_s (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 16)
  return t'1

/-- C++ `AP_Motors::AP_Motors_limit::set_rpy : void (bool)`, `AP_Motors_Class.cpp:364-369`. -/
def AP_Motors.AP_Motors_limit.set_rpy (this : UInt64) (flag : Bool) : PMem.M Unit := do
  let mut flag := flag
  PMem.stB this flag
  PMem.stB (this + 1) flag
  PMem.stB (this + 2) flag
  return ()

/-- C++ `AP_Motors::AP_Motors_limit::set_throttle : void (bool)`, `AP_Motors_Class.cpp:372-376`. -/
def AP_Motors.AP_Motors_limit.set_throttle (this : UInt64) (flag : Bool) : PMem.M Unit := do
  let mut flag := flag
  PMem.stB (this + 3) flag
  PMem.stB (this + 4) flag
  return ()

/-- C++ `AP_Motors::AP_Motors_limit::set_all : void (bool)`, `AP_Motors_Class.cpp:357-361`. -/
def AP_Motors.AP_Motors_limit.set_all (this : UInt64) (flag : Bool) : PMem.M Unit := do
  let mut flag := flag
  AP_Motors.AP_Motors_limit.set_rpy this flag
  AP_Motors.AP_Motors_limit.set_throttle this flag
  return ()

/-- C++ `Thrust_Linearization::get_spin_min : float () const`, `AP_Motors_Thrust_Linearization.h:33-?`. -/
def Thrust_Linearization.get_spin_min (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 4)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `AP_Motors::set_spoolup_block : void (bool)`, `AP_Motors_Class.h:189-?`. -/
def AP_Motors.set_spoolup_block (this : UInt64) (set' : Bool) : PMem.M Unit := do
  let mut set' := set'
  PMem.stB (this + 223) set'
  return ()

/-- C++ `AP_Motors::get_spoolup_block : bool () const`, `AP_Motors_Class.h:188-?`. -/
def AP_Motors.get_spoolup_block (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 223)
  return t'1

/-- C++ `AP_Motors::get_throttle : float () const`, `<scratch space>:219-?`. -/
def AP_Motors.get_throttle (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← DigitalLPF'float.get (this + 72)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← constrain_value_line'float t'2 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((219 : Int32)))
  return t'3

/-- C++ `Thrust_Linearization::get_battery_index : int8_t () const`, `AP_Motors_Thrust_Linearization.h:39-?`. -/
def Thrust_Linearization.get_battery_index (this : UInt64) : PMem.M Int8 := do
  let t'1 ← AP_ParamTBase'signed_char_1.get (this + 12)
  let t'2 ← PMem.ldI8 t'1
  return t'2

/-- C++ `Thrust_Linearization::get_battery_min_voltage : float () const`, `AP_Motors_Thrust_Linearization.h:42-?`. -/
def Thrust_Linearization.get_battery_min_voltage (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP_ParamTBase'float_4.get (this + 20)
  let t'2 ← PMem.ldF32 t'1
  return t'2

/-- C++ `Thrust_Linearization::get_lift_max : float () const`, `AP_Motors_Thrust_Linearization.h:45-?`. -/
def Thrust_Linearization.get_lift_max (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 24)
  return t'1

/-- C++ `Thrust_Linearization::get_compensation_gain : float () const`, `AP_Motors_Thrust_Linearization.cpp:189-206`. -/
def Thrust_Linearization.get_compensation_gain (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← Thrust_Linearization.get_lift_max this
  if (decide (t'1 ≤ (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))))) then
    return Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'2 ← Thrust_Linearization.get_lift_max this
  let mut ret : Binary32 := ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) / t'2)
  let t'3 ← VehicleBridge.ahrs'0
  let t'4 ← VehicleBridge.AP_AHRS.get_air_density_ratio'0 t'3
  let mut air_density_ratio : Binary32 := t'4
  if ((decide (air_density_ratio > (Binary64.toBinary32 ((Binary64.ofBits 0x3fd3333333333333 /- 29999999999999999/100000000000000000 -/))))) && (decide (air_density_ratio < (Binary64.toBinary32 ((Binary64.ofBits 0x3ff8000000000000 /- 3/2 -/)))))) then
    let t'5 ← constrain_value_line'float air_density_ratio (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff4000000000000 /- 5/4 -/))) (Int32.toUInt32 ((202 : Int32)))
    let t'6 := (ret * ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) / t'5))
    ret := t'6
  return ret

/-- C++ `AP_MotorsMatrix::boost_ratio : float (float, float) const`, `AP_MotorsMatrix.cpp:207-210`. -/
def AP_MotorsMatrix.boost_ratio (this : UInt64) (boost_value : Binary32) (normal_value : Binary32) : PMem.M Binary32 := do
  let mut boost_value := boost_value
  let mut normal_value := normal_value
  let t'1 ← PMem.ldF32 (this + 208)
  let t'2 ← PMem.ldF32 (this + 208)
  return ((t'1 * boost_value) + (((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - t'2) * normal_value))

/-- C++ `AP_MotorsMatrix::check_for_failed_motor : void (float)`, `AP_MotorsMatrix.cpp:415-462`. -/
def AP_MotorsMatrix.check_for_failed_motor (this : UInt64) (throttle_thrust_best_plus_adj : Binary32) : PMem.M Unit := do
  let mut throttle_thrust_best_plus_adj := throttle_thrust_best_plus_adj
  let t'1 ← PMem.ldF32 (this + 16)
  let t'2 ← PMem.ldF32 (this + 16)
  let mut alpha : Binary32 := (t'1 / (t'2 + (Binary32.ofBits 0x3f000000 /- 1/2 -/)))
  for i'3 in [0:12] do
    let i : UInt8 := UInt8.ofNat i'3
    let t'4 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    if t'4 then
      let t'5 := ((this + 696) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      let t'6 ← PMem.ldF32 t'5
      let t'7 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      let t'8 ← PMem.ldF32 ((this + 696) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      let t'9 := (t'6 + (alpha * (t'7 - t'8)))
      PMem.stF32 t'5 t'9
  let mut rpyt_high : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut rpyt_sum : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  let mut number_motors : UInt8 := Binary32.toUInt8 ((Binary32.ofBits 0x00000000 /- 0 -/))
  for i'2'10 in [0:12] do
    let i'2 : UInt8 := UInt8.ofNat i'2'10
    let t'11 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 1).toUInt64)
    if t'11 then
      let t'12 := (number_motors + (Int8.toUInt8 (Int32.toInt8 ((1 : Int32)))))
      number_motors := t'12
      let t'13 ← PMem.ldF32 ((this + 696) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
      let t'14 := (rpyt_sum + t'13)
      rpyt_sum := t'14
      let t'15 ← PMem.ldF32 ((this + 696) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
      if (decide (t'15 > rpyt_high)) then
        let t'16 ← PMem.ldF32 ((this + 696) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
        rpyt_high := t'16
        let t'17 ← PMem.ldB (this + 205)
        if !t'17 then
          PMem.stU8 (this + 744) i'2
  let mut thrust_balance : Binary32 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  if (decide (rpyt_sum > (Binary32.ofBits 0x3dcccccd /- 100000001/1000000000 -/))) then
    let t'18 := ((rpyt_high * (Int32.toBinary32 ((UInt32.toInt32 (UInt8.toUInt32 (number_motors)))))) / rpyt_sum)
    thrust_balance := t'18
  let t'19 ← PMem.ldU32 (this + 752)
  let mut sc'21 := ((UInt32.toInt32 (t'19)) == (UInt32.toInt32 ((20 : UInt32))))
  if !sc'21 then
    let t'20 ← PMem.ldU32 (this + 752)
    sc'21 := ((UInt32.toInt32 (t'20)) == (UInt32.toInt32 ((21 : UInt32))))
  let mut is_corotating : Bool := sc'21
  let mut sc'23 := ((decide ((UInt32.toInt32 (UInt8.toUInt32 (number_motors))) ≥ (6 : Int32))) && (decide (thrust_balance ≥ (Binary32.ofBits 0x3fc00000 /- 3/2 -/))))
  if sc'23 then
    let t'22 ← PMem.ldB (this + 206)
    sc'23 := t'22
  if (sc'23 && (!is_corotating)) then
    PMem.stB (this + 206) false
  let mut sc'25 := (decide (thrust_balance ≤ (Binary32.ofBits 0x3fa00000 /- 5/4 -/)))
  if sc'25 then
    let t'24 ← PMem.ldB (this + 206)
    sc'25 := !t'24
  if sc'25 then
    PMem.stB (this + 206) true
  let t'26 ← PMem.ldF32 (this + 368)
  let t'27 ← Thrust_Linearization.get_compensation_gain (this + 224)
  let mut sc'29 := ((decide ((t'26 * t'27) > throttle_thrust_best_plus_adj)) && (decide (rpyt_high < (Binary32.ofBits 0x3f666666 /- 112499997/125000000 -/))))
  if sc'29 then
    let t'28 ← PMem.ldB (this + 206)
    sc'29 := t'28
  if sc'29 then
    PMem.stB (this + 205) false
  return ()

/-- C++ `AP_MotorsMatrix::output_armed_stabilizing : void ()`, `AP_MotorsMatrix.cpp:214-405`. -/
def AP_MotorsMatrix.output_armed_stabilizing.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← Thrust_Linearization.get_compensation_gain (this + 224)
  let mut compensation_gain : Binary32 := t'1
  let t'2 ← PMem.ldF32 (this + 24)
  let t'3 ← PMem.ldF32 (this + 28)
  let mut roll_thrust : Binary32 := ((t'2 + t'3) * compensation_gain)
  let t'4 ← PMem.ldF32 (this + 32)
  let t'5 ← PMem.ldF32 (this + 36)
  let mut pitch_thrust : Binary32 := ((t'4 + t'5) * compensation_gain)
  let t'6 ← PMem.ldF32 (this + 40)
  let t'7 ← PMem.ldF32 (this + 44)
  let mut yaw_thrust : Binary32 := ((t'6 + t'7) * compensation_gain)
  let t'8 ← AP_Motors.get_throttle this
  let mut throttle_thrust : Binary32 := (t'8 * compensation_gain)
  let t'9 ← PMem.ldF32 (this + 68)
  PMem.stF32 (fp + 0) (t'9 * compensation_gain)
  let t'10 ← PMem.ldF32 (this + 368)
  let t'11 ← AP_MotorsMatrix.boost_ratio this (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (t'10 * compensation_gain)
  let mut throttle_thrust_max : Binary32 := t'11
  if (decide (throttle_thrust ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
    let t'12 := (Binary32.ofBits 0x00000000 /- 0 -/)
    throttle_thrust := t'12
    PMem.stB ((this + 8) + 3) true
  if (decide (throttle_thrust ≥ throttle_thrust_max)) then
    throttle_thrust := throttle_thrust_max
    PMem.stB ((this + 8) + 4) true
  let t'13 ← PMem.ldF32 (fp + 0)
  let t'14 ← constrain_value_line'float t'13 throttle_thrust throttle_thrust_max (Int32.toUInt32 ((248 : Int32)))
  PMem.stF32 (fp + 0) t'14
  PMem.stF32 (fp + 4) (Binary32.ofBits 0x3f000000 /- 1/2 -/)
  let t'15 ← MIN'float_float (fp + 4) (fp + 0)
  let t'16 ← PMem.ldF32 t'15
  let mut throttle_thrust_best_rpy : Binary32 := t'16
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x3f800000 /- 1 -/)
  for i'17 in [0:12] do
    let i : UInt8 := UInt8.ofNat i'17
    let t'18 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    if t'18 then
      let t'19 ← PMem.ldF32 ((this + 444) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      let t'20 ← PMem.ldF32 ((this + 492) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      let t'21 := ((roll_thrust * t'19) + (pitch_thrust * t'20))
      PMem.stF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64) t'21
      let t'22 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      let t'23 ← is_zero t'22
      let mut sc'27 := !t'23
      if sc'27 then
        let t'24 ← PMem.ldB (this + 205)
        let mut sc'26 := !t'24
        if !sc'26 then
          let t'25 ← PMem.ldU8 (this + 744)
          sc'26 := ((UInt32.toInt32 (UInt8.toUInt32 (i))) != (UInt32.toInt32 (UInt8.toUInt32 (t'25))))
        sc'27 := sc'26
      if sc'27 then
        let t'28 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
        let mut thrust_rp_best_throttle : Binary32 := (throttle_thrust_best_rpy + t'28)
        let t'29 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
        let t'30 ← is_positive'float (yaw_thrust * t'29)
        if t'30 then
          let t'31 := ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - thrust_rp_best_throttle)
          PMem.stF32 (fp + 16) t'31
        else
          PMem.stF32 (fp + 16) thrust_rp_best_throttle
        PMem.stF32 (fp + 28) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
        let t'32 ← MAX'float_float (fp + 16) (fp + 28)
        let t'33 ← PMem.ldF32 t'32
        let t'34 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
        PMem.stF32 (fp + 24) (t'33 / (Binary32.abs t'34))
        let t'35 ← MIN'float_float (fp + 8) (fp + 24)
        let t'36 ← PMem.ldF32 t'35
        PMem.stF32 (fp + 8) t'36
  let t'37 ← AP_ParamT'short_2.operator_const_short__ (this + 280)
  let t'38 ← PMem.ldI16 t'37
  PMem.stF32 (fp + 32) ((Int16.toBinary32 (t'38)) * (Binary32.ofBits 0x3a83126f /- 20000001/20000000000 -/))
  let t'39 ← PMem.ldF32 (fp + 32)
  let t'40 ← AP_MotorsMatrix.boost_ratio this (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/))) t'39
  PMem.stF32 (fp + 32) t'40
  let t'41 ← MAX'float_float (fp + 8) (fp + 32)
  let t'42 ← PMem.ldF32 t'41
  PMem.stF32 (fp + 8) t'42
  let t'43 ← PMem.ldB (this + 205)
  let mut sc'46 := t'43
  if sc'46 then
    let t'44 ← PMem.ldU8 (this + 744)
    let t'45 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (t'44))) * 1).toUInt64)
    sc'46 := t'45
  if sc'46 then
    let t'47 ← PMem.ldU8 (this + 744)
    let t'48 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (t'47))) * 4).toUInt64)
    let t'49 ← is_zero t'48
    if !t'49 then
      let t'50 ← PMem.ldU8 (this + 744)
      let t'51 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (t'50))) * 4).toUInt64)
      let mut thrust_rp_best_throttle'2 : Binary32 := (throttle_thrust_best_rpy + t'51)
      let t'52 ← PMem.ldU8 (this + 744)
      let t'53 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (t'52))) * 4).toUInt64)
      let t'54 ← is_positive'float (yaw_thrust * t'53)
      if t'54 then
        let t'55 := ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - thrust_rp_best_throttle'2)
        PMem.stF32 (fp + 40) t'55
      else
        PMem.stF32 (fp + 40) thrust_rp_best_throttle'2
      PMem.stF32 (fp + 52) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
      let t'56 ← MAX'float_float (fp + 40) (fp + 52)
      let t'57 ← PMem.ldF32 t'56
      let t'58 ← PMem.ldU8 (this + 744)
      let t'59 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (t'58))) * 4).toUInt64)
      PMem.stF32 (fp + 48) (t'57 / (Binary32.abs t'59))
      let t'60 ← PMem.ldF32 (fp + 8)
      let t'61 ← MIN'float_float (fp + 8) (fp + 48)
      let t'62 ← PMem.ldF32 t'61
      let t'63 ← AP_MotorsMatrix.boost_ratio this t'60 t'62
      PMem.stF32 (fp + 8) t'63
  let t'64 ← PMem.ldF32 (fp + 8)
  if (decide ((Binary32.abs yaw_thrust) > t'64)) then
    let t'65 ← PMem.ldF32 (fp + 8)
    let t'66 ← PMem.ldF32 (fp + 8)
    let t'67 ← constrain_value_line'float yaw_thrust (-t'65) t'66 (Int32.toUInt32 ((330 : Int32)))
    yaw_thrust := t'67
    PMem.stB ((this + 8) + 2) true
  let mut rpy_low : Binary32 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  let mut rpy_high : Binary32 := -(Binary32.ofBits 0x3f800000 /- 1 -/)
  for i'2'68 in [0:12] do
    let i'2 : UInt8 := UInt8.ofNat i'2'68
    let t'69 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 1).toUInt64)
    if t'69 then
      let t'70 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
      let t'71 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
      let t'72 := (t'70 + (yaw_thrust * t'71))
      PMem.stF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64) t'72
      let t'73 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
      if (decide (t'73 < rpy_low)) then
        let t'74 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
        rpy_low := t'74
      let t'75 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
      let mut sc'79 := (decide (t'75 > rpy_high))
      if sc'79 then
        let t'76 ← PMem.ldB (this + 205)
        let mut sc'78 := !t'76
        if !sc'78 then
          let t'77 ← PMem.ldU8 (this + 744)
          sc'78 := ((UInt32.toInt32 (UInt8.toUInt32 (i'2))) != (UInt32.toInt32 (UInt8.toUInt32 (t'77))))
        sc'79 := sc'78
      if sc'79 then
        let t'80 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
        rpy_high := t'80
  let t'81 ← PMem.ldB (this + 205)
  if t'81 then
    let t'82 ← PMem.ldU8 (this + 744)
    let t'83 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (t'82))) * 4).toUInt64)
    let mut sc'86 := (decide (t'83 > rpy_high))
    if sc'86 then
      let t'84 ← PMem.ldU8 (this + 744)
      let t'85 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (t'84))) * 1).toUInt64)
      sc'86 := t'85
    if sc'86 then
      let t'87 ← PMem.ldU8 (this + 744)
      let t'88 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (t'87))) * 4).toUInt64)
      let t'89 ← AP_MotorsMatrix.boost_ratio this rpy_high t'88
      rpy_high := t'89
  PMem.stF32 (fp + 56) (Binary32.ofBits 0x3f800000 /- 1 -/)
  if (decide ((rpy_high - rpy_low) > (Binary32.ofBits 0x3f800000 /- 1 -/))) then
    let t'90 := ((Binary32.ofBits 0x3f800000 /- 1 -/) / (rpy_high - rpy_low))
    PMem.stF32 (fp + 56) t'90
  let t'91 ← PMem.ldF32 (fp + 0)
  if (decide ((t'91 + rpy_low) < (Int32.toBinary32 ((0 : Int32))))) then
    let t'92 ← PMem.ldF32 (fp + 0)
    PMem.stF32 (fp + 60) ((-t'92) / rpy_low)
    let t'93 ← MIN'float_float (fp + 56) (fp + 60)
    let t'94 ← PMem.ldF32 t'93
    PMem.stF32 (fp + 56) t'94
  let t'95 ← PMem.ldF32 (fp + 56)
  let t'96 := (rpy_high * t'95)
  rpy_high := t'96
  let t'97 ← PMem.ldF32 (fp + 56)
  let t'98 := (rpy_low * t'97)
  rpy_low := t'98
  let t'99 := -rpy_low
  throttle_thrust_best_rpy := t'99
  let mut thr_adj : Binary32 := (throttle_thrust - throttle_thrust_best_rpy)
  let t'100 ← PMem.ldF32 (fp + 56)
  if (decide (t'100 < (Binary32.ofBits 0x3f800000 /- 1 -/))) then
    AP_Motors.AP_Motors_limit.set_rpy (this + 8) true
    if (decide (thr_adj > (Binary32.ofBits 0x00000000 /- 0 -/))) then
      PMem.stB ((this + 8) + 4) true
    let t'101 := (Binary32.ofBits 0x00000000 /- 0 -/)
    thr_adj := t'101
  else
    if (decide (thr_adj < (Binary32.ofBits 0x00000000 /- 0 -/))) then
      let t'102 := (Binary32.ofBits 0x00000000 /- 0 -/)
      thr_adj := t'102
    else
      if (decide (thr_adj > ((Binary32.ofBits 0x3f800000 /- 1 -/) - (throttle_thrust_best_rpy + rpy_high)))) then
        let t'103 := ((Binary32.ofBits 0x3f800000 /- 1 -/) - (throttle_thrust_best_rpy + rpy_high))
        thr_adj := t'103
        PMem.stB ((this + 8) + 4) true
  let mut throttle_thrust_best_plus_adj : Binary32 := (throttle_thrust_best_rpy + thr_adj)
  for i'3'104 in [0:12] do
    let i'3 : UInt8 := UInt8.ofNat i'3'104
    let t'105 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i'3))) * 1).toUInt64)
    if t'105 then
      let t'106 ← PMem.ldF32 ((this + 588) + ((UInt64.toInt64 (UInt8.toUInt64 (i'3))) * 4).toUInt64)
      let t'107 ← PMem.ldF32 (fp + 56)
      let t'108 ← PMem.ldF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i'3))) * 4).toUInt64)
      let t'109 := ((throttle_thrust_best_plus_adj * t'106) + (t'107 * t'108))
      PMem.stF32 ((this + 636) + ((UInt64.toInt64 (UInt8.toUInt64 (i'3))) * 4).toUInt64) t'109
  let t'110 := (throttle_thrust_best_plus_adj / compensation_gain)
  PMem.stF32 (this + 52) t'110
  AP_MotorsMatrix.check_for_failed_motor this throttle_thrust_best_plus_adj
  return ()

def AP_MotorsMatrix.output_armed_stabilizing (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 64
  let r ← AP_MotorsMatrix.output_armed_stabilizing.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMulticopter::motor_enabled_mask : bool (uint8_t) const`, `functor.h:232-234`. -/
def AP_MotorsMulticopter.motor_enabled_mask (this : UInt64) (i : UInt8) : PMem.M Bool := do
  let mut i := i
  let t'1 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← PMem.ldU32 (this + 440)
    sc'3 := ((t'2 &&& ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i))))))) == (Int32.toUInt32 ((0 : Int32))))
  return sc'3

/-- C++ `AP_MotorsMulticopter::actuator_spin_up_to_ground_idle : float () const`, `AP_MotorsMulticopter.cpp:515-518`. -/
def AP_MotorsMulticopter.actuator_spin_up_to_ground_idle (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 352)
  let t'2 ← constrain_value_line'float t'1 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((517 : Int32)))
  let t'3 ← Thrust_Linearization.get_spin_min (this + 224)
  return (t'2 * t'3)

/-- C++ `Thrust_Linearization::apply_thrust_curve_and_volt_scaling : float (float) const`, `AP_Motors_Thrust_Linearization.cpp:119-133`. -/
def Thrust_Linearization.apply_thrust_curve_and_volt_scaling (this : UInt64) (thrust : Binary32) : PMem.M Binary32 := do
  let mut thrust := thrust
  let mut battery_scale : Binary32 := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
  let t'1 ← DigitalLPF'float.get (this + 32)
  let t'2 ← PMem.ldF32 t'1
  let t'3 ← is_positive'float t'2
  if t'3 then
    let t'4 ← DigitalLPF'float.get (this + 32)
    let t'5 ← PMem.ldF32 t'4
    let t'6 := ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) / t'5)
    battery_scale := t'6
  let t'7 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'8 ← PMem.ldF32 t'7
  let t'9 ← constrain_value_line'float t'8 (-(Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((126 : Int32)))
  let mut thrust_curve_expo : Binary32 := t'9
  let t'10 ← is_zero thrust_curve_expo
  if t'10 then
    let t'11 ← PMem.ldF32 (this + 24)
    return ((t'11 * thrust) * battery_scale)
  let t'12 ← PMem.ldF32 (this + 24)
  let t'13 ← safe_sqrt'float ((((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - thrust_curve_expo) * ((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - thrust_curve_expo)) + ((((Binary64.toBinary32 ((Binary64.ofBits 0x4010000000000000 /- 4 -/))) * thrust_curve_expo) * t'12) * thrust))
  let mut throttle_ratio : Binary32 := (((thrust_curve_expo - (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))) + t'13) / ((Binary64.toBinary32 ((Binary64.ofBits 0x4000000000000000 /- 2 -/))) * thrust_curve_expo))
  let t'14 ← constrain_value_line'float (throttle_ratio * battery_scale) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((132 : Int32)))
  return t'14

/-- C++ `Thrust_Linearization::thrust_to_actuator : float (float) const`, `AP_Motors_Thrust_Linearization.cpp:104-108`. -/
def Thrust_Linearization.thrust_to_actuator (this : UInt64) (thrust_in : Binary32) : PMem.M Binary32 := do
  let mut thrust_in := thrust_in
  let t'1 ← constrain_value_line'float thrust_in (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((106 : Int32)))
  thrust_in := t'1
  let t'2 ← AP_ParamT'float_4.operator_const_float__'1 (this + 4)
  let t'3 ← PMem.ldF32 t'2
  let t'4 ← AP_ParamT'float_4.operator_'2 (this + 8) (this + 4)
  let t'5 ← Thrust_Linearization.apply_thrust_curve_and_volt_scaling this thrust_in
  return (t'3 + (t'4 * t'5))

/-- C++ `AP_MotorsMulticopter::get_pwm_output_min : int16_t () const`, `<scratch space>:77-?`. -/
def AP_MotorsMulticopter.get_pwm_output_min (this : UInt64) : PMem.M Int16 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 308)
  let t'2 ← PMem.ldI16 t'1
  return t'2

/-- C++ `AP_MotorsMulticopter::get_pwm_output_max : int16_t () const`, `<scratch space>:78-?`. -/
def AP_MotorsMulticopter.get_pwm_output_max (this : UInt64) : PMem.M Int16 := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 310)
  let t'2 ← PMem.ldI16 t'1
  return t'2

/-- C++ `AP_MotorsMulticopter::output_to_pwm : int16_t (float)`, `AP_MotorsMulticopter.cpp:461-477`. -/
def AP_MotorsMulticopter.output_to_pwm (this : UInt64) (actuator : Binary32) : PMem.M Int16 := do
  let mut actuator := actuator
  let mut pwm_output : Binary32 := default  -- uninitialized in C
  let t'1 ← PMem.ldU8 (this + 173)
  if (t'1 == (0 : UInt8)) then
    let t'2 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 317)
    let t'3 ← PMem.ldI8 t'2
    let mut sc'5 := t'3 != (0 : Int8)
    if sc'5 then
      let t'4 ← AP_Motors.armed this
      sc'5 := !t'4
    if sc'5 then
      let t'6 := Int32.toBinary32 ((0 : Int32))
      pwm_output := t'6
    else
      let t'7 ← AP_MotorsMulticopter.get_pwm_output_min this
      let t'8 := Int16.toBinary32 (t'7)
      pwm_output := t'8
  else
    let t'9 ← AP_MotorsMulticopter.get_pwm_output_min this
    let t'10 ← AP_MotorsMulticopter.get_pwm_output_max this
    let t'11 ← AP_MotorsMulticopter.get_pwm_output_min this
    let t'12 := ((Int32.toBinary32 ((Int16.toInt32 (t'9)))) + ((Int32.toBinary32 (((Int16.toInt32 (t'10)) - (Int16.toInt32 (t'11))))) * actuator))
    pwm_output := t'12
  return Binary32.toInt16 (pwm_output)

/-- `AP_MotorsMulticopter.update_external_limits` as a pure function of its arguments (it reads and writes no memory). -/
def AP_MotorsMulticopter.update_external_limits.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_MotorsMulticopter::update_external_limits : void ()`, `AP_MotorsMulticopter.cpp:307-317`. -/
def AP_MotorsMulticopter.update_external_limits (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_MotorsMulticopter.update_external_limits.pure' this)

/-- C++ `AP_Motors::initialised_ok : bool () const`, `AP_Motors_Class.h:174-?`. -/
def AP_Motors.initialised_ok (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 222)
  return t'1

/-- C++ `AP_MotorsMulticopter::check_mot_pwm_params : bool () const`, `AP_MotorsMulticopter.cpp:536-545`. -/
def AP_MotorsMulticopter.check_mot_pwm_params (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_ParamT'short_2.operator_const_short__ (this + 308)
  let t'2 ← PMem.ldI16 t'1
  let mut sc'7 := (decide ((Int16.toInt32 (t'2)) < (1 : Int32)))
  if !sc'7 then
    let t'3 ← AP_ParamT'short_2.operator_const_short__ (this + 308)
    let t'4 ← PMem.ldI16 t'3
    let t'5 ← AP_ParamT'short_2.operator_const_short__ (this + 310)
    let t'6 ← PMem.ldI16 t'5
    sc'7 := (decide ((Int16.toInt32 (t'4)) ≥ (Int16.toInt32 (t'6))))
  if sc'7 then
    return false
  return true

/-- C++ `AP_Motors::get_frame_mav_type : MAV_TYPE () const`, `<scratch space>:334-?`. -/
def AP_Motors.get_frame_mav_type (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← PMem.ldU32 (this + 216)
  return t'1

/-- C++ `AP_Motors::get_thrust_boost : bool () const`, `<scratch space>:228-?`. -/
def AP_Motors.get_thrust_boost (this : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldB (this + 205)
  return t'1

/-- `AP_Motors.AP_Motors_limit.AP_Motors_limit` as a pure function of its arguments (it reads and writes no memory). -/
def AP_Motors.AP_Motors_limit.AP_Motors_limit.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `AP_Motors::AP_Motors_limit::AP_Motors_limit : void () noexcept`, `<scratch space>:?-?`. -/
def AP_Motors.AP_Motors_limit.AP_Motors_limit (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.AP_Motors.AP_Motors_limit.AP_Motors_limit.pure' this)

/-- C++ `AP_Motors::AP_Motors : void (uint16_t)`, `AP_Motors_Class.cpp:36-60`. -/
def AP_Motors.AP_Motors.body (fp : UInt64) (this : UInt64) (speed_hz : UInt16) : PMem.M Unit := do
  let mut speed_hz := speed_hz
  AP_Motors.AP_Motors_limit.AP_Motors_limit (this + 8)
  PMem.stU16 (this + 20) speed_hz
  LowPassFilter'float.LowPassFilter (this + 72)
  Filter'float.Filter (this + 88)
  LowPassFilter'float.LowPassFilter (this + 160)
  PMem.stU8 (this + 172) (0 : UInt8)
  PMem.stU8 (this + 173) (0 : UInt8)
  AP_Enum'AP_Motors_PWMType.AP_Enum (this + 204)
  AP_Param.AP_Param'2 (this + 212)
  PMem.stU64 (0x12ef0 : UInt64) /- &AP_Motors::_singleton -/ this
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  LowPassFilter'float.set_cutoff_frequency (this + 72) (fp + 0)
  PMem.stF32 (fp + 4) (Binary32.ofBits 0x00000000 /- 0 -/)
  DigitalLPF'float.reset (this + 72) (fp + 4)
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x42480000 /- 50 -/)
  LowPassFilter'float.set_cutoff_frequency (this + 160) (fp + 8)
  PMem.stF32 (fp + 12) (Binary32.ofBits 0x00000000 /- 0 -/)
  DigitalLPF'float.reset (this + 160) (fp + 12)
  DerivativeFilter'float_7.reset (this + 88)
  AP_Motors.AP_Motors_limit.set_all (this + 8) true
  PMem.stB (this + 205) false
  PMem.stB (this + 206) true
  return ()

def AP_Motors.AP_Motors (this : UInt64) (speed_hz : UInt16) : PMem.M Unit := do
  let fp ← PMem.enter 16
  let r ← AP_Motors.AP_Motors.body fp this speed_hz
  PMem.leave fp
  return r

/-- C++ `Thrust_Linearization::Thrust_Linearization : void (AP_Motors &)`, `AP_Motors_Thrust_Linearization.cpp:90-101`. -/
def Thrust_Linearization.Thrust_Linearization.body (fp : UInt64) (this : UInt64) (_motors : UInt64) : PMem.M Unit := do
  AP_Param.AP_Param'2 (this + 0)
  AP_Param.AP_Param'2 (this + 4)
  AP_Param.AP_Param'2 (this + 8)
  AP_Param.AP_Param'2 (this + 12)
  AP_Param.AP_Param'2 (this + 16)
  AP_Param.AP_Param'2 (this + 20)
  PMem.stF32 (this + 24) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  LowPassFilter'float.LowPassFilter (this + 32)
  PMem.stU64 (this + 48) _motors
  PMem.stF32 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x3fe0000000000000 /- 1/2 -/)))
  LowPassFilter'float.set_cutoff_frequency (this + 32) (fp + 0)
  PMem.stF32 (fp + 4) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
  DigitalLPF'float.reset (this + 32) (fp + 4)
  return ()

def Thrust_Linearization.Thrust_Linearization (this : UInt64) (_motors : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 8
  let r ← Thrust_Linearization.Thrust_Linearization.body fp this _motors
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMulticopter::AP_MotorsMulticopter : void (uint16_t)`, `AP_MotorsMulticopter.cpp:265-270`. -/
def AP_MotorsMulticopter.AP_MotorsMulticopter (this : UInt64) (speed_hz : UInt16) : PMem.M Unit := do
  let mut speed_hz := speed_hz
  AP_Motors.AP_Motors this speed_hz
  Thrust_Linearization.Thrust_Linearization (this + 224) this
  AP_Param.AP_Param'2 (this + 280)
  AP_Param.AP_Param'2 (this + 284)
  AP_Param.AP_Param'2 (this + 288)
  AP_Param.AP_Param'2 (this + 292)
  AP_Param.AP_Param'2 (this + 296)
  AP_Param.AP_Param'2 (this + 300)
  AP_Param.AP_Param'2 (this + 304)
  AP_Param.AP_Param'2 (this + 308)
  AP_Param.AP_Param'2 (this + 310)
  AP_Param.AP_Param'2 (this + 312)
  AP_Param.AP_Param'2 (this + 316)
  AP_Param.AP_Param'2 (this + 317)
  AP_Param.AP_Param'2 (this + 320)
  AP_Param.AP_Param'2 (this + 324)
  AP_Param.AP_Param'2 (this + 328)
  AP_Param.AP_Param'2 (this + 332)
  AP_Param.AP_Param'2 (this + 336)
  PMem.stF32 (this + 364) (Binary32.ofBits 0x3f800000 /- 1 -/)
  AP_Param.setup_object_defaults this (0x1b68 : UInt64) /- &AP_MotorsMulticopter::var_info -/
  return ()

/-- C++ `AP_MotorsMatrix::AP_MotorsMatrix : void (uint16_t)`, `AP_MotorsMatrix.h:18-25`. -/
def AP_MotorsMatrix.AP_MotorsMatrix (this : UInt64) (speed_hz : UInt16) : PMem.M Unit := do
  let mut speed_hz := speed_hz
  AP_MotorsMulticopter.AP_MotorsMulticopter this speed_hz
  PMem.stU64 (this + 760) (0x14223 : UInt64) /- "" -/
  PMem.stU64 (this + 768) (0x14223 : UInt64) /- "" -/
  let t'1 ← PMem.ldU64 (0xdf20 : UInt64) /- &AP_MotorsMatrix::_singleton -/
  if (t'1 != (0 : UInt64)) then
    pure ()
  PMem.stU64 (0xdf20 : UInt64) /- &AP_MotorsMatrix::_singleton -/ this
  return ()

/-- C++ `AP_Motors::is_brushed_pwm_type : bool () const`, `<scratch space>:329-?`. -/
def AP_Motors.is_brushed_pwm_type (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Enum'AP_Motors_PWMType.operator_const_AP_Motors.PWMType (this + 204)
  return (t'1 == (3 : UInt8))

/-- C++ `AP_MotorsMatrix::remove_motor : void (int8_t)`, `AP_MotorsMatrix.cpp:549-560`. -/
def AP_MotorsMatrix.remove_motor (this : UInt64) (motor_num : Int8) : PMem.M Unit := do
  let mut motor_num := motor_num
  if ((decide ((Int8.toInt32 (motor_num)) ≥ (0 : Int32))) && (decide ((Int8.toInt32 (motor_num)) < (12 : Int32)))) then
    PMem.stB ((this + 340) + ((Int8.toInt64 (motor_num)) * 1).toUInt64) false
    let t'1 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((this + 444) + ((Int8.toInt64 (motor_num)) * 4).toUInt64) t'1
    let t'2 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((this + 492) + ((Int8.toInt64 (motor_num)) * 4).toUInt64) t'2
    let t'3 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((this + 540) + ((Int8.toInt64 (motor_num)) * 4).toUInt64) t'3
    let t'4 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 ((this + 588) + ((Int8.toInt64 (motor_num)) * 4).toUInt64) t'4
  return ()

/-- C++ `AP_Motors::set_initialised_ok : void (bool)`, `AP_Motors_Class.h:175-?`. -/
def AP_Motors.set_initialised_ok (this : UInt64) (val : Bool) : PMem.M Unit := do
  let mut val := val
  PMem.stB (this + 222) val
  return ()

/-- C++ `AP_MotorsMatrix::normalise_rpy_factors : void ()`, `AP_MotorsMatrix.cpp:1354-1388`. -/
def AP_MotorsMatrix.normalise_rpy_factors.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (fp + 16) (Binary32.ofBits 0x00000000 /- 0 -/)
  PMem.stF32 (fp + 24) (Binary32.ofBits 0x00000000 /- 0 -/)
  for i'1 in [0:12] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    if t'2 then
      let t'3 ← PMem.ldF32 ((this + 444) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      PMem.stF32 (fp + 28) (Binary32.abs t'3)
      let t'4 ← MAX'float_float (fp + 0) (fp + 28)
      let t'5 ← PMem.ldF32 t'4
      PMem.stF32 (fp + 0) t'5
      let t'6 ← PMem.ldF32 ((this + 492) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      PMem.stF32 (fp + 32) (Binary32.abs t'6)
      let t'7 ← MAX'float_float (fp + 8) (fp + 32)
      let t'8 ← PMem.ldF32 t'7
      PMem.stF32 (fp + 8) t'8
      let t'9 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      PMem.stF32 (fp + 36) (Binary32.abs t'9)
      let t'10 ← MAX'float_float (fp + 16) (fp + 36)
      let t'11 ← PMem.ldF32 t'10
      PMem.stF32 (fp + 16) t'11
      PMem.stF32 (fp + 40) (Binary32.ofBits 0x00000000 /- 0 -/)
      let t'12 ← MAX'float_float (fp + 40) ((this + 588) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 4).toUInt64)
      let t'13 ← MAX'float_float (fp + 24) t'12
      let t'14 ← PMem.ldF32 t'13
      PMem.stF32 (fp + 24) t'14
  for i'2'15 in [0:12] do
    let i'2 : UInt8 := UInt8.ofNat i'2'15
    let t'16 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 1).toUInt64)
    if t'16 then
      let t'17 ← PMem.ldF32 (fp + 0)
      let t'18 ← is_zero t'17
      if !t'18 then
        let t'19 ← PMem.ldF32 ((this + 444) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
        let t'20 ← PMem.ldF32 (fp + 0)
        let t'21 := (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'19) / t'20)
        PMem.stF32 ((this + 444) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64) t'21
      let t'22 ← PMem.ldF32 (fp + 8)
      let t'23 ← is_zero t'22
      if !t'23 then
        let t'24 ← PMem.ldF32 ((this + 492) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
        let t'25 ← PMem.ldF32 (fp + 8)
        let t'26 := (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'24) / t'25)
        PMem.stF32 ((this + 492) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64) t'26
      let t'27 ← PMem.ldF32 (fp + 16)
      let t'28 ← is_zero t'27
      if !t'28 then
        let t'29 ← PMem.ldF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
        let t'30 ← PMem.ldF32 (fp + 16)
        let t'31 := (((Binary32.ofBits 0x3f000000 /- 1/2 -/) * t'29) / t'30)
        PMem.stF32 ((this + 540) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64) t'31
      let t'32 ← PMem.ldF32 (fp + 24)
      let t'33 ← is_zero t'32
      if !t'33 then
        PMem.stF32 (fp + 44) (Binary32.ofBits 0x00000000 /- 0 -/)
        let t'34 ← PMem.ldF32 ((this + 588) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64)
        let t'35 ← PMem.ldF32 (fp + 24)
        PMem.stF32 (fp + 48) (t'34 / t'35)
        let t'36 ← MAX'float_float (fp + 44) (fp + 48)
        let t'37 ← PMem.ldF32 t'36
        PMem.stF32 ((this + 588) + ((UInt64.toInt64 (UInt8.toUInt64 (i'2))) * 4).toUInt64) t'37
  return ()

def AP_MotorsMatrix.normalise_rpy_factors (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 52
  let r ← AP_MotorsMatrix.normalise_rpy_factors.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_Motors::set_radio_passthrough : void (float, float, float, float)`, `AP_Motors_Class.cpp:89-95`. -/
def AP_Motors.set_radio_passthrough (this : UInt64) (roll_input : Binary32) (pitch_input : Binary32) (throttle_input : Binary32) (yaw_input : Binary32) : PMem.M Unit := do
  let mut roll_input := roll_input
  let mut pitch_input := pitch_input
  let mut throttle_input := throttle_input
  let mut yaw_input := yaw_input
  PMem.stF32 (this + 188) roll_input
  PMem.stF32 (this + 192) pitch_input
  PMem.stF32 (this + 196) throttle_input
  PMem.stF32 (this + 200) yaw_input
  return ()

/-- C++ `AP_Motors::is_normal_pwm_type : bool () const`, `<scratch space>:332-?`. -/
def AP_Motors.is_normal_pwm_type (this : UInt64) : PMem.M Bool := do
  let t'1 ← AP_Enum'AP_Motors_PWMType.operator_const_AP_Motors.PWMType (this + 204)
  let mut sc'3 := (t'1 == (0 : UInt8))
  if !sc'3 then
    let t'2 ← AP_Enum'AP_Motors_PWMType.operator_const_AP_Motors.PWMType (this + 204)
    sc'3 := (t'2 == (8 : UInt8))
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← AP_Enum'AP_Motors_PWMType.operator_const_AP_Motors.PWMType (this + 204)
    sc'5 := (t'4 == (9 : UInt8))
  return sc'5

/-- C++ `AP_Motors::set_dt_s : void (float)`, `<scratch space>:259-?`. -/
def AP_Motors.set_dt_s (this : UInt64) (dt_s : Binary32) : PMem.M Unit := do
  let mut dt_s := dt_s
  PMem.stF32 (this + 16) dt_s
  return ()

/-- C++ `AP_Motors::get_throttle_slew_rate : float () const`, `<scratch space>:221-?`. -/
def AP_Motors.get_throttle_slew_rate (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 56)
  return t'1

/-- C++ `AP_Motors::get_throttle_out : float () const`, `<scratch space>:215-?`. -/
def AP_Motors.get_throttle_out (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 52)
  return t'1

/-- C++ `AP_Motors::set_roll : void (float)`, `AP_Motors_Class.h:192-?`. -/
def AP_Motors.set_roll (this : UInt64) (roll_in : Binary32) : PMem.M Unit := do
  let mut roll_in := roll_in
  PMem.stF32 (this + 24) roll_in
  return ()

/-- C++ `AP_Motors::set_roll_ff : void (float)`, `AP_Motors_Class.h:193-?`. -/
def AP_Motors.set_roll_ff (this : UInt64) (roll_in : Binary32) : PMem.M Unit := do
  let mut roll_in := roll_in
  PMem.stF32 (this + 28) roll_in
  return ()

/-- C++ `AP_Motors::set_pitch : void (float)`, `AP_Motors_Class.h:194-?`. -/
def AP_Motors.set_pitch (this : UInt64) (pitch_in : Binary32) : PMem.M Unit := do
  let mut pitch_in := pitch_in
  PMem.stF32 (this + 32) pitch_in
  return ()

/-- C++ `AP_Motors::set_pitch_ff : void (float)`, `AP_Motors_Class.h:195-?`. -/
def AP_Motors.set_pitch_ff (this : UInt64) (pitch_in : Binary32) : PMem.M Unit := do
  let mut pitch_in := pitch_in
  PMem.stF32 (this + 36) pitch_in
  return ()

/-- C++ `AP_Motors::set_yaw : void (float)`, `AP_Motors_Class.h:196-?`. -/
def AP_Motors.set_yaw (this : UInt64) (yaw_in : Binary32) : PMem.M Unit := do
  let mut yaw_in := yaw_in
  PMem.stF32 (this + 40) yaw_in
  return ()

/-- C++ `AP_Motors::set_yaw_ff : void (float)`, `AP_Motors_Class.h:197-?`. -/
def AP_Motors.set_yaw_ff (this : UInt64) (yaw_in : Binary32) : PMem.M Unit := do
  let mut yaw_in := yaw_in
  PMem.stF32 (this + 44) yaw_in
  return ()

/-- C++ `AP_Motors::set_interlock : void (bool)`, `AP_Motors_Class.h:182-?`. -/
def AP_Motors.set_interlock (this : UInt64) (set' : Bool) : PMem.M Unit := do
  let mut set' := set'
  PMem.stB (this + 221) set'
  return ()

/-- C++ `AP_Motors::get_spool_state : enum SpoolState () const`, `<scratch space>:254-?`. -/
def AP_Motors.get_spool_state (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldU8 (this + 173)
  return t'1

/-- C++ `AP_MotorsMulticopter::get_throttle_thrust_max : float () const`, `<scratch space>:62-?`. -/
def AP_MotorsMulticopter.get_throttle_thrust_max (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← PMem.ldF32 (this + 368)
  return t'1

/-- C++ `AP_Motors::set_throttle_filter_cutoff : void (float)`, `<scratch space>:200-?`. -/
def AP_Motors.set_throttle_filter_cutoff.body (fp : UInt64) (this : UInt64) (filt_hz : Binary32) : PMem.M Unit := do
  PMem.stF32 (fp + 0) filt_hz
  LowPassFilter'float.set_cutoff_frequency (this + 72) (fp + 0)
  return ()

def AP_Motors.set_throttle_filter_cutoff (this : UInt64) (filt_hz : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_Motors.set_throttle_filter_cutoff.body fp this filt_hz
  PMem.leave fp
  return r

/-- C++ `AP_Motors::set_throttle : void (float)`, `AP_Motors_Class.h:198-?`. -/
def AP_Motors.set_throttle (this : UInt64) (throttle_in : Binary32) : PMem.M Unit := do
  let mut throttle_in := throttle_in
  PMem.stF32 (this + 48) throttle_in
  return ()

/-- C++ `AP_Motors::set_throttle_avg_max : void (float)`, `AP_Motors_Class.h:199-?`. -/
def AP_Motors.set_throttle_avg_max (this : UInt64) (throttle_avg_max : Binary32) : PMem.M Unit := do
  let mut throttle_avg_max := throttle_avg_max
  let t'1 ← constrain_value_line'float throttle_avg_max (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((199 : Int32)))
  PMem.stF32 (this + 68) t'1
  return ()

/-- C++ `AP_MotorsMatrix::get_lost_motor : uint8_t () const`, `AP_Motors_Class.h:69-?`. -/
def AP_MotorsMatrix.get_lost_motor (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldU8 (this + 744)
  return t'1

/-- C++ `AP_Motors::set_thrust_boost : void (bool)`, `<scratch space>:227-?`. -/
def AP_Motors.set_thrust_boost (this : UInt64) (enable : Bool) : PMem.M Unit := do
  let mut enable := enable
  PMem.stB (this + 205) enable
  return ()

/-- C++ `AP_Motors::get_desired_spool_state : enum DesiredSpoolState () const`, `<scratch space>:242-?`. -/
def AP_Motors.get_desired_spool_state (this : UInt64) : PMem.M UInt8 := do
  let t'1 ← PMem.ldU8 (this + 172)
  return t'1

/-- C++ `AP_MotorsMulticopter::update_throttle_hover : void (float)`, `AP_MotorsMulticopter.cpp:561-567`. -/
def AP_MotorsMulticopter.update_throttle_hover.body (fp : UInt64) (this : UInt64) (dt : Binary32) : PMem.M Unit := do
  let mut dt := dt
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 316)
  let t'2 ← PMem.ldI8 t'1
  if ((Int8.toInt32 (t'2)) != (UInt32.toInt32 ((0 : UInt32)))) then
    let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 312)
    let t'4 ← PMem.ldF32 t'3
    let t'5 ← AP_Motors.get_throttle this
    let t'6 ← AP_ParamT'float_4.operator_const_float__'1 (this + 312)
    let t'7 ← PMem.ldF32 t'6
    let t'8 ← constrain_value_line'float (t'4 + ((dt / (dt + (Binary32.ofBits 0x41200000 /- 10 -/))) * (t'5 - t'7))) (Binary32.ofBits 0x3e000000 /- 1/8 -/) (Binary32.ofBits 0x3f300000 /- 11/16 -/) (Int32.toUInt32 ((565 : Int32)))
    PMem.stF32 (fp + 0) t'8
    AP_ParamTBase'float_4.set (this + 312) (fp + 0)
  return ()

def AP_MotorsMulticopter.update_throttle_hover (this : UInt64) (dt : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_MotorsMulticopter.update_throttle_hover.body fp this dt
  PMem.leave fp
  return r

end Vehicle_lib
