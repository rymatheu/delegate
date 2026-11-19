import ArduLean.Runtime.Hal
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.Filter.Filter
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor
import ArduLean.Vehicle.libraries.SRV_Channel.SRV_Channel
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2
import ArduLean.Vehicle.libraries.Filter.Filter_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2

/-!
ArduPilot `libraries/AP_Motors`, part 2 of 2. Sources: `libraries/AP_Motors/AP_MotorsMulticopter.cpp`, `libraries/AP_Motors/AP_MotorsMatrix.cpp`, `libraries/AP_Motors/AP_Motors_Class.cpp`, `libraries/AP_Motors/AP_Motors_Thrust_Linearization.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_Motors::get_frame_and_type_string : void (char *, uint8_t) const`, `AP_Motors_Class.cpp:62-75`. -/
def AP_Motors.get_frame_and_type_string.body (fp : UInt64) (this : UInt64) (buffer : UInt64) (buflen : UInt8) : PMem.M Unit := do
  let mut buffer := buffer
  let mut buflen := buflen
  let t'1 ← AP_Motors.get_frame_string this
  let mut frame_str : UInt64 := t'1
  let t'2 ← AP_MotorsMatrix.get_type_string this
  let mut type_str : UInt64 := t'2
  let mut sc'4 := (type_str != (0 : UInt64))
  if sc'4 then
    let t'3 ← PMem.strlen type_str
    sc'4 := t'3 != (0 : UInt64)
  if sc'4 then
    PMem.stU64 (fp + 0) frame_str
    PMem.stU64 (fp + 8) type_str
    let t'5 ← AP_HAL.Util.snprintf (0 : UInt64) buffer (UInt8.toUInt64 (buflen)) (0x1ae2a : UInt64) /- "Frame: %s/%s" -/ (fp + 0)
    discard <| pure (t'5)
  else
    PMem.stU64 (fp + 16) frame_str
    let t'6 ← AP_HAL.Util.snprintf (0 : UInt64) buffer (UInt8.toUInt64 (buflen)) (0x1ae37 : UInt64) /- "Frame: %s" -/ (fp + 16)
    discard <| pure (t'6)
  return ()

def AP_Motors.get_frame_and_type_string (this : UInt64) (buffer : UInt64) (buflen : UInt8) : PMem.M Unit := do
  let fp ← PMem.enter 24
  let r ← AP_Motors.get_frame_and_type_string.body fp this buffer buflen
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMulticopter::save_params_on_disarm : void ()`, `AP_MotorsMulticopter.cpp:947-953`. -/
def AP_MotorsMulticopter.save_params_on_disarm (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 316)
  let t'2 ← PMem.ldI8 t'1
  if ((Int8.toInt32 (t'2)) == (UInt32.toInt32 ((2 : UInt32)))) then
    AP_Param.save (this + 312) false
  return ()

/-- C++ `AP_Motors::armed : void (bool)`, `AP_Motors_Class.cpp:77-86`. -/
def AP_Motors.armed'2 (this : UInt64) (arm : Bool) : PMem.M Unit := do
  let mut arm := arm
  let t'1 ← PMem.ldB (this + 220)
  if ((if t'1 then (1 : Int32) else (0 : Int32)) != (if arm then (1 : Int32) else (0 : Int32))) then
    PMem.stB (this + 220) arm
    PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 4) arm
    if !arm then
      AP_MotorsMulticopter.save_params_on_disarm this
  return ()

/-- C++ `AP_MotorsMulticopter::update_throttle_filter : void ()`, `AP_MotorsMulticopter.cpp:348-375`. -/
def AP_MotorsMulticopter.update_throttle_filter.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← DigitalLPF'float.get (this + 72)
  let t'2 ← PMem.ldF32 t'1
  let mut last_thr : Binary32 := t'2
  let t'3 ← AP_Motors.armed this
  if t'3 then
    let t'4 ← LowPassFilter'float.apply (this + 72) (this + 48) (this + 16)
    discard <| pure (t'4)
    let t'5 ← DigitalLPF'float.get (this + 72)
    let t'6 ← PMem.ldF32 t'5
    if (decide (t'6 < (Binary32.ofBits 0x00000000 /- 0 -/))) then
      PMem.stF32 (fp + 0) (Binary32.ofBits 0x00000000 /- 0 -/)
      DigitalLPF'float.reset (this + 72) (fp + 0)
    let t'7 ← DigitalLPF'float.get (this + 72)
    let t'8 ← PMem.ldF32 t'7
    if (decide (t'8 > (Binary32.ofBits 0x3f800000 /- 1 -/))) then
      PMem.stF32 (fp + 4) (Binary32.ofBits 0x3f800000 /- 1 -/)
      DigitalLPF'float.reset (this + 72) (fp + 4)
  else
    PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
    DigitalLPF'float.reset (this + 72) (fp + 8)
  let t'9 ← DigitalLPF'float.get (this + 72)
  let t'10 ← PMem.ldF32 t'9
  let mut new_thr : Binary32 := t'10
  let t'11 ← is_equal'float_float last_thr new_thr
  if !t'11 then
    DerivativeFilter'float_7.update (this + 88) new_thr ((← PMem.clock).toUInt32)
  let t'12 ← DerivativeFilter'float_7.slope (this + 88)
  PMem.stF32 (fp + 16) (Binary32.abs (t'12 * (Binary64.toBinary32 ((Binary64.ofBits 0x412e848000000000 /- 1000000 -/)))))
  let t'13 ← LowPassFilter'float.apply (this + 160) (fp + 16) (this + 16)
  PMem.stF32 (this + 56) t'13
  return ()

def AP_MotorsMulticopter.update_throttle_filter (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← AP_MotorsMulticopter.update_throttle_filter.body fp this
  PMem.leave fp
  return r

/-- C++ `Thrust_Linearization::update_lift_max_from_batt_voltage : void ()`, `AP_Motors_Thrust_Linearization.cpp:156-186`. -/
def Thrust_Linearization.update_lift_max_from_batt_voltage.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU64 (this + 48)
  let t'2 ← AP_Motors.has_option t'1 (1 : UInt8)
  let mut c'3 : Binary32 := default
  if t'2 then
    let t'4 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 12)
    let t'5 ← PMem.ldI8 t'4
    let t'6 ← AP.battery
    let t'7 ← AP_BattMonitor.voltage t'6 (Int8.toUInt8 (t'5))
    c'3 := t'7
  else
    let t'8 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 12)
    let t'9 ← PMem.ldI8 t'8
    let t'10 ← AP.battery
    let t'11 ← AP_BattMonitor.voltage_resting_estimate t'10 (Int8.toUInt8 (t'9))
    c'3 := t'11
  let mut _batt_voltage : Binary32 := c'3
  let t'12 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'13 ← PMem.ldF32 t'12
  let mut sc'15 := (decide (t'13 ≤ (Int32.toBinary32 ((0 : Int32)))))
  if !sc'15 then
    let t'14 ← AP_ParamT'float_4.operator__ (this + 20) (this + 16)
    sc'15 := t'14
  let mut sc'18 := sc'15
  if !sc'18 then
    let t'16 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
    let t'17 ← PMem.ldF32 t'16
    sc'18 := (decide (_batt_voltage < ((Binary64.toBinary32 ((Binary64.ofBits 0x3fd0000000000000 /- 1/4 -/))) * t'17)))
  if sc'18 then
    PMem.stF32 (fp + 0) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
    DigitalLPF'float.reset (this + 32) (fp + 0)
    let t'19 := Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))
    PMem.stF32 (this + 24) t'19
    return ()
  let t'20 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'21 ← PMem.ldF32 t'20
  PMem.stF32 (fp + 4) (t'21 * (Binary64.toBinary32 ((Binary64.ofBits 0x3fe3333333333333 /- 29999999999999999/50000000000000000 -/))))
  let t'22 ← MAX'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 20) (fp + 4)
  AP_ParamTBase'float_4.set (this + 20) t'22
  let t'23 ← AP_ParamT'float_4.operator_const_float__'1 (this + 20)
  let t'24 ← PMem.ldF32 t'23
  let t'25 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
  let t'26 ← PMem.ldF32 t'25
  let t'27 ← constrain_value_line'float _batt_voltage t'24 t'26 (Int32.toUInt32 ((172 : Int32)))
  _batt_voltage := t'27
  let t'28 ← PMem.ldU64 (this + 48)
  let t'29 ← AP_Motors.has_option t'28 (1 : UInt8)
  if !t'29 then
    let t'30 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'31 ← PMem.ldF32 t'30
    PMem.stF32 (fp + 8) (_batt_voltage / t'31)
    let t'32 ← PMem.ldU64 (this + 48)
    let t'33 ← AP_Motors.get_dt_s t'32
    PMem.stF32 (fp + 12) t'33
    let t'34 ← LowPassFilter'float.apply (this + 32) (fp + 8) (fp + 12)
    discard <| pure (t'34)
  else
    let t'35 ← AP_ParamT'float_4.operator_const_float__'1 (this + 16)
    let t'36 ← PMem.ldF32 t'35
    PMem.stF32 (fp + 16) (_batt_voltage / t'36)
    DigitalLPF'float.reset (this + 32) (fp + 16)
  let t'37 ← AP_ParamT'float_4.operator_const_float__'1 this
  let t'38 ← PMem.ldF32 t'37
  let t'39 ← constrain_value_line'float t'38 (-(Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) (Int32.toUInt32 ((183 : Int32)))
  let mut thrust_curve_expo : Binary32 := t'39
  let t'40 ← DigitalLPF'float.get (this + 32)
  let t'41 ← PMem.ldF32 t'40
  let t'42 ← DigitalLPF'float.get (this + 32)
  let t'43 ← PMem.ldF32 t'42
  let t'44 ← DigitalLPF'float.get (this + 32)
  let t'45 ← PMem.ldF32 t'44
  let t'46 := ((t'41 * ((Int32.toBinary32 ((1 : Int32))) - thrust_curve_expo)) + ((thrust_curve_expo * t'43) * t'45))
  PMem.stF32 (this + 24) t'46
  return ()

def Thrust_Linearization.update_lift_max_from_batt_voltage (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← Thrust_Linearization.update_lift_max_from_batt_voltage.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMulticopter::get_current_limit_max_throttle : float ()`, `AP_MotorsMulticopter.cpp:379-438`. -/
def AP_MotorsMulticopter.get_current_limit_max_throttle.body (fp : UInt64) (this : UInt64) : PMem.M Binary32 := do
  let t'1 ← AP.battery
  let battery : UInt64 := t'1
  let t'2 ← Thrust_Linearization.get_battery_index (this + 224)
  let mut batt_idx : UInt8 := Int8.toUInt8 (t'2)
  let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 300)
  let t'4 ← PMem.ldF32 t'3
  let mut sc'6 := (decide (t'4 ≤ (Int32.toBinary32 ((0 : Int32)))))
  if !sc'6 then
    let t'5 ← AP_Motors.armed this
    sc'6 := !t'5
  let mut sc'8 := sc'6
  if !sc'8 then
    let t'7 ← AP_BattMonitor.current_amps battery (fp + 0) batt_idx
    sc'8 := !t'7
  if sc'8 then
    let t'9 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    PMem.stF32 (this + 364) t'9
    return (Binary32.ofBits 0x3f800000 /- 1 -/)
  let t'10 ← AP_BattMonitor.get_resistance battery batt_idx
  let mut _batt_resistance : Binary32 := t'10
  let t'11 ← is_zero _batt_resistance
  if t'11 then
    let t'12 := (Binary32.ofBits 0x3f800000 /- 1 -/)
    PMem.stF32 (this + 364) t'12
    return (Binary32.ofBits 0x3f800000 /- 1 -/)
  let t'13 ← PMem.ldF32 (fp + 0)
  let t'14 ← AP_BattMonitor.voltage battery batt_idx
  let t'15 ← Thrust_Linearization.get_battery_min_voltage (this + 224)
  PMem.stF32 (fp + 4) (t'13 + ((t'14 - t'15) / _batt_resistance))
  let t'16 ← MIN'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 300) (fp + 4)
  let t'17 ← PMem.ldF32 t'16
  let mut batt_current_max : Binary32 := t'17
  let t'18 ← PMem.ldF32 (fp + 0)
  let mut batt_current_ratio : Binary32 := (t'18 / batt_current_max)
  let t'19 := (this + 364)
  let t'20 ← PMem.ldF32 t'19
  let t'21 ← PMem.ldF32 (this + 16)
  let t'22 ← PMem.ldF32 (this + 16)
  let t'23 ← AP_ParamT'float_4.operator_const_float__'1 (this + 304)
  let t'24 ← PMem.ldF32 t'23
  let t'25 := (t'20 + ((t'21 / (t'22 + t'24)) * ((Binary32.ofBits 0x3f800000 /- 1 -/) - batt_current_ratio)))
  PMem.stF32 t'19 t'25
  let t'26 ← PMem.ldF32 (this + 364)
  let t'27 ← constrain_value_line'float t'26 (Binary32.ofBits 0x3e4ccccd /- 200000003/1000000000 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((427 : Int32)))
  PMem.stF32 (this + 364) t'27
  let t'28 ← AP_MotorsMulticopter.get_throttle_hover this
  let t'29 ← AP_MotorsMulticopter.get_throttle_hover this
  let t'30 ← PMem.ldF32 (this + 364)
  return (t'28 + (((Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/))) - t'29) * t'30))

def AP_MotorsMulticopter.get_current_limit_max_throttle (this : UInt64) : PMem.M Binary32 := do
  let fp ← PMem.enter 8
  let r ← AP_MotorsMulticopter.get_current_limit_max_throttle.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMulticopter::output_logic : void ()`, `AP_MotorsMulticopter.cpp:595-888`. -/
def AP_MotorsMulticopter.output_logic.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  PMem.stF32 (fp + 0) (Binary32.ofBits 0x3d4ccccd /- 500000007/10000000000 -/)
  let t'1 ← AP_Motors.armed this
  if t'1 then
    let t'2 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 317)
    let t'3 ← PMem.ldI8 t'2
    let mut sc'7 := t'3 != (0 : Int8)
    if sc'7 then
      let t'4 ← PMem.ldF32 (this + 372)
      let t'5 ← AP_ParamT'float_4.operator_const_float__'1 (this + 292)
      let t'6 ← PMem.ldF32 t'5
      sc'7 := (decide (t'4 < t'6))
    if sc'7 then
      let t'8 := (this + 372)
      let t'9 ← PMem.ldF32 t'8
      let t'10 ← PMem.ldF32 (this + 16)
      let t'11 := (t'9 + t'10)
      PMem.stF32 t'8 t'11
    else
      let t'12 ← AP_ParamT'float_4.operator_const_float__'1 (this + 292)
      let t'13 ← PMem.ldF32 t'12
      PMem.stF32 (this + 372) t'13
  else
    let t'14 := (Binary32.ofBits 0x00000000 /- 0 -/)
    PMem.stF32 (this + 372) t'14
  let t'15 ← AP_Motors.armed this
  let mut sc'17 := !t'15
  if !sc'17 then
    let t'16 ← AP_Motors.get_interlock this
    sc'17 := !t'16
  if sc'17 then
    PMem.stU8 (this + 172) (0 : UInt8)
    PMem.stU8 (this + 173) (0 : UInt8)
  let t'18 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
  let t'19 ← PMem.ldF32 t'18
  let t'20 ← PMem.ldF32 (fp + 0)
  if (decide (t'19 < t'20)) then
    AP_ParamTBase'float_4.set (this + 324) (fp + 0)
  for _ in [0:1] do
    let t'21 ← PMem.ldU8 (this + 173)
    let sw'22 := t'21
    if sw'22 == (0 : UInt8) then
      AP_Motors.AP_Motors_limit.set_all (this + 8) true
      let t'23 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 (this + 352) t'23
      let t'24 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 (this + 368) t'24
      let t'25 := Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/))
      PMem.stF32 (this + 356) t'25
      PMem.stB (this + 205) false
      let t'26 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 (this + 208) t'26
      let t'27 ← PMem.ldU8 (this + 172)
      let mut sc'31 := (t'27 != (0 : UInt8))
      if sc'31 then
        let t'28 ← PMem.ldF32 (this + 372)
        let t'29 ← AP_ParamTBase'float_4.get (this + 292)
        let t'30 ← PMem.ldF32 t'29
        sc'31 := (decide (t'28 ≥ t'30))
      if sc'31 then
        PMem.stU8 (this + 173) (1 : UInt8)
    else if sw'22 == (1 : UInt8) then
      AP_Motors.AP_Motors_limit.set_all (this + 8) true
      PMem.stF32 (fp + 8) (Binary32.ofBits 0x00000000 /- 0 -/)
      let t'32 ← Thrust_Linearization.get_spin_min (this + 224)
      let t'33 ← is_positive'float t'32
      if t'33 then
        let t'34 ← AP_ParamT'float_4.operator_const_float__'1 (this + 296)
        let t'35 ← PMem.ldF32 t'34
        let t'36 ← Thrust_Linearization.get_spin_min (this + 224)
        let t'37 := (t'35 / t'36)
        PMem.stF32 (fp + 8) t'37
      let t'38 ← PMem.ldF32 (this + 352)
      let t'39 ← PMem.ldF32 (fp + 8)
      if (decide (t'38 ≥ t'39)) then
        let t'40 ← PMem.ldF32 (this + 356)
        let t'41 ← PMem.ldF32 (this + 16)
        PMem.stF32 (fp + 12) (t'40 + t'41)
        let t'42 ← MIN'AP_ParamT_float_AP_PARAM_FLOAT_float (this + 332) (fp + 12)
        let t'43 ← PMem.ldF32 t'42
        PMem.stF32 (this + 356) t'43
      for _ in [0:1] do
        let t'44 ← PMem.ldU8 (this + 172)
        let sw'45 := t'44
        if sw'45 == (0 : UInt8) then
          let t'46 ← AP_ParamT'float_4.operator_const_float__'1 (this + 328)
          let t'47 ← PMem.ldF32 t'46
          let t'48 ← PMem.ldF32 (fp + 0)
          let mut c'49 : UInt64 := 0
          if (decide (t'47 > t'48)) then
            c'49 := (this + 328)
          else
            c'49 := (this + 324)
          let t'50 ← AP_ParamT'float_4.operator_const_float__'1 c'49
          let t'51 ← PMem.ldF32 t'50
          let mut spool_time : Binary32 := t'51
          let t'52 ← PMem.ldF32 (this + 16)
          let mut spool_step : Binary32 := (t'52 / spool_time)
          let t'53 := (this + 352)
          let t'54 ← PMem.ldF32 t'53
          let t'55 := (t'54 - spool_step)
          PMem.stF32 t'53 t'55
          let t'56 ← PMem.ldF32 (this + 352)
          if (decide (t'56 ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
            let t'57 := (Binary32.ofBits 0x00000000 /- 0 -/)
            PMem.stF32 (this + 352) t'57
            PMem.stU8 (this + 173) (0 : UInt8)
          break
          let t'58 ← PMem.ldF32 (this + 16)
          let t'59 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
          let t'60 ← PMem.ldF32 t'59
          let mut spool_step'2 : Binary32 := (t'58 / t'60)
          let t'61 := (this + 352)
          let t'62 ← PMem.ldF32 t'61
          let t'63 := (t'62 + spool_step'2)
          PMem.stF32 t'61 t'63
          let t'64 ← PMem.ldF32 (this + 356)
          let t'65 ← AP_ParamT'float_4.operator_const_float__'1 (this + 332)
          let t'66 ← PMem.ldF32 t'65
          if (decide (t'64 < t'66)) then
            let t'67 ← MIN'float_float (this + 352) (fp + 8)
            let t'68 ← PMem.ldF32 t'67
            PMem.stF32 (this + 352) t'68
            break
          let t'69 ← PMem.ldF32 (this + 352)
          if (decide (t'69 < (Binary32.ofBits 0x3f800000 /- 1 -/))) then
            PMem.stB (this + 360) false
          else
            let t'70 := (Binary32.ofBits 0x3f800000 /- 1 -/)
            PMem.stF32 (this + 352) t'70
            let t'71 ← PMem.ldB (this + 360)
            if !t'71 then
              PMem.stB (this + 360) true
              AP_Motors.set_spoolup_block this true
          let t'72 ← PMem.ldB (this + 360)
          let mut sc'74 := t'72
          if sc'74 then
            let t'73 ← AP_Motors.get_spoolup_block this
            sc'74 := !t'73
          if sc'74 then
            PMem.stU8 (this + 173) (2 : UInt8)
          break
          let t'75 ← PMem.ldF32 (this + 16)
          let t'76 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
          let t'77 ← PMem.ldF32 t'76
          let mut spool_up_step : Binary32 := (t'75 / t'77)
          let t'78 ← AP_ParamT'float_4.operator_const_float__'1 (this + 328)
          let t'79 ← PMem.ldF32 t'78
          let t'80 ← PMem.ldF32 (fp + 0)
          let mut c'81 : UInt64 := 0
          if (decide (t'79 > t'80)) then
            c'81 := (this + 328)
          else
            c'81 := (this + 324)
          let t'82 ← AP_ParamT'float_4.operator_const_float__'1 c'81
          let t'83 ← PMem.ldF32 t'82
          let mut spool_down_time : Binary32 := t'83
          let t'84 ← PMem.ldF32 (this + 16)
          let mut spool_down_step : Binary32 := (t'84 / spool_down_time)
          let t'85 := (this + 352)
          let t'86 ← PMem.ldF32 t'85
          let t'87 ← PMem.ldF32 (fp + 8)
          let t'88 ← PMem.ldF32 (this + 352)
          let t'89 ← constrain_value_line'float (t'87 - t'88) (-spool_down_step) spool_up_step (Int32.toUInt32 ((760 : Int32)))
          let t'90 := (t'86 + t'89)
          PMem.stF32 t'85 t'90
          break
        else if sw'45 == (2 : UInt8) then
          let t'91 ← PMem.ldF32 (this + 16)
          let t'92 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
          let t'93 ← PMem.ldF32 t'92
          let mut spool_step'3 : Binary32 := (t'91 / t'93)
          let t'94 := (this + 352)
          let t'95 ← PMem.ldF32 t'94
          let t'96 := (t'95 + spool_step'3)
          PMem.stF32 t'94 t'96
          let t'97 ← PMem.ldF32 (this + 356)
          let t'98 ← AP_ParamT'float_4.operator_const_float__'1 (this + 332)
          let t'99 ← PMem.ldF32 t'98
          if (decide (t'97 < t'99)) then
            let t'100 ← MIN'float_float (this + 352) (fp + 8)
            let t'101 ← PMem.ldF32 t'100
            PMem.stF32 (this + 352) t'101
            break
          let t'102 ← PMem.ldF32 (this + 352)
          if (decide (t'102 < (Binary32.ofBits 0x3f800000 /- 1 -/))) then
            PMem.stB (this + 360) false
          else
            let t'103 := (Binary32.ofBits 0x3f800000 /- 1 -/)
            PMem.stF32 (this + 352) t'103
            let t'104 ← PMem.ldB (this + 360)
            if !t'104 then
              PMem.stB (this + 360) true
              AP_Motors.set_spoolup_block this true
          let t'105 ← PMem.ldB (this + 360)
          let mut sc'107 := t'105
          if sc'107 then
            let t'106 ← AP_Motors.get_spoolup_block this
            sc'107 := !t'106
          if sc'107 then
            PMem.stU8 (this + 173) (2 : UInt8)
          break
          let t'108 ← PMem.ldF32 (this + 16)
          let t'109 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
          let t'110 ← PMem.ldF32 t'109
          let mut spool_up_step'2 : Binary32 := (t'108 / t'110)
          let t'111 ← AP_ParamT'float_4.operator_const_float__'1 (this + 328)
          let t'112 ← PMem.ldF32 t'111
          let t'113 ← PMem.ldF32 (fp + 0)
          let mut c'114 : UInt64 := 0
          if (decide (t'112 > t'113)) then
            c'114 := (this + 328)
          else
            c'114 := (this + 324)
          let t'115 ← AP_ParamT'float_4.operator_const_float__'1 c'114
          let t'116 ← PMem.ldF32 t'115
          let mut spool_down_time'2 : Binary32 := t'116
          let t'117 ← PMem.ldF32 (this + 16)
          let mut spool_down_step'2 : Binary32 := (t'117 / spool_down_time'2)
          let t'118 := (this + 352)
          let t'119 ← PMem.ldF32 t'118
          let t'120 ← PMem.ldF32 (fp + 8)
          let t'121 ← PMem.ldF32 (this + 352)
          let t'122 ← constrain_value_line'float (t'120 - t'121) (-spool_down_step'2) spool_up_step'2 (Int32.toUInt32 ((760 : Int32)))
          let t'123 := (t'119 + t'122)
          PMem.stF32 t'118 t'123
          break
        else if sw'45 == (1 : UInt8) then
          let t'124 ← PMem.ldF32 (this + 16)
          let t'125 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
          let t'126 ← PMem.ldF32 t'125
          let mut spool_up_step'3 : Binary32 := (t'124 / t'126)
          let t'127 ← AP_ParamT'float_4.operator_const_float__'1 (this + 328)
          let t'128 ← PMem.ldF32 t'127
          let t'129 ← PMem.ldF32 (fp + 0)
          let mut c'130 : UInt64 := 0
          if (decide (t'128 > t'129)) then
            c'130 := (this + 328)
          else
            c'130 := (this + 324)
          let t'131 ← AP_ParamT'float_4.operator_const_float__'1 c'130
          let t'132 ← PMem.ldF32 t'131
          let mut spool_down_time'3 : Binary32 := t'132
          let t'133 ← PMem.ldF32 (this + 16)
          let mut spool_down_step'3 : Binary32 := (t'133 / spool_down_time'3)
          let t'134 := (this + 352)
          let t'135 ← PMem.ldF32 t'134
          let t'136 ← PMem.ldF32 (fp + 8)
          let t'137 ← PMem.ldF32 (this + 352)
          let t'138 ← constrain_value_line'float (t'136 - t'137) (-spool_down_step'3) spool_up_step'3 (Int32.toUInt32 ((760 : Int32)))
          let t'139 := (t'135 + t'138)
          PMem.stF32 t'134 t'139
          break
        else
          pure ()
      let t'140 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 (this + 368) t'140
      PMem.stB (this + 205) false
      let t'141 := (Binary32.ofBits 0x00000000 /- 0 -/)
      PMem.stF32 (this + 208) t'141
      break
      let t'142 ← PMem.ldF32 (this + 16)
      let t'143 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
      let t'144 ← PMem.ldF32 t'143
      let mut spool_step'4 : Binary32 := (t'142 / t'144)
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'145 ← PMem.ldU8 (this + 172)
      if (t'145 != (2 : UInt8)) then
        PMem.stU8 (this + 173) (4 : UInt8)
        break
      let t'146 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'146
      let t'147 := (this + 368)
      let t'148 ← PMem.ldF32 t'147
      let t'149 := (t'148 + spool_step'4)
      PMem.stF32 t'147 t'149
      let t'150 ← PMem.ldF32 (this + 368)
      let t'151 ← AP_Motors.get_throttle this
      PMem.stF32 (fp + 16) t'151
      let t'152 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      PMem.stF32 (fp + 20) t'152
      let t'153 ← MIN'float_float (fp + 16) (fp + 20)
      let t'154 ← PMem.ldF32 t'153
      if (decide (t'150 ≥ t'154)) then
        let t'155 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
        PMem.stF32 (this + 368) t'155
        PMem.stU8 (this + 173) (3 : UInt8)
      else
        let t'156 ← PMem.ldF32 (this + 368)
        if (decide (t'156 < (Binary32.ofBits 0x00000000 /- 0 -/))) then
          let t'157 := (Binary32.ofBits 0x00000000 /- 0 -/)
          PMem.stF32 (this + 368) t'157
      PMem.stB (this + 205) false
      PMem.stF32 (fp + 24) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
      let t'158 ← PMem.ldF32 (this + 208)
      PMem.stF32 (fp + 28) (t'158 - spool_step'4)
      let t'159 ← MAX'float_float (fp + 24) (fp + 28)
      let t'160 ← PMem.ldF32 t'159
      PMem.stF32 (this + 208) t'160
      break
      let t'161 ← PMem.ldF32 (this + 16)
      let t'162 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
      let t'163 ← PMem.ldF32 t'162
      let mut spool_step'5 : Binary32 := (t'161 / t'163)
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'164 ← PMem.ldU8 (this + 172)
      if (t'164 != (2 : UInt8)) then
        PMem.stU8 (this + 173) (4 : UInt8)
        break
      let t'165 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'165
      let t'166 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      PMem.stF32 (this + 368) t'166
      let t'167 ← PMem.ldB (this + 205)
      let mut sc'169 := t'167
      if sc'169 then
        let t'168 ← PMem.ldB (this + 206)
        sc'169 := !t'168
      if sc'169 then
        PMem.stF32 (fp + 32) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
        let t'170 ← PMem.ldF32 (this + 208)
        PMem.stF32 (fp + 36) (t'170 + spool_step'5)
        let t'171 ← MIN'float_float (fp + 32) (fp + 36)
        let t'172 ← PMem.ldF32 t'171
        PMem.stF32 (this + 208) t'172
      else
        PMem.stF32 (fp + 40) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
        let t'173 ← PMem.ldF32 (this + 208)
        PMem.stF32 (fp + 44) (t'173 - spool_step'5)
        let t'174 ← MAX'float_float (fp + 40) (fp + 44)
        let t'175 ← PMem.ldF32 t'174
        PMem.stF32 (this + 208) t'175
      break
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'176 ← PMem.ldU8 (this + 172)
      if (t'176 == (2 : UInt8)) then
        PMem.stU8 (this + 173) (2 : UInt8)
        break
      let t'177 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'177
      let t'178 ← AP_ParamT'float_4.operator_const_float__'1 (this + 328)
      let t'179 ← PMem.ldF32 t'178
      let t'180 ← PMem.ldF32 (fp + 0)
      let mut c'181 : UInt64 := 0
      if (decide (t'179 > t'180)) then
        c'181 := (this + 328)
      else
        c'181 := (this + 324)
      let t'182 ← AP_ParamT'float_4.operator_const_float__'1 c'181
      let t'183 ← PMem.ldF32 t'182
      let mut spool_time'2 : Binary32 := t'183
      let t'184 ← PMem.ldF32 (this + 16)
      let mut spool_step'6 : Binary32 := (t'184 / spool_time'2)
      let t'185 := (this + 368)
      let t'186 ← PMem.ldF32 t'185
      let t'187 := (t'186 - spool_step'6)
      PMem.stF32 t'185 t'187
      let t'188 ← PMem.ldF32 (this + 368)
      if (decide (t'188 ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
        let t'189 := (Binary32.ofBits 0x00000000 /- 0 -/)
        PMem.stF32 (this + 368) t'189
      let t'190 ← PMem.ldF32 (this + 368)
      let t'191 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      if (decide (t'190 ≥ t'191)) then
        let t'192 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
        PMem.stF32 (this + 368) t'192
      else
        let t'193 ← PMem.ldF32 (this + 368)
        let t'194 ← is_zero t'193
        if t'194 then
          PMem.stU8 (this + 173) (1 : UInt8)
      PMem.stF32 (fp + 48) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
      let t'195 ← PMem.ldF32 (this + 208)
      PMem.stF32 (fp + 52) (t'195 - spool_step'6)
      let t'196 ← MAX'float_float (fp + 48) (fp + 52)
      let t'197 ← PMem.ldF32 t'196
      PMem.stF32 (this + 208) t'197
    else if sw'22 == (2 : UInt8) then
      let t'198 ← PMem.ldF32 (this + 16)
      let t'199 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
      let t'200 ← PMem.ldF32 t'199
      let mut spool_step'7 : Binary32 := (t'198 / t'200)
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'201 ← PMem.ldU8 (this + 172)
      if (t'201 != (2 : UInt8)) then
        PMem.stU8 (this + 173) (4 : UInt8)
        break
      let t'202 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'202
      let t'203 := (this + 368)
      let t'204 ← PMem.ldF32 t'203
      let t'205 := (t'204 + spool_step'7)
      PMem.stF32 t'203 t'205
      let t'206 ← PMem.ldF32 (this + 368)
      let t'207 ← AP_Motors.get_throttle this
      PMem.stF32 (fp + 56) t'207
      let t'208 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      PMem.stF32 (fp + 60) t'208
      let t'209 ← MIN'float_float (fp + 56) (fp + 60)
      let t'210 ← PMem.ldF32 t'209
      if (decide (t'206 ≥ t'210)) then
        let t'211 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
        PMem.stF32 (this + 368) t'211
        PMem.stU8 (this + 173) (3 : UInt8)
      else
        let t'212 ← PMem.ldF32 (this + 368)
        if (decide (t'212 < (Binary32.ofBits 0x00000000 /- 0 -/))) then
          let t'213 := (Binary32.ofBits 0x00000000 /- 0 -/)
          PMem.stF32 (this + 368) t'213
      PMem.stB (this + 205) false
      PMem.stF32 (fp + 64) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
      let t'214 ← PMem.ldF32 (this + 208)
      PMem.stF32 (fp + 68) (t'214 - spool_step'7)
      let t'215 ← MAX'float_float (fp + 64) (fp + 68)
      let t'216 ← PMem.ldF32 t'215
      PMem.stF32 (this + 208) t'216
      break
      let t'217 ← PMem.ldF32 (this + 16)
      let t'218 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
      let t'219 ← PMem.ldF32 t'218
      let mut spool_step'8 : Binary32 := (t'217 / t'219)
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'220 ← PMem.ldU8 (this + 172)
      if (t'220 != (2 : UInt8)) then
        PMem.stU8 (this + 173) (4 : UInt8)
        break
      let t'221 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'221
      let t'222 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      PMem.stF32 (this + 368) t'222
      let t'223 ← PMem.ldB (this + 205)
      let mut sc'225 := t'223
      if sc'225 then
        let t'224 ← PMem.ldB (this + 206)
        sc'225 := !t'224
      if sc'225 then
        PMem.stF32 (fp + 72) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
        let t'226 ← PMem.ldF32 (this + 208)
        PMem.stF32 (fp + 76) (t'226 + spool_step'8)
        let t'227 ← MIN'float_float (fp + 72) (fp + 76)
        let t'228 ← PMem.ldF32 t'227
        PMem.stF32 (this + 208) t'228
      else
        PMem.stF32 (fp + 80) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
        let t'229 ← PMem.ldF32 (this + 208)
        PMem.stF32 (fp + 84) (t'229 - spool_step'8)
        let t'230 ← MAX'float_float (fp + 80) (fp + 84)
        let t'231 ← PMem.ldF32 t'230
        PMem.stF32 (this + 208) t'231
      break
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'232 ← PMem.ldU8 (this + 172)
      if (t'232 == (2 : UInt8)) then
        PMem.stU8 (this + 173) (2 : UInt8)
        break
      let t'233 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'233
      let t'234 ← AP_ParamT'float_4.operator_const_float__'1 (this + 328)
      let t'235 ← PMem.ldF32 t'234
      let t'236 ← PMem.ldF32 (fp + 0)
      let mut c'237 : UInt64 := 0
      if (decide (t'235 > t'236)) then
        c'237 := (this + 328)
      else
        c'237 := (this + 324)
      let t'238 ← AP_ParamT'float_4.operator_const_float__'1 c'237
      let t'239 ← PMem.ldF32 t'238
      let mut spool_time'3 : Binary32 := t'239
      let t'240 ← PMem.ldF32 (this + 16)
      let mut spool_step'9 : Binary32 := (t'240 / spool_time'3)
      let t'241 := (this + 368)
      let t'242 ← PMem.ldF32 t'241
      let t'243 := (t'242 - spool_step'9)
      PMem.stF32 t'241 t'243
      let t'244 ← PMem.ldF32 (this + 368)
      if (decide (t'244 ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
        let t'245 := (Binary32.ofBits 0x00000000 /- 0 -/)
        PMem.stF32 (this + 368) t'245
      let t'246 ← PMem.ldF32 (this + 368)
      let t'247 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      if (decide (t'246 ≥ t'247)) then
        let t'248 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
        PMem.stF32 (this + 368) t'248
      else
        let t'249 ← PMem.ldF32 (this + 368)
        let t'250 ← is_zero t'249
        if t'250 then
          PMem.stU8 (this + 173) (1 : UInt8)
      PMem.stF32 (fp + 88) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
      let t'251 ← PMem.ldF32 (this + 208)
      PMem.stF32 (fp + 92) (t'251 - spool_step'9)
      let t'252 ← MAX'float_float (fp + 88) (fp + 92)
      let t'253 ← PMem.ldF32 t'252
      PMem.stF32 (this + 208) t'253
    else if sw'22 == (3 : UInt8) then
      let t'254 ← PMem.ldF32 (this + 16)
      let t'255 ← AP_ParamT'float_4.operator_const_float__'1 (this + 324)
      let t'256 ← PMem.ldF32 t'255
      let mut spool_step'10 : Binary32 := (t'254 / t'256)
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'257 ← PMem.ldU8 (this + 172)
      if (t'257 != (2 : UInt8)) then
        PMem.stU8 (this + 173) (4 : UInt8)
        break
      let t'258 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'258
      let t'259 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      PMem.stF32 (this + 368) t'259
      let t'260 ← PMem.ldB (this + 205)
      let mut sc'262 := t'260
      if sc'262 then
        let t'261 ← PMem.ldB (this + 206)
        sc'262 := !t'261
      if sc'262 then
        PMem.stF32 (fp + 96) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
        let t'263 ← PMem.ldF32 (this + 208)
        PMem.stF32 (fp + 100) (t'263 + spool_step'10)
        let t'264 ← MIN'float_float (fp + 96) (fp + 100)
        let t'265 ← PMem.ldF32 t'264
        PMem.stF32 (this + 208) t'265
      else
        PMem.stF32 (fp + 104) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
        let t'266 ← PMem.ldF32 (this + 208)
        PMem.stF32 (fp + 108) (t'266 - spool_step'10)
        let t'267 ← MAX'float_float (fp + 104) (fp + 108)
        let t'268 ← PMem.ldF32 t'267
        PMem.stF32 (this + 208) t'268
      break
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'269 ← PMem.ldU8 (this + 172)
      if (t'269 == (2 : UInt8)) then
        PMem.stU8 (this + 173) (2 : UInt8)
        break
      let t'270 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'270
      let t'271 ← AP_ParamT'float_4.operator_const_float__'1 (this + 328)
      let t'272 ← PMem.ldF32 t'271
      let t'273 ← PMem.ldF32 (fp + 0)
      let mut c'274 : UInt64 := 0
      if (decide (t'272 > t'273)) then
        c'274 := (this + 328)
      else
        c'274 := (this + 324)
      let t'275 ← AP_ParamT'float_4.operator_const_float__'1 c'274
      let t'276 ← PMem.ldF32 t'275
      let mut spool_time'4 : Binary32 := t'276
      let t'277 ← PMem.ldF32 (this + 16)
      let mut spool_step'11 : Binary32 := (t'277 / spool_time'4)
      let t'278 := (this + 368)
      let t'279 ← PMem.ldF32 t'278
      let t'280 := (t'279 - spool_step'11)
      PMem.stF32 t'278 t'280
      let t'281 ← PMem.ldF32 (this + 368)
      if (decide (t'281 ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
        let t'282 := (Binary32.ofBits 0x00000000 /- 0 -/)
        PMem.stF32 (this + 368) t'282
      let t'283 ← PMem.ldF32 (this + 368)
      let t'284 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      if (decide (t'283 ≥ t'284)) then
        let t'285 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
        PMem.stF32 (this + 368) t'285
      else
        let t'286 ← PMem.ldF32 (this + 368)
        let t'287 ← is_zero t'286
        if t'287 then
          PMem.stU8 (this + 173) (1 : UInt8)
      PMem.stF32 (fp + 112) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
      let t'288 ← PMem.ldF32 (this + 208)
      PMem.stF32 (fp + 116) (t'288 - spool_step'11)
      let t'289 ← MAX'float_float (fp + 112) (fp + 116)
      let t'290 ← PMem.ldF32 t'289
      PMem.stF32 (this + 208) t'290
    else if sw'22 == (4 : UInt8) then
      AP_Motors.AP_Motors_limit.set_all (this + 8) false
      let t'291 ← PMem.ldU8 (this + 172)
      if (t'291 == (2 : UInt8)) then
        PMem.stU8 (this + 173) (2 : UInt8)
        break
      let t'292 := (Binary32.ofBits 0x3f800000 /- 1 -/)
      PMem.stF32 (this + 352) t'292
      let t'293 ← AP_ParamT'float_4.operator_const_float__'1 (this + 328)
      let t'294 ← PMem.ldF32 t'293
      let t'295 ← PMem.ldF32 (fp + 0)
      let mut c'296 : UInt64 := 0
      if (decide (t'294 > t'295)) then
        c'296 := (this + 328)
      else
        c'296 := (this + 324)
      let t'297 ← AP_ParamT'float_4.operator_const_float__'1 c'296
      let t'298 ← PMem.ldF32 t'297
      let mut spool_time'5 : Binary32 := t'298
      let t'299 ← PMem.ldF32 (this + 16)
      let mut spool_step'12 : Binary32 := (t'299 / spool_time'5)
      let t'300 := (this + 368)
      let t'301 ← PMem.ldF32 t'300
      let t'302 := (t'301 - spool_step'12)
      PMem.stF32 t'300 t'302
      let t'303 ← PMem.ldF32 (this + 368)
      if (decide (t'303 ≤ (Binary32.ofBits 0x00000000 /- 0 -/))) then
        let t'304 := (Binary32.ofBits 0x00000000 /- 0 -/)
        PMem.stF32 (this + 368) t'304
      let t'305 ← PMem.ldF32 (this + 368)
      let t'306 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
      if (decide (t'305 ≥ t'306)) then
        let t'307 ← AP_MotorsMulticopter.get_current_limit_max_throttle this
        PMem.stF32 (this + 368) t'307
      else
        let t'308 ← PMem.ldF32 (this + 368)
        let t'309 ← is_zero t'308
        if t'309 then
          PMem.stU8 (this + 173) (1 : UInt8)
      PMem.stF32 (fp + 120) (Binary64.toBinary32 ((Binary64.ofBits 0x0000000000000000 /- 0 -/)))
      let t'310 ← PMem.ldF32 (this + 208)
      PMem.stF32 (fp + 124) (t'310 - spool_step'12)
      let t'311 ← MAX'float_float (fp + 120) (fp + 124)
      let t'312 ← PMem.ldF32 t'311
      PMem.stF32 (this + 208) t'312
    else
      pure ()
  return ()

def AP_MotorsMulticopter.output_logic (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 128
  let r ← AP_MotorsMulticopter.output_logic.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMatrix::thrust_compensation : void ()`, `AP_MotorsMatrix.cpp:1396-1401`. -/
def AP_MotorsMatrix.thrust_compensation (this : UInt64) : PMem.M Unit := do
  let t'1 ← Functor'void_float_unsigned_char.operator_bool (this + 376)
  if t'1 then
    Functor'void_float_unsigned_char.operator__ (this + 376) (this + 636) (Int8.toUInt8 (Int32.toInt8 ((12 : Int32))))
  return ()

/-- C++ `AP_Motors::rc_write : void (uint8_t, uint16_t)`, `AP_Motors_Class.cpp:100-109`. -/
def AP_Motors.rc_write (this : UInt64) (chan : UInt8) (pwm : UInt16) : PMem.M Unit := do
  let mut chan := chan
  let mut pwm := pwm
  let t'1 ← SRV_Channels.get_motor_function chan
  let mut function : Int32 := t'1
  let t'2 ← PMem.ldU32 (this + 180)
  if (((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (chan)))))) &&& t'2) != (0 : UInt32) then
    let t'3 ← PMem.ldF32 ((this + 180) + 4)
    SRV_Channels.set_output_scaled function ((UInt16.toBinary32 (pwm)) - t'3)
  else
    SRV_Channels.set_output_pwm function pwm
  return ()

/-- C++ `AP_MotorsMulticopter::set_actuator_with_slew : void (float &, float)`, `AP_MotorsMulticopter.cpp:484-511`. -/
def AP_MotorsMulticopter.set_actuator_with_slew.body (fp : UInt64) (this : UInt64) (actuator_output : UInt64) (input : Binary32) : PMem.M Unit := do
  let mut input := input
  let mut output_slew_limit_up : Binary32 := (Binary32.ofBits 0x3f800000 /- 1 -/)
  let mut output_slew_limit_dn : Binary32 := (Binary32.ofBits 0x00000000 /- 0 -/)
  discard <| PMem.memcpy (fp + 0) (this + 284) 4
  let t'1 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 0)
  if t'1 then
    let t'2 ← PMem.ldF32 (this + 16)
    let t'3 ← AP_ParamT'float_4.operator_const_float__'1 (this + 284)
    let t'4 ← PMem.ldF32 t'3
    let t'5 ← constrain_value_line'float t'4 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f000000 /- 1/2 -/) (Int32.toUInt32 ((499 : Int32)))
    let mut output_delta_up_max : Binary32 := (t'2 / t'5)
    let t'6 ← PMem.ldF32 actuator_output
    let t'7 ← constrain_value_line'float (t'6 + output_delta_up_max) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((500 : Int32)))
    output_slew_limit_up := t'7
  discard <| PMem.memcpy (fp + 8) (this + 288) 4
  let t'8 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 8)
  if t'8 then
    let t'9 ← PMem.ldF32 (this + 16)
    let t'10 ← AP_ParamT'float_4.operator_const_float__'1 (this + 288)
    let t'11 ← PMem.ldF32 t'10
    let t'12 ← constrain_value_line'float t'11 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f000000 /- 1/2 -/) (Int32.toUInt32 ((505 : Int32)))
    let mut output_delta_dn_max : Binary32 := (t'9 / t'12)
    let t'13 ← PMem.ldF32 actuator_output
    let t'14 ← constrain_value_line'float (t'13 - output_delta_dn_max) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((506 : Int32)))
    output_slew_limit_dn := t'14
  let t'15 ← constrain_value_line'float input output_slew_limit_dn output_slew_limit_up (Int32.toUInt32 ((510 : Int32)))
  PMem.stF32 actuator_output t'15
  return ()

def AP_MotorsMulticopter.set_actuator_with_slew (this : UInt64) (actuator_output : UInt64) (input : Binary32) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← AP_MotorsMulticopter.set_actuator_with_slew.body fp this actuator_output input
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMatrix::output_to_motors : void ()`, `AP_MotorsMatrix.cpp:144-184`. -/
def AP_MotorsMatrix.output_to_motors (this : UInt64) : PMem.M Unit := do
  let mut i : Int8 := default  -- uninitialized in C
  for _ in [0:1] do
    let t'1 ← PMem.ldU8 (this + 173)
    let sw'2 := t'1
    if sw'2 == (0 : UInt8) then
      for i'2'3 in [0:12] do
        let i'2 : Int8 := Int8.ofNat i'2'3
        let t'4 ← AP_MotorsMulticopter.motor_enabled_mask this (Int8.toUInt8 (i'2))
        if t'4 then
          let t'5 := (Binary32.ofBits 0x00000000 /- 0 -/)
          PMem.stF32 ((this + 392) + ((Int8.toInt64 (i'2)) * 4).toUInt64) t'5
      break
      for i'3'6 in [0:12] do
        let i'3 : Int8 := Int8.ofNat i'3'6
        let t'7 ← PMem.ldB ((this + 340) + ((Int8.toInt64 (i'3)) * 1).toUInt64)
        if t'7 then
          let t'8 ← AP_MotorsMulticopter.actuator_spin_up_to_ground_idle this
          AP_MotorsMulticopter.set_actuator_with_slew this ((this + 392) + ((Int8.toInt64 (i'3)) * 4).toUInt64) t'8
    else if sw'2 == (1 : UInt8) then
      for i'4'9 in [0:12] do
        let i'4 : Int8 := Int8.ofNat i'4'9
        let t'10 ← PMem.ldB ((this + 340) + ((Int8.toInt64 (i'4)) * 1).toUInt64)
        if t'10 then
          let t'11 ← AP_MotorsMulticopter.actuator_spin_up_to_ground_idle this
          AP_MotorsMulticopter.set_actuator_with_slew this ((this + 392) + ((Int8.toInt64 (i'4)) * 4).toUInt64) t'11
    else if sw'2 == (2 : UInt8) || sw'2 == (3 : UInt8) || sw'2 == (4 : UInt8) then
      for i'5'12 in [0:12] do
        let i'5 : Int8 := Int8.ofNat i'5'12
        let t'13 ← PMem.ldB ((this + 340) + ((Int8.toInt64 (i'5)) * 1).toUInt64)
        if t'13 then
          let t'14 ← PMem.ldF32 ((this + 636) + ((Int8.toInt64 (i'5)) * 4).toUInt64)
          let t'15 ← Thrust_Linearization.thrust_to_actuator (this + 224) t'14
          AP_MotorsMulticopter.set_actuator_with_slew this ((this + 392) + ((Int8.toInt64 (i'5)) * 4).toUInt64) t'15
    else
      pure ()
  for i'6'16 in [0:12] do
    let i'6 : Int8 := Int8.ofNat i'6'16
    let t'17 ← PMem.ldB ((this + 340) + ((Int8.toInt64 (i'6)) * 1).toUInt64)
    if t'17 then
      let t'18 ← PMem.ldF32 ((this + 392) + ((Int8.toInt64 (i'6)) * 4).toUInt64)
      let t'19 ← AP_MotorsMulticopter.output_to_pwm this t'18
      AP_Motors.rc_write this (Int8.toUInt8 (i'6)) (Int16.toUInt16 (t'19))
  return ()

/-- C++ `AP_MotorsMulticopter::output_boost_throttle : void ()`, `AP_MotorsMulticopter.cpp:320-328`. -/
def AP_MotorsMulticopter.output_boost_throttle (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamT'float_4.operator_const_float__'1 (this + 336)
  let t'2 ← PMem.ldF32 t'1
  if (decide (t'2 > (Int32.toBinary32 ((0 : Int32))))) then
    let t'3 ← AP_Motors.get_throttle this
    let t'4 ← AP_ParamT'float_4.operator_const_float__'1 (this + 336)
    let t'5 ← PMem.ldF32 t'4
    let t'6 ← constrain_value_line'float (t'3 * t'5) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int32.toUInt32 ((323 : Int32)))
    let mut throttle : Binary32 := t'6
    SRV_Channels.set_output_scaled (81 : Int32) (throttle * (Int32.toBinary32 ((1000 : Int32))))
  else
    SRV_Channels.set_output_scaled (81 : Int32) (Int32.toBinary32 ((0 : Int32)))
  return ()

/-- C++ `AP_MotorsMulticopter::output_rpyt : void ()`, `AP_MotorsMulticopter.cpp:331-337`. -/
def AP_MotorsMulticopter.output_rpyt (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldF32 (this + 28)
  SRV_Channels.set_output_scaled (124 : Int32) (t'1 * (Int32.toBinary32 ((4500 : Int32))))
  let t'2 ← PMem.ldF32 (this + 36)
  SRV_Channels.set_output_scaled (125 : Int32) (t'2 * (Int32.toBinary32 ((4500 : Int32))))
  let t'3 ← PMem.ldF32 (this + 44)
  SRV_Channels.set_output_scaled (127 : Int32) (t'3 * (Int32.toBinary32 ((4500 : Int32))))
  let t'4 ← AP_Motors.get_throttle this
  SRV_Channels.set_output_scaled (126 : Int32) (t'4 * (Int32.toBinary32 ((1000 : Int32))))
  return ()

/-- C++ `AP_MotorsMulticopter::output : void ()`, `AP_MotorsMulticopter.cpp:273-304`. -/
def AP_MotorsMulticopter.output (this : UInt64) : PMem.M Unit := do
  AP_MotorsMulticopter.update_throttle_filter this
  Thrust_Linearization.update_lift_max_from_batt_voltage (this + 224)
  AP_MotorsMulticopter.output_logic this
  AP_MotorsMatrix.output_armed_stabilizing this
  AP_MotorsMatrix.thrust_compensation this
  AP_MotorsMatrix.output_to_motors this
  AP_MotorsMulticopter.output_boost_throttle this
  AP_MotorsMulticopter.output_rpyt this
  AP_MotorsMulticopter.update_external_limits this
  let t'1 := Int32.toUInt32 ((0 : Int32))
  PMem.stU32 (this + 440) t'1
  return ()

/-- C++ `AP_MotorsMulticopter::output_min : void ()`, `AP_MotorsMulticopter.cpp:340-345`. -/
def AP_MotorsMulticopter.output_min (this : UInt64) : PMem.M Unit := do
  AP_MotorsMulticopter.set_desired_spool_state this (0 : UInt8)
  PMem.stU8 (this + 173) (0 : UInt8)
  AP_MotorsMulticopter.output this
  return ()

/-- C++ `AP_Motors::arming_checks : bool (size_t, char *) const`, `AP_Motors_Class.cpp:322-330`. -/
def AP_Motors.arming_checks.body (fp : UInt64) (this : UInt64) (buflen : UInt64) (buffer : UInt64) : PMem.M Bool := do
  let mut buflen := buflen
  let mut buffer := buffer
  let t'1 ← AP_Motors.initialised_ok this
  if !t'1 then
    let t'2 ← AP_HAL.Util.snprintf (0 : UInt64) buffer buflen (0x1ae41 : UInt64) /- "Check frame class and type" -/ (fp + 0)
    discard <| pure (t'2)
    return false
  return true

def AP_Motors.arming_checks (this : UInt64) (buflen : UInt64) (buffer : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Motors.arming_checks.body fp this buflen buffer
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMulticopter::arming_checks : bool (size_t, char *) const`, `AP_MotorsMulticopter.cpp:965-1000`. -/
def AP_MotorsMulticopter.arming_checks.body (fp : UInt64) (this : UInt64) (buflen : UInt64) (buffer : UInt64) : PMem.M Bool := do
  let mut buflen := buflen
  let mut buffer := buffer
  let t'1 ← AP_Motors.arming_checks this buflen buffer
  if !t'1 then
    return false
  for i'2 in [0:12] do
    let i : UInt8 := UInt8.ofNat i'2
    let t'3 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    if !t'3 then
      continue
    let t'4 ← SRV_Channels.get_motor_function i
    let mut function : Int32 := t'4
    let t'5 ← SRV_Channels.find_channel function (fp + 0)
    if !t'5 then
      PMem.stU64 (fp + 8) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      let t'6 ← AP_HAL.Util.snprintf (0 : UInt64) buffer buflen (0x1afd2 : UInt64) /- "no SERVOx_FUNCTION set to Motor%u" -/ (fp + 8)
      discard <| pure (t'6)
      return false
  let t'7 ← Thrust_Linearization.get_spin_min (this + 224)
  if (decide (t'7 > (Binary64.toBinary32 ((Binary64.ofBits 0x3fd3333333333333 /- 29999999999999999/100000000000000000 -/))))) then
    PMem.stU64 (fp + 16) (0x14208 : UInt64) /- "MOT_" -/
    let t'8 ← Thrust_Linearization.get_spin_min (this + 224)
    PMem.stU64 (fp + 24) (Binary64.toBits (Binary32.toBinary64 (t'8)))
    let t'9 ← AP_HAL.Util.snprintf (0 : UInt64) buffer buflen (0x1aff4 : UInt64) /- "%sSPIN_MIN too high %.2f > 0.3" -/ (fp + 16)
    discard <| pure (t'9)
    return false
  let t'10 ← AP_ParamT'float_4.operator_const_float__'1 (this + 296)
  let t'11 ← PMem.ldF32 t'10
  let t'12 ← Thrust_Linearization.get_spin_min (this + 224)
  if (decide (t'11 > t'12)) then
    PMem.stU64 (fp + 32) (0x14208 : UInt64) /- "MOT_" -/
    PMem.stU64 (fp + 40) (0x14208 : UInt64) /- "MOT_" -/
    let t'13 ← AP_HAL.Util.snprintf (0 : UInt64) buffer buflen (0x1b013 : UInt64) /- "%sSPIN_ARM > %sSPIN_MIN" -/ (fp + 32)
    discard <| pure (t'13)
    return false
  let t'14 ← AP_MotorsMulticopter.check_mot_pwm_params this
  if !t'14 then
    PMem.stU64 (fp + 48) (0x14208 : UInt64) /- "MOT_" -/
    PMem.stU64 (fp + 56) (0x14208 : UInt64) /- "MOT_" -/
    let t'15 ← AP_HAL.Util.snprintf (0 : UInt64) buffer buflen (0x1b02b : UInt64) /- "Check %sPWM_MIN and %sPWM_MAX" -/ (fp + 48)
    discard <| pure (t'15)
    return false
  return true

def AP_MotorsMulticopter.arming_checks (this : UInt64) (buflen : UInt64) (buffer : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 64
  let r ← AP_MotorsMulticopter.arming_checks.body fp this buflen buffer
  PMem.leave fp
  return r

/-- C++ `AP_Motors::motor_mask_to_srv_channel_mask : uint32_t (uint32_t) const`, `AP_Motors_Class.cpp:202-213`. -/
def AP_Motors.motor_mask_to_srv_channel_mask (this : UInt64) (mask : UInt32) : PMem.M UInt32 := do
  let mut mask := mask
  let mut mask2 : UInt32 := Int32.toUInt32 ((0 : Int32))
  for i'1 in [0:32] do
    let i : UInt8 := UInt8.ofNat i'1
    let mut bit : UInt32 := UInt64.toUInt32 (((1 : UInt64) <<< (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (i))))))))
    if (mask &&& bit) != (0 : UInt32) then
      let t'2 ← SRV_Channels.get_motor_function i
      let mut function : Int32 := t'2
      let t'3 ← SRV_Channels.get_output_channel_mask function
      let t'4 := (mask2 ||| t'3)
      mask2 := t'4
  return mask2

/-- C++ `AP_Motors::rc_set_freq : void (uint32_t, uint16_t)`, `AP_Motors_Class.cpp:123-195`. -/
def AP_Motors.rc_set_freq (this : UInt64) (motor_mask : UInt32) (freq_hz : UInt16) : PMem.M Unit := do
  let mut motor_mask := motor_mask
  let mut freq_hz := freq_hz
  if (decide ((UInt32.toInt32 (UInt16.toUInt32 (freq_hz))) > (50 : Int32))) then
    let t'1 := (this + 176)
    let t'2 ← PMem.ldU32 t'1
    let t'3 := (t'2 ||| motor_mask)
    PMem.stU32 t'1 t'3
  let t'4 ← AP_Motors.motor_mask_to_srv_channel_mask this motor_mask
  let mut mask : UInt32 := t'4
  let t'5 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  discard <| PMem.halDev "AP_HAL::RCOutput::set_freq" t'5 #[(UInt32.toUInt64 (mask)), (UInt16.toUInt64 (freq_hz))]
  let t'6 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  let t'7 ← SRV_Channels.get_dshot_esc_type
  discard <| PMem.halDev "AP_HAL::RCOutput::set_dshot_esc_type" t'6 #[(UInt32.toUInt64 (t'7))]
  let t'8 ← AP_Enum'AP_Motors_PWMType.operator_const_AP_Motors.PWMType (this + 204)
  let mut type' : UInt8 := t'8
  let sw'9 := type'
  if sw'9 == (1 : UInt8) then
    if ((decide ((UInt32.toInt32 (UInt16.toUInt32 (freq_hz))) > (50 : Int32))) && (mask != (Int32.toUInt32 ((0 : Int32))))) then
      let t'10 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
      discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'10 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((2 : UInt32)))]
  else if sw'9 == (2 : UInt8) then
    if ((decide ((UInt32.toInt32 (UInt16.toUInt32 (freq_hz))) > (50 : Int32))) && (mask != (Int32.toUInt32 ((0 : Int32))))) then
      let t'11 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
      discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'11 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((3 : UInt32)))]
  else if sw'9 == (3 : UInt8) then
    let t'12 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'12 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((4 : UInt32)))]
  else if sw'9 == (4 : UInt8) then
    let t'13 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'13 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((5 : UInt32)))]
  else if sw'9 == (5 : UInt8) then
    let t'14 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'14 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((6 : UInt32)))]
  else if sw'9 == (6 : UInt8) then
    let t'15 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'15 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((7 : UInt32)))]
  else if sw'9 == (7 : UInt8) then
    let t'16 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'16 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((8 : UInt32)))]
  else if sw'9 == (8 : UInt8) || sw'9 == (9 : UInt8) then
    if (type' == (8 : UInt8)) then
      let t'17 := Binary64.toBinary32 ((Binary64.ofBits 0x408f400000000000 /- 1000 -/))
      PMem.stF32 ((this + 180) + 4) t'17
    else
      let t'18 := Binary64.toBinary32 ((Binary64.ofBits 0x4097700000000000 /- 1500 -/))
      PMem.stF32 ((this + 180) + 4) t'18
    let t'19 := (this + 180)
    let t'20 ← PMem.ldU32 t'19
    let t'21 := (t'20 ||| motor_mask)
    PMem.stU32 t'19 t'21
    for i'22 in [0:16] do
      let i : UInt8 := UInt8.ofNat i'22
      if (((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i)))))) &&& motor_mask) != (0 : UInt32) then
        if (type' == (8 : UInt8)) then
          let t'23 ← SRV_Channels.get_motor_function i
          SRV_Channels.set_range t'23 (Int16.toUInt16 (Int32.toInt16 ((1000 : Int32))))
        else
          let t'24 ← SRV_Channels.get_motor_function i
          SRV_Channels.set_angle t'24 (Int16.toUInt16 (Int32.toInt16 ((500 : Int32))))
    let t'25 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'25 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((1 : UInt32)))]
  else
    let t'26 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::set_output_mode" t'26 #[(UInt32.toUInt64 (mask)), (UInt32.toUInt64 ((1 : UInt32)))]
  return ()

/-- C++ `AP_MotorsMatrix::set_update_rate : void (uint16_t)`, `AP_MotorsMatrix.cpp:116-128`. -/
def AP_MotorsMatrix.set_update_rate (this : UInt64) (speed_hz : UInt16) : PMem.M Unit := do
  let mut speed_hz := speed_hz
  PMem.stU16 (this + 20) speed_hz
  let mut mask : UInt32 := Int32.toUInt32 ((0 : Int32))
  for i'1 in [0:12] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    if t'2 then
      let t'3 := (mask ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i)))))))
      mask := t'3
  let t'4 ← PMem.ldU16 (this + 20)
  AP_Motors.rc_set_freq this mask t'4
  return ()

/-- C++ `AP_Motors::add_motor_num : void (int8_t)`, `AP_Motors_Class.cpp:218-225`. -/
def AP_Motors.add_motor_num (this : UInt64) (motor_num : Int8) : PMem.M Unit := do
  let mut motor_num := motor_num
  if ((decide ((Int8.toInt32 (motor_num)) ≥ (0 : Int32))) && (decide ((Int8.toInt32 (motor_num)) < (12 : Int32)))) then
    let t'1 ← SRV_Channels.get_motor_function (Int8.toUInt8 (motor_num))
    let mut function : Int32 := t'1
    let t'2 ← SRV_Channels.set_aux_channel_default function (Int8.toUInt8 (motor_num))
    discard <| pure (t'2)
  return ()

/-- C++ `AP_MotorsMatrix::add_motor_raw : void (int8_t, float, float, float, uint8_t, float)`, `AP_MotorsMatrix.cpp:504-529`. -/
def AP_MotorsMatrix.add_motor_raw (this : UInt64) (motor_num : Int8) (roll_fac : Binary32) (pitch_fac : Binary32) (yaw_fac : Binary32) (testing_order : UInt8) (throttle_factor : Binary32) : PMem.M Unit := do
  let mut motor_num := motor_num
  let mut roll_fac := roll_fac
  let mut pitch_fac := pitch_fac
  let mut yaw_fac := yaw_fac
  let mut testing_order := testing_order
  let mut throttle_factor := throttle_factor
  let t'1 ← AP_Motors.initialised_ok this
  if t'1 then
    return ()
  if ((decide ((Int8.toInt32 (motor_num)) ≥ (0 : Int32))) && (decide ((Int8.toInt32 (motor_num)) < (12 : Int32)))) then
    PMem.stB ((this + 340) + ((Int8.toInt64 (motor_num)) * 1).toUInt64) true
    PMem.stF32 ((this + 444) + ((Int8.toInt64 (motor_num)) * 4).toUInt64) roll_fac
    PMem.stF32 ((this + 492) + ((Int8.toInt64 (motor_num)) * 4).toUInt64) pitch_fac
    PMem.stF32 ((this + 540) + ((Int8.toInt64 (motor_num)) * 4).toUInt64) yaw_fac
    PMem.stF32 ((this + 588) + ((Int8.toInt64 (motor_num)) * 4).toUInt64) throttle_factor
    PMem.stU8 ((this + 684) + ((Int8.toInt64 (motor_num)) * 1).toUInt64) testing_order
    AP_Motors.add_motor_num this motor_num
  return ()

/-- C++ `AP_MotorsMatrix::add_motor : void (int8_t, float, float, float, uint8_t)`, `AP_MotorsMatrix.cpp:538-546`. -/
def AP_MotorsMatrix.add_motor (this : UInt64) (motor_num : Int8) (roll_factor_in_degrees : Binary32) (pitch_factor_in_degrees : Binary32) (yaw_factor : Binary32) (testing_order : UInt8) : PMem.M Unit := do
  let mut motor_num := motor_num
  let mut roll_factor_in_degrees := roll_factor_in_degrees
  let mut pitch_factor_in_degrees := pitch_factor_in_degrees
  let mut yaw_factor := yaw_factor
  let mut testing_order := testing_order
  let t'1 ← radians (roll_factor_in_degrees + (Int32.toBinary32 ((90 : Int32))))
  let t'2 ← radians pitch_factor_in_degrees
  AP_MotorsMatrix.add_motor_raw this motor_num (Musl.cosf.cosf t'1) (Musl.cosf.cosf t'2) yaw_factor testing_order (Binary32.ofBits 0x3f800000 /- 1 -/)
  return ()

/-- C++ `AP_MotorsMatrix::add_motor : void (int8_t, float, float, uint8_t)`, `AP_MotorsMatrix.cpp:532-535`. -/
def AP_MotorsMatrix.add_motor'2 (this : UInt64) (motor_num : Int8) (angle_degrees : Binary32) (yaw_factor : Binary32) (testing_order : UInt8) : PMem.M Unit := do
  let mut motor_num := motor_num
  let mut angle_degrees := angle_degrees
  let mut yaw_factor := yaw_factor
  let mut testing_order := testing_order
  AP_MotorsMatrix.add_motor this motor_num angle_degrees angle_degrees yaw_factor testing_order
  return ()

/-- C++ `AP_MotorsMatrix::add_motors : void (const struct MotorDef *, uint8_t)`, `AP_MotorsMatrix.cpp:562-568`. -/
def AP_MotorsMatrix.add_motors (this : UInt64) (motors : UInt64) (num_motors : UInt8) : PMem.M Unit := do
  let mut motors := motors
  let mut num_motors := num_motors
  for i'1 in [0:num_motors.toNat] do
    let i : UInt8 := UInt8.ofNat i'1
    let motor : UInt64 := (motors + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
    let t'2 ← PMem.ldF32 motor
    let t'3 ← PMem.ldF32 (motor + 4)
    let t'4 ← PMem.ldU8 (motor + 8)
    AP_MotorsMatrix.add_motor'2 this (UInt8.toInt8 (i)) t'2 t'3 t'4
  return ()

/-- C++ `AP_MotorsMatrix::add_motors_raw : void (const struct MotorDefRaw *, uint8_t)`, `AP_MotorsMatrix.cpp:569-575`. -/
def AP_MotorsMatrix.add_motors_raw (this : UInt64) (motors : UInt64) (num_motors : UInt8) : PMem.M Unit := do
  let mut motors := motors
  let mut num_motors := num_motors
  for i'1 in [0:num_motors.toNat] do
    let i : UInt8 := UInt8.ofNat i'1
    let m : UInt64 := (motors + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 16).toUInt64)
    let t'2 ← PMem.ldF32 m
    let t'3 ← PMem.ldF32 (m + 4)
    let t'4 ← PMem.ldF32 (m + 8)
    let t'5 ← PMem.ldU8 (m + 12)
    AP_MotorsMatrix.add_motor_raw this (UInt8.toInt8 (i)) t'2 t'3 t'4 t'5 (Binary32.ofBits 0x3f800000 /- 1 -/)
  return ()

/-- C++ `AP_MotorsMatrix::setup_quad_matrix : bool (motor_frame_type)`, `AP_MotorsMatrix.cpp:577-773`. -/
def AP_MotorsMatrix.setup_quad_matrix (this : UInt64) (frame_type : UInt32) : PMem.M Bool := do
  let mut frame_type := frame_type
  let t'1 := (0x1ae82 : UInt64) /- "QUAD" -/
  PMem.stU64 (this + 760) t'1
  PMem.stU32 (this + 216) (2 : UInt32)
  for _ in [0:1] do
    let sw'2 := UInt32.toInt32 (frame_type)
    if sw'2 == (0 : Int32) then
      let t'3 := (0x1ae87 : UInt64) /- "PLUS" -/
      PMem.stU64 (this + 768) t'3
      AP_MotorsMatrix.add_motors this (0x12ef8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'4 := (0x1ae8c : UInt64) /- "X" -/
      PMem.stU64 (this + 768) t'4
      AP_MotorsMatrix.add_motors this (0x12f38 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_0 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'5 := (0x1ae8e : UInt64) /- "BF_X" -/
      PMem.stU64 (this + 768) t'5
      AP_MotorsMatrix.add_motors this (0x12f68 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_1 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'6 := (0x1ae93 : UInt64) /- "X_REV" -/
      PMem.stU64 (this + 768) t'6
      AP_MotorsMatrix.add_motors this (0x12f98 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_2 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'7 := (0x1ae99 : UInt64) /- "DJI_X" -/
      PMem.stU64 (this + 768) t'7
      AP_MotorsMatrix.add_motors this (0x12fc8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_3 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'8 := (0x1ae9f : UInt64) /- "CW_X" -/
      PMem.stU64 (this + 768) t'8
      AP_MotorsMatrix.add_motors this (0x12ff8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_4 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'9 := (0x1aea4 : UInt64) /- "V" -/
      PMem.stU64 (this + 768) t'9
      AP_MotorsMatrix.add_motors this (0x13028 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_5 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'10 := (0x1aea6 : UInt64) /- "H" -/
      PMem.stU64 (this + 768) t'10
      AP_MotorsMatrix.add_motors this (0x13058 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_6 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'11 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'11
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'12 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'12
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (1 : Int32) then
      let t'13 := (0x1ae8c : UInt64) /- "X" -/
      PMem.stU64 (this + 768) t'13
      AP_MotorsMatrix.add_motors this (0x12f38 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_0 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'14 := (0x1ae8e : UInt64) /- "BF_X" -/
      PMem.stU64 (this + 768) t'14
      AP_MotorsMatrix.add_motors this (0x12f68 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_1 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'15 := (0x1ae93 : UInt64) /- "X_REV" -/
      PMem.stU64 (this + 768) t'15
      AP_MotorsMatrix.add_motors this (0x12f98 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_2 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'16 := (0x1ae99 : UInt64) /- "DJI_X" -/
      PMem.stU64 (this + 768) t'16
      AP_MotorsMatrix.add_motors this (0x12fc8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_3 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'17 := (0x1ae9f : UInt64) /- "CW_X" -/
      PMem.stU64 (this + 768) t'17
      AP_MotorsMatrix.add_motors this (0x12ff8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_4 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'18 := (0x1aea4 : UInt64) /- "V" -/
      PMem.stU64 (this + 768) t'18
      AP_MotorsMatrix.add_motors this (0x13028 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_5 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'19 := (0x1aea6 : UInt64) /- "H" -/
      PMem.stU64 (this + 768) t'19
      AP_MotorsMatrix.add_motors this (0x13058 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_6 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'20 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'20
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'21 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'21
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (12 : Int32) then
      let t'22 := (0x1ae8e : UInt64) /- "BF_X" -/
      PMem.stU64 (this + 768) t'22
      AP_MotorsMatrix.add_motors this (0x12f68 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_1 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'23 := (0x1ae93 : UInt64) /- "X_REV" -/
      PMem.stU64 (this + 768) t'23
      AP_MotorsMatrix.add_motors this (0x12f98 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_2 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'24 := (0x1ae99 : UInt64) /- "DJI_X" -/
      PMem.stU64 (this + 768) t'24
      AP_MotorsMatrix.add_motors this (0x12fc8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_3 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'25 := (0x1ae9f : UInt64) /- "CW_X" -/
      PMem.stU64 (this + 768) t'25
      AP_MotorsMatrix.add_motors this (0x12ff8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_4 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'26 := (0x1aea4 : UInt64) /- "V" -/
      PMem.stU64 (this + 768) t'26
      AP_MotorsMatrix.add_motors this (0x13028 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_5 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'27 := (0x1aea6 : UInt64) /- "H" -/
      PMem.stU64 (this + 768) t'27
      AP_MotorsMatrix.add_motors this (0x13058 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_6 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'28 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'28
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'29 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'29
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (18 : Int32) then
      let t'30 := (0x1ae93 : UInt64) /- "X_REV" -/
      PMem.stU64 (this + 768) t'30
      AP_MotorsMatrix.add_motors this (0x12f98 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_2 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'31 := (0x1ae99 : UInt64) /- "DJI_X" -/
      PMem.stU64 (this + 768) t'31
      AP_MotorsMatrix.add_motors this (0x12fc8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_3 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'32 := (0x1ae9f : UInt64) /- "CW_X" -/
      PMem.stU64 (this + 768) t'32
      AP_MotorsMatrix.add_motors this (0x12ff8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_4 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'33 := (0x1aea4 : UInt64) /- "V" -/
      PMem.stU64 (this + 768) t'33
      AP_MotorsMatrix.add_motors this (0x13028 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_5 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'34 := (0x1aea6 : UInt64) /- "H" -/
      PMem.stU64 (this + 768) t'34
      AP_MotorsMatrix.add_motors this (0x13058 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_6 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'35 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'35
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'36 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'36
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (13 : Int32) then
      let t'37 := (0x1ae99 : UInt64) /- "DJI_X" -/
      PMem.stU64 (this + 768) t'37
      AP_MotorsMatrix.add_motors this (0x12fc8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_3 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'38 := (0x1ae9f : UInt64) /- "CW_X" -/
      PMem.stU64 (this + 768) t'38
      AP_MotorsMatrix.add_motors this (0x12ff8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_4 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'39 := (0x1aea4 : UInt64) /- "V" -/
      PMem.stU64 (this + 768) t'39
      AP_MotorsMatrix.add_motors this (0x13028 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_5 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'40 := (0x1aea6 : UInt64) /- "H" -/
      PMem.stU64 (this + 768) t'40
      AP_MotorsMatrix.add_motors this (0x13058 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_6 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'41 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'41
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'42 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'42
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (14 : Int32) then
      let t'43 := (0x1ae9f : UInt64) /- "CW_X" -/
      PMem.stU64 (this + 768) t'43
      AP_MotorsMatrix.add_motors this (0x12ff8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_4 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'44 := (0x1aea4 : UInt64) /- "V" -/
      PMem.stU64 (this + 768) t'44
      AP_MotorsMatrix.add_motors this (0x13028 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_5 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'45 := (0x1aea6 : UInt64) /- "H" -/
      PMem.stU64 (this + 768) t'45
      AP_MotorsMatrix.add_motors this (0x13058 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_6 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'46 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'46
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'47 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'47
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (2 : Int32) then
      let t'48 := (0x1aea4 : UInt64) /- "V" -/
      PMem.stU64 (this + 768) t'48
      AP_MotorsMatrix.add_motors this (0x13028 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_5 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'49 := (0x1aea6 : UInt64) /- "H" -/
      PMem.stU64 (this + 768) t'49
      AP_MotorsMatrix.add_motors this (0x13058 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_6 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'50 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'50
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'51 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'51
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (3 : Int32) then
      let t'52 := (0x1aea6 : UInt64) /- "H" -/
      PMem.stU64 (this + 768) t'52
      AP_MotorsMatrix.add_motors this (0x13058 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_6 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'53 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'53
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'54 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'54
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (4 : Int32) then
      let t'55 := (0x1aea8 : UInt64) /- "VTAIL" -/
      PMem.stU64 (this + 768) t'55
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
      break
      let t'56 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'56
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (5 : Int32) then
      let t'57 := (0x1aeae : UInt64) /- "ATAIL" -/
      PMem.stU64 (this + 768) t'57
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((0 : UInt32)))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((60 : Int32))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((1 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((1 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((-(160 : Int32)))) (Int32.toBinary32 ((1 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((3 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((2 : UInt32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((-(60 : Int32)))) (Int32.toBinary32 ((0 : Int32))) (Int8.toUInt8 (Int32.toInt8 ((4 : Int32))))
      AP_MotorsMatrix.add_motor this (UInt8.toInt8 (UInt32.toUInt8 ((3 : UInt32)))) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((160 : Int32))) (Int32.toBinary32 ((-(1 : Int32)))) (Int8.toUInt8 (Int32.toInt8 ((2 : Int32))))
    else if sw'2 == (6 : Int32) then
      let t'58 := (0x1aeb4 : UInt64) /- "PLUSREV" -/
      PMem.stU64 (this + 768) t'58
      AP_MotorsMatrix.add_motors this (0x13088 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_7 -/ (UInt64.toUInt8 (((48 : UInt64) / (12 : UInt64))))
      break
      let t'59 := (0x1aebc : UInt64) /- "Y4" -/
      PMem.stU64 (this + 768) t'59
      AP_MotorsMatrix.add_motors_raw this (0x12ef8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_8 -/ (UInt64.toUInt8 (((64 : UInt64) / (16 : UInt64))))
    else if sw'2 == (19 : Int32) then
      let t'60 := (0x1aebc : UInt64) /- "Y4" -/
      PMem.stU64 (this + 768) t'60
      AP_MotorsMatrix.add_motors_raw this (0x12ef8 : UInt64) /- &AP_MotorsMatrix::setup_quad_matrix(...)::motors_8 -/ (UInt64.toUInt8 (((64 : UInt64) / (16 : UInt64))))
    else
      return false
  return true

/-- C++ `AP_MotorsMatrix::setup_motors : void (motor_frame_class, motor_frame_type)`, `AP_MotorsMatrix.cpp:1291-1350`. -/
def AP_MotorsMatrix.setup_motors (this : UInt64) (frame_class : UInt32) (frame_type : UInt32) : PMem.M Unit := do
  let mut frame_class := frame_class
  let mut frame_type := frame_type
  for i'1 in [0:12] do
    let i : Int8 := Int8.ofNat i'1
    AP_MotorsMatrix.remove_motor this i
  AP_Motors.set_initialised_ok this false
  let mut success : Bool := true
  let sw'2 := UInt32.toInt32 (frame_class)
  if sw'2 == (1 : Int32) then
    let t'3 ← AP_MotorsMatrix.setup_quad_matrix this frame_type
    success := t'3
  else
    success := false
    PMem.stU32 (this + 216) (0 : UInt32)
  AP_MotorsMatrix.normalise_rpy_factors this
  if !success then
    let t'4 := (0x1aebf : UInt64) /- "UNSUPPORTED" -/
    PMem.stU64 (this + 760) t'4
  AP_Motors.set_initialised_ok this success
  return ()

/-- C++ `AP_MotorsMatrix::init : void (motor_frame_class, motor_frame_type)`, `AP_MotorsMatrix.cpp:23-41`. -/
def AP_MotorsMatrix.init (this : UInt64) (frame_class : UInt32) (frame_type : UInt32) : PMem.M Unit := do
  let mut frame_class := frame_class
  let mut frame_type := frame_type
  PMem.stU32 (this + 748) frame_class
  PMem.stU32 (this + 752) frame_type
  AP_MotorsMatrix.setup_motors this frame_class frame_type
  let t'1 ← PMem.ldU16 (this + 20)
  AP_MotorsMatrix.set_update_rate this t'1
  return ()

/-- C++ `AP_MotorsMulticopter::convert_pwm_min_max_param : void (int16_t, int16_t)`, `AP_MotorsMulticopter.cpp:956-963`. -/
def AP_MotorsMulticopter.convert_pwm_min_max_param.body (fp : UInt64) (this : UInt64) (radio_min : Int16) (radio_max : Int16) : PMem.M Unit := do
  PMem.stI16 (fp + 0) radio_min
  PMem.stI16 (fp + 2) radio_max
  let t'1 ← AP_Param.configured (this + 308)
  let mut sc'3 := t'1
  if !sc'3 then
    let t'2 ← AP_Param.configured (this + 310)
    sc'3 := t'2
  if sc'3 then
    return ()
  AP_ParamTBase'short_2.set_and_save (this + 308) (fp + 0)
  AP_ParamTBase'short_2.set_and_save (this + 310) (fp + 2)
  return ()

def AP_MotorsMulticopter.convert_pwm_min_max_param (this : UInt64) (radio_min : Int16) (radio_max : Int16) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_MotorsMulticopter.convert_pwm_min_max_param.body fp this radio_min radio_max
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMulticopter::get_motor_mask : uint32_t ()`, `AP_MotorsMulticopter.cpp:941-944`. -/
def AP_MotorsMulticopter.get_motor_mask (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← SRV_Channels.get_output_channel_mask (81 : Int32)
  return t'1

/-- C++ `AP_MotorsMatrix::get_motor_mask : uint32_t ()`, `AP_MotorsMatrix.cpp:188-202`. -/
def AP_MotorsMatrix.get_motor_mask (this : UInt64) : PMem.M UInt32 := do
  let mut motor_mask : UInt32 := Int32.toUInt32 ((0 : Int32))
  for i'1 in [0:12] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    if t'2 then
      let t'3 := (motor_mask ||| ((1 : UInt32) <<< (Int32.toUInt32 ((UInt32.toInt32 (UInt8.toUInt32 (i)))))))
      motor_mask := t'3
  let t'4 ← AP_Motors.motor_mask_to_srv_channel_mask this motor_mask
  let mut mask : UInt32 := t'4
  let t'5 ← AP_MotorsMulticopter.get_motor_mask this
  let t'6 := (mask ||| t'5)
  mask := t'6
  return mask

/-- C++ `AP_MotorsMulticopter::update_throttle_range : void ()`, `AP_MotorsMulticopter.cpp:548-558`. -/
def AP_MotorsMulticopter.update_throttle_range.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_MotorsMatrix.get_motor_mask this
  let t'2 ← SRV_Channels.have_digital_outputs t'1
  let mut sc'4 := t'2
  if !sc'4 then
    let t'3 ← AP_Enum'AP_Motors_PWMType.operator_const_AP_Motors.PWMType (this + 204)
    sc'4 := (t'3 == (8 : UInt8))
  let mut sc'6 := sc'4
  if !sc'6 then
    let t'5 ← AP_Enum'AP_Motors_PWMType.operator_const_AP_Motors.PWMType (this + 204)
    sc'6 := (t'5 == (9 : UInt8))
  if sc'6 then
    PMem.stI16 (fp + 0) (Int32.toInt16 ((1000 : Int32)))
    AP_ParamTBase'short_2.set_and_default (this + 308) (fp + 0)
    PMem.stI16 (fp + 2) (Int32.toInt16 ((2000 : Int32)))
    AP_ParamTBase'short_2.set_and_default (this + 310) (fp + 2)
  let t'7 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  let t'8 ← AP_MotorsMulticopter.get_pwm_output_min this
  let t'9 ← AP_MotorsMulticopter.get_pwm_output_max this
  discard <| PMem.halDev "AP_HAL::RCOutput::set_esc_scaling" t'7 #[(UInt16.toUInt64 ((Int16.toUInt16 (t'8)))), (UInt16.toUInt64 ((Int16.toUInt16 (t'9))))]
  return ()

def AP_MotorsMulticopter.update_throttle_range (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 4
  let r ← AP_MotorsMulticopter.update_throttle_range.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_MotorsMulticopter::set_throttle_passthrough_for_esc_calibration : void (float)`, `AP_MotorsMulticopter.cpp:892-906`. -/
def AP_MotorsMulticopter.set_throttle_passthrough_for_esc_calibration (this : UInt64) (throttle_input : Binary32) : PMem.M Unit := do
  let mut throttle_input := throttle_input
  let t'1 ← AP_Motors.armed this
  if t'1 then
    let t'2 ← AP_MotorsMulticopter.get_pwm_output_min this
    let t'3 ← constrain_value_line'float throttle_input (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x3f800000 /- 1 -/) (Int32.toUInt32 ((895 : Int32)))
    let t'4 ← AP_MotorsMulticopter.get_pwm_output_max this
    let t'5 ← AP_MotorsMulticopter.get_pwm_output_min this
    let mut pwm_out : UInt16 := Binary32.toUInt16 (((Int32.toBinary32 ((Int16.toInt32 (t'2)))) + (t'3 * (Int32.toBinary32 (((Int16.toInt32 (t'4)) - (Int16.toInt32 (t'5))))))))
    for i'6 in [0:12] do
      let i : UInt16 := UInt16.ofNat i'6
      let t'7 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 1).toUInt64)
      if t'7 then
        AP_Motors.rc_write this (UInt16.toUInt8 (i)) pwm_out
    SRV_Channels.set_output_pwm (74 : Int32) pwm_out
    SRV_Channels.set_output_pwm (73 : Int32) pwm_out
  return ()

/-- C++ `AP_MotorsMatrix::_output_test_seq : void (uint8_t, int16_t)`, `AP_MotorsMatrix.cpp:467-476`. -/
def AP_MotorsMatrix._output_test_seq (this : UInt64) (motor_seq : UInt8) (pwm : Int16) : PMem.M Unit := do
  let mut motor_seq := motor_seq
  let mut pwm := pwm
  for i'1 in [0:12] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← PMem.ldB ((this + 340) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
    let mut sc'4 := t'2
    if sc'4 then
      let t'3 ← PMem.ldU8 ((this + 684) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 1).toUInt64)
      sc'4 := ((UInt32.toInt32 (UInt8.toUInt32 (t'3))) == (UInt32.toInt32 (UInt8.toUInt32 (motor_seq))))
    if sc'4 then
      AP_Motors.rc_write this i (Int16.toUInt16 (pwm))
  return ()

/-- C++ `AP_Motors::output_test_seq : bool (uint8_t, int16_t)`, `AP_Motors_Class.cpp:312-320`. -/
def AP_Motors.output_test_seq (this : UInt64) (motor_seq : UInt8) (pwm : Int16) : PMem.M Bool := do
  let mut motor_seq := motor_seq
  let mut pwm := pwm
  let t'1 ← AP_Motors.armed this
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← PMem.ldB (this + 221)
    sc'3 := t'2
  if sc'3 then
    AP_MotorsMatrix._output_test_seq this motor_seq pwm
    return true
  AP_MotorsMulticopter.output_min this
  return false

/-- C++ `AP_MotorsMatrix::set_frame_class_and_type : void (motor_frame_class, motor_frame_type)`, `AP_MotorsMatrix.cpp:131-142`. -/
def AP_MotorsMatrix.set_frame_class_and_type (this : UInt64) (frame_class : UInt32) (frame_type : UInt32) : PMem.M Unit := do
  let mut frame_class := frame_class
  let mut frame_type := frame_type
  let t'1 ← AP_Motors.armed this
  let mut sc'5 := t'1
  if !sc'5 then
    let t'2 ← PMem.ldU32 (this + 748)
    let mut sc'4 := ((UInt32.toInt32 (frame_class)) == (UInt32.toInt32 (t'2)))
    if sc'4 then
      let t'3 ← PMem.ldU32 (this + 752)
      sc'4 := ((UInt32.toInt32 (t'3)) == (UInt32.toInt32 (frame_type)))
    sc'5 := sc'4
  if sc'5 then
    return ()
  PMem.stU32 (this + 748) frame_class
  PMem.stU32 (this + 752) frame_type
  AP_MotorsMatrix.init this frame_class frame_type
  return ()

end Vehicle_lib
