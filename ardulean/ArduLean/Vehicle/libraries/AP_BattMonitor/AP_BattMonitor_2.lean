import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.libraries.AP_BattMonitor.AP_BattMonitor
import ArduLean.Vehicle.libraries.AP_Math.AP_Math_2
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2

/-!
ArduPilot `libraries/AP_BattMonitor`, part 2 of 2. Sources: `libraries/AP_BattMonitor/AP_BattMonitor_Backend.cpp`, `libraries/AP_BattMonitor/AP_BattMonitor.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_BattMonitor_Backend::arming_checks : bool (char *, size_t) const`, `AP_BattMonitor_Backend.cpp:211-238`. -/
def AP_BattMonitor_Backend.arming_checks.body (fp : UInt64) (this : UInt64) (buffer : UInt64) (buflen : UInt64) : PMem.M Bool := do
  let mut buffer := buffer
  let mut buflen := buflen
  AP_BattMonitor_Backend.check_failsafe_types this (fp + 0) (fp + 8) (fp + 16) (fp + 24)
  let t'1 ← PMem.ldU64 (this + 24)
  discard <| PMem.memcpy (fp + 32) (t'1 + 28) 4
  let t'2 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 32)
  let mut sc'8 := t'2
  if sc'8 then
    let t'3 ← PMem.ldU64 (this + 16)
    let t'4 ← PMem.ldF32 (t'3 + 28)
    let t'5 ← PMem.ldU64 (this + 24)
    let t'6 ← AP_ParamT'float_4.operator_const_float__'1 (t'5 + 28)
    let t'7 ← PMem.ldF32 t'6
    sc'8 := (decide (t'4 < t'7))
  let mut below_arming_voltage : Bool := sc'8
  let t'9 ← PMem.ldU64 (this + 24)
  let t'10 ← AP_ParamT'int_3.operator_const_int__ (t'9 + 24)
  let t'11 ← PMem.ldI32 t'10
  let mut sc'20 := (decide (t'11 > (0 : Int32)))
  if sc'20 then
    let t'12 ← PMem.ldU64 (this + 24)
    let t'13 ← AP_ParamT'int_3.operator_const_int__ t'12
    let t'14 ← PMem.ldI32 t'13
    let t'15 ← PMem.ldU64 (this + 16)
    let t'16 ← PMem.ldF32 (t'15 + 36)
    let t'17 ← PMem.ldU64 (this + 24)
    let t'18 ← AP_ParamT'int_3.operator_const_int__ (t'17 + 24)
    let t'19 ← PMem.ldI32 t'18
    sc'20 := (decide (((Int32.toBinary32 (t'14)) - t'16) < (Int32.toBinary32 (t'19))))
  let mut below_arming_capacity : Bool := sc'20
  let t'21 ← PMem.ldU64 (this + 24)
  discard <| PMem.memcpy (fp + 40) (t'21 + 20) 4
  let t'22 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 40)
  let mut sc'25 := t'22
  if sc'25 then
    let t'23 ← PMem.ldU64 (this + 24)
    discard <| PMem.memcpy (fp + 48) (t'23 + 12) 4
    let t'24 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 48)
    sc'25 := t'24
  let mut sc'29 := sc'25
  if sc'29 then
    let t'26 ← PMem.ldU64 (this + 24)
    let t'27 ← PMem.ldU64 (this + 24)
    let t'28 ← AP_ParamT'float_4.operator_ (t'26 + 12) (t'27 + 20)
    sc'29 := !t'28
  let mut fs_capacity_inversion : Bool := sc'29
  let t'30 ← PMem.ldU64 (this + 24)
  discard <| PMem.memcpy (fp + 56) (t'30 + 16) 4
  let t'31 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 56)
  let mut sc'34 := t'31
  if sc'34 then
    let t'32 ← PMem.ldU64 (this + 24)
    discard <| PMem.memcpy (fp + 64) (t'32 + 8) 4
    let t'33 ← is_positive'AP_ParamT_float_AP_PARAM_FLOAT (fp + 64)
    sc'34 := t'33
  let mut sc'38 := sc'34
  if sc'38 then
    let t'35 ← PMem.ldU64 (this + 24)
    let t'36 ← PMem.ldU64 (this + 24)
    let t'37 ← AP_ParamT'float_4.operator_ (t'35 + 8) (t'36 + 16)
    sc'38 := !t'37
  let mut fs_voltage_inversion : Bool := sc'38
  let t'39 ← PMem.ldU64 (this + 16)
  let t'40 ← PMem.ldB (t'39 + 73)
  let t'41 ← update_check buflen buffer (!t'40) (0x16805 : UInt64) /- "unhealthy" -/
  let mut result : Bool := t'41
  let mut sc'43 := result
  if sc'43 then
    let t'42 ← update_check buflen buffer below_arming_voltage (0x16693 : UInt64) /- "below minimum arming voltage" -/
    sc'43 := t'42
  result := sc'43
  let mut sc'45 := result
  if sc'45 then
    let t'44 ← update_check buflen buffer below_arming_capacity (0x166b0 : UInt64) /- "below minimum arming capacity" -/
    sc'45 := t'44
  result := sc'45
  let mut sc'48 := result
  if sc'48 then
    let t'46 ← PMem.ldB (fp + 16)
    let t'47 ← update_check buflen buffer t'46 (0x166ce : UInt64) /- "critical voltage failsafe" -/
    sc'48 := t'47
  result := sc'48
  let mut sc'51 := result
  if sc'51 then
    let t'49 ← PMem.ldB (fp + 24)
    let t'50 ← update_check buflen buffer t'49 (0x166e8 : UInt64) /- "critical capacity failsafe" -/
    sc'51 := t'50
  result := sc'51
  let mut sc'54 := result
  if sc'54 then
    let t'52 ← PMem.ldB (fp + 0)
    let t'53 ← update_check buflen buffer t'52 (0x16703 : UInt64) /- "low voltage failsafe" -/
    sc'54 := t'53
  result := sc'54
  let mut sc'57 := result
  if sc'57 then
    let t'55 ← PMem.ldB (fp + 8)
    let t'56 ← update_check buflen buffer t'55 (0x16718 : UInt64) /- "low capacity failsafe" -/
    sc'57 := t'56
  result := sc'57
  let mut sc'59 := result
  if sc'59 then
    let t'58 ← update_check buflen buffer fs_capacity_inversion (0x1672e : UInt64) /- "capacity failsafe critical >= low" -/
    sc'59 := t'58
  result := sc'59
  let mut sc'61 := result
  if sc'61 then
    let t'60 ← update_check buflen buffer fs_voltage_inversion (0x16750 : UInt64) /- "voltage failsafe critical >= low" -/
    sc'61 := t'60
  result := sc'61
  return result

def AP_BattMonitor_Backend.arming_checks (this : UInt64) (buffer : UInt64) (buflen : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 68
  let r ← AP_BattMonitor_Backend.arming_checks.body fp this buffer buflen
  PMem.leave fp
  return r

/-- C++ `AP_BattMonitor::arming_checks : bool (size_t, char *) const`, `AP_BattMonitor.cpp:1100-1133`. -/
def AP_BattMonitor.arming_checks.body (fp : UInt64) (this : UInt64) (buflen : UInt64) (buffer : UInt64) : PMem.M Bool := do
  let mut buflen := buflen
  let mut buffer := buffer
  for i'1 in [0:9] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← AP_BattMonitor.configured_type this i
    let mut expected_type : Int32 := t'2
    let t'3 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    if ((t'3 == (0 : UInt64)) && (expected_type == (0 : Int32))) then
      continue
    if (expected_type == (10 : Int32)) then
      PMem.stU64 (fp + 56) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      PMem.stU64 (fp + 64) (0x167e3 : UInt64) /- "feature BATTERY_SUM not available" -/
      let t'4 ← AP_HAL.Util.snprintf (0 : UInt64) buffer buflen (0x167d5 : UInt64) /- "Battery %d %s" -/ (fp + 56)
      discard <| pure (t'4)
      return false
    let t'5 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    let mut sc'7 := (t'5 == (0 : UInt64))
    if !sc'7 then
      let t'6 ← AP_BattMonitor.allocated_type this i
      sc'7 := (t'6 != expected_type)
    if sc'7 then
      PMem.stU64 (fp + 72) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      PMem.stU64 (fp + 80) (0x16805 : UInt64) /- "unhealthy" -/
      let t'8 ← AP_HAL.Util.snprintf (0 : UInt64) buffer buflen (0x167d5 : UInt64) /- "Battery %d %s" -/ (fp + 72)
      discard <| pure (t'8)
      return false
    let t'9 ← PMem.ldU64 ((this + 1416) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 8).toUInt64)
    let t'10 ← AP_BattMonitor_Backend.arming_checks t'9 (fp + 0) (51 : UInt64)
    if !t'10 then
      PMem.stU64 (fp + 88) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      PMem.stU64 (fp + 96) (fp + 0)
      let t'11 ← AP_HAL.Util.snprintf (0 : UInt64) buffer buflen (0x167d5 : UInt64) /- "Battery %d %s" -/ (fp + 88)
      discard <| pure (t'11)
      return false
  return true

def AP_BattMonitor.arming_checks (this : UInt64) (buflen : UInt64) (buffer : UInt64) : PMem.M Bool := do
  let fp ← PMem.enter 104
  let r ← AP_BattMonitor.arming_checks.body fp this buflen buffer
  PMem.leave fp
  return r

/-- C++ `AP_BattMonitor::checkPoweringOff : void ()`, `AP_BattMonitor.cpp:1136-1158`. -/
def AP_BattMonitor.checkPoweringOff.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    let t'4 ← PMem.ldU8 (this + 1492)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'4)))))) then break
    let t'5 ← PMem.ldB (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 112).toUInt64) + 80)
    let mut sc'7 := t'5
    if sc'7 then
      let t'6 ← PMem.ldB (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 112).toUInt64) + 81)
      sc'7 := !t'6
    if sc'7 then
      PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 25) true
      discard <| PMem.memset ((fp + 0) + 0) 0 4
      discard <| PMem.memset ((fp + 0) + 4) 0 4
      discard <| PMem.memset ((fp + 0) + 8) 0 4
      discard <| PMem.memset ((fp + 0) + 12) 0 4
      discard <| PMem.memset ((fp + 0) + 16) 0 4
      discard <| PMem.memset ((fp + 0) + 20) 0 4
      discard <| PMem.memset ((fp + 0) + 24) 0 4
      discard <| PMem.memset ((fp + 0) + 28) 0 2
      discard <| PMem.memset ((fp + 0) + 30) 0 1
      discard <| PMem.memset ((fp + 0) + 31) 0 1
      discard <| PMem.memset ((fp + 0) + 32) 0 1
      let t'8 := UInt32.toUInt16 ((42000 : UInt32))
      PMem.stU16 ((fp + 0) + 28) t'8
      let t'9 := Int32.toBinary32 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))
      PMem.stF32 (fp + 0) t'9
      GCS_MAVLINK.send_to_components (Int32.toUInt32 ((76 : Int32))) (fp + 0) (UInt64.toUInt8 ((33 : UInt64)))
      let t'10 ← PMem.ldU32 (0xbc50 : UInt64) /- &mavlink_system -/
      PMem.stU64 (fp + 40) (UInt32.toUInt64 (t'10))
      PMem.stU64 (fp + 48) (Int64.toUInt64 (Int32.toInt64 (((UInt32.toInt32 (UInt8.toUInt32 (i))) + (1 : Int32)))))
      let t'11 ← gcs
      GCS.send_text t'11 (4 : UInt32) (0x1680f : UInt64) /- "Vehicle %u battery %d is powering off" -/ (fp + 40)
      PMem.stB (((this + 408) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 112).toUInt64) + 81) true
  return ()

def AP_BattMonitor.checkPoweringOff (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 56
  let r ← AP_BattMonitor.checkPoweringOff.body fp this
  PMem.leave fp
  return r

end Vehicle_lib
