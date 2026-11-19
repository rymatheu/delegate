import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Mission.AP_Mission
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.Dispatch
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.libraries.AP_Scheduler.AP_Scheduler
import ArduLean.Vehicle.libraries.SRV_Channel.SRV_Channel
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel_2
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.libraries.AP_Motors.AP_Motors_2
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.World
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming_3
import ArduLean.Vehicle.ArduCopter.ArduCopter_3
import ArduLean.Vehicle.Dispatch_3
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_3

/-!
Cross-library module `Arming`: pre-arm checks and arming (AP_Arming with AP_Arming_Copter's overrides), with the GCS sends and motor output they reach. It belongs to the top of the call graph, where ArduPilot's libraries call each other in a cycle, so it cannot be cut by library. Largest functions: `GCS_MAVLINK.update_send`, `AP_Arming_Copter.arm`, `Copter.motors_output`, `GCS.update_send`, `AP_Arming_Copter.run_pre_arm_checks`, `AP_Arming.arm`, `AP_Arming.pre_arm_checks`, `AP_Arming.update`, `GCS_MAVLINK.handle_param_request_list`, `AP_Arming.manual_transmitter_checks`. Sources: `libraries/GCS_MAVLink/GCS_Common.cpp`, `ArduCopter/AP_Arming_Copter.cpp`, `libraries/AP_Arming/AP_Arming.cpp`, `ArduCopter/motors.cpp`, `ArduCopter/GCS_MAVLink_Copter.cpp`, `libraries/GCS_MAVLink/GCS_Param.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `GCS_MAVLINK_Copter::send_banner : void ()`, `GCS_MAVLink_Copter.cpp:371-381`. -/
def GCS_MAVLINK_Copter.send_banner.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  GCS_MAVLINK.send_banner this
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  if (t'1 == (0 : UInt64)) then
    GCS_MAVLINK.send_text this (6 : UInt32) (0x13fbd : UInt64) /- "motors not allocated" -/ (fp + 0)
    return ()
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  AP_Motors.get_frame_and_type_string t'2 (fp + 8) (UInt64.toUInt8 (((30 : UInt64) / (1 : UInt64))))
  PMem.stU64 (fp + 40) (fp + 8)
  GCS_MAVLINK.send_text this (6 : UInt32) (0x13fd2 : UInt64) /- "%s" -/ (fp + 40)
  return ()

def GCS_MAVLINK_Copter.send_banner (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 48
  let r ← GCS_MAVLINK_Copter.send_banner.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_param_request_list : void (const mavlink_message_t &)`, `GCS_Param.cpp:206-223`. -/
def GCS_MAVLINK.handle_param_request_list.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← GCS_MAVLINK_Copter.params_ready this
  if !t'1 then
    return ()
  __mavlink_param_request_list_t.__mavlink_param_request_list_t (fp + 0)
  mavlink_msg_param_request_list_decode msg (fp + 0)
  GCS_MAVLINK_Copter.send_banner this
  let t'2 ← AP_Param.first (this + 492) (this + 488) (0 : UInt64)
  PMem.stU64 (this + 32) t'2
  let t'3 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  PMem.stU16 (this + 496) t'3
  let t'4 ← AP_Param.count_parameters
  PMem.stU16 (this + 498) t'4
  let t'5 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 (this + 500) t'5
  return ()

def GCS_MAVLINK.handle_param_request_list (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 2
  let r ← GCS_MAVLINK.handle_param_request_list.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_common_param_message : void (const mavlink_message_t &)`, `GCS_Param.cpp:524-537`. -/
def GCS_MAVLINK.handle_common_param_message (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldBits msg 104 24
  let sw'2 := UInt32.toInt32 ((UInt64.toUInt32 (t'1)))
  if sw'2 == (21 : Int32) then
    GCS_MAVLINK.handle_param_request_list this msg
  else if sw'2 == (23 : Int32) then
    GCS_MAVLINK.handle_param_set this msg
  else if sw'2 == (20 : Int32) then
    GCS_MAVLINK.handle_param_request_read this msg
  else
    pure ()
  return ()

/-- C++ `AP_Arming::manual_transmitter_checks : bool (bool)`, `AP_Arming.cpp:930-945`. -/
def AP_Arming.manual_transmitter_checks.body (fp : UInt64) (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.check_enabled this (64 : Int32)
  if t'1 then
    let t'2 ← PMem.ldB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 10)
    if t'2 then
      AP_Arming.check_failed this (64 : Int32) report (0x1a470 : UInt64) /- "Radio failsafe on" -/ (fp + 0)
      return false
    let t'3 ← AP_Arming_Copter.rc_calibration_checks this report
    if !t'3 then
      return false
  let t'4 ← AP_Arming.rc_in_calibration_check this report
  return t'4

def AP_Arming.manual_transmitter_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.manual_transmitter_checks.body fp this report
  PMem.leave fp
  return r

/-- C++ `AP_Arming::pre_arm_checks : bool (bool)`, `AP_Arming.cpp:1706-1800`. -/
def AP_Arming.pre_arm_checks (this : UInt64) (report : Bool) : PMem.M Bool := do
  let mut report := report
  let t'1 ← AP_Arming.hardware_safety_check this report
  let t'2 ← AP_Arming_Copter.barometer_checks this report
  let t'3 ← AP_Arming_Copter.ins_checks this report
  let t'4 ← AP_Arming.compass_checks this report
  let t'5 ← AP_Arming_Copter.gps_checks this report
  let t'6 ← AP_Arming.battery_checks this report
  let t'7 ← AP_Arming.manual_transmitter_checks this report
  let t'8 ← AP_Arming.rc_option_checks this report
  let t'9 ← AP_Arming.mission_checks this report
  let t'10 ← AP_Arming.servo_checks this report
  let t'11 ← AP_Arming_Copter.board_voltage_checks this report
  let t'12 ← AP_Arming.system_checks this report
  let t'13 ← AP_Arming.terrain_checks this report
  let t'14 ← AP_Arming.can_checks this report
  let t'15 ← AP_Arming.disarm_switch_checks this report
  let t'16 ← AP_Arming.serial_protocol_checks this report
  let t'17 ← AP_Arming.estop_checks this report
  let mut checks_result : Bool := (((((((((((((((((if t'1 then (1 : Int32) else (0 : Int32)) &&& (if t'2 then (1 : Int32) else (0 : Int32))) &&& (if t'3 then (1 : Int32) else (0 : Int32))) &&& (if t'4 then (1 : Int32) else (0 : Int32))) &&& (if t'5 then (1 : Int32) else (0 : Int32))) &&& (if t'6 then (1 : Int32) else (0 : Int32))) &&& (if t'7 then (1 : Int32) else (0 : Int32))) &&& (if t'8 then (1 : Int32) else (0 : Int32))) &&& (if t'9 then (1 : Int32) else (0 : Int32))) &&& (if t'10 then (1 : Int32) else (0 : Int32))) &&& (if t'11 then (1 : Int32) else (0 : Int32))) &&& (if t'12 then (1 : Int32) else (0 : Int32))) &&& (if t'13 then (1 : Int32) else (0 : Int32))) &&& (if t'14 then (1 : Int32) else (0 : Int32))) &&& (if t'15 then (1 : Int32) else (0 : Int32))) &&& (if t'16 then (1 : Int32) else (0 : Int32))) &&& (if t'17 then (1 : Int32) else (0 : Int32))) != (0 : Int32)
  let mut sc'19 := !checks_result
  if sc'19 then
    let t'18 ← PMem.ldB (this + 69)
    sc'19 := t'18
  if sc'19 then
    PMem.stB (this + 70) true
  PMem.stB (this + 69) checks_result
  return checks_result

/-- C++ `AP_Arming_Copter::run_pre_arm_checks : bool (bool)`, `AP_Arming_Copter.cpp:17-87`. -/
def AP_Arming_Copter.run_pre_arm_checks.body (fp : UInt64) (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'2 ← AP_Motors.armed t'1
  if t'2 then
    return true
  if !((← get).sysInit) then
    AP_Arming.check_failed'2 this display_failure (0x13957 : UInt64) /- "System not initialised" -/ (fp + 0)
    return false
  let mut passed : Bool := true
  let t'3 ← rc
  let t'4 ← RC_Channels.find_channel_for_option t'3 (32 : Int32)
  let mut sc'10 := (t'4 != 0)
  if sc'10 then
    let t'5 ← rc
    let t'6 ← RC_Channels.find_channel_for_option t'5 (31 : Int32)
    let mut sc'9 := (t'6 != 0)
    if !sc'9 then
      let t'7 ← rc
      let t'8 ← RC_Channels.find_channel_for_option t'7 (165 : Int32)
      sc'9 := (t'8 != 0)
    sc'10 := sc'9
  if sc'10 then
    AP_Arming.check_failed'2 this display_failure (0x1396e : UInt64) /- "Interlock/E-Stop Conflict" -/ (fp + 8)
    passed := false
  let t'11 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 18)
  let mut sc'13 := t'11
  if sc'13 then
    let t'12 ← PMem.ldB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 20)
    sc'13 := t'12
  if sc'13 then
    AP_Arming.check_failed'2 this display_failure (0x13988 : UInt64) /- "Motor Interlock Enabled" -/ (fp + 16)
    passed := false
  let t'14 ← AP_Arming.disarm_switch_checks this display_failure
  if !t'14 then
    passed := false
  let t'15 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'16 ← AP_MotorsMulticopter.arming_checks t'15 ((100 : UInt64) / (1 : UInt64)) (fp + 24)
  if !t'16 then
    PMem.stU64 (fp + 128) (fp + 24)
    AP_Arming.check_failed'2 this display_failure (0x139a0 : UInt64) /- "Motors: %s" -/ (fp + 128)
    passed := false
  if !passed then
    return false
  let t'17 ← AP_Arming.should_skip_all_checks this
  if t'17 then
    let t'18 ← AP_Arming_Copter.mandatory_checks this display_failure
    return t'18
  let t'19 ← AP_Arming_Copter.parameter_checks this display_failure
  let t'20 ← AP_Arming_Copter.oa_checks this display_failure
  let t'21 ← AP_Arming_Copter.gcs_failsafe_check this display_failure
  let t'22 ← AP_Arming_Copter.winch_checks this display_failure
  let t'23 ← AP_Arming_Copter.rc_throttle_failsafe_checks this display_failure
  let t'24 ← AP_Arming_Copter.alt_checks this display_failure
  let t'25 ← AP_Arming.pre_arm_checks this display_failure
  return (((((((if t'19 then (1 : Int32) else (0 : Int32)) &&& (if t'20 then (1 : Int32) else (0 : Int32))) &&& (if t'21 then (1 : Int32) else (0 : Int32))) &&& (if t'22 then (1 : Int32) else (0 : Int32))) &&& (if t'23 then (1 : Int32) else (0 : Int32))) &&& (if t'24 then (1 : Int32) else (0 : Int32))) &&& (if t'25 then (1 : Int32) else (0 : Int32))) != (0 : Int32)

def AP_Arming_Copter.run_pre_arm_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 136
  let r ← AP_Arming_Copter.run_pre_arm_checks.body fp this display_failure
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::pre_arm_checks : bool (bool)`, `AP_Arming_Copter.cpp:8-13`. -/
def AP_Arming_Copter.pre_arm_checks (this : UInt64) (display_failure : Bool) : PMem.M Bool := do
  let mut display_failure := display_failure
  let t'1 ← AP_Arming_Copter.run_pre_arm_checks this display_failure
  let mut passed : Bool := t'1
  AP_Arming_Copter.set_pre_arm_check this passed
  return passed

/-- C++ `AP_Arming::arm : bool (AP_Arming::Method, const bool)`, `AP_Arming.cpp:1898-1971`. -/
def AP_Arming.arm.body (fp : UInt64) (this : UInt64) (method : Int32) (do_arming_checks : Bool) : PMem.M Bool := do
  let mut method := method
  let mut do_arming_checks := do_arming_checks
  let t'1 ← PMem.ldB (this + 35)
  if t'1 then
    return false
  if (method == (0 : Int32)) then
    let t'2 ← AP_Arming.get_rudder_arming_type this
    let sw'3 := t'2
    if sw'3 == (0 : Int32) then
      return false
    else if sw'3 == (1 : Int32) || sw'3 == (2 : Int32) then
      pure ()
    else
      pure ()
  PMem.stB (this + 68) true
  let mut sc'5 := !do_arming_checks
  if sc'5 then
    let t'4 ← AP_Arming_Copter.mandatory_checks this true
    sc'5 := t'4
  let mut sc'9 := sc'5
  if !sc'9 then
    let t'6 ← AP_Arming_Copter.pre_arm_checks this true
    let mut sc'8 := t'6
    if sc'8 then
      let t'7 ← AP_Arming_Copter.arm_checks this method
      sc'8 := t'7
    sc'9 := sc'8
  if sc'9 then
    PMem.stB (this + 35) true
    let t'10 := (← PMem.clock)
    PMem.stU64 (this + 56) t'10
    PMem.stI32 (this + 48) method
  else
    PMem.stB (this + 35) false
  PMem.stB (this + 68) false
  let t'11 ← PMem.ldB (this + 35)
  let mut sc'13 := (t'11 && do_arming_checks)
  if sc'13 then
    let t'12 ← AP_Arming.should_skip_all_checks this
    sc'13 := t'12
  if sc'13 then
    let t'14 ← gcs
    GCS.send_text t'14 (4 : UInt32) (0x1a71a : UInt64) /- "Warning: Arming Checks Disabled" -/ (fp + 0)
  let t'15 ← PMem.ldB (this + 35)
  return t'15

def AP_Arming.arm (this : UInt64) (method : Int32) (do_arming_checks : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← AP_Arming.arm.body fp this method do_arming_checks
  PMem.leave fp
  return r

/-- C++ `AP_Arming_Copter::arm : bool (const AP_Arming::Method, const bool)`, `AP_Arming_Copter.cpp:674-786`. -/
def AP_Arming_Copter.arm.body (fp : UInt64) (this : UInt64) (method : Int32) (do_arming_checks : Bool) : PMem.M Bool := do
  let mut method := method
  let mut do_arming_checks := do_arming_checks
  let t'1 ← PMem.ldB (0x13180 : UInt64) /- &AP_Arming_Copter::arm(...)::in_arm_motors -/
  if t'1 then
    return false
  PMem.stB (0x13180 : UInt64) /- &AP_Arming_Copter::arm(...)::in_arm_motors -/ true
  let t'2 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  let t'3 ← AP_Motors.armed t'2
  if t'3 then
    PMem.stB (0x13180 : UInt64) /- &AP_Arming_Copter::arm(...)::in_arm_motors -/ false
    return true
  let t'4 ← AP_Arming.arm this method do_arming_checks
  if !t'4 then
    let t'5 := if true then (1 : UInt32) else (0 : UInt32)
    PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 0 1 (UInt32.toUInt64 (t'5))
    PMem.stB (0x13180 : UInt64) /- &AP_Arming_Copter::arm(...)::in_arm_motors -/ false
    return false
  Copter.failsafe_disable (0x86d8 : UInt64) /- &copter -/
  PMem.stB ((0xccc0 : UInt64) /- &AP_Notify::flags -/ + 4) true
  for i'6 in [0:11] do
    let i : UInt8 := UInt8.ofNat i'6
    pure ()
  AP_Arming.send_arm_disarm_statustext this (0x13bd1 : UInt64) /- "Arming motors" -/
  Copter.init_simple_bearing (0x86d8 : UInt64) /- &copter -/
  let t'7 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'7
  let t'8 ← VehicleBridge.AP_AHRS.get_yaw_rad'0 ahrs
  PMem.stF32 ((0x86d8 : UInt64) /- &copter -/ + 9576) t'8
  let t'9 ← VehicleBridge.AP_AHRS.home_is_set'0 ahrs
  if !t'9 then
    VehicleBridge.AP_AHRS.resetHeightDatum'0 ahrs
    worldOutputs'drain
    let t'10 := Int32.toBinary32 ((0 : Int32))
    PMem.stF32 ((0x86d8 : UInt64) /- &copter -/ + 9504) t'10
  else
    let t'11 ← VehicleBridge.AP_AHRS.home_is_locked'0 ahrs
    if !t'11 then
      let t'12 ← Copter.set_home_to_current_location (0x86d8 : UInt64) /- &copter -/ false
      if !t'12 then
        pure ()
      PMem.stF32 (fp + 0) (Int32.toBinary32 ((0 : Int32)))
      for _ in [0:1] do
        let mut __unique_name___COUNTER__ : Bool := default  -- uninitialized in C
        let t'13 ← VehicleBridge.ahrs'0
        let t'14 ← VehicleBridge.AP_AHRS.get_relative_position_D_origin_float'1 t'13 (fp + 0)
        __unique_name___COUNTER__ := t'14
      let t'15 ← PMem.ldF32 (fp + 0)
      let t'16 := -t'15
      PMem.stF32 ((0x86d8 : UInt64) /- &copter -/ + 9504) t'16
  Copter.update_super_simple_bearing (0x86d8 : UInt64) /- &copter -/ false
  let t'17 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  discard <| PMem.halDev "AP_HAL::Util::set_soft_armed" t'17 #[(if true then (1 : UInt64) else 0)]
  let t'18 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  AP_MotorsMulticopter.output_min t'18
  let t'19 ← PMem.ldU64 ((0x86d8 : UInt64) /- &copter -/ + 9528)
  AP_Motors.armed'2 t'19 true
  Copter.failsafe_enable (0x86d8 : UInt64) /- &copter -/
  let t'20 ← AP.scheduler
  AP.PerfInfo.ignore_this_loop t'20
  PMem.stB (0x13180 : UInt64) /- &AP_Arming_Copter::arm(...)::in_arm_motors -/ false
  let t'21 := ((← PMem.clock) / 1000).toUInt32
  PMem.stU32 ((0x86d8 : UInt64) /- &copter -/ + 11216) t'21
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 21) true
  PMem.stB (((0x86d8 : UInt64) /- &copter -/ + 9448) + 25) false
  return true

def AP_Arming_Copter.arm (this : UInt64) (method : Int32) (do_arming_checks : Bool) : PMem.M Bool := do
  let fp ← PMem.enter 4
  let r ← AP_Arming_Copter.arm.body fp this method do_arming_checks
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK_Copter::try_send_message : bool (enum ap_message)`, `GCS_MAVLink_Copter.cpp:293-324`. -/
def GCS_MAVLINK_Copter.try_send_message (this : UInt64) (id : UInt8) : PMem.M Bool := do
  let mut id := id
  for _ in [0:1] do
    let sw'1 := UInt32.toInt32 (UInt8.toUInt32 (id))
    if sw'1 == (36 : Int32) then
      let t'2 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((12 : Int32))))
      if !t'2 then
        return false
      GCS_MAVLINK_Copter.send_wind this
    else if sw'1 == (64 : Int32) then
      break
      let t'3 ← GCS_MAVLINK.try_send_message this id
      return t'3
    else
      let t'4 ← GCS_MAVLINK.try_send_message this id
      return t'4
  return true

/-- C++ `GCS_MAVLINK::handle_command_get_home_position : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:5043-5058`. -/
def GCS_MAVLINK.handle_command_get_home_position (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  let t'1 ← VehicleBridge.ahrs'0
  let t'2 ← VehicleBridge.AP_AHRS.home_is_set'0 t'1
  if !t'2 then
    return (4 : UInt32)
  let t'3 ← GCS_MAVLINK_Copter.try_send_message this (70 : UInt8)
  if !t'3 then
    GCS_MAVLINK.send_message this (70 : UInt8)
  let t'4 ← GCS_MAVLINK_Copter.try_send_message this (69 : UInt8)
  if !t'4 then
    GCS_MAVLINK.send_message this (69 : UInt8)
  return (0 : UInt32)

/-- C++ `GCS_MAVLINK::handle_command_run_prearm_checks : MAV_RESULT (const mavlink_command_int_t &)`, `GCS_Common.cpp:4931-4938`. -/
def GCS_MAVLINK.handle_command_run_prearm_checks (this : UInt64) (packet : UInt64) : PMem.M UInt32 := do
  if (← get).armed then
    return (1 : UInt32)
  let t'1 ← AP.arming
  let t'2 ← AP_Arming_Copter.pre_arm_checks t'1 true
  discard <| pure (t'2)
  return (0 : UInt32)

/-- C++ `GCS_MAVLINK::do_try_send_message : bool (const ap_message)`, `GCS_Common.cpp:1356-1387`. -/
def GCS_MAVLINK.do_try_send_message (this : UInt64) (id : UInt8) : PMem.M Bool := do
  let mut id := id
  let mut in_delay_callback : Bool := (← get).inDelayCb
  let mut sc'2 := in_delay_callback
  if sc'2 then
    let t'1 ← GCS_MAVLINK.should_send_message_in_delay_callback this id
    sc'2 := !t'1
  if sc'2 then
    return true
  let t'3 ← GCS_MAVLINK.telemetry_delayed this
  if t'3 then
    return false
  let t'4 ← GCS_MAVLINK_Copter.try_send_message this id
  if !t'4 then
    return false
  return true

/-- C++ `GCS_MAVLINK::update_send : void ()`, `GCS_Common.cpp:1566-1695`. -/
def GCS_MAVLINK.update_send (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 764)
  if !t'1 then
    GCS_MAVLINK.initialise_message_intervals_from_streamrates this
    PMem.stB (this + 764) true
  let mut start : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let mut start16 : UInt16 := UInt32.toUInt16 ((start &&& (Int32.toUInt32 ((65535 : Int32)))))
  for _ in PMem.loopFuel do
    if !((decide (((((← PMem.clock) / 1000).toUInt32) - start) < (Int32.toUInt32 ((5 : Int32)))))) then break
    let t'2 ← gcs
    let t'3 ← GCS.out_of_time t'2
    if t'3 then
      break
    let t'4 ← GCS_MAVLINK.deferred_message_to_send_index this start16
    let mut next : Int8 := t'4
    if ((Int8.toInt32 (next)) != (-(1 : Int32))) then
      let t'5 ← PMem.ldU8 ((this + 506) + ((Int8.toInt64 (next)) * 6).toUInt64)
      let t'6 ← GCS_MAVLINK.do_try_send_message this t'5
      if !t'6 then
        break
      let t'7 ← PMem.ldU16 (((this + 506) + ((Int8.toInt64 (next)) * 6).toUInt64) + 2)
      let mut interval_ms : UInt16 := t'7
      let t'8 := (((this + 506) + ((Int8.toInt64 (next)) * 6).toUInt64) + 4)
      let t'9 ← PMem.ldU16 t'8
      let t'10 := (t'9 + (Int16.toUInt16 (Int32.toInt16 ((UInt32.toInt32 (UInt16.toUInt32 (interval_ms)))))))
      PMem.stU16 t'8 t'10
      let t'11 ← PMem.ldU16 (((this + 506) + ((Int8.toInt64 (next)) * 6).toUInt64) + 4)
      if (decide ((UInt32.toInt32 (UInt16.toUInt32 ((Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (start16))) - (UInt32.toInt32 (UInt16.toUInt32 (t'11)))))))))) > (UInt32.toInt32 (UInt16.toUInt32 (interval_ms))))) then
        PMem.stU16 (((this + 506) + ((Int8.toInt64 (next)) * 6).toUInt64) + 4) start16
      let t'12 := Int32.toInt8 ((-(1 : Int32)))
      PMem.stI8 (this + 524) t'12
      continue
    let t'13 ← Bitmask'102.first_set (this + 748)
    let mut fs : Int16 := t'13
    if ((Int16.toInt32 (fs)) != (-(1 : Int32))) then
      let mut next'2 : UInt8 := Int8.toUInt8 (Int16.toInt8 (fs))
      let t'14 ← GCS_MAVLINK.do_try_send_message this next'2
      if !t'14 then
        break
      Bitmask'102.clear (this + 748) (UInt8.toUInt16 (next'2))
      continue
    let t'15 ← GCS_MAVLINK.next_deferred_bucket_message_to_send this start16
    let mut next'3 : UInt8 := t'15
    if ((UInt32.toInt32 (UInt8.toUInt32 (next'3))) != (UInt32.toInt32 (UInt8.toUInt32 ((255 : UInt8))))) then
      let t'16 ← GCS_MAVLINK.do_try_send_message this next'3
      if !t'16 then
        break
      Bitmask'102.clear (this + 732) (UInt8.toUInt16 (next'3))
      let t'17 ← Bitmask'102.count (this + 732)
      if ((UInt32.toInt32 (UInt16.toUInt32 (t'17))) == (0 : Int32)) then
        let t'18 ← PMem.ldU8 (this + 728)
        let t'19 ← GCS_MAVLINK.get_reschedule_interval_ms this ((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (t'18))) * 20).toUInt64)
        let mut interval_ms'2 : UInt16 := t'19
        let t'20 ← PMem.ldU8 (this + 728)
        let t'21 := (((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (t'20))) * 20).toUInt64) + 18)
        let t'22 ← PMem.ldU16 t'21
        let t'23 := (t'22 + (Int16.toUInt16 (Int32.toInt16 ((UInt32.toInt32 (UInt16.toUInt32 (interval_ms'2)))))))
        PMem.stU16 t'21 t'23
        let t'24 ← PMem.ldU8 (this + 728)
        let t'25 ← PMem.ldU16 (((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (t'24))) * 20).toUInt64) + 18)
        if (decide ((UInt32.toInt32 (UInt16.toUInt32 ((Int16.toUInt16 (Int32.toInt16 (((UInt32.toInt32 (UInt16.toUInt32 (start16))) - (UInt32.toInt32 (UInt16.toUInt32 (t'25)))))))))) > (UInt32.toInt32 (UInt16.toUInt32 (interval_ms'2))))) then
          let t'26 ← PMem.ldU8 (this + 728)
          PMem.stU16 (((this + 528) + ((UInt64.toInt64 (UInt8.toUInt64 (t'26))) * 20).toUInt64) + 18) start16
        GCS_MAVLINK.find_next_bucket_to_send this start16
      continue
    break
  let t'27 := (this + 858)
  let t'28 ← PMem.ldU16 t'27
  let t'29 ← PMem.ldU8 ((this + 408) + 10)
  let t'30 ← PMem.ldU8 (this + 856)
  let t'31 := (t'28 + (Int16.toUInt16 (Int32.toInt16 ((UInt32.toInt32 (UInt8.toUInt32 ((Int8.toUInt8 (Int32.toInt8 (((UInt32.toInt32 (UInt8.toUInt32 (t'29))) - (UInt32.toInt32 (UInt8.toUInt32 (t'30))))))))))))))
  PMem.stU16 t'27 t'31
  let t'32 ← PMem.ldU8 ((this + 408) + 10)
  PMem.stU8 (this + 856) t'32
  return ()

/-- C++ `GCS::update_send : void ()`, `GCS_Common.cpp:2743-2793`. -/
def GCS.update_send (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ (this + 160)
  let t'2 ← PMem.ldU32 t'1
  PMem.stU32 (0xbc50 : UInt64) /- &mavlink_system -/ t'2
  PMem.stB (this + 473) true
  let t'3 ← PMem.ldB (this + 472)
  if !t'3 then
    PMem.stB (this + 472) true
    let t'4 ← PMem.alloc 56
    let t'5 ← AP.mission
    MissionItemProtocol_Waypoints.MissionItemProtocol_Waypoints t'4 t'5
    PMem.stU64 ((0xbc58 : UInt64) /- &GCS::missionitemprotocols -/ + ((UInt64.toInt64 (UInt32.toUInt64 ((0 : UInt32)))) * 8).toUInt64) t'4
  let __range1 : UInt64 := (0xbc58 : UInt64) /- &GCS::missionitemprotocols -/
  let mut __begin1 : UInt64 := __range1
  let mut __end1 : UInt64 := (__range1 + ((3 : Int64) * 8).toUInt64)
  let mut first'6 := true
  for _ in PMem.loopFuel do
    if !first'6 then
      let t'7 := (__begin1 + 8)
      __begin1 := t'7
      pure ()
    first'6 := false
    if !((__begin1 != __end1)) then break
    let t'8 ← PMem.ldU64 __begin1
    let mut prot : UInt64 := t'8
    if (prot == (0 : UInt64)) then
      continue
    MissionItemProtocol.update prot
  let t'9 ← PMem.ldU8 (this + 536)
  let mut i : UInt8 := t'9
  let mut first'10 := true
  for _ in PMem.loopFuel do
    if !first'10 then
      let t'11 := i
      let t'12 := (t'11 + 1)
      i := t'12
      pure ()
    first'10 := false
    let t'13 ← GCS.num_gcs this
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i))) < (UInt32.toInt32 (UInt8.toUInt32 (t'13)))))) then break
    let t'14 ← GCS_Copter.chan this i
    GCS_MAVLINK.update_send t'14
  let mut i'2 : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'15 := true
  for _ in PMem.loopFuel do
    if !first'15 then
      let t'16 := i'2
      let t'17 := (t'16 + 1)
      i'2 := t'17
      pure ()
    first'15 := false
    let t'18 ← PMem.ldU8 (this + 536)
    if !((decide ((UInt32.toInt32 (UInt8.toUInt32 (i'2))) < (UInt32.toInt32 (UInt8.toUInt32 (t'18)))))) then break
    let t'19 ← GCS_Copter.chan this i'2
    GCS_MAVLINK.update_send t'19
  GCS.service_statustext this
  let t'20 := (this + 536)
  let t'21 ← PMem.ldU8 t'20
  let t'22 := (t'21 + 1)
  PMem.stU8 t'20 t'22
  let t'23 ← PMem.ldU8 (this + 536)
  let t'24 ← GCS.num_gcs this
  if (decide ((UInt32.toInt32 (UInt8.toUInt32 (t'23))) ≥ (UInt32.toInt32 (UInt8.toUInt32 (t'24))))) then
    let t'25 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
    PMem.stU8 (this + 536) t'25
  return ()

/-- C++ `Copter::motors_output : void (bool)`, `motors.cpp:62-121`. -/
def Copter.motors_output (this : UInt64) (full_push : Bool) : PMem.M Unit := do
  let mut full_push := full_push
  let t'1 ← PMem.ldB ((this + 9448) + 21)
  let mut sc'9 := t'1
  if sc'9 then
    let t'2 ← PMem.ldU64 (this + 9528)
    let t'3 ← AP_Motors.armed t'2
    let mut sc'5 := !t'3
    if !sc'5 then
      let t'4 ← PMem.ldU32 (this + 11216)
      sc'5 := (decide ((UInt32.toBinary32 (((((← PMem.clock) / 1000).toUInt32) - t'4))) > ((Binary32.ofBits 0x40000000 /- 2 -/) * (Binary32.ofBits 0x447a0000 /- 1000 -/))))
    let mut sc'8 := sc'5
    if !sc'8 then
      let t'6 ← PMem.ldU64 (this + 9488)
      let t'7 ← vcall'Mode'mode_number'1 t'6
      sc'8 := (t'7 == (18 : UInt8))
    sc'9 := sc'8
  if sc'9 then
    PMem.stB ((this + 9448) + 21) false
  SRV_Channels.calc_pwm
  let t'10 ← AP.srv
  let srv : UInt64 := t'10
  SRV_Channels.cork srv
  SRV_Channels.output_ch_all
  let t'11 ← PMem.ldU64 (this + 9528)
  let t'12 ← AP_Motors.armed t'11
  let mut sc'14 := t'12
  if sc'14 then
    let t'13 ← PMem.ldB ((this + 9448) + 21)
    sc'14 := !t'13
  let mut sc'18 := sc'14
  if sc'18 then
    let t'15 ← PMem.ldB ((this + 9448) + 18)
    let mut sc'17 := !t'15
    if !sc'17 then
      let t'16 ← PMem.ldB ((this + 9448) + 20)
      sc'17 := t'16
    sc'18 := sc'17
  let mut sc'20 := sc'18
  if sc'20 then
    let t'19 ← SRV_Channels.get_emergency_stop
    sc'20 := !t'19
  let mut interlock : Bool := sc'20
  let t'21 ← PMem.ldU64 (this + 9528)
  let t'22 ← AP_Motors.get_interlock t'21
  if ((!t'22) && interlock) then
    let t'23 ← PMem.ldU64 (this + 9528)
    AP_Motors.set_interlock t'23 true
  else
    let t'24 ← PMem.ldU64 (this + 9528)
    let t'25 ← AP_Motors.get_interlock t'24
    if (t'25 && (!interlock)) then
      let t'26 ← PMem.ldU64 (this + 9528)
      AP_Motors.set_interlock t'26 false
  let t'27 ← PMem.ldB ((this + 9448) + 12)
  if t'27 then
    Copter.motor_test_output this
  else
    let t'28 ← PMem.ldB ((this + 9448) + 11)
    if t'28 then
      Copter.compassmot_output this
    else
      let t'29 ← PMem.ldU64 (this + 9488)
      vcall'Mode'output_to_motors'30 t'29
  if full_push then
    SRV_Channels.push srv
  else
    let t'30 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
    discard <| PMem.halDev "AP_HAL::RCOutput::push" t'30 #[]
  return ()

/-- C++ `Copter::motors_output_main : void ()`, `motors.cpp:124-129`. -/
def Copter.motors_output_main (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 13209)
  if !t'1 then
    Copter.motors_output this true
  return ()

/-- C++ `AP_Arming::update : void ()`, `AP_Arming.cpp:265-289`. -/
def AP_Arming.update (this : UInt64) : PMem.M Unit := do
  let mut now_ms : UInt32 := ((← PMem.clock) / 1000).toUInt32
  let mut display_fail : Bool := false
  let t'1 ← PMem.ldB (this + 70)
  let mut sc'3 := t'1
  if sc'3 then
    let t'2 ← PMem.ldU32 (this + 64)
    sc'3 := (decide ((now_ms - t'2) > (Int32.toUInt32 ((4000 : Int32)))))
  let mut sc'5 := sc'3
  if !sc'5 then
    let t'4 ← PMem.ldU32 (this + 64)
    sc'5 := (decide ((now_ms - t'4) > (Int32.toUInt32 (((30 : Int32) * (1000 : Int32))))))
  if sc'5 then
    PMem.stB (this + 70) false
    display_fail := true
    PMem.stU32 (this + 64) now_ms
  let t'6 ← AP_Arming.option_enabled this (1 : Int32)
  if t'6 then
    display_fail := false
  let t'7 ← AP_Arming_Copter.pre_arm_checks this display_fail
  discard <| pure (t'7)
  return ()

end Vehicle_lib
