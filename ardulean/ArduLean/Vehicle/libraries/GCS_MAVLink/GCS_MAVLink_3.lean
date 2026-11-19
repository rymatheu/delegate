import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_Arming.AP_Arming
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.mavlink.mavlink
import ArduLean.Vehicle.ArduCopter.ArduCopter_2
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink_2
import ArduLean.Vehicle.World
import ArduLean.Vehicle.ArduCopter.ArduCopter_3

/-!
ArduPilot `libraries/GCS_MAVLink`, part 3 of 3. Sources: `libraries/GCS_MAVLink/GCS_Common.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `GCS_MAVLINK::send_banner : void ()`, `GCS_Common.cpp:4714-4761`. -/
def GCS_MAVLINK.send_banner.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let t'1 ← AP.fwversion
  let fwver : UInt64 := t'1
  let t'2 ← PMem.ldU64 (fwver + 24)
  PMem.stU64 (fp + 0) t'2
  GCS_MAVLINK.send_text this (6 : UInt32) (0x13fd2 : UInt64) /- "%s" -/ (fp + 0)
  let t'3 ← PMem.ldU64 (fwver + 60)
  let mut sc'5 := (t'3 != 0)
  if sc'5 then
    let t'4 ← PMem.ldU64 (fwver + 76)
    sc'5 := (t'4 != 0)
  if sc'5 then
    let t'6 ← PMem.ldU64 (fwver + 60)
    PMem.stU64 (fp + 8) t'6
    let t'7 ← PMem.ldU64 (fwver + 68)
    PMem.stU64 (fp + 16) t'7
    let t'8 ← PMem.ldU64 (fwver + 76)
    PMem.stU64 (fp + 24) t'8
    let t'9 ← PMem.ldU64 (fwver + 84)
    PMem.stU64 (fp + 32) t'9
    GCS_MAVLINK.send_text this (6 : UInt32) (0x18ae5 : UInt64) /- "%s: %s %s: %s" -/ (fp + 8)
  else
    let t'10 ← PMem.ldU64 (fwver + 76)
    if (t'10 != 0) then
      let t'11 ← PMem.ldU64 (fwver + 76)
      PMem.stU64 (fp + 40) t'11
      let t'12 ← PMem.ldU64 (fwver + 84)
      PMem.stU64 (fp + 48) t'12
      GCS_MAVLINK.send_text this (6 : UInt32) (0x14cdf : UInt64) /- "%s: %s" -/ (fp + 40)
  let t'13 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'14 ← PMem.halDev "AP_HAL::Util::get_system_id" t'13 #[(fp + 56)]
  if (t'14 != 0) then
    PMem.stU64 (fp + 112) (fp + 56)
    GCS_MAVLINK.send_text this (6 : UInt32) (0x13fd2 : UInt64) /- "%s" -/ (fp + 112)
  let t'15 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 72)
  let t'16 ← PMem.halDev "AP_HAL::RCOutput::get_output_mode_banner" t'15 #[(fp + 120), (UInt8.toUInt64 ((UInt64.toUInt8 ((50 : UInt64)))))]
  if (t'16 != 0) then
    PMem.stU64 (fp + 176) (fp + 120)
    GCS_MAVLINK.send_text this (6 : UInt32) (0x13fd2 : UInt64) /- "%s" -/ (fp + 176)
  for i'17 in [0:6] do
    let i : UInt8 := UInt8.ofNat i'17
    let t'18 ← VehicleBridge.ins'0
    let t'19 ← VehicleBridge.AP_InertialSensor.get_output_banner'3 t'18 i (fp + 120) (UInt64.toUInt8 ((50 : UInt64)))
    worldOutputs'drain
    if t'19 then
      PMem.stU64 (fp + 184) (fp + 120)
      GCS_MAVLINK.send_text this (6 : UInt32) (0x13fd2 : UInt64) /- "%s" -/ (fp + 184)
  return ()

def GCS_MAVLINK.send_banner (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 192
  let r ← GCS_MAVLINK.send_banner.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_utm_global_position : void () const`, `GCS_Common.cpp:6154-6295`. -/
def GCS_MAVLINK.send_utm_global_position.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  let mut flags : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))
  let t'1 ← VehicleBridge.rtc'0
  let t'2 ← VehicleBridge.AP_RTC.get_utc_usec'1 t'1 (fp + 0)
  if t'2 then
    let t'3 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((1 : UInt32)))))))
    flags := t'3
  PMem.stU8 (fp + 32) (UInt64.toUInt8 (((18 : UInt64) / (1 : UInt64))))
  let t'4 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 88)
  let t'5 ← PMem.halDev "AP_HAL::Util::get_system_id_unformatted" t'4 #[(fp + 8), (fp + 32)]
  discard <| pure ((t'5 != 0))
  let t'6 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((2 : UInt32)))))))
  flags := t'6
  let mut lat : Int32 := (0 : Int32)
  let mut lon : Int32 := (0 : Int32)
  let mut alt_mm : Int32 := (0 : Int32)
  let mut relative_alt_mm : Int32 := (0 : Int32)
  let t'7 ← VehicleBridge.ahrs'0
  let ahrs : UInt64 := t'7
  Location.Location (fp + 40)
  let t'8 ← VehicleBridge.AP_AHRS.get_location'1 ahrs (fp + 40)
  if t'8 then
    let t'9 ← PMem.ldI32 ((fp + 40) + 8)
    lat := t'9
    let t'10 ← PMem.ldI32 ((fp + 40) + 12)
    lon := t'10
    let t'11 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((4 : UInt32)))))))
    flags := t'11
  let t'12 ← PMem.ldF32 (0xbef8 : UInt64) /- &NaNf -/
  PMem.stF32 (fp + 56) t'12
  let t'13 ← VehicleBridge.gps'0
  let t'14 ← VehicleBridge.AP_GPS.get_undulation'1 t'13 (fp + 56)
  if t'14 then
    let t'15 ← GCS_MAVLINK.global_position_int_alt this
    alt_mm := t'15
    let t'16 ← PMem.ldF32 (fp + 56)
    let t'17 := (alt_mm - (Binary32.toInt32 ((t'16 * (Int32.toBinary32 ((1000 : Int32)))))))
    alt_mm := t'17
    let t'18 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((8 : UInt32)))))))
    flags := t'18
  let mut vx : Int16 := Int32.toInt16 ((0 : Int32))
  let mut vy : Int16 := Int32.toInt16 ((0 : Int32))
  let mut vz : Int16 := Int32.toInt16 ((0 : Int32))
  Vector3'float.Vector3'2 (fp + 64)
  let t'19 ← VehicleBridge.AP_AHRS.get_velocity_NED'1 ahrs (fp + 64)
  if t'19 then
    let t'20 ← PMem.ldF32 (fp + 64)
    let t'21 := Binary32.toInt16 ((t'20 * (Int32.toBinary32 ((100 : Int32)))))
    vx := t'21
    let t'22 ← PMem.ldF32 ((fp + 64) + 4)
    let t'23 := Binary32.toInt16 ((t'22 * (Int32.toBinary32 ((100 : Int32)))))
    vy := t'23
    let t'24 ← PMem.ldF32 ((fp + 64) + 8)
    let t'25 := Binary32.toInt16 ((t'24 * (Int32.toBinary32 ((100 : Int32)))))
    vz := t'25
    let t'26 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((32 : UInt32)))))))
    flags := t'26
    let t'27 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((64 : UInt32)))))))
    flags := t'27
  let mut next_lat : Int32 := (0 : Int32)
  let mut next_lon : Int32 := (0 : Int32)
  let mut next_alt_mm : Int32 := (0 : Int32)
  Location.Location (fp + 80)
  let t'28 ← PMem.ldF32 (fp + 56)
  let mut sc'30 := !(Binary32.isNaN t'28)
  if sc'30 then
    let t'29 ← GCS_MAVLINK_Copter.get_target_location this (fp + 80)
    sc'30 := t'29
  let mut sc'32 := sc'30
  if sc'32 then
    let t'31 ← Location.initialised (fp + 80)
    sc'32 := t'31
  if sc'32 then
    let t'33 ← Location.get_alt_m (fp + 80) (0 : Int32) (fp + 96)
    if t'33 then
      let t'34 ← PMem.ldI32 ((fp + 80) + 8)
      next_lat := t'34
      let t'35 ← PMem.ldI32 ((fp + 80) + 12)
      next_lon := t'35
      let t'36 ← PMem.ldF32 (fp + 96)
      let t'37 := Binary32.toInt32 ((t'36 * (Binary32.ofBits 0x447a0000 /- 1000 -/)))
      next_alt_mm := t'37
      let t'38 ← PMem.ldF32 (fp + 56)
      let t'39 := (next_alt_mm - (Binary32.toInt32 ((t'38 * (Int32.toBinary32 ((1000 : Int32)))))))
      next_alt_mm := t'39
      let t'40 := (flags ||| (Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 ((128 : UInt32)))))))
      flags := t'40
  let mut flight_state : UInt8 := UInt32.toUInt8 ((1 : UInt32))
  let t'41 ← GCS_MAVLINK_Copter.landed_state this
  let sw'42 := UInt32.toInt32 (t'41)
  if sw'42 == (0 : Int32) || sw'42 == (5 : Int32) then
    let t'43 := UInt32.toUInt8 ((1 : UInt32))
    flight_state := t'43
  else if sw'42 == (1 : Int32) then
    let t'44 := UInt32.toUInt8 ((2 : UInt32))
    flight_state := t'44
  else if sw'42 == (2 : Int32) || sw'42 == (3 : Int32) || sw'42 == (4 : Int32) then
    let t'45 := UInt32.toUInt8 ((3 : UInt32))
    flight_state := t'45
  else
    pure ()
  let mut h_acc_mm : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut v_acc_mm : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let mut vel_acc_cms : UInt16 := Int16.toUInt16 (Int32.toInt16 ((0 : Int32)))
  let t'46 ← VehicleBridge.AP_AHRS.get_pos_vel_uncertainty'3 ahrs (fp + 104) (fp + 112) (fp + 120)
  if t'46 then
    let t'47 ← PMem.ldF32 (fp + 104)
    let t'48 ← constrain_value_line'float (t'47 * (Binary32.ofBits 0x447a0000 /- 1000 -/)) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((65535 : Int32))) (Int32.toUInt32 ((6268 : Int32)))
    let t'49 := Binary32.toUInt16 (t'48)
    h_acc_mm := t'49
    let t'50 ← PMem.ldF32 (fp + 112)
    let t'51 ← constrain_value_line'float (t'50 * (Binary32.ofBits 0x447a0000 /- 1000 -/)) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((65535 : Int32))) (Int32.toUInt32 ((6269 : Int32)))
    let t'52 := Binary32.toUInt16 (t'51)
    v_acc_mm := t'52
    let t'53 ← PMem.ldF32 (fp + 120)
    let t'54 ← constrain_value_line'float (t'53 * (Binary32.ofBits 0x42c80000 /- 100 -/)) (Int32.toBinary32 ((0 : Int32))) (Int32.toBinary32 ((65535 : Int32))) (Int32.toUInt32 ((6270 : Int32)))
    let t'55 := Binary32.toUInt16 (t'54)
    vel_acc_cms := t'55
  let t'56 ← PMem.ldU64 (fp + 0)
  PMem.stU64 ((fp + 128) + 0) t'56
  PMem.stI32 ((fp + 128) + 8) lat
  PMem.stI32 ((fp + 128) + 12) lon
  PMem.stI32 ((fp + 128) + 16) alt_mm
  PMem.stI32 ((fp + 128) + 20) relative_alt_mm
  PMem.stI32 ((fp + 128) + 24) next_lat
  PMem.stI32 ((fp + 128) + 28) next_lon
  PMem.stI32 ((fp + 128) + 32) next_alt_mm
  PMem.stI16 ((fp + 128) + 36) vx
  PMem.stI16 ((fp + 128) + 38) vy
  PMem.stI16 ((fp + 128) + 40) vz
  PMem.stU16 ((fp + 128) + 42) h_acc_mm
  PMem.stU16 ((fp + 128) + 44) v_acc_mm
  PMem.stU16 ((fp + 128) + 46) vel_acc_cms
  PMem.stU16 ((fp + 128) + 48) (Int16.toUInt16 (Int32.toInt16 ((0 : Int32))))
  discard <| PMem.memset ((fp + 128) + 50) 0 18
  PMem.stU8 ((fp + 128) + 68) flight_state
  PMem.stU8 ((fp + 128) + 69) flags
  let t'57 ← PMem.memcpy ((fp + 128) + 50) (fp + 8) (18 : UInt64)
  discard <| pure (t'57)
  let t'58 ← PMem.ldU32 (this + 40)
  mavlink_msg_utm_global_position_send_struct t'58 (fp + 128)
  return ()

def GCS_MAVLINK.send_utm_global_position (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 198
  let r ← GCS_MAVLINK.send_utm_global_position.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_position_target_global_int : void ()`, `GCS_Common.cpp:6355-6391`. -/
def GCS_MAVLINK.send_position_target_global_int.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  Location.Location (fp + 0)
  let t'1 ← GCS_MAVLINK_Copter.get_target_location this (fp + 0)
  if !t'1 then
    return ()
  let t'2 ← Location.initialised (fp + 0)
  if !t'2 then
    return ()
  let t'3 ← Location.get_alt_m (fp + 0) (0 : Int32) (fp + 16)
  if !t'3 then
    return ()
  let t'4 ← PMem.ldU32 (this + 40)
  let t'5 ← PMem.ldU16 (0x12e60 : UInt64) /- &GCS_MAVLINK::send_position_target_global_int(...)::TYPE_MASK -/
  let t'6 ← PMem.ldI32 ((fp + 0) + 8)
  let t'7 ← PMem.ldI32 ((fp + 0) + 12)
  let t'8 ← PMem.ldF32 (fp + 16)
  mavlink_msg_position_target_global_int_send t'4 (((← PMem.clock) / 1000).toUInt32) (UInt32.toUInt8 ((0 : UInt32))) t'5 t'6 t'7 t'8 (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/) (Binary32.ofBits 0x00000000 /- 0 -/)
  return ()

def GCS_MAVLINK.send_position_target_global_int (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 20
  let r ← GCS_MAVLINK.send_position_target_global_int.body fp this
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::send_extended_sys_state : void () const`, `GCS_Common.cpp:6066-6069`. -/
def GCS_MAVLINK.send_extended_sys_state (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldU32 (this + 40)
  let t'2 ← GCS_MAVLINK_Copter.vtol_state this
  let t'3 ← GCS_MAVLINK_Copter.landed_state this
  mavlink_msg_extended_sys_state_send t'1 (UInt32.toUInt8 (t'2)) (UInt32.toUInt8 (t'3))
  return ()

/-- C++ `GCS_MAVLINK::send_flight_information : void ()`, `GCS_Common.cpp:6479-6526`. -/
def GCS_MAVLINK.send_flight_information (this : UInt64) : PMem.M Unit := do
  let mut time_boot_micros : UInt64 := (← PMem.clock)
  let mut time_boot_ms : UInt32 := UInt64.toUInt32 ((time_boot_micros / (Int64.toUInt64 (Int32.toInt64 ((1000 : Int32))))))
  let t'1 ← AP.arming
  let t'2 ← AP_Arming.arm_time_us t'1
  let mut arm_time_us : UInt64 := t'2
  let t'3 ← GCS_MAVLINK_Copter.landed_state this
  let mut current_landed_state : UInt32 := t'3
  let t'4 ← PMem.ldU32 (this + 16)
  if ((UInt32.toInt32 (t'4)) != (UInt32.toInt32 (current_landed_state))) then
    let sw'5 := UInt32.toInt32 (current_landed_state)
    if sw'5 == (2 : Int32) || sw'5 == (3 : Int32) || sw'5 == (4 : Int32) then
      let t'6 ← PMem.ldU64 ((this + 16) + 8)
      if !(t'6 != (0 : UInt64)) then
        PMem.stU64 ((this + 16) + 8) time_boot_micros
    else if sw'5 == (1 : Int32) then
      let t'7 := Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))
      PMem.stU64 ((this + 16) + 8) t'7
    else if sw'5 == (0 : Int32) || sw'5 == (5 : Int32) then
      pure ()
    else
      pure ()
    PMem.stU32 (this + 16) current_landed_state
  let t'8 ← PMem.ldU64 ((this + 16) + 8)
  let mut takeoff_time_us : UInt64 := t'8
  let mut flight_number : UInt64 := Int64.toUInt64 (Int32.toInt64 ((0 : Int32)))
  let t'9 ← PMem.ldU32 (this + 40)
  mavlink_msg_flight_information_send t'9 time_boot_ms arm_time_us takeoff_time_us flight_number (Int32.toUInt32 ((0 : Int32)))
  return ()

/-- C++ `GCS_MAVLINK::try_send_message : bool (const enum ap_message)`, `GCS_Common.cpp:6606-7081`. -/
def GCS_MAVLINK.try_send_message.body (fp : UInt64) (this : UInt64) (id : UInt8) : PMem.M Bool := do
  let mut id := id
  let mut ret : Bool := true
  let sw'1 := UInt32.toInt32 (UInt8.toUInt32 (id))
  if sw'1 == (3 : Int32) then
    let t'2 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((28 : Int32))))
    if !t'2 then
      return false
    GCS_MAVLINK.send_attitude this
  else if sw'1 == (4 : Int32) then
    let t'3 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((48 : Int32))))
    if !t'3 then
      return false
    GCS_MAVLINK.send_attitude_quaternion this
  else if sw'1 == (31 : Int32) then
    let t'4 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((25 : Int32))))
    if !t'4 then
      return false
    GCS_MAVLINK.queued_param_send this
  else if sw'1 == (0 : Int32) then
    let t'5 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((9 : Int32))))
    if !t'5 then
      return false
    let t'6 := ((← PMem.clock) / 1000).toUInt32
    PMem.stU32 (this + 8) t'6
    GCS_MAVLINK.send_heartbeat this
  else if sw'1 == (5 : Int32) then
    let t'7 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((28 : Int32))))
    if !t'7 then
      return false
    GCS_MAVLINK.send_global_position_int this
  else if sw'1 == (70 : Int32) then
    let t'8 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((60 : Int32))))
    if !t'8 then
      return false
    GCS_MAVLINK.send_home_position this
  else if sw'1 == (69 : Int32) then
    let t'9 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((20 : Int32))))
    if !t'9 then
      return false
    GCS_MAVLINK.send_gps_global_origin this
  else if sw'1 == (101 : Int32) then
    let t'10 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((70 : Int32))))
    if !t'10 then
      return false
    GCS_MAVLINK.send_utm_global_position this
  else if sw'1 == (11 : Int32) || sw'1 == (61 : Int32) || sw'1 == (28 : Int32) || sw'1 == (29 : Int32) || sw'1 == (30 : Int32) then
    let t'11 ← GCS_MAVLINK.try_send_mission_message this id
    ret := t'11
  else if sw'1 == (65 : Int32) then
    let t'12 ← GCS_MAVLINK.send_battery_status this
    discard <| pure (t'12)
  else if sw'1 == (55 : Int32) then
    let t'13 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((26 : Int32))))
    if !t'13 then
      return false
    let t'14 ← VehicleBridge.ahrs'0
    VehicleBridge.AP_AHRS.send_ekf_status_report'1 t'14 this (GCS_MAVLINK.get_chan this)
    worldOutputs'drain
  else if sw'1 == (9 : Int32) then
    let t'15 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((8 : Int32))))
    if !t'15 then
      return false
    GCS_MAVLINK.send_meminfo this
  else if sw'1 == (38 : Int32) then
    GCS_MAVLINK.send_distance_sensor this
  else if sw'1 == (26 : Int32) then
    let t'16 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((12 : Int32))))
    if !t'16 then
      return false
    GCS_MAVLINK.send_system_time this
  else if sw'1 == (22 : Int32) then
    let t'17 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((52 : Int32))))
    if !t'17 then
      return false
    let t'18 ← PMem.ldU32 (this + 40)
    let t'19 ← VehicleBridge.gps'0
    VehicleBridge.AP_GPS.send_mavlink_gps_raw'1 t'19 t'18
    worldOutputs'drain
  else if sw'1 == (24 : Int32) then
    let t'20 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((57 : Int32))))
    if !t'20 then
      return false
    let t'21 ← PMem.ldU32 (this + 40)
    let t'22 ← VehicleBridge.gps'0
    VehicleBridge.AP_GPS.send_mavlink_gps2_raw'1 t'22 t'21
    worldOutputs'drain
  else if sw'1 == (56 : Int32) then
    let t'23 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((28 : Int32))))
    if !t'23 then
      return false
    GCS_MAVLINK.send_local_position this
  else if sw'1 == (92 : Int32) then
    let t'24 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((37 : Int32))))
    if !t'24 then
      return false
    GCS_MAVLINK_Copter.send_attitude_target this
  else if sw'1 == (62 : Int32) then
    let t'25 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((51 : Int32))))
    if !t'25 then
      return false
    GCS_MAVLINK.send_position_target_global_int this
  else if sw'1 == (63 : Int32) then
    let t'26 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((51 : Int32))))
    if !t'26 then
      return false
    GCS_MAVLINK_Copter.send_position_target_local_ned this
  else if sw'1 == (8 : Int32) then
    let t'27 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((6 : Int32))))
    if !t'27 then
      return false
    GCS_MAVLINK.send_power_status this
  else if sw'1 == (13 : Int32) then
    let t'28 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((42 : Int32))))
    if !t'28 then
      return false
    GCS_MAVLINK.send_rc_channels this
  else if sw'1 == (14 : Int32) then
    let t'29 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((22 : Int32))))
    if !t'29 then
      return false
    GCS_MAVLINK.send_rc_channels_raw this
  else if sw'1 == (15 : Int32) then
    let t'30 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((29 : Int32))))
    if !t'30 then
      return false
    GCS_MAVLINK.send_raw_imu this
  else if sw'1 == (16 : Int32) then
    let t'31 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((24 : Int32))))
    if !t'31 then
      return false
  else if sw'1 == (17 : Int32) then
    let t'32 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((24 : Int32))))
    if !t'32 then
      return false
  else if sw'1 == (18 : Int32) then
    let t'33 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((24 : Int32))))
    if !t'33 then
      return false
  else if sw'1 == (96 : Int32) then
    let t'34 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((63 : Int32))))
    if !t'34 then
      return false
    GCS_MAVLINK.send_highres_imu this
  else if sw'1 == (19 : Int32) then
    let t'35 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((16 : Int32))))
    if !t'35 then
      return false
    GCS_MAVLINK.send_scaled_pressure this
  else if sw'1 == (20 : Int32) then
    let t'36 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((16 : Int32))))
    if !t'36 then
      return false
    GCS_MAVLINK.send_scaled_pressure2 this
  else if sw'1 == (21 : Int32) then
    let t'37 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((16 : Int32))))
    if !t'37 then
      return false
    GCS_MAVLINK.send_scaled_pressure3 this
  else if sw'1 == (12 : Int32) then
    let t'38 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((37 : Int32))))
    if !t'38 then
      return false
    GCS_MAVLINK.send_servo_output_raw this
  else if sw'1 == (33 : Int32) then
    let t'39 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((44 : Int32))))
    if !t'39 then
      return false
    GCS_MAVLINK.send_simstate this
  else if sw'1 == (34 : Int32) then
    let t'40 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((92 : Int32))))
    if !t'40 then
      return false
    GCS_MAVLINK.send_sim_state this
  else if sw'1 == (7 : Int32) then
    let t'41 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((43 : Int32))))
    if !t'41 then
      return false
    GCS_MAVLINK.send_sys_status this
  else if sw'1 == (2 : Int32) then
    let t'42 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((24 : Int32))))
    if !t'42 then
      return false
    GCS_MAVLINK.send_ahrs2 this
  else if sw'1 == (57 : Int32) then
    let t'43 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((33 : Int32))))
    if !t'43 then
      return false
    GCS_MAVLINK_Copter.send_pid_tuning this
  else if sw'1 == (10 : Int32) then
    let t'44 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((26 : Int32))))
    if !t'44 then
      return false
    GCS_MAVLINK_Copter.send_nav_controller_output this
  else if sw'1 == (1 : Int32) then
    let t'45 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((28 : Int32))))
    if !t'45 then
      return false
    GCS_MAVLINK.send_ahrs this
  else if sw'1 == (72 : Int32) then
    let t'46 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((2 : Int32))))
    if !t'46 then
      return false
    GCS_MAVLINK.send_extended_sys_state this
  else if sw'1 == (6 : Int32) then
    let t'47 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((20 : Int32))))
    if !t'47 then
      return false
    GCS_MAVLINK.send_vfr_hud this
  else if sw'1 == (58 : Int32) then
    let t'48 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((32 : Int32))))
    if !t'48 then
      return false
    GCS_MAVLINK.send_vibration this
  else if sw'1 == (73 : Int32) then
    let t'49 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((78 : Int32))))
    if !t'49 then
      return false
    GCS_MAVLINK.send_autopilot_version this
  else if sw'1 == (98 : Int32) then
    let t'50 ← GCS_MAVLINK.send_available_modes this
    ret := t'50
  else if sw'1 == (99 : Int32) then
    let t'51 ← GCS_MAVLINK.send_available_mode_monitor this
    ret := t'51
  else if sw'1 == (100 : Int32) then
    let t'52 ← GCS_MAVLINK.check_payload_size this (Int16.toUInt16 (Int32.toInt16 ((32 : Int32))))
    if !t'52 then
      return false
    GCS_MAVLINK.send_flight_information this
  else if sw'1 == (64 : Int32) then
    pure ()
  else
    PMem.stU64 (fp + 0) (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt8.toUInt32 (id))))))
    let t'53 ← gcs
    GCS.send_text t'53 (7 : UInt32) (0x18b70 : UInt64) /- "Sending unknown message (%u)" -/ (fp + 0)
  return ret

def GCS_MAVLINK.try_send_message (this : UInt64) (id : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 8
  let r ← GCS_MAVLINK.try_send_message.body fp this id
  PMem.leave fp
  return r

/-- C++ `GCS_MAVLINK::handle_system_time_message : void (const mavlink_message_t &)`, `GCS_Common.cpp:3830-3836`. -/
def GCS_MAVLINK.handle_system_time_message.body (fp : UInt64) (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  __mavlink_system_time_t.__mavlink_system_time_t (fp + 0)
  mavlink_msg_system_time_decode msg (fp + 0)
  let t'1 ← PMem.ldU64 (fp + 0)
  let t'2 ← VehicleBridge.rtc'0
  VehicleBridge.AP_RTC.set_utc_usec'2 t'2 t'1 (1 : UInt8)
  worldOutputs'drain
  return ()

def GCS_MAVLINK.handle_system_time_message (this : UInt64) (msg : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 12
  let r ← GCS_MAVLINK.handle_system_time_message.body fp this msg
  PMem.leave fp
  return r

/-- C++ `GCS::create_gcs_mavlink_backend : bool (AP_HAL::UARTDriver &)`, `GCS_Common.cpp:2828-2850`. -/
def GCS.create_gcs_mavlink_backend (this : UInt64) (uart : UInt64) : PMem.M Bool := do
  let t'1 ← PMem.ldU8 (this + 28)
  if (decide ((UInt8.toUInt64 (t'1)) ≥ ((128 : UInt64) / (8 : UInt64)))) then
    return false
  let t'2 ← GCS_Copter.new_gcs_mavlink_backend this uart
  let t'3 ← PMem.ldU8 (this + 28)
  PMem.stU64 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'3))) * 8).toUInt64) t'2
  let t'4 ← PMem.ldU8 (this + 28)
  let t'5 ← PMem.ldU64 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'4))) * 8).toUInt64)
  if (t'5 == (0 : UInt64)) then
    return false
  let t'6 := (0xbc70 : UInt64) /- &GCS_MAVLINK::var_info -/
  let t'7 ← PMem.ldU8 (this + 28)
  PMem.stU64 ((0x8658 : UInt64) /- &GCS::_chan_var_info -/ + ((UInt64.toInt64 (UInt8.toUInt64 (t'7))) * 8).toUInt64) t'6
  let t'8 ← PMem.ldU8 (this + 28)
  let t'9 ← PMem.ldU64 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'8))) * 8).toUInt64)
  let t'10 ← PMem.ldU8 (this + 28)
  let t'11 ← PMem.ldU64 ((0x8658 : UInt64) /- &GCS::_chan_var_info -/ + ((UInt64.toInt64 (UInt8.toUInt64 (t'10))) * 8).toUInt64)
  AP_Param.load_object_from_eeprom t'9 t'11
  let t'12 ← PMem.ldU8 (this + 28)
  let t'13 ← PMem.ldU8 (this + 28)
  let t'14 ← PMem.ldU64 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'13))) * 8).toUInt64)
  let t'15 ← GCS_MAVLINK.init t'14 t'12
  if !t'15 then
    let t'16 ← PMem.ldU8 (this + 28)
    PMem.stU64 ((this + 32) + ((UInt64.toInt64 (UInt8.toUInt64 (t'16))) * 8).toUInt64) (0 : UInt64)
    return false
  let t'17 := (this + 28)
  let t'18 ← PMem.ldU8 t'17
  let t'19 := (t'18 + 1)
  PMem.stU8 t'17 t'19
  return true

/-- C++ `GCS::setup_console : void ()`, `GCS_Common.cpp:2812-2825`. -/
def GCS.setup_console (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.findSerialProto (1 : Int32) (Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))
  let mut uart : UInt64 := t'1
  if (uart == (0 : UInt64)) then
    return ()
  if (((128 : UInt64) / (8 : UInt64)) == (Int64.toUInt64 (Int32.toInt64 ((0 : Int32))))) then
    return ()
  let t'2 ← GCS.create_gcs_mavlink_backend this uart
  if !t'2 then
    pure ()
  return ()

/-- C++ `GCS::setup_uarts : void ()`, `GCS_Common.cpp:2852-2885`. -/
def GCS.setup_uarts (this : UInt64) : PMem.M Unit := do
  for i'1 in [1:255] do
    let i : UInt8 := UInt8.ofNat i'1
    let t'2 ← PMem.findSerialProto (1 : Int32) i
    let mut uart : UInt64 := t'2
    if (uart == (0 : UInt64)) then
      return ()
    let t'3 ← GCS.create_gcs_mavlink_backend this uart
    if !t'3 then
      pure ()
  return ()

end Vehicle_lib
