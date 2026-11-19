import ArduLean.Runtime.Memory
import ArduLean.Vehicle.libraries.AP_Math.AP_Math
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.StorageManager.StorageManager
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.RC_Channel.RC_Channel
import ArduLean.Vehicle.ArduCopter.ArduCopter
import ArduLean.Vehicle.libraries.AP_Common.AP_Common
import ArduLean.Vehicle.libraries.GCS_MAVLink.GCS_MAVLink
import ArduLean.Vehicle.ArduCopter.ArduCopter_3

/-!
`Startup`: generated items without a C++ function of their own.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ static construction (17 statics, 2 not constructed): the global constructors of the units in the reference executable's order. -/
def staticConstruct : PMem.M Unit := do
  let fp ← PMem.enter 64
  -- copter (ArduCopter/Copter.cpp)
  Copter.Copter (0x86d8 : UInt64) /- &copter -/
  -- Mode::auto_yaw (ArduCopter/autoyaw.cpp): its initializer is in no dump
  -- guided_angle_state (ArduCopter/mode_guided.cpp)
  QuaternionT'float.QuaternionT ((0x12e00 : UInt64) /- &guided_angle_state -/ + 4)
  Vector3'float.Vector3'2 ((0x12e00 : UInt64) /- &guided_angle_state -/ + 20)
  -- guided_limit (ArduCopter/mode_guided.cpp)
  Vector3'double.Vector3 ((0xedb8 : UInt64) /- &guided_limit -/ + 24)
  -- Mode::auto_takeoff (ArduCopter/takeoff.cpp)
  _AutoTakeoff._AutoTakeoff (0x131b0 : UInt64) /- &Mode::auto_takeoff -/
  -- GCS_MAVLINK::routing (libraries/GCS_MAVLink/GCS_MAVLink.cpp): its initializer is in no dump
  -- dummy_rcchannel (libraries/RC_Channel/RC_Channels.cpp)
  RC_Channel.RC_Channel (0xed70 : UInt64) /- &dummy_rcchannel -/
  -- GCS_MAVLINK::last_radio_status (libraries/GCS_MAVLink/GCS_Common.cpp)
  GCS_MAVLINK.LastRadioStatus.LastRadioStatus (0x130d0 : UInt64) /- &GCS_MAVLINK::last_radio_status -/
  -- AP_Mission::_storage (libraries/AP_Mission/AP_Mission.cpp)
  StorageAccess.StorageAccess (0xbf28 : UInt64) /- &AP_Mission::_storage -/ (3 : UInt32)
  -- AP_Vehicle::scheduler_tasks (libraries/AP_Vehicle/AP_Vehicle.cpp)
  PMem.stU64 (fp + 0) ((0x138d8 : UInt64) /- &vehicle -/ + 3992)
  PMem.stU64 (fp + 8) (0x7e000020 : UInt64)
  let t'1 := (fp + 0)
  Functor'void.Functor'2 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 0) + 0) t'1
  PMem.stU64 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 0) + 16) (0x18587 : UInt64) /- "AP_Notify::update" -/
  PMem.stF32 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 0) + 24) (Int32.toBinary32 ((50 : Int32)))
  PMem.stU16 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 0) + 28) (Int16.toUInt16 (Int32.toInt16 ((300 : Int32))))
  PMem.stU8 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 0) + 30) (Int8.toUInt8 (Int32.toInt8 ((78 : Int32))))
  PMem.stU64 (fp + 16) (0x138d8 : UInt64) /- &vehicle -/
  PMem.stU64 (fp + 24) (0x7e000030 : UInt64)
  let t'2 := (fp + 16)
  Functor'void.Functor'2 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 32) + 0) t'2
  PMem.stU64 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 32) + 16) (0x18599 : UInt64) /- "AP_Vehicle::send_watchdog_reset_statustext" -/
  PMem.stF32 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 32) + 24) (Binary64.toBinary32 ((Binary64.ofBits 0x3fb999999999999a /- 10000000000000001/100000000000000000 -/)))
  PMem.stU16 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 32) + 28) (Int16.toUInt16 (Int32.toInt16 ((20 : Int32))))
  PMem.stU8 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 32) + 30) (Int8.toUInt8 (Int32.toInt8 ((225 : Int32))))
  PMem.stU64 (fp + 32) (0x138d8 : UInt64) /- &vehicle -/
  PMem.stU64 (fp + 40) (0x7e000040 : UInt64)
  let t'3 := (fp + 32)
  Functor'void.Functor'2 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 64) + 0) t'3
  PMem.stU64 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 64) + 16) (0x185c4 : UInt64) /- "AP_Vehicle::one_Hz_update" -/
  PMem.stF32 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 64) + 24) (Int32.toBinary32 ((1 : Int32)))
  PMem.stU16 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 64) + 28) (Int16.toUInt16 (Int32.toInt16 ((100 : Int32))))
  PMem.stU8 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 64) + 30) (Int8.toUInt8 (Int32.toInt8 ((252 : Int32))))
  PMem.stU64 (fp + 48) (0x138d8 : UInt64) /- &vehicle -/
  PMem.stU64 (fp + 56) (0x7e000050 : UInt64)
  let t'4 := (fp + 48)
  Functor'void.Functor'2 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 96) + 0) t'4
  PMem.stU64 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 96) + 16) (0x185de : UInt64) /- "AP_Vehicle::update_arming" -/
  PMem.stF32 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 96) + 24) (Int32.toBinary32 ((1 : Int32)))
  PMem.stU16 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 96) + 28) (Int16.toUInt16 (Int32.toInt16 ((50 : Int32))))
  PMem.stU8 (((0xcc38 : UInt64) /- &AP_Vehicle::scheduler_tasks -/ + 96) + 30) (Int8.toUInt8 (Int32.toInt8 ((253 : Int32))))
  -- SRV_Channels::function_mask (libraries/SRV_Channel/SRV_Channels.cpp)
  -- NaNf (ArduCopter/AP_Arming_Copter.cpp)
  PMem.stF32 (0xbef8 : UInt64) /- &NaNf -/ (Binary32.ofBits 0x7fc04152)
  -- AP_Param::save_queue (libraries/AP_Param/AP_Param.cpp)
  ObjectBuffer_TS'AP_Param_param_save.ObjectBuffer_TS (0xbf38 : UInt64) /- &AP_Param::save_queue -/ (Int32.toUInt32 ((30 : Int32)))
  -- save_dummy (libraries/AP_Param/AP_Param.cpp)
  AP_Param.AP_Param'2 (0xbb68 : UInt64) /- &save_dummy -/
  -- AP_Param::_storage (libraries/AP_Param/AP_Param.cpp)
  StorageAccess.StorageAccess (0xbb70 : UInt64) /- &AP_Param::_storage -/ (0 : UInt32)
  -- GCS_MAVLINK::param_requests (libraries/GCS_MAVLink/GCS_Param.cpp)
  ObjectBuffer'GCS_MAVLINK_pending_param_request.ObjectBuffer (0xbee8 : UInt64) /- &GCS_MAVLINK::param_requests -/ (Int32.toUInt32 ((20 : Int32)))
  -- GCS_MAVLINK::param_replies (libraries/GCS_MAVLink/GCS_Param.cpp)
  ObjectBuffer'GCS_MAVLINK_pending_param_reply.ObjectBuffer (0xbed8 : UInt64) /- &GCS_MAVLINK::param_replies -/ (Int32.toUInt32 ((5 : Int32)))
  PMem.leave fp

/-- Dynamic initialization of statics with default member initializers (3 statics). -/
def staticDynamicInit : PMem.M Unit := do
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 0 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 1 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 2 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 3 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 4 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 5 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 6 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 7 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 8 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 9 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 10 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 11 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 12 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 13 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 14 3 (UInt32.toUInt64 ((Int32.toUInt32 ((3 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 17 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 18 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 19 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 20 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stBits (0xce38 : UInt64) /- &AP_Notify::events -/ 21 1 (UInt32.toUInt64 ((Int32.toUInt32 ((1 : Int32)))))
  PMem.stU8 ((0x130d0 : UInt64) /- &GCS_MAVLINK::last_radio_status -/ + 12) (Int8.toUInt8 (Int32.toInt8 ((100 : Int32))))
  PMem.stI32 ((0xeb78 : UInt64) /- &Mode::auto_yaw -/ + 0) (1 : Int32)

end Vehicle_lib
