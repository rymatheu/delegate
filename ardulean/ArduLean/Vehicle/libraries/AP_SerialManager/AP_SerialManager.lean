import ArduLean.Runtime.Bridge
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL
import ArduLean.Vehicle.libraries.AP_Param.AP_Param
import ArduLean.Vehicle.libraries.AP_HAL.AP_HAL_2
import ArduLean.Vehicle.libraries.AP_Param.AP_Param_2

/-!
ArduPilot `libraries/AP_SerialManager`. Sources: `libraries/AP_SerialManager/AP_SerialManager.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `AP_SerialManager::get_singleton : AP_SerialManager *()`, `AP_Common.h:159-161`. -/
def AP_SerialManager.get_singleton  : PMem.M UInt64 := do
  let t'1 ← PMem.ldU64 (0xed60 : UInt64) /- &AP_SerialManager::_singleton -/
  return t'1

/-- C++ `AP::serialmanager : AP_SerialManager &()`, `AP_SerialManager.cpp:968-971`. -/
def AP.serialmanager  : PMem.M UInt64 := do
  let t'1 ← AP_SerialManager.get_singleton
  return t'1

/-- C++ `AP_SerialManager::have_serial : bool (enum SerialProtocol, uint8_t) const`, `AP_SerialManager.cpp:663-666`. -/
def AP_SerialManager.have_serial (this : UInt64) (protocol : Int32) (instance' : UInt8) : PMem.M Bool := do
  let mut protocol := protocol
  let mut instance' := instance'
  let t'1 ← PMem.findSerialProto protocol instance'
  return (t'1 != (0 : UInt64))

/-- C++ `AP_SerialManager::pre_arm_checks : bool (char *, const uint8_t)`, `AP_SerialManager.cpp:844-863`. -/
def AP_SerialManager.pre_arm_checks.body (fp : UInt64) (this : UInt64) (failure_msg : UInt64) (failure_msg_len : UInt8) : PMem.M Bool := do
  let mut failure_msg := failure_msg
  let mut failure_msg_len := failure_msg_len
  let mut i : UInt8 := Int8.toUInt8 (Int32.toInt8 ((0 : Int32)))
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := i
      let t'3 := (t'2 + 1)
      i := t'3
      pure ()
    first'1 := false
    if !((decide ((UInt8.toUInt64 (i)) < ((120 : UInt64) / (12 : UInt64))))) then break
    let _state : UInt64 := ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
    let t'4 ← AP_ParamT'int_3.operator_const_int__ (_state + 4)
    let t'5 ← PMem.ldI32 t'4
    if (t'5 &&& (1024 : Int32)) != (0 : Int32) then
      PMem.stU64 (fp + 0) (UInt32.toUInt64 ((UInt8.toUInt32 (i))))
      let t'6 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x18447 : UInt64) /- "SERIAL%u_OPTIONS bit 10 ('no forward mavlink') must not be set; use MAVn_OPTIONS bit 1 instead" -/ (fp + 0)
      discard <| pure (t'6)
      return false
    let t'7 ← AP_ParamT'int_3.operator_const_int__ (_state + 4)
    let t'8 ← PMem.ldI32 t'7
    if (t'8 &&& (4096 : Int32)) != (0 : Int32) then
      PMem.stU64 (fp + 8) (UInt32.toUInt64 ((UInt8.toUInt32 (i))))
      let t'9 ← AP_HAL.Util.snprintf (0 : UInt64) failure_msg (UInt8.toUInt64 (failure_msg_len)) (0x184a6 : UInt64) /- "SERIAL%u_OPTIONS bit 12 ('no stream overrides') must not be set; use MAVn_OPTIONS bit 2 instead" -/ (fp + 8)
      discard <| pure (t'9)
      return false
  return true

def AP_SerialManager.pre_arm_checks (this : UInt64) (failure_msg : UInt64) (failure_msg_len : UInt8) : PMem.M Bool := do
  let fp ← PMem.enter 16
  let r ← AP_SerialManager.pre_arm_checks.body fp this failure_msg failure_msg_len
  PMem.leave fp
  return r

/-- `AP_SerialManager.map_baudrate` as a pure function of its arguments (it reads and writes no memory). -/
def AP_SerialManager.map_baudrate.pure' (rate : Int32) : Id UInt32 := do
  let mut rate := rate
  if (decide (rate ≤ (0 : Int32))) then
    rate := (57 : Int32)
  let sw'1 := rate
  if sw'1 == (1 : Int32) then
    return Int32.toUInt32 ((1200 : Int32))
  else if sw'1 == (2 : Int32) then
    return Int32.toUInt32 ((2400 : Int32))
  else if sw'1 == (4 : Int32) then
    return Int32.toUInt32 ((4800 : Int32))
  else if sw'1 == (9 : Int32) then
    return Int32.toUInt32 ((9600 : Int32))
  else if sw'1 == (19 : Int32) then
    return Int32.toUInt32 ((19200 : Int32))
  else if sw'1 == (38 : Int32) then
    return Int32.toUInt32 ((38400 : Int32))
  else if sw'1 == (57 : Int32) then
    return Int32.toUInt32 ((57600 : Int32))
  else if sw'1 == (100 : Int32) then
    return Int32.toUInt32 ((100000 : Int32))
  else if sw'1 == (111 : Int32) then
    return Int32.toUInt32 ((111100 : Int32))
  else if sw'1 == (115 : Int32) then
    return Int32.toUInt32 ((115200 : Int32))
  else if sw'1 == (230 : Int32) then
    return Int32.toUInt32 ((230400 : Int32))
  else if sw'1 == (256 : Int32) then
    return Int32.toUInt32 ((256000 : Int32))
  else if sw'1 == (460 : Int32) then
    return Int32.toUInt32 ((460800 : Int32))
  else if sw'1 == (500 : Int32) then
    return Int32.toUInt32 ((500000 : Int32))
  else if sw'1 == (921 : Int32) then
    return Int32.toUInt32 ((921600 : Int32))
  else if sw'1 == (1500 : Int32) then
    return Int32.toUInt32 ((1500000 : Int32))
  else if sw'1 == (2000 : Int32) then
    return Int32.toUInt32 ((2000000 : Int32))
  else
    pure ()
  if (decide (rate > (2000 : Int32))) then
    return Int32.toUInt32 (rate)
  return Int32.toUInt32 ((rate * (1000 : Int32)))

/-- C++ `AP_SerialManager::map_baudrate : uint32_t (int32_t)`, `AP_SerialManager.cpp:738-771`. -/
def AP_SerialManager.map_baudrate (rate : Int32) : PMem.M UInt32 :=
  pure (_root_.Vehicle_lib.AP_SerialManager.map_baudrate.pure' rate)

/-- C++ `AP_SerialManager::UARTState::baudrate : uint32_t () const`, `AP_Common.h:216-218`. -/
def AP_SerialManager.UARTState.baudrate (this : UInt64) : PMem.M UInt32 := do
  let t'1 ← AP_ParamT'int_3.operator_const_int__ this
  let t'2 ← PMem.ldI32 t'1
  let t'3 ← AP_SerialManager.map_baudrate t'2
  return t'3

/-- C++ `AP_SerialManager::init_console : void ()`, `AP_SerialManager.cpp:413-424`. -/
def AP_SerialManager.init_console (this : UInt64) : PMem.M Unit := do
  let t'1 ← PMem.ldB (this + 139)
  if !t'1 then
    PMem.stB (this + 139) true
    let t'2 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((Int8.toUInt8 (Int32.toInt8 ((0 : Int32))))))]
    (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" t'2 #[((Int32.toUInt32 ((115200 : Int32)))).toUInt64])
  return ()

/-- C++ `AP_SerialManager::convert_parameters : void ()`, `AP_SerialManager.cpp:593-599`. -/
def AP_SerialManager.convert_parameters (this : UInt64) : PMem.M Unit := do
  let __range1 : UInt64 := (this + 16)
  let mut __begin1 : UInt64 := __range1
  let mut __end1 : UInt64 := (__range1 + ((10 : Int64) * 12).toUInt64)
  let mut first'1 := true
  for _ in PMem.loopFuel do
    if !first'1 then
      let t'2 := (__begin1 + 12)
      __begin1 := t'2
      pure ()
    first'1 := false
    if !((__begin1 != __end1)) then break
    let _state : UInt64 := __begin1
    let t'3 ← AP_Param.convert_parameter_width (_state + 4) (2 : UInt32) (Binary64.toBinary32 ((Binary64.ofBits 0x3ff0000000000000 /- 1 -/)))
    discard <| pure (t'3)
  return ()

/-- C++ `AP_SerialManager::set_options : void (uint16_t)`, `AP_SerialManager.cpp:797-804`. -/
def AP_SerialManager.set_options (this : UInt64) (i : UInt16) : PMem.M Unit := do
  let mut i := i
  let opt : UInt64 := ((this + 16) + ((UInt64.toInt64 (UInt16.toUInt64 (i))) * 12).toUInt64)
  let t'1 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 ((UInt16.toUInt8 (i))))]
  let t'2 ← AP_ParamT'int_3.operator_const_int__ (opt + 4)
  let t'3 ← PMem.ldI32 t'2
  let t'4 ← PMem.halDev "AP_HAL::UARTDriver::set_options" t'1 #[(UInt16.toUInt64 ((Int16.toUInt16 (Int32.toInt16 (t'3)))))]
  if !(t'4 != 0) then
    for _ in [0:1] do
      let t'5 ← PMem.ldU64 ((0xba88 : UInt64) /- &hal -/ + 48)
      discard <| PMem.halDev "AP_HAL::BetterStream::printf" t'5 #[(0x18421 : UInt64) /- "Unable to setup options for Serial%u\n" -/, (Int64.toUInt64 (Int32.toInt64 ((UInt32.toInt32 (UInt16.toUInt32 (i))))))]
  return ()

/-- C++ `AP_SerialManager::init : void ()`, `AP_SerialManager.cpp:427-591`. -/
def AP_SerialManager.init.body (fp : UInt64) (this : UInt64) : PMem.M Unit := do
  AP_SerialManager.convert_parameters this
  let t'1 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (this + 138)
  let t'2 ← PMem.ldI8 t'1
  if ((Int8.toInt32 (t'2)) != (-(1 : Int32))) then
    PMem.stI8 (fp + 0) (Int32.toInt8 ((-(1 : Int32))))
    AP_ParamTBase'signed_char_1.set_and_save_ifchanged (this + 137) (fp + 0)
  AP_SerialManager.init_console this
  for i'3 in [1:8] do
    let i : UInt8 := UInt8.ofNat i'3
    let t'4 ← PMem.halDev "AP_HAL::HAL::serial" (0xba88 : UInt64) /- &hal -/ #[(UInt8.toUInt64 (i))]
    let mut uart : UInt64 := t'4
    PMem.stU8 (((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) + 9) i
    if (uart != (0 : UInt64)) then
      AP_SerialManager.set_options this (UInt8.toUInt16 (i))
      let t'5 ← AP_ParamT'signed_char_1.operator_const_signed_char__ (((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) + 8)
      let t'6 ← PMem.ldI8 t'5
      let sw'7 := Int8.toInt32 (t'6)
      if sw'7 == (-1 : Int32) then
        discard <| PMem.halDev "AP_HAL::UARTDriver::disable_rxtx" uart #[]
      else if sw'7 == (0 : Int32) || sw'7 == (1 : Int32) || sw'7 == (2 : Int32) || sw'7 == (43 : Int32) then
        let t'8 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'8).toUInt64])
      else if sw'7 == (3 : Int32) then
        PMem.stI32 (fp + 4) ((9600 : Int32) / (1000 : Int32))
        AP_ParamTBase'int_3.set_and_default ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) (fp + 4)
      else if sw'7 == (4 : Int32) || sw'7 == (10 : Int32) then
        PMem.stI32 (fp + 8) ((57600 : Int32) / (1000 : Int32))
        AP_ParamTBase'int_3.set_and_default ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) (fp + 8)
      else if sw'7 == (5 : Int32) || sw'7 == (6 : Int32) then
        let t'9 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'9).toUInt64])
      else if sw'7 == (7 : Int32) then
        PMem.stI32 (fp + 12) ((115200 : Int32) / (1000 : Int32))
        AP_ParamTBase'int_3.set_and_default ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) (fp + 12)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[((Int32.toUInt32 ((115200 : Int32)))).toUInt64])
      else if sw'7 == (8 : Int32) then
        PMem.stI32 (fp + 16) ((115200 : Int32) / (1000 : Int32))
        AP_ParamTBase'int_3.set_and_default ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) (fp + 16)
        let t'10 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'10).toUInt64])
      else if sw'7 == (12 : Int32) then
        PMem.stI8 (fp + 20) (Int32.toInt8 ((9 : Int32)))
        AP_ParamTBase'signed_char_1.set_and_save (((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) + 8) (fp + 20)
      else if sw'7 == (15 : Int32) then
        pure ()
      else if sw'7 == (16 : Int32) then
        PMem.stI32 (fp + 24) ((115200 : Int32) / (1000 : Int32))
        AP_ParamTBase'int_3.set_and_default ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) (fp + 24)
        let t'11 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'11).toUInt64])
      else if sw'7 == (19 : Int32) then
        let t'12 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'12).toUInt64])
        let t'13 ← PMem.halDev "AP_HAL::UARTDriver::set_unbuffered_writes" uart #[(if true then (1 : UInt64) else 0)]
        discard <| pure ((t'13 != 0))
      else if sw'7 == (22 : Int32) then
        let t'14 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'14).toUInt64])
      else if sw'7 == (24 : Int32) then
        PMem.stI32 (fp + 28) (115 : Int32)
        AP_ParamTBase'int_3.set_default ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64) (fp + 28)
        let t'15 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'15).toUInt64])
      else if sw'7 == (30 : Int32) then
        pure ()
      else if sw'7 == (46 : Int32) then
        let t'16 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'16).toUInt64])
        let t'17 ← VehicleBridge.ins'0
        VehicleBridge.AP_InertialSensor.set_imu_out_uart'1 t'17 uart
        let t'18 ← PMem.halDev "AP_HAL::UARTDriver::set_unbuffered_writes" uart #[(if true then (1 : UInt64) else 0)]
        discard <| pure ((t'18 != 0))
      else if sw'7 == (50 : Int32) then
        pure ()
      else
        let t'19 ← AP_SerialManager.UARTState.baudrate ((this + 16) + ((UInt64.toInt64 (UInt8.toUInt64 (i))) * 12).toUInt64)
        (discard <| PMem.halDev "AP_HAL::UARTDriver::begin" uart #[(t'19).toUInt64])
  return ()

def AP_SerialManager.init (this : UInt64) : PMem.M Unit := do
  let fp ← PMem.enter 32
  let r ← AP_SerialManager.init.body fp this
  PMem.leave fp
  return r

/-- C++ `AP_SerialManager::AP_SerialManager : void ()`, `AP_SerialManager.cpp:405-410`. -/
def AP_SerialManager.AP_SerialManager (this : UInt64) : PMem.M Unit := do
  HALSITL.Semaphore.Semaphore (this + 8)
  AP_Param.AP_Param'2 ((this + 16) + 0)
  AP_Param.AP_Param'2 (((this + 16) + 0) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 0) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 12)
  AP_Param.AP_Param'2 (((this + 16) + 12) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 12) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 24)
  AP_Param.AP_Param'2 (((this + 16) + 24) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 24) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 36)
  AP_Param.AP_Param'2 (((this + 16) + 36) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 36) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 48)
  AP_Param.AP_Param'2 (((this + 16) + 48) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 48) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 60)
  AP_Param.AP_Param'2 (((this + 16) + 60) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 60) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 72)
  AP_Param.AP_Param'2 (((this + 16) + 72) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 72) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 84)
  AP_Param.AP_Param'2 (((this + 16) + 84) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 84) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 96)
  AP_Param.AP_Param'2 (((this + 16) + 96) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 96) + 8)
  AP_Param.AP_Param'2 ((this + 16) + 108)
  AP_Param.AP_Param'2 (((this + 16) + 108) + 4)
  AP_Param.AP_Param'2 (((this + 16) + 108) + 8)
  AP_Param.AP_Param'2 (this + 136)
  AP_Param.AP_Param'2 (this + 137)
  AP_Param.AP_Param'2 (this + 138)
  PMem.stU64 (0xed60 : UInt64) /- &AP_SerialManager::_singleton -/ this
  AP_Param.setup_object_defaults this (0x78c8 : UInt64) /- &AP_SerialManager::var_info -/
  return ()

end Vehicle_lib
