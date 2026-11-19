import ArduLean.Runtime.CFloat

/-!
ArduPilot `libraries/AP_HAL`. Sources: `libraries/AP_HAL/Device.h`, `libraries/AP_HAL/Device.cpp`, `libraries/AP_HAL/Scheduler.h`, `libraries/AP_HAL/UARTDriver.h`, `libraries/AP_HAL/system.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- C++ `bool timeout_expired(const unsigned int past_time, const unsigned int now, const unsigned long timeout)`, `AP_HAL/system.h:31-38`. -/
def timeout_expired (past_time now : UInt32) (timeout : UInt64) : Bool := Id.run do
  let dt : UInt32 := now - past_time
  return (decide (UInt32.toUInt64 dt ≥ timeout))

namespace Device

/-- C++ `enum Device::BusType`, `AP_HAL/Device.h:35-44`. -/
inductive BusType where
  | BUS_TYPE_UNKNOWN
  | BUS_TYPE_I2C
  | BUS_TYPE_SPI
  | BUS_TYPE_UAVCAN
  | BUS_TYPE_SITL
  | BUS_TYPE_MSP
  | BUS_TYPE_SERIAL
  | BUS_TYPE_WSPI
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `Device::BusType` (underlying type `uint32_t`). -/
def BusType.toInt : BusType → UInt32
  | .BUS_TYPE_UNKNOWN => (0 : UInt32)
  | .BUS_TYPE_I2C => (1 : UInt32)
  | .BUS_TYPE_SPI => (2 : UInt32)
  | .BUS_TYPE_UAVCAN => (3 : UInt32)
  | .BUS_TYPE_SITL => (4 : UInt32)
  | .BUS_TYPE_MSP => (5 : UInt32)
  | .BUS_TYPE_SERIAL => (6 : UInt32)
  | .BUS_TYPE_WSPI => (7 : UInt32)

end Device

namespace AP_HAL.Device

/-- C++ `static uint32_t AP_HAL::Device::make_bus_id(enum BusType bus_type, uint8_t bus, uint8_t address, uint8_t devtype)`, `AP_HAL/Device.cpp:222-229`. -/
def make_bus_id (bus_type : Device.BusType) (bus address devtype : UInt8) : UInt32 := Id.run do
  let mut d : UInt32 := (0 : UInt32)
  d := (d &&& ~~~((7 : UInt32) <<< 0)) ||| (((Device.BusType.toInt bus_type) &&& (7 : UInt32)) <<< 0)
  d := (d &&& ~~~((31 : UInt32) <<< 3)) ||| (((UInt8.toUInt32 bus) &&& (31 : UInt32)) <<< 3)
  d := (d &&& ~~~((255 : UInt32) <<< 8)) ||| (((UInt8.toUInt32 address) &&& (255 : UInt32)) <<< 8)
  d := (d &&& ~~~((255 : UInt32) <<< 16)) ||| (((UInt8.toUInt32 devtype) &&& (255 : UInt32)) <<< 16)
  return d

end AP_HAL.Device

namespace AP_HAL.Device

/-- C++ `static uint8_t AP_HAL::Device::devid_get_devtype(uint32_t dev_id)`, `AP_HAL/Device.cpp:270-274`. -/
def devid_get_devtype (dev_id : UInt32) : UInt8 := Id.run do
  let mut d : UInt32 := (0 : UInt32)
  d := dev_id
  return (UInt32.toUInt8 ((d >>> 16) &&& 255))

end AP_HAL.Device

namespace ExpectDelay

/-- State of C++ `ExpectDelay` (`AP_HAL/Scheduler.h:139-143`): its data members. -/
structure State where
deriving Inhabited

-- not read in the Lean: ms
set_option linter.unusedVariables false in
/-- C++ `ExpectDelay::ExpectDelay(uint32_t ms)`, `AP_HAL/Scheduler.h:141`. -/
def init (ms : UInt32) : State := Id.run do
  let mut s : State := {}
  return s

end ExpectDelay

namespace EstUART

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_HAL::UARTDriver::set_flow_control(enum flow_control flow_control_setting)`, `AP_HAL/UARTDriver.h:116` (a member of `AP_HAL::UARTDriver`, translated for `EstUART`).
-/

end EstUART

end Estimator_lib
