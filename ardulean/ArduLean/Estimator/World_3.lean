import ArduLean.Runtime.CFloat
import ArduLean.Estimator.mavlink.mavlink
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.Filter.Filter
import ArduLean.Estimator.libraries.AP_Common.AP_Common
import ArduLean.Estimator.libraries.AP_Param.AP_Param
import ArduLean.Estimator.libraries.SITL.SITL
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Estimator.libraries.AP_RTC.AP_RTC
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS
import ArduLean.Estimator.libraries.AP_InertialSensor.AP_InertialSensor
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro
import ArduLean.Estimator.libraries.AP_DAL.AP_DAL
import ArduLean.Estimator.libraries.AP_Common.AP_Common_2
import ArduLean.Estimator.libraries.AP_Compass.AP_Compass_2
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_2
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro_2

/-!
`World`: generated items without a C++ function of their own.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- The file-scope objects of the program (--world): for each, its state, its parameters, the
values it reads from the boundary (set by the caller) and what it writes to the boundary. A
reference member of one object to another is the other's field here. -/
structure World where
  /-- C++ `NavEKF3 EKF3` (AP_AHRS/AP_AHRS_NavEKF3.cpp:13), state. -/
  EKF3 : NavEKF3.State := {}
  /-- C++ `EstScheduler est_scheduler` (reference/hal/est_scheduler.cpp:4), state. -/
  est_scheduler : EstScheduler.State := {}
  /-- C++ `SITL::SIM sitl` (ardupilot/unity_estimator.cpp:78), state. -/
  sitl : SITL.SIM.State := {}
  /-- C++ `AP_Baro barometer` (ardupilot/unity_estimator.cpp:79), state. -/
  barometer : AP_Baro.State := {}
  /-- C++ `AP_Baro barometer` (ardupilot/unity_estimator.cpp:79), boundary inputs. -/
  barometer'inp : AP_Baro.Inputs := {}
  /-- C++ `Compass compass` (ardupilot/unity_estimator.cpp:80), state. -/
  compass : Compass.State := {}
  /-- C++ `Compass compass` (ardupilot/unity_estimator.cpp:80), boundary inputs. -/
  compass'inp : Compass.Inputs := {}
  /-- C++ `AP_InertialSensor ins` (ardupilot/unity_estimator.cpp:81), state. -/
  ins : AP_InertialSensor.State := {}
  /-- C++ `AP_InertialSensor ins` (ardupilot/unity_estimator.cpp:81), boundary inputs. -/
  ins'inp : AP_InertialSensor.Inputs := {}
  /-- C++ `AP_GPS gps` (ardupilot/unity_estimator.cpp:82), state. -/
  gps : AP_GPS.State := {}
  /-- C++ `AP_GPS gps` (ardupilot/unity_estimator.cpp:82), boundary inputs. -/
  gps'inp : AP_GPS.Inputs := {}
  /-- C++ `AP_RTC rtc` (ardupilot/unity_estimator.cpp:83), state. -/
  rtc : AP_RTC.State := {}
  /-- C++ `AP_RTC rtc` (ardupilot/unity_estimator.cpp:83), boundary inputs. -/
  rtc'inp : AP_RTC.Inputs := {}
  /-- C++ `EstUART est_uart` (ardupilot/unity_estimator.cpp:84), state. -/
  est_uart : EstUART.State := {}
  /-- C++ `AP_AHRS ahrs` (ardupilot/unity_estimator.cpp:87), state. -/
  ahrs : AP_AHRS.State := {}
  /-- C++ `AP_AHRS ahrs` (ardupilot/unity_estimator.cpp:87), boundary inputs. -/
  ahrs'inp : AP_AHRS.Inputs := {}
  /-- C++ `uint8_t bus_id` (AP_InertialSensor/AP_InertialSensor_SITL.h:62), static data member of `AP_InertialSensor_SITL`. -/
  AP_InertialSensor_SITL'bus_id : UInt8 := (0 : UInt8)
  /-- C++ `bool logging_started` (AP_DAL/AP_DAL.h:413), static data member of `AP_DAL`. -/
  AP_DAL'logging_started : Bool := false
  /-- C++ `bool force_write` (AP_DAL/AP_DAL.h:414), static data member of `AP_DAL`. -/
  AP_DAL'force_write : Bool := false
  /-- C++ `Matrix24 KHP` (AP_NavEKF/AP_NavEKF_core_common.h:45), static data member of `NavEKF_core_common`. -/
  NavEKF_core_common'KHP : Array Binary64 := Array.replicate 576 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- C++ `Vector28 Kfusion` (AP_NavEKF/AP_NavEKF_core_common.h:46), static data member of `NavEKF_core_common`. -/
  NavEKF_core_common'Kfusion : Array Binary64 := Array.replicate 28 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- C++ `bool created` (AP_Math/AP_Math.cpp:466), static data member of `fill_nanf`. -/
  fill_nanf'created : Bool := false
  /-- C++ `double many_nanfs[2048]` (AP_Math/AP_Math.cpp:467), static data member of `fill_nanf`. -/
  fill_nanf'many_nanfs : Array Binary64 := Array.replicate 2048 (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- C++ `uint64_t lastUnhealthyTime_us` (AP_NavEKF3/AP_NavEKF3.cpp:965), static data member of `NavEKF3::UpdateFilter`. -/
  NavEKF3_UpdateFilter'lastUnhealthyTime_us : UInt64 := (0 : UInt64)
  /-- The objects of C++ class `AP_Baro_SITL` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'AP_Baro_SITL i`). -/
  heap'AP_Baro_SITL : Array AP_Baro_SITL.State := #[]
  /-- The objects of C++ class `AP_Compass_SITL` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'AP_Compass_SITL i`). -/
  heap'AP_Compass_SITL : Array AP_Compass_SITL.State := #[]
  /-- What the objects of C++ class `AP_Compass_SITL` read from the boundary (--front-ends: one set of values for the class, set by the caller). -/
  heap'AP_Compass_SITL'inp : AP_Compass_SITL.Inputs := {}
  /-- The objects of C++ class `AP_GPS_SITL` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'AP_GPS_SITL i`). -/
  heap'AP_GPS_SITL : Array AP_GPS_SITL.State := #[]
  /-- The objects of C++ class `AP_DAL` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'AP_DAL i`). -/
  heap'AP_DAL : Array AP_DAL.State := #[]
  /-- What the objects of C++ class `AP_DAL` read from the boundary (--front-ends: one set of values for the class, set by the caller). -/
  heap'AP_DAL'inp : AP_DAL.Inputs := {}
  /-- The objects of C++ class `AP_DAL_Airspeed` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'AP_DAL_Airspeed i`). -/
  heap'AP_DAL_Airspeed : Array AP_DAL_Airspeed.State := #[]
  /-- The objects of C++ class `NavEKF3_core` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'NavEKF3_core i`). -/
  heap'NavEKF3_core : Array NavEKF3_core.State := #[]
  /-- The objects of C++ class `EKFGSF_yaw` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'EKFGSF_yaw i`). -/
  heap'EKFGSF_yaw : Array EKFGSF_yaw.State := #[]
  /-- The objects of C++ class `AP_AHRS_View` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'AP_AHRS_View i`). -/
  heap'AP_AHRS_View : Array AP_AHRS_View.State := #[]
  /-- The objects of C++ class `AP_InertialSensor_SITL` created by `new` (heap slots, in creation order; a pointer to one is `WPtr.heap'AP_InertialSensor_SITL i`). -/
  heap'AP_InertialSensor_SITL : Array AP_InertialSensor_SITL.State := #[]
  /-- What the objects of C++ class `AP_InertialSensor_SITL` read from the boundary (--front-ends: one set of values for the class, set by the caller). -/
  heap'AP_InertialSensor_SITL'inp : AP_InertialSensor_SITL.Inputs := {}
  /-- C++ `AP_DAL * _singleton` (a static pointer member of a class without a file-scope object), its value. -/
  AP_DAL'_singleton : WPtr := WPtr.null
  deriving Inhabited

/-- C++ `uint32_t millis()`, `reference/hal/est_scheduler.cpp:223`. -/
def millis (w : World) : UInt32 := Id.run do
  return UInt64.toUInt32 ((EstScheduler.clock_us w.est_scheduler / Int64.toUInt64 (Int32.toInt64 (1000 : Int32))) &&& UInt32.toUInt64 (4294967295 : UInt32))

/-- C++ `uint32_t micros()`, `reference/hal/est_scheduler.cpp:222`. -/
def micros (w : World) : UInt32 := Id.run do
  return UInt64.toUInt32 (EstScheduler.clock_us w.est_scheduler &&& UInt32.toUInt64 (4294967295 : UInt32))

/-- C++ `EstRecord est_input()`, `reference/hal/est_scheduler.cpp:227`. -/
def est_input (w : World) : EstRecord := Id.run do
  return EstScheduler.current w.est_scheduler

/-- C++ `uint64_t millis64()`, `reference/hal/est_scheduler.cpp:221`. -/
def millis64 (w : World) : UInt64 := Id.run do
  return EstScheduler.clock_us w.est_scheduler / Int64.toUInt64 (Int32.toInt64 (1000 : Int32))

/-- C++ `uint64_t micros64()`, `reference/hal/est_scheduler.cpp:220`. -/
def micros64 (w : World) : UInt64 := Id.run do
  return EstScheduler.clock_us w.est_scheduler

/-- C++ `uint64_t est_step_period_us()`, `reference/hal/est_scheduler.cpp:228`. -/
def est_step_period_us (w : World) : UInt64 := Id.run do
  return EstScheduler.step_period_us w.est_scheduler

/-- C++ `void est_event(uint8_t ev)`, `reference/hal/est_scheduler.cpp:235`. -/
def est_event (w : World) (ev : UInt8) : World := Id.run do
  let mut w := w
  let t'1 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
  w := { w with est_scheduler := default }
  w := { w with est_scheduler := EstScheduler.note_event t'1 ev }
  return w

/-- C++ `bool est_gps_pending()`, `reference/hal/est_scheduler.cpp:230`. -/
def est_gps_pending (w : World) : Bool := Id.run do
  return EstScheduler.gps_pending w.est_scheduler

/-- C++ `EstRecord est_gps_take()`, `reference/hal/est_scheduler.cpp:231`. -/
def est_gps_take (w : World) : World × EstRecord := Id.run do
  let mut w := w
  let t'1 := w.est_scheduler  -- the object out of the World for the call (--swap-out)
  w := { w with est_scheduler := default }
  let (t'2, t'3) := EstScheduler.gps_take t'1
  w := { w with est_scheduler := t'2 }
  return (w, t'3)

/-- C++ `uint32_t gps_time_week_ms(uint16_t & time_week)`, `reference/hal/sensors_gps.cpp:17-27`. -/
def gps_time_week_ms (w : World) (time_week : UInt16) : UInt16 × UInt32 := Id.run do
  let mut time_week := time_week
  let now : UInt64 := micros64 w
  let tv_sec : UInt64 := Int64.toUInt64 w.sitl.start_time_UTC + now / (1000000 : UInt64)
  let tv_usec : UInt64 := now % (1000000 : UInt64)
  let epoch : UInt32 := UInt64.toUInt32 (Int64.toUInt64 (Int32.toInt64 ((86400 : Int32) * ((10 : Int32) * (365 : Int32) + ((1980 : Int32) - (1969 : Int32)) / (4 : Int32) + (1 : Int32) + (6 : Int32) - (2 : Int32)))) - ((18000 : UInt64) / (1000 : UInt64)))
  let epoch_seconds : UInt32 := UInt64.toUInt32 (tv_sec - UInt32.toUInt64 epoch)
  time_week := UInt64.toUInt16 (UInt32.toUInt64 epoch_seconds / ((7 : UInt64) * (86400 : UInt64)))
  let t_ms : UInt32 := UInt64.toUInt32 (tv_usec / Int64.toUInt64 (Int32.toInt64 (1000 : Int32)))
  return (time_week, UInt64.toUInt32 ((UInt32.toUInt64 epoch_seconds % ((7 : UInt64) * (86400 : UInt64))) * (1000 : UInt64) + UInt32.toUInt64 ((t_ms / Int32.toUInt32 (200 : Int32)) * Int32.toUInt32 (200 : Int32))))

/-- C++ `uint16_t est_imu_rate_hz()`, `reference/hal/est_scheduler.cpp:229`. -/
def est_imu_rate_hz (w : World) : UInt16 := Id.run do
  return EstScheduler.imu_rate_hz w.est_scheduler

end Estimator_lib
