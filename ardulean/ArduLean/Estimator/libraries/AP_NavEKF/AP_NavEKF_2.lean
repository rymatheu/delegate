import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math
import ArduLean.Estimator.libraries.AP_NavEKF.AP_NavEKF
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3
import ArduLean.Estimator.libraries.AP_Param.AP_Param_2

/-!
ArduPilot `libraries/AP_NavEKF`, part 2 of 3. Sources: `libraries/AP_NavEKF/EKF_Buffer.cpp`, `libraries/AP_NavEKF/EKF_Buffer.h`, `libraries/AP_NavEKF/AP_NavEKF_Source.cpp`, `libraries/AP_NavEKF/AP_NavEKF_Source.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace EKF_obs_buffer_t_NavEKF3_core_gps_elements

/-- State of C++ `EKF_obs_buffer_t<NavEKF3_core::gps_elements>` (`AP_NavEKF/EKF_Buffer.h:62-89`): its data members; base classes flattened, base first: `ekf_ring_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:43`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:44`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::gps_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.gps_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t size` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:47`). -/
  size : UInt8 := (0 : UInt8)
  /-- `uint8_t oldest` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:50`). -/
  oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:53`). -/
  count : UInt8 := (0 : UInt8)
deriving Inhabited

end EKF_obs_buffer_t_NavEKF3_core_gps_elements

namespace EKF_obs_buffer_t_NavEKF3_core_mag_elements

/-- State of C++ `EKF_obs_buffer_t<NavEKF3_core::mag_elements>` (`AP_NavEKF/EKF_Buffer.h:62-89`): its data members; base classes flattened, base first: `ekf_ring_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:43`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:44`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::mag_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.mag_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t size` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:47`). -/
  size : UInt8 := (0 : UInt8)
  /-- `uint8_t oldest` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:50`). -/
  oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:53`). -/
  count : UInt8 := (0 : UInt8)
deriving Inhabited

end EKF_obs_buffer_t_NavEKF3_core_mag_elements

namespace EKF_obs_buffer_t_NavEKF3_core_baro_elements

/-- State of C++ `EKF_obs_buffer_t<NavEKF3_core::baro_elements>` (`AP_NavEKF/EKF_Buffer.h:62-89`): its data members; base classes flattened, base first: `ekf_ring_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:43`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:44`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::baro_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.baro_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t size` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:47`). -/
  size : UInt8 := (0 : UInt8)
  /-- `uint8_t oldest` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:50`). -/
  oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:53`). -/
  count : UInt8 := (0 : UInt8)
deriving Inhabited

end EKF_obs_buffer_t_NavEKF3_core_baro_elements

namespace EKF_obs_buffer_t_NavEKF3_core_of_elements

/-- State of C++ `EKF_obs_buffer_t<NavEKF3_core::of_elements>` (`AP_NavEKF/EKF_Buffer.h:62-89`): its data members; base classes flattened, base first: `ekf_ring_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:43`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:44`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::of_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.of_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t size` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:47`). -/
  size : UInt8 := (0 : UInt8)
  /-- `uint8_t oldest` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:50`). -/
  oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:53`). -/
  count : UInt8 := (0 : UInt8)
deriving Inhabited

end EKF_obs_buffer_t_NavEKF3_core_of_elements

namespace EKF_obs_buffer_t_NavEKF3_core_gps_elements

/-- C++ `ekf_ring_buffer::ekf_ring_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:12-15` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::gps_elements>`). -/
def ekf_ring_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  s := { s with buffer := #[] }
  s := { s with buffer'alloc := false }
  return s

/-- C++ `EKF_obs_buffer_t<NavEKF3_core::gps_elements>::EKF_obs_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:70-72`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_ring_buffer.construct s (UInt64.toUInt8 (56 : UInt64))
  return s

end EKF_obs_buffer_t_NavEKF3_core_gps_elements

namespace EKF_obs_buffer_t_NavEKF3_core_mag_elements

/-- C++ `ekf_ring_buffer::ekf_ring_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:12-15` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::mag_elements>`). -/
def ekf_ring_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  s := { s with buffer := #[] }
  s := { s with buffer'alloc := false }
  return s

/-- C++ `EKF_obs_buffer_t<NavEKF3_core::mag_elements>::EKF_obs_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:70-72`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_ring_buffer.construct s (UInt64.toUInt8 (32 : UInt64))
  return s

end EKF_obs_buffer_t_NavEKF3_core_mag_elements

namespace EKF_obs_buffer_t_NavEKF3_core_baro_elements

/-- C++ `ekf_ring_buffer::ekf_ring_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:12-15` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::baro_elements>`). -/
def ekf_ring_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  s := { s with buffer := #[] }
  s := { s with buffer'alloc := false }
  return s

/-- C++ `EKF_obs_buffer_t<NavEKF3_core::baro_elements>::EKF_obs_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:70-72`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_ring_buffer.construct s (UInt64.toUInt8 (16 : UInt64))
  return s

end EKF_obs_buffer_t_NavEKF3_core_baro_elements

namespace EKF_obs_buffer_t_NavEKF3_core_of_elements

/-- C++ `ekf_ring_buffer::ekf_ring_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:12-15` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::of_elements>`). -/
def ekf_ring_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  s := { s with buffer := #[] }
  s := { s with buffer'alloc := false }
  return s

/-- C++ `EKF_obs_buffer_t<NavEKF3_core::of_elements>::EKF_obs_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:70-72`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_ring_buffer.construct s (UInt64.toUInt8 (96 : UInt64))
  return s

end EKF_obs_buffer_t_NavEKF3_core_of_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_imu_elements

/-- State of C++ `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>` (`AP_NavEKF/EKF_Buffer.h:148-205`): its data members; base classes flattened, base first: `ekf_imu_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:137`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:138`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::imu_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.imu_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t _size` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:139`). -/
  _size : UInt8 := (0 : UInt8)
  /-- `uint8_t _oldest` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:139`). -/
  _oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t _youngest` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:139`). -/
  _youngest : UInt8 := (0 : UInt8)
  /-- `bool _filled` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:140`). -/
  _filled : Bool := false
deriving Inhabited

end EKF_IMU_buffer_t_NavEKF3_core_imu_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_output_elements

/-- State of C++ `EKF_IMU_buffer_t<NavEKF3_core::output_elements>` (`AP_NavEKF/EKF_Buffer.h:148-205`): its data members; base classes flattened, base first: `ekf_imu_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:137`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:138`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::output_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.output_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t _size` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:139`). -/
  _size : UInt8 := (0 : UInt8)
  /-- `uint8_t _oldest` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:139`). -/
  _oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t _youngest` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:139`). -/
  _youngest : UInt8 := (0 : UInt8)
  /-- `bool _filled` of `ekf_imu_buffer` (`AP_NavEKF/EKF_Buffer.h:140`). -/
  _filled : Bool := false
deriving Inhabited

end EKF_IMU_buffer_t_NavEKF3_core_output_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_imu_elements

/-- C++ `ekf_imu_buffer::ekf_imu_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:120-122` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>`). -/
def ekf_imu_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  return s

/-- C++ `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>::EKF_IMU_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:152-154`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_imu_buffer.construct s (UInt64.toUInt8 (72 : UInt64))
  return s

end EKF_IMU_buffer_t_NavEKF3_core_imu_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_output_elements

/-- C++ `ekf_imu_buffer::ekf_imu_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:120-122` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::output_elements>`). -/
def ekf_imu_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  return s

/-- C++ `EKF_IMU_buffer_t<NavEKF3_core::output_elements>::EKF_IMU_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:152-154`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_imu_buffer.construct s (UInt64.toUInt8 (80 : UInt64))
  return s

end EKF_IMU_buffer_t_NavEKF3_core_output_elements

namespace EKF_obs_buffer_t_NavEKF3_core_tas_elements

/-- State of C++ `EKF_obs_buffer_t<NavEKF3_core::tas_elements>` (`AP_NavEKF/EKF_Buffer.h:62-89`): its data members; base classes flattened, base first: `ekf_ring_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:43`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:44`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::tas_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.tas_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t size` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:47`). -/
  size : UInt8 := (0 : UInt8)
  /-- `uint8_t oldest` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:50`). -/
  oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:53`). -/
  count : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `ekf_ring_buffer::ekf_ring_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:12-15` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::tas_elements>`). -/
def ekf_ring_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  s := { s with buffer := #[] }
  s := { s with buffer'alloc := false }
  return s

/-- C++ `EKF_obs_buffer_t<NavEKF3_core::tas_elements>::EKF_obs_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:70-72`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_ring_buffer.construct s (UInt64.toUInt8 (32 : UInt64))
  return s

end EKF_obs_buffer_t_NavEKF3_core_tas_elements

namespace EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

/-- State of C++ `EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>` (`AP_NavEKF/EKF_Buffer.h:62-89`): its data members; base classes flattened, base first: `ekf_ring_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:43`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:44`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::vel_odm_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.vel_odm_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t size` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:47`). -/
  size : UInt8 := (0 : UInt8)
  /-- `uint8_t oldest` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:50`). -/
  oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:53`). -/
  count : UInt8 := (0 : UInt8)
deriving Inhabited

end EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

/-- State of C++ `EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>` (`AP_NavEKF/EKF_Buffer.h:62-89`): its data members; base classes flattened, base first: `ekf_ring_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:43`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:44`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::wheel_odm_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.wheel_odm_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t size` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:47`). -/
  size : UInt8 := (0 : UInt8)
  /-- `uint8_t oldest` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:50`). -/
  oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:53`). -/
  count : UInt8 := (0 : UInt8)
deriving Inhabited

end EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

/-- C++ `ekf_ring_buffer::ekf_ring_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:12-15` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>`). -/
def ekf_ring_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  s := { s with buffer := #[] }
  s := { s with buffer'alloc := false }
  return s

/-- C++ `EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>::EKF_obs_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:70-72`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_ring_buffer.construct s (UInt64.toUInt8 (88 : UInt64))
  return s

end EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

/-- C++ `ekf_ring_buffer::ekf_ring_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:12-15` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>`). -/
def ekf_ring_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  s := { s with buffer := #[] }
  s := { s with buffer'alloc := false }
  return s

/-- C++ `EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>::EKF_obs_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:70-72`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_ring_buffer.construct s (UInt64.toUInt8 (56 : UInt64))
  return s

end EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_yaw_elements

/-- State of C++ `EKF_obs_buffer_t<NavEKF3_core::yaw_elements>` (`AP_NavEKF/EKF_Buffer.h:62-89`): its data members; base classes flattened, base first: `ekf_ring_buffer`. -/
structure State where
  /-- `const uint8_t elsize` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:43`). -/
  elsize : UInt8 := (0 : UInt8)
  /-- `void * buffer` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:44`): the elements (`calloc(size, elsize)`), as `NavEKF3_core::yaw_elements` (--ring-buffers). -/
  buffer : Array NavEKF3_core.yaw_elements := #[]
  /-- `buffer != nullptr` (--ring-buffers): the elements are allocated. -/
  buffer'alloc : Bool := false
  /-- `uint8_t size` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:47`). -/
  size : UInt8 := (0 : UInt8)
  /-- `uint8_t oldest` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:50`). -/
  oldest : UInt8 := (0 : UInt8)
  /-- `uint8_t count` of `ekf_ring_buffer` (`AP_NavEKF/EKF_Buffer.h:53`). -/
  count : UInt8 := (0 : UInt8)
deriving Inhabited

/-- C++ `ekf_ring_buffer::ekf_ring_buffer(uint8_t elsize)`, `AP_NavEKF/EKF_Buffer.cpp:12-15` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::yaw_elements>`). -/
def ekf_ring_buffer.construct (s : State) (_elsize : UInt8) : State := Id.run do
  let mut s := s
  s := { s with elsize := _elsize }
  s := { s with buffer := #[] }
  s := { s with buffer'alloc := false }
  return s

/-- C++ `EKF_obs_buffer_t<NavEKF3_core::yaw_elements>::EKF_obs_buffer_t()`, `AP_NavEKF/EKF_Buffer.h:70-72`. -/
def construct : State := Id.run do
  let mut s : State := {}
  s := ekf_ring_buffer.construct s (UInt64.toUInt8 (32 : UInt64))
  return s

end EKF_obs_buffer_t_NavEKF3_core_yaw_elements

namespace EKF_obs_buffer_t_NavEKF3_core_baro_elements

/-- C++ `void ekf_ring_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:107-111` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::baro_elements>`). -/
def ekf_ring_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::baro_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:86-88`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_ring_buffer.reset s
  return s

end EKF_obs_buffer_t_NavEKF3_core_baro_elements

namespace AP_NavEKF_Source

/-- C++ `SourceXY AP_NavEKF_Source::getPosXYSource(uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.h:79`. -/
def getPosXYSource (s : State) (core_index : UInt8) : AP_NavEKF_Source.SourceXY := Id.run do
  return AP_Enum_AP_NavEKF_Source_SourceXY.op_to_AP_NavEKF_Source_SourceXY s._source_set[UInt8.toNat (getActiveSourceSet s core_index)]!.posxy

end AP_NavEKF_Source

namespace AP_NavEKF_Source

/-- C++ `SourceZ AP_NavEKF_Source::getPosZSource(uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.cpp:239-248`. -/
def getPosZSource (s : State) (core_index : UInt8) : AP_NavEKF_Source.SourceZ := Id.run do
  return AP_Enum_AP_NavEKF_Source_SourceZ.op_to_AP_NavEKF_Source_SourceZ s._source_set[UInt8.toNat (getActiveSourceSet s core_index)]!.posz

/-- C++ `SourceXY AP_NavEKF_Source::getVelXYSource(uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.h:87`. -/
def getVelXYSource (s : State) (core_index : UInt8) : AP_NavEKF_Source.SourceXY := Id.run do
  return AP_Enum_AP_NavEKF_Source_SourceXY.op_to_AP_NavEKF_Source_SourceXY s._source_set[UInt8.toNat (getActiveSourceSet s core_index)]!.velxy

/-- C++ `SourceZ AP_NavEKF_Source::getVelZSource(uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.h:88`. -/
def getVelZSource (s : State) (core_index : UInt8) : AP_NavEKF_Source.SourceZ := Id.run do
  return AP_Enum_AP_NavEKF_Source_SourceZ.op_to_AP_NavEKF_Source_SourceZ s._source_set[UInt8.toNat (getActiveSourceSet s core_index)]!.velz

end AP_NavEKF_Source

namespace EKF_obs_buffer_t_NavEKF3_core_gps_elements

/-- C++ `void ekf_ring_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:107-111` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::gps_elements>`). -/
def ekf_ring_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `bool ekf_ring_buffer::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.cpp:17-29` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::gps_elements>`). -/
def ekf_ring_buffer.init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt8.toUInt64 _size)) { time_ms := (0 : UInt32), lat := (0 : Int32), lng := (0 : Int32), hgt := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), vel := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, sensor_idx := (0 : UInt8), corrected := false, have_vz := false } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with size := _size }
  s := ekf_ring_buffer.reset s
  return (s, true)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::gps_elements>::init(uint8_t _size)`, `AP_NavEKF/EKF_Buffer.h:74-76`. -/
def init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := ekf_ring_buffer.init s _size
  s := t'1
  return (s, t'2)

end EKF_obs_buffer_t_NavEKF3_core_gps_elements

namespace EKF_obs_buffer_t_NavEKF3_core_mag_elements

/-- C++ `void ekf_ring_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:107-111` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::mag_elements>`). -/
def ekf_ring_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `bool ekf_ring_buffer::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.cpp:17-29` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::mag_elements>`). -/
def ekf_ring_buffer.init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt8.toUInt64 _size)) { time_ms := (0 : UInt32), mag := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with size := _size }
  s := ekf_ring_buffer.reset s
  return (s, true)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::mag_elements>::init(uint8_t _size)`, `AP_NavEKF/EKF_Buffer.h:74-76`. -/
def init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := ekf_ring_buffer.init s _size
  s := t'1
  return (s, t'2)

end EKF_obs_buffer_t_NavEKF3_core_mag_elements

namespace EKF_obs_buffer_t_NavEKF3_core_tas_elements

/-- C++ `void ekf_ring_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:107-111` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::tas_elements>`). -/
def ekf_ring_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `bool ekf_ring_buffer::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.cpp:17-29` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::tas_elements>`). -/
def ekf_ring_buffer.init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt8.toUInt64 _size)) { time_ms := (0 : UInt32), tas := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), tasVariance := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), allowFusion := false } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with size := _size }
  s := ekf_ring_buffer.reset s
  return (s, true)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::tas_elements>::init(uint8_t _size)`, `AP_NavEKF/EKF_Buffer.h:74-76`. -/
def init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := ekf_ring_buffer.init s _size
  s := t'1
  return (s, t'2)

end EKF_obs_buffer_t_NavEKF3_core_tas_elements

namespace EKF_obs_buffer_t_NavEKF3_core_of_elements

/-- C++ `void ekf_ring_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:107-111` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::of_elements>`). -/
def ekf_ring_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `bool ekf_ring_buffer::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.cpp:17-29` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::of_elements>`). -/
def ekf_ring_buffer.init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt8.toUInt64 _size)) { time_ms := (0 : UInt32), flowRadXY := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, flowRadXYcomp := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, bodyRadXYZ := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, body_offset := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, heightOverride := (Binary32.ofBits 0x00000000 /- 0.0 -/) } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with size := _size }
  s := ekf_ring_buffer.reset s
  return (s, true)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::of_elements>::init(uint8_t _size)`, `AP_NavEKF/EKF_Buffer.h:74-76`. -/
def init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := ekf_ring_buffer.init s _size
  s := t'1
  return (s, t'2)

end EKF_obs_buffer_t_NavEKF3_core_of_elements

namespace EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

/-- C++ `void ekf_ring_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:107-111` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>`). -/
def ekf_ring_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `bool ekf_ring_buffer::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.cpp:17-29` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>`). -/
def ekf_ring_buffer.init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt8.toUInt64 _size)) { time_ms := (0 : UInt32), vel := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, velErr := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), body_offset := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, angRate := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with size := _size }
  s := ekf_ring_buffer.reset s
  return (s, true)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>::init(uint8_t _size)`, `AP_NavEKF/EKF_Buffer.h:74-76`. -/
def init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := ekf_ring_buffer.init s _size
  s := t'1
  return (s, t'2)

end EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

/-- C++ `void ekf_ring_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:107-111` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>`). -/
def ekf_ring_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `bool ekf_ring_buffer::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.cpp:17-29` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>`). -/
def ekf_ring_buffer.init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt8.toUInt64 _size)) { time_ms := (0 : UInt32), delAng := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), radius := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), hub_offset := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, delTime := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with size := _size }
  s := ekf_ring_buffer.reset s
  return (s, true)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>::init(uint8_t _size)`, `AP_NavEKF/EKF_Buffer.h:74-76`. -/
def init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := ekf_ring_buffer.init s _size
  s := t'1
  return (s, t'2)

end EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_yaw_elements

/-- C++ `void ekf_ring_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:107-111` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::yaw_elements>`). -/
def ekf_ring_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with count := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  return s

/-- C++ `bool ekf_ring_buffer::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.cpp:17-29` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::yaw_elements>`). -/
def ekf_ring_buffer.init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt8.toUInt64 _size)) { time_ms := (0 : UInt32), yawAng := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), yawAngErr := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), order := NavEKF3_core.rotationOrder.TAIT_BRYAN_321 } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with size := _size }
  s := ekf_ring_buffer.reset s
  return (s, true)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::yaw_elements>::init(uint8_t _size)`, `AP_NavEKF/EKF_Buffer.h:74-76`. -/
def init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := ekf_ring_buffer.init s _size
  s := t'1
  return (s, t'2)

end EKF_obs_buffer_t_NavEKF3_core_yaw_elements

namespace EKF_obs_buffer_t_NavEKF3_core_baro_elements

/-- C++ `bool ekf_ring_buffer::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.cpp:17-29` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::baro_elements>`). -/
def ekf_ring_buffer.init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt8.toUInt64 _size)) { time_ms := (0 : UInt32), hgt := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with size := _size }
  s := ekf_ring_buffer.reset s
  return (s, true)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::baro_elements>::init(uint8_t _size)`, `AP_NavEKF/EKF_Buffer.h:74-76`. -/
def init (s : State) (_size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := ekf_ring_buffer.init s _size
  s := t'1
  return (s, t'2)

end EKF_obs_buffer_t_NavEKF3_core_baro_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_imu_elements

/-- C++ `bool ekf_imu_buffer::init(uint32_t size)`, `AP_NavEKF/EKF_Buffer.cpp:133-148` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>`). -/
def init_uint32_t (s : State) (size : UInt32) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt32.toUInt64 size)) { delAng := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, delVel := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, delAngDT := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), delVelDT := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), time_ms := (0 : UInt32), gyro_index := (0 : UInt8), accel_index := (0 : UInt8) } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with _size := UInt32.toUInt8 size }
  s := { s with _youngest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with _oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with _filled := false }
  return (s, true)

/-- C++ `bool EKF_IMU_buffer_t<NavEKF3_core::imu_elements>::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.h:156-158`. -/
def init_uint8_t (s : State) (size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := init_uint32_t s (UInt8.toUInt32 size)
  s := t'1
  return (s, t'2)

end EKF_IMU_buffer_t_NavEKF3_core_imu_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_output_elements

/-- C++ `bool ekf_imu_buffer::init(uint32_t size)`, `AP_NavEKF/EKF_Buffer.cpp:133-148` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::output_elements>`). -/
def init_uint32_t (s : State) (size : UInt32) : State × Bool := Id.run do
  let mut s := s
  if s.buffer'alloc then
    pure ()  -- C++ `free(buffer)`: the storage is allocated again below (--ring-buffers)
  s := { s with buffer := Array.replicate (UInt64.toNat (UInt32.toUInt64 size)) { quat := { q1 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), q2 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), q3 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), q4 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, velocity := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, position := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } } }
  s := { s with buffer'alloc := true }
  if !s.buffer'alloc then
    return (s, false)
  s := { s with _size := UInt32.toUInt8 size }
  s := { s with _youngest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with _oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with _filled := false }
  return (s, true)

/-- C++ `bool EKF_IMU_buffer_t<NavEKF3_core::output_elements>::init(uint8_t size)`, `AP_NavEKF/EKF_Buffer.h:156-158`. -/
def init_uint8_t (s : State) (size : UInt8) : State × Bool := Id.run do
  let mut s := s
  let (t'1, t'2) := init_uint32_t s (UInt8.toUInt32 size)
  s := t'1
  return (s, t'2)

end EKF_IMU_buffer_t_NavEKF3_core_output_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_imu_elements

/-- C++ `bool ekf_imu_buffer::is_filled() const`, `AP_NavEKF/EKF_Buffer.h:110-112` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>`). -/
def ekf_imu_buffer.is_filled (s : State) : Bool := Id.run do
  return s._filled

/-- C++ `bool EKF_IMU_buffer_t<NavEKF3_core::imu_elements>::is_filled() const`, `AP_NavEKF/EKF_Buffer.h:169-171`. -/
def is_filled (s : State) : Bool := Id.run do
  return ekf_imu_buffer.is_filled s

end EKF_IMU_buffer_t_NavEKF3_core_imu_elements

namespace EKF_obs_buffer_t_NavEKF3_core_mag_elements

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::mag_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:86-88`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_ring_buffer.reset s
  return s

end EKF_obs_buffer_t_NavEKF3_core_mag_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_imu_elements

/-- C++ `void ekf_imu_buffer::push_youngest_element(const void * element)`, `AP_NavEKF/EKF_Buffer.cpp:154-169` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>`). -/
def push_youngest_element_const_void_ptr (s : State) (element : NavEKF3_core.imu_elements) : State := Id.run do
  let mut s := s
  if !s.buffer'alloc then
    pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
    return s
  s := { s with _youngest := s._youngest + (1 : UInt8) }
  if UInt32.toInt32 (UInt8.toUInt32 s._youngest) == UInt32.toInt32 (UInt8.toUInt32 s._size) then
    s := { s with _youngest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
    s := { s with _filled := true }
  s := { s with buffer := s.buffer.set! (UInt8.toNat s._youngest) element }
  s := { s with _oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s._youngest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s._size))) }
  return s

/-- C++ `void EKF_IMU_buffer_t<NavEKF3_core::imu_elements>::push_youngest_element(NavEKF3_core::imu_elements element)`, `AP_NavEKF/EKF_Buffer.h:164-166`. -/
def push_youngest_element_imu_elements (s : State) (element : NavEKF3_core.imu_elements) : State := Id.run do
  let mut s := s
  s := push_youngest_element_const_void_ptr s element
  return s

/-- C++ `void ekf_imu_buffer::get_oldest_element(void * element)`, `AP_NavEKF/EKF_Buffer.cpp:172-180` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>`). -/
def get_oldest_element_void_ptr (s : State) (element : NavEKF3_core.imu_elements) : NavEKF3_core.imu_elements := Id.run do
  let mut element := element
  if !s.buffer'alloc then
    pure ()  -- C++ `AP_InternalError::error(...)`: left out (--drop)
    element := { delAng := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, delVel := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, delAngDT := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), delVelDT := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), time_ms := (0 : UInt32), gyro_index := (0 : UInt8), accel_index := (0 : UInt8) }
  else
    element := s.buffer[UInt8.toNat s._oldest]!
  return element

/-- C++ `NavEKF3_core::imu_elements EKF_IMU_buffer_t<NavEKF3_core::imu_elements>::get_oldest_element()`, `AP_NavEKF/EKF_Buffer.h:174-178`. -/
def get_oldest_element_void (s : State) : NavEKF3_core.imu_elements := Id.run do
  let mut ret : NavEKF3_core.imu_elements := {}
  ret := get_oldest_element_void_ptr s ret
  return ret

end EKF_IMU_buffer_t_NavEKF3_core_imu_elements

namespace EKF_obs_buffer_t_NavEKF3_core_mag_elements

/-- C++ `void ekf_ring_buffer::push(const void * element)`, `AP_NavEKF/EKF_Buffer.cpp:86-103` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::mag_elements>`). -/
def push_const_void_ptr (s : State) (element : NavEKF3_core.mag_elements) : State := Id.run do
  let mut s := s
  if !s.buffer'alloc then
    return s
  let head : UInt8 := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + UInt32.toInt32 (UInt8.toUInt32 s.count)) % UInt32.toInt32 (UInt8.toUInt32 s.size)))
  s := { s with buffer := s.buffer.set! (UInt8.toNat head) element }
  if UInt32.toInt32 (UInt8.toUInt32 s.count) < UInt32.toInt32 (UInt8.toUInt32 s.size) then
    s := { s with count := s.count + (1 : UInt8) }
  else
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  return s

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::mag_elements>::push(const NavEKF3_core::mag_elements & element)`, `AP_NavEKF/EKF_Buffer.h:82-84`. -/
def push_mag_elements (s : State) (element : NavEKF3_core.mag_elements) : State := Id.run do
  let mut s := s
  s := push_const_void_ptr s element
  return s

end EKF_obs_buffer_t_NavEKF3_core_mag_elements

namespace AP_NavEKF_Source

/-- C++ `bool AP_NavEKF_Source::useVelZSource(SourceZ velz_source, uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.cpp:188-205`. -/
def useVelZSource (s : State) (velz_source : AP_NavEKF_Source.SourceZ) (core_index : UInt8) : Bool := Id.run do
  if velz_source == AP_Enum_AP_NavEKF_Source_SourceZ.op_to_AP_NavEKF_Source_SourceZ s._source_set[UInt8.toNat (getActiveSourceSet s core_index)]!.velz then
    return true
  if option_is_set s AP_NavEKF_Source.SourceOptions.FUSE_ALL_VELOCITIES then
    for i' in [0:3] do
      let i : UInt8 := Nat.toUInt8 i'
      if AP_Enum_AP_NavEKF_Source_SourceZ.op_to_AP_NavEKF_Source_SourceZ s._source_set[UInt8.toNat i]!.velz == velz_source then
        return true
  return false

end AP_NavEKF_Source

namespace EKF_obs_buffer_t_NavEKF3_core_gps_elements

/-- C++ `void ekf_ring_buffer::push(const void * element)`, `AP_NavEKF/EKF_Buffer.cpp:86-103` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::gps_elements>`). -/
def push_const_void_ptr (s : State) (element : NavEKF3_core.gps_elements) : State := Id.run do
  let mut s := s
  if !s.buffer'alloc then
    return s
  let head : UInt8 := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + UInt32.toInt32 (UInt8.toUInt32 s.count)) % UInt32.toInt32 (UInt8.toUInt32 s.size)))
  s := { s with buffer := s.buffer.set! (UInt8.toNat head) element }
  if UInt32.toInt32 (UInt8.toUInt32 s.count) < UInt32.toInt32 (UInt8.toUInt32 s.size) then
    s := { s with count := s.count + (1 : UInt8) }
  else
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  return s

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::gps_elements>::push(const NavEKF3_core::gps_elements & element)`, `AP_NavEKF/EKF_Buffer.h:82-84`. -/
def push_gps_elements (s : State) (element : NavEKF3_core.gps_elements) : State := Id.run do
  let mut s := s
  s := push_const_void_ptr s element
  return s

end EKF_obs_buffer_t_NavEKF3_core_gps_elements

namespace EKF_obs_buffer_t_NavEKF3_core_yaw_elements

/-- C++ `void ekf_ring_buffer::push(const void * element)`, `AP_NavEKF/EKF_Buffer.cpp:86-103` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::yaw_elements>`). -/
def push_const_void_ptr (s : State) (element : NavEKF3_core.yaw_elements) : State := Id.run do
  let mut s := s
  if !s.buffer'alloc then
    return s
  let head : UInt8 := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + UInt32.toInt32 (UInt8.toUInt32 s.count)) % UInt32.toInt32 (UInt8.toUInt32 s.size)))
  s := { s with buffer := s.buffer.set! (UInt8.toNat head) element }
  if UInt32.toInt32 (UInt8.toUInt32 s.count) < UInt32.toInt32 (UInt8.toUInt32 s.size) then
    s := { s with count := s.count + (1 : UInt8) }
  else
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  return s

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::yaw_elements>::push(const NavEKF3_core::yaw_elements & element)`, `AP_NavEKF/EKF_Buffer.h:82-84`. -/
def push_yaw_elements (s : State) (element : NavEKF3_core.yaw_elements) : State := Id.run do
  let mut s := s
  s := push_const_void_ptr s element
  return s

end EKF_obs_buffer_t_NavEKF3_core_yaw_elements

namespace EKF_obs_buffer_t_NavEKF3_core_baro_elements

/-- C++ `void ekf_ring_buffer::push(const void * element)`, `AP_NavEKF/EKF_Buffer.cpp:86-103` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::baro_elements>`). -/
def push_const_void_ptr (s : State) (element : NavEKF3_core.baro_elements) : State := Id.run do
  let mut s := s
  if !s.buffer'alloc then
    return s
  let head : UInt8 := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + UInt32.toInt32 (UInt8.toUInt32 s.count)) % UInt32.toInt32 (UInt8.toUInt32 s.size)))
  s := { s with buffer := s.buffer.set! (UInt8.toNat head) element }
  if UInt32.toInt32 (UInt8.toUInt32 s.count) < UInt32.toInt32 (UInt8.toUInt32 s.size) then
    s := { s with count := s.count + (1 : UInt8) }
  else
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  return s

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::baro_elements>::push(const NavEKF3_core::baro_elements & element)`, `AP_NavEKF/EKF_Buffer.h:82-84`. -/
def push_baro_elements (s : State) (element : NavEKF3_core.baro_elements) : State := Id.run do
  let mut s := s
  s := push_const_void_ptr s element
  return s

end EKF_obs_buffer_t_NavEKF3_core_baro_elements

namespace EKF_obs_buffer_t_NavEKF3_core_tas_elements

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::tas_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:86-88`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_ring_buffer.reset s
  return s

end EKF_obs_buffer_t_NavEKF3_core_tas_elements

namespace EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:86-88`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_ring_buffer.reset s
  return s

end EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:86-88`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_ring_buffer.reset s
  return s

end EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_gps_elements

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::gps_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:86-88`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_ring_buffer.reset s
  return s

end EKF_obs_buffer_t_NavEKF3_core_gps_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_output_elements

/-- C++ `void ekf_imu_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:191-196` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::output_elements>`). -/
def ekf_imu_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with _youngest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with _oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  let t'1 := UInt32.toNat (UInt8.toUInt32 s._size)
  s := { s with buffer := s.buffer.mapIdx (fun i x => if i < t'1 then { quat := { q1 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), q2 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), q3 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), q4 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, velocity := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, position := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) } } else x) }
  return s

/-- C++ `void EKF_IMU_buffer_t<NavEKF3_core::output_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:186-188`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_imu_buffer.reset s
  return s

end EKF_IMU_buffer_t_NavEKF3_core_output_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_imu_elements

/-- C++ `void ekf_imu_buffer::reset()`, `AP_NavEKF/EKF_Buffer.cpp:191-196` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>`). -/
def ekf_imu_buffer.reset (s : State) : State := Id.run do
  let mut s := s
  s := { s with _youngest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  s := { s with _oldest := Int8.toUInt8 (Int32.toInt8 (0 : Int32)) }
  let t'1 := UInt32.toNat (UInt8.toUInt32 s._size)
  s := { s with buffer := s.buffer.mapIdx (fun i x => if i < t'1 then { delAng := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, delVel := { x := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), y := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), z := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }, delAngDT := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), delVelDT := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), time_ms := (0 : UInt32), gyro_index := (0 : UInt8), accel_index := (0 : UInt8) } else x) }
  return s

/-- C++ `void EKF_IMU_buffer_t<NavEKF3_core::imu_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:186-188`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_imu_buffer.reset s
  return s

end EKF_IMU_buffer_t_NavEKF3_core_imu_elements

namespace EKF_obs_buffer_t_NavEKF3_core_yaw_elements

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::yaw_elements>::reset()`, `AP_NavEKF/EKF_Buffer.h:86-88`. -/
def reset (s : State) : State := Id.run do
  let mut s := s
  s := ekf_ring_buffer.reset s
  return s

end EKF_obs_buffer_t_NavEKF3_core_yaw_elements

namespace AP_NavEKF_Source

/-- C++ `bool AP_NavEKF_Source::useVelXYSource(SourceXY velxy_source, uint8_t core_index) const`, `AP_NavEKF/AP_NavEKF_Source.cpp:169-186`. -/
def useVelXYSource (s : State) (velxy_source : AP_NavEKF_Source.SourceXY) (core_index : UInt8) : Bool := Id.run do
  if velxy_source == AP_Enum_AP_NavEKF_Source_SourceXY.op_to_AP_NavEKF_Source_SourceXY s._source_set[UInt8.toNat (getActiveSourceSet s core_index)]!.velxy then
    return true
  if option_is_set s AP_NavEKF_Source.SourceOptions.FUSE_ALL_VELOCITIES then
    for i' in [0:3] do
      let i : UInt8 := Nat.toUInt8 i'
      if AP_Enum_AP_NavEKF_Source_SourceXY.op_to_AP_NavEKF_Source_SourceXY s._source_set[UInt8.toNat i]!.velxy == velxy_source then
        return true
  return false

end AP_NavEKF_Source

namespace EKF_obs_buffer_t_NavEKF3_core_mag_elements

/-- C++ `uint32_t ekf_ring_buffer::time_ms(uint8_t idx) const`, `AP_NavEKF/EKF_Buffer.cpp:42-46` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::mag_elements>`). -/
def time_ms (s : State) (idx : UInt8) : UInt32 := Id.run do
  let t'1 := UInt8.toNat idx
  return s.buffer[t'1]!.time_ms

/-- C++ `bool ekf_ring_buffer::recall(void * element, const uint32_t sample_time_ms)`, `AP_NavEKF/EKF_Buffer.cpp:53-80` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::mag_elements>`). -/
def recall_void_ptr_uint32_t (s : State) (element : NavEKF3_core.mag_elements) (sample_time_ms : UInt32) : State × NavEKF3_core.mag_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let mut ret : Bool := false
  let mut best_index : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 s.count) > (0 : Int32))) then break
    let toldest : UInt32 := time_ms s s.oldest
    let dt : Int32 := UInt32.toInt32 (sample_time_ms - toldest)
    let «matches» : Bool := decide (dt ≥ (0 : Int32)) && decide (dt < (100 : Int32))
    if «matches» then
      best_index := s.oldest
      ret := true
    if dt < (0 : Int32) then
      break
    s := { s with count := s.count - (1 : UInt8) }
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  if ret then
    element := s.buffer[UInt8.toNat best_index]!
  return (s, element, ret)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::mag_elements>::recall(NavEKF3_core::mag_elements & element, uint32_t sample_time)`, `AP_NavEKF/EKF_Buffer.h:78-80`. -/
def recall_mag_elements_uint32_t (s : State) (element : NavEKF3_core.mag_elements) (sample_time : UInt32) : State × NavEKF3_core.mag_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let (t'1, t'2, t'3) := recall_void_ptr_uint32_t s element sample_time
  s := t'1
  element := t'2
  return (s, element, t'3)

end EKF_obs_buffer_t_NavEKF3_core_mag_elements

namespace EKF_obs_buffer_t_NavEKF3_core_yaw_elements

/-- C++ `uint32_t ekf_ring_buffer::time_ms(uint8_t idx) const`, `AP_NavEKF/EKF_Buffer.cpp:42-46` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::yaw_elements>`). -/
def time_ms (s : State) (idx : UInt8) : UInt32 := Id.run do
  let t'1 := UInt8.toNat idx
  return s.buffer[t'1]!.time_ms

/-- C++ `bool ekf_ring_buffer::recall(void * element, const uint32_t sample_time_ms)`, `AP_NavEKF/EKF_Buffer.cpp:53-80` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::yaw_elements>`). -/
def recall_void_ptr_uint32_t (s : State) (element : NavEKF3_core.yaw_elements) (sample_time_ms : UInt32) : State × NavEKF3_core.yaw_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let mut ret : Bool := false
  let mut best_index : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 s.count) > (0 : Int32))) then break
    let toldest : UInt32 := time_ms s s.oldest
    let dt : Int32 := UInt32.toInt32 (sample_time_ms - toldest)
    let «matches» : Bool := decide (dt ≥ (0 : Int32)) && decide (dt < (100 : Int32))
    if «matches» then
      best_index := s.oldest
      ret := true
    if dt < (0 : Int32) then
      break
    s := { s with count := s.count - (1 : UInt8) }
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  if ret then
    element := s.buffer[UInt8.toNat best_index]!
  return (s, element, ret)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::yaw_elements>::recall(NavEKF3_core::yaw_elements & element, uint32_t sample_time)`, `AP_NavEKF/EKF_Buffer.h:78-80`. -/
def recall_yaw_elements_uint32_t (s : State) (element : NavEKF3_core.yaw_elements) (sample_time : UInt32) : State × NavEKF3_core.yaw_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let (t'1, t'2, t'3) := recall_void_ptr_uint32_t s element sample_time
  s := t'1
  element := t'2
  return (s, element, t'3)

end EKF_obs_buffer_t_NavEKF3_core_yaw_elements

namespace EKF_obs_buffer_t_NavEKF3_core_gps_elements

/-- C++ `uint32_t ekf_ring_buffer::time_ms(uint8_t idx) const`, `AP_NavEKF/EKF_Buffer.cpp:42-46` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::gps_elements>`). -/
def time_ms (s : State) (idx : UInt8) : UInt32 := Id.run do
  let t'1 := UInt8.toNat idx
  return s.buffer[t'1]!.time_ms

/-- C++ `bool ekf_ring_buffer::recall(void * element, const uint32_t sample_time_ms)`, `AP_NavEKF/EKF_Buffer.cpp:53-80` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::gps_elements>`). -/
def recall_void_ptr_uint32_t (s : State) (element : NavEKF3_core.gps_elements) (sample_time_ms : UInt32) : State × NavEKF3_core.gps_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let mut ret : Bool := false
  let mut best_index : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 s.count) > (0 : Int32))) then break
    let toldest : UInt32 := time_ms s s.oldest
    let dt : Int32 := UInt32.toInt32 (sample_time_ms - toldest)
    let «matches» : Bool := decide (dt ≥ (0 : Int32)) && decide (dt < (100 : Int32))
    if «matches» then
      best_index := s.oldest
      ret := true
    if dt < (0 : Int32) then
      break
    s := { s with count := s.count - (1 : UInt8) }
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  if ret then
    element := s.buffer[UInt8.toNat best_index]!
  return (s, element, ret)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::gps_elements>::recall(NavEKF3_core::gps_elements & element, uint32_t sample_time)`, `AP_NavEKF/EKF_Buffer.h:78-80`. -/
def recall_gps_elements_uint32_t (s : State) (element : NavEKF3_core.gps_elements) (sample_time : UInt32) : State × NavEKF3_core.gps_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let (t'1, t'2, t'3) := recall_void_ptr_uint32_t s element sample_time
  s := t'1
  element := t'2
  return (s, element, t'3)

end EKF_obs_buffer_t_NavEKF3_core_gps_elements

namespace EKF_obs_buffer_t_NavEKF3_core_baro_elements

/-- C++ `uint32_t ekf_ring_buffer::time_ms(uint8_t idx) const`, `AP_NavEKF/EKF_Buffer.cpp:42-46` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::baro_elements>`). -/
def time_ms (s : State) (idx : UInt8) : UInt32 := Id.run do
  let t'1 := UInt8.toNat idx
  return s.buffer[t'1]!.time_ms

/-- C++ `bool ekf_ring_buffer::recall(void * element, const uint32_t sample_time_ms)`, `AP_NavEKF/EKF_Buffer.cpp:53-80` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::baro_elements>`). -/
def recall_void_ptr_uint32_t (s : State) (element : NavEKF3_core.baro_elements) (sample_time_ms : UInt32) : State × NavEKF3_core.baro_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let mut ret : Bool := false
  let mut best_index : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 s.count) > (0 : Int32))) then break
    let toldest : UInt32 := time_ms s s.oldest
    let dt : Int32 := UInt32.toInt32 (sample_time_ms - toldest)
    let «matches» : Bool := decide (dt ≥ (0 : Int32)) && decide (dt < (100 : Int32))
    if «matches» then
      best_index := s.oldest
      ret := true
    if dt < (0 : Int32) then
      break
    s := { s with count := s.count - (1 : UInt8) }
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  if ret then
    element := s.buffer[UInt8.toNat best_index]!
  return (s, element, ret)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::baro_elements>::recall(NavEKF3_core::baro_elements & element, uint32_t sample_time)`, `AP_NavEKF/EKF_Buffer.h:78-80`. -/
def recall_baro_elements_uint32_t (s : State) (element : NavEKF3_core.baro_elements) (sample_time : UInt32) : State × NavEKF3_core.baro_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let (t'1, t'2, t'3) := recall_void_ptr_uint32_t s element sample_time
  s := t'1
  element := t'2
  return (s, element, t'3)

end EKF_obs_buffer_t_NavEKF3_core_baro_elements

namespace EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

/-- C++ `uint32_t ekf_ring_buffer::time_ms(uint8_t idx) const`, `AP_NavEKF/EKF_Buffer.cpp:42-46` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>`). -/
def time_ms (s : State) (idx : UInt8) : UInt32 := Id.run do
  let t'1 := UInt8.toNat idx
  return s.buffer[t'1]!.time_ms

/-- C++ `bool ekf_ring_buffer::recall(void * element, const uint32_t sample_time_ms)`, `AP_NavEKF/EKF_Buffer.cpp:53-80` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>`). -/
def recall_void_ptr_uint32_t (s : State) (element : NavEKF3_core.vel_odm_elements) (sample_time_ms : UInt32) : State × NavEKF3_core.vel_odm_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let mut ret : Bool := false
  let mut best_index : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 s.count) > (0 : Int32))) then break
    let toldest : UInt32 := time_ms s s.oldest
    let dt : Int32 := UInt32.toInt32 (sample_time_ms - toldest)
    let «matches» : Bool := decide (dt ≥ (0 : Int32)) && decide (dt < (100 : Int32))
    if «matches» then
      best_index := s.oldest
      ret := true
    if dt < (0 : Int32) then
      break
    s := { s with count := s.count - (1 : UInt8) }
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  if ret then
    element := s.buffer[UInt8.toNat best_index]!
  return (s, element, ret)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::vel_odm_elements>::recall(NavEKF3_core::vel_odm_elements & element, uint32_t sample_time)`, `AP_NavEKF/EKF_Buffer.h:78-80`. -/
def recall_vel_odm_elements_uint32_t (s : State) (element : NavEKF3_core.vel_odm_elements) (sample_time : UInt32) : State × NavEKF3_core.vel_odm_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let (t'1, t'2, t'3) := recall_void_ptr_uint32_t s element sample_time
  s := t'1
  element := t'2
  return (s, element, t'3)

end EKF_obs_buffer_t_NavEKF3_core_vel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

/-- C++ `uint32_t ekf_ring_buffer::time_ms(uint8_t idx) const`, `AP_NavEKF/EKF_Buffer.cpp:42-46` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>`). -/
def time_ms (s : State) (idx : UInt8) : UInt32 := Id.run do
  let t'1 := UInt8.toNat idx
  return s.buffer[t'1]!.time_ms

/-- C++ `bool ekf_ring_buffer::recall(void * element, const uint32_t sample_time_ms)`, `AP_NavEKF/EKF_Buffer.cpp:53-80` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>`). -/
def recall_void_ptr_uint32_t (s : State) (element : NavEKF3_core.wheel_odm_elements) (sample_time_ms : UInt32) : State × NavEKF3_core.wheel_odm_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let mut ret : Bool := false
  let mut best_index : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 s.count) > (0 : Int32))) then break
    let toldest : UInt32 := time_ms s s.oldest
    let dt : Int32 := UInt32.toInt32 (sample_time_ms - toldest)
    let «matches» : Bool := decide (dt ≥ (0 : Int32)) && decide (dt < (100 : Int32))
    if «matches» then
      best_index := s.oldest
      ret := true
    if dt < (0 : Int32) then
      break
    s := { s with count := s.count - (1 : UInt8) }
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  if ret then
    element := s.buffer[UInt8.toNat best_index]!
  return (s, element, ret)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::wheel_odm_elements>::recall(NavEKF3_core::wheel_odm_elements & element, uint32_t sample_time)`, `AP_NavEKF/EKF_Buffer.h:78-80`. -/
def recall_wheel_odm_elements_uint32_t (s : State) (element : NavEKF3_core.wheel_odm_elements) (sample_time : UInt32) : State × NavEKF3_core.wheel_odm_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let (t'1, t'2, t'3) := recall_void_ptr_uint32_t s element sample_time
  s := t'1
  element := t'2
  return (s, element, t'3)

end EKF_obs_buffer_t_NavEKF3_core_wheel_odm_elements

namespace EKF_obs_buffer_t_NavEKF3_core_tas_elements

/-- C++ `void ekf_ring_buffer::push(const void * element)`, `AP_NavEKF/EKF_Buffer.cpp:86-103` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::tas_elements>`). -/
def push_const_void_ptr (s : State) (element : NavEKF3_core.tas_elements) : State := Id.run do
  let mut s := s
  if !s.buffer'alloc then
    return s
  let head : UInt8 := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + UInt32.toInt32 (UInt8.toUInt32 s.count)) % UInt32.toInt32 (UInt8.toUInt32 s.size)))
  s := { s with buffer := s.buffer.set! (UInt8.toNat head) element }
  if UInt32.toInt32 (UInt8.toUInt32 s.count) < UInt32.toInt32 (UInt8.toUInt32 s.size) then
    s := { s with count := s.count + (1 : UInt8) }
  else
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  return s

/-- C++ `void EKF_obs_buffer_t<NavEKF3_core::tas_elements>::push(const NavEKF3_core::tas_elements & element)`, `AP_NavEKF/EKF_Buffer.h:82-84`. -/
def push_tas_elements (s : State) (element : NavEKF3_core.tas_elements) : State := Id.run do
  let mut s := s
  s := push_const_void_ptr s element
  return s

/-- C++ `uint32_t ekf_ring_buffer::time_ms(uint8_t idx) const`, `AP_NavEKF/EKF_Buffer.cpp:42-46` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::tas_elements>`). -/
def time_ms (s : State) (idx : UInt8) : UInt32 := Id.run do
  let t'1 := UInt8.toNat idx
  return s.buffer[t'1]!.time_ms

/-- C++ `bool ekf_ring_buffer::recall(void * element, const uint32_t sample_time_ms)`, `AP_NavEKF/EKF_Buffer.cpp:53-80` (a member of `ekf_ring_buffer`, translated for `EKF_obs_buffer_t<NavEKF3_core::tas_elements>`). -/
def recall_void_ptr_uint32_t (s : State) (element : NavEKF3_core.tas_elements) (sample_time_ms : UInt32) : State × NavEKF3_core.tas_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let mut ret : Bool := false
  let mut best_index : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  for _ in [0:2^64] do  -- C loop without a constant trip count (--general-loops)
    if !(decide (UInt32.toInt32 (UInt8.toUInt32 s.count) > (0 : Int32))) then break
    let toldest : UInt32 := time_ms s s.oldest
    let dt : Int32 := UInt32.toInt32 (sample_time_ms - toldest)
    let «matches» : Bool := decide (dt ≥ (0 : Int32)) && decide (dt < (100 : Int32))
    if «matches» then
      best_index := s.oldest
      ret := true
    if dt < (0 : Int32) then
      break
    s := { s with count := s.count - (1 : UInt8) }
    s := { s with oldest := Int8.toUInt8 (Int32.toInt8 ((UInt32.toInt32 (UInt8.toUInt32 s.oldest) + (1 : Int32)) % UInt32.toInt32 (UInt8.toUInt32 s.size))) }
  if ret then
    element := s.buffer[UInt8.toNat best_index]!
  return (s, element, ret)

/-- C++ `bool EKF_obs_buffer_t<NavEKF3_core::tas_elements>::recall(NavEKF3_core::tas_elements & element, uint32_t sample_time)`, `AP_NavEKF/EKF_Buffer.h:78-80`. -/
def recall_tas_elements_uint32_t (s : State) (element : NavEKF3_core.tas_elements) (sample_time : UInt32) : State × NavEKF3_core.tas_elements × Bool := Id.run do
  let mut s := s
  let mut element := element
  let (t'1, t'2, t'3) := recall_void_ptr_uint32_t s element sample_time
  s := t'1
  element := t'2
  return (s, element, t'3)

end EKF_obs_buffer_t_NavEKF3_core_tas_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_output_elements

/-- C++ `NavEKF3_core::output_elements & EKF_IMU_buffer_t<NavEKF3_core::output_elements>::operator[](uint32_t index)`, `AP_NavEKF/EKF_Buffer.h:191-194`. -/
def op_index (s : State) (index : UInt32) : NavEKF3_core.output_elements := Id.run do
  let t'1 := UInt8.toNat (UInt32.toUInt8 index)
  return s.buffer[t'1]!

end EKF_IMU_buffer_t_NavEKF3_core_output_elements

namespace EKF_IMU_buffer_t_NavEKF3_core_imu_elements

/-- C++ `uint8_t ekf_imu_buffer::get_youngest_index() const`, `AP_NavEKF/EKF_Buffer.h:132-134` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>`). -/
def ekf_imu_buffer.get_youngest_index_void (s : State) : UInt8 := Id.run do
  return s._youngest

/-- C++ `uint8_t EKF_IMU_buffer_t<NavEKF3_core::imu_elements>::get_youngest_index()`, `AP_NavEKF/EKF_Buffer.h:202-204`. -/
def get_youngest_index_void (s : State) : UInt8 := Id.run do
  return ekf_imu_buffer.get_youngest_index_void s

/-- C++ `uint8_t ekf_imu_buffer::get_oldest_index() const`, `AP_NavEKF/EKF_Buffer.h:127-129` (a member of `ekf_imu_buffer`, translated for `EKF_IMU_buffer_t<NavEKF3_core::imu_elements>`). -/
def ekf_imu_buffer.get_oldest_index_void (s : State) : UInt8 := Id.run do
  return s._oldest

/-- C++ `uint8_t EKF_IMU_buffer_t<NavEKF3_core::imu_elements>::get_oldest_index()`, `AP_NavEKF/EKF_Buffer.h:197-199`. -/
def get_oldest_index_void (s : State) : UInt8 := Id.run do
  return ekf_imu_buffer.get_oldest_index_void s

end EKF_IMU_buffer_t_NavEKF3_core_imu_elements

end Estimator_lib
