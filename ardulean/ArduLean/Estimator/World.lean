import ArduLean.Runtime.CFloat
import ArduLean.Estimator.libraries.AP_Math.AP_Math

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

/-- A pointer to an object of the program (--world-pointers): null, a file-scope object, or the object
with index `i` among those of a class that `new` creates (closed world: every object a pointer can
point to is one of these; README.md, "Phase 3: World pointers"). -/
inductive WPtr where
  | null
  | EKF3
  | est_scheduler
  | sitl
  | barometer
  | compass
  | ins
  | gps
  | rtc
  | est_uart
  | ahrs
  | heap'AP_Baro_SITL (i : Nat)
  | heap'AP_Compass_SITL (i : Nat)
  | heap'AP_GPS_SITL (i : Nat)
  | heap'AP_DAL (i : Nat)
  | heap'AP_DAL_Airspeed (i : Nat)
  | heap'NavEKF3_core (i : Nat)
  | heap'EKFGSF_yaw (i : Nat)
  | heap'AP_AHRS_View (i : Nat)
  | heap'AP_InertialSensor_SITL (i : Nat)
  | ahrs'ekf3  -- the member object `ahrs.ekf3` (--member-pointers)
  | ahrs'dcm  -- the member object `ahrs.dcm` (--member-pointers)
  | ahrs'dcm_estimates  -- the member object `ahrs.dcm_estimates` (--member-pointers)
  | ahrs'ekf3_estimates  -- the member object `ahrs.ekf3_estimates` (--member-pointers)
  | ahrs'sim  -- the member object `ahrs.sim` (--member-pointers)
  | ahrs'sim_estimates  -- the member object `ahrs.sim_estimates` (--member-pointers)
  deriving DecidableEq, Inhabited

/-- The index of a heap object among those of its class (0 for the others). -/
def WPtr.index : WPtr → Nat
  | .heap'AP_Baro_SITL i => i
  | .heap'AP_Compass_SITL i => i
  | .heap'AP_GPS_SITL i => i
  | .heap'AP_DAL i => i
  | .heap'AP_DAL_Airspeed i => i
  | .heap'NavEKF3_core i => i
  | .heap'EKFGSF_yaw i => i
  | .heap'AP_AHRS_View i => i
  | .heap'AP_InertialSensor_SITL i => i
  | _ => 0

/-- A name of the object (for the difftest: `null`, the field, `heap'C#i`). -/
def WPtr.name : WPtr → String
  | .null => "null"
  | .EKF3 => "EKF3"
  | .est_scheduler => "est_scheduler"
  | .sitl => "sitl"
  | .barometer => "barometer"
  | .compass => "compass"
  | .ins => "ins"
  | .gps => "gps"
  | .rtc => "rtc"
  | .est_uart => "est_uart"
  | .ahrs => "ahrs"
  | .heap'AP_Baro_SITL i => "heap'AP_Baro_SITL#" ++ toString i
  | .heap'AP_Compass_SITL i => "heap'AP_Compass_SITL#" ++ toString i
  | .heap'AP_GPS_SITL i => "heap'AP_GPS_SITL#" ++ toString i
  | .heap'AP_DAL i => "heap'AP_DAL#" ++ toString i
  | .heap'AP_DAL_Airspeed i => "heap'AP_DAL_Airspeed#" ++ toString i
  | .heap'NavEKF3_core i => "heap'NavEKF3_core#" ++ toString i
  | .heap'EKFGSF_yaw i => "heap'EKFGSF_yaw#" ++ toString i
  | .heap'AP_AHRS_View i => "heap'AP_AHRS_View#" ++ toString i
  | .heap'AP_InertialSensor_SITL i => "heap'AP_InertialSensor_SITL#" ++ toString i
  | .ahrs'ekf3 => "ahrs'ekf3"
  | .ahrs'dcm => "ahrs'dcm"
  | .ahrs'dcm_estimates => "ahrs'dcm_estimates"
  | .ahrs'ekf3_estimates => "ahrs'ekf3_estimates"
  | .ahrs'sim => "ahrs'sim"
  | .ahrs'sim_estimates => "ahrs'sim_estimates"

/-- A `Functor<void>` (AP_HAL::MemberProc) of the program (--world-pointers): empty, or a member function
of a class bound to an object, one constructor per `FUNCTOR_BIND` of the program (closed world). -/
inductive WFun where
  | null
  | AP_Baro_SITL__timer (obj : WPtr)
  | AP_Compass_SITL__timer (obj : WPtr)
  | AP_InertialSensor_SITL_timer_update (obj : WPtr)
  deriving DecidableEq, Inhabited

/-- A name of the functor (for the difftest: `null`, or the constructor `@` the object's name). -/
def WFun.name : WFun → String
  | .null => "null"
  | .AP_Baro_SITL__timer o => "AP_Baro_SITL__timer@" ++ o.name
  | .AP_Compass_SITL__timer o => "AP_Compass_SITL__timer@" ++ o.name
  | .AP_InertialSensor_SITL_timer_update o => "AP_InertialSensor_SITL_timer_update@" ++ o.name

/-- (--text-buffers) The text a `char` buffer holds, as the formatted write that made it (the formatting is
the vehicle's translated AP_HAL::Util::snprintf, where the text leaves the translation): `none` never written
(a zero-filled buffer: the empty string; a caller's buffer: unchanged), `null` the null pointer (a
`const char *` result, --text-results), `fmt size fmt args` `snprintf(buf, size, fmt, args...)` (the
arguments tagged as for --text-log), `text size src args` the same with the text of the buffer `src` as
the format. -/
inductive CText where
  | none
  | null
  | fmt (size : UInt64) (fmt : String) (args : Array (Sum UInt64 String))
  | text (size : UInt64) (src : CText) (args : Array (Sum UInt64 String))
deriving Inhabited

/-- (--text-results) whether a `const char *` text is the null pointer -/
def CText.isNull : CText → Bool
  | .null => true
  | _ => false

/-- C++ `struct EstRecord`, `reference/hal/est_input.h:18-35`. -/
structure EstRecord where
  /-- `uint64_t t_us` of `EstRecord` (`reference/hal/est_input.h:19`). -/
  t_us : UInt64 := (0 : UInt64)
  /-- `uint8_t imu_n[2]` of `EstRecord` (`reference/hal/est_input.h:20`). -/
  imu_n : Array UInt8 := Array.replicate 2 (0 : UInt8)
  /-- `Vector3f accel[16]` of `EstRecord` (`reference/hal/est_input.h:21`). -/
  accel : Array Vector3f.State := Array.replicate 16 {}
  /-- `Vector3f gyro[16]` of `EstRecord` (`reference/hal/est_input.h:22`). -/
  gyro : Array Vector3f.State := Array.replicate 16 {}
  /-- `bool baro` of `EstRecord` (`reference/hal/est_input.h:23`). -/
  baro : Bool := false
  /-- `float baro_pa` of `EstRecord` (`reference/hal/est_input.h:24`). -/
  baro_pa : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float baro_degc` of `EstRecord` (`reference/hal/est_input.h:25`). -/
  baro_degc : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `bool mag` of `EstRecord` (`reference/hal/est_input.h:26`). -/
  mag : Bool := false
  /-- `Vector3f mag_mgauss` of `EstRecord` (`reference/hal/est_input.h:27`). -/
  mag_mgauss : Vector3f.State := {}
  /-- `bool gps` of `EstRecord` (`reference/hal/est_input.h:28`). -/
  gps : Bool := false
  /-- `double gps_lat_deg` of `EstRecord` (`reference/hal/est_input.h:29`). -/
  gps_lat_deg : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double gps_lon_deg` of `EstRecord` (`reference/hal/est_input.h:30`). -/
  gps_lon_deg : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double gps_alt_m` of `EstRecord` (`reference/hal/est_input.h:31`). -/
  gps_alt_m : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double gps_vn` of `EstRecord` (`reference/hal/est_input.h:32`). -/
  gps_vn : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double gps_ve` of `EstRecord` (`reference/hal/est_input.h:33`). -/
  gps_ve : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
  /-- `double gps_vd` of `EstRecord` (`reference/hal/est_input.h:34`). -/
  gps_vd : Binary64 := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/)
deriving Inhabited

namespace EstScheduler

/-- State of C++ `EstScheduler` (`reference/hal/est_scheduler.h:30-102`): its data members; base classes flattened, base first: `AP_HAL::Scheduler`. -/
structure State where
  /-- `uint16_t _min_delay_cb_ms` of `AP_HAL::Scheduler` (`AP_HAL/Scheduler.h:98`). -/
  _min_delay_cb_ms : UInt16 := (0 : UInt16)
  /-- `bool _in_delay_callback` of `AP_HAL::Scheduler` (`AP_HAL/Scheduler.h:132`). -/
  _in_delay_callback : Bool := false
  /-- `EstRecord _recs[1024]` of `EstScheduler` (`reference/hal/est_scheduler.h:82`). -/
  _recs : Array EstRecord := Array.replicate 1024 {}
  /-- `uint16_t _head` of `EstScheduler` (`reference/hal/est_scheduler.h:83`). -/
  _head : UInt16 := (0 : UInt16)
  /-- `uint16_t _count` of `EstScheduler` (`reference/hal/est_scheduler.h:84`). -/
  _count : UInt16 := (0 : UInt16)
  /-- `EstRecord _in` of `EstScheduler` (`reference/hal/est_scheduler.h:85`). -/
  _in : EstRecord := {}
  /-- `uint64_t _clock_us` of `EstScheduler` (`reference/hal/est_scheduler.h:86`). -/
  _clock_us : UInt64 := Int64.toUInt64 (Int32.toInt64 (1 : Int32))
  /-- `uint64_t _step_period` of `EstScheduler` (`reference/hal/est_scheduler.h:87`). -/
  _step_period : UInt64 := Int64.toUInt64 (Int32.toInt64 (2500 : Int32))
  /-- `uint32_t _lines` of `EstScheduler` (`reference/hal/est_scheduler.h:88`). -/
  _lines : UInt32 := (0 : UInt32)
  /-- `bool _exhausted` of `EstScheduler` (`reference/hal/est_scheduler.h:89`). -/
  _exhausted : Bool := false
  /-- `bool _initialized` of `EstScheduler` (`reference/hal/est_scheduler.h:90`). -/
  _initialized : Bool := false
  /-- `AP_HAL::MemberProc _timer_proc[8]` of `EstScheduler` (`reference/hal/est_scheduler.h:91`). -/
  _timer_proc : Array WFun := Array.replicate 8 WFun.null
  /-- `uint8_t _num_timer` of `EstScheduler` (`reference/hal/est_scheduler.h:92`). -/
  _num_timer : UInt8 := (0 : UInt8)
  /-- `bool _in_timer_proc` of `EstScheduler` (`reference/hal/est_scheduler.h:93`). -/
  _in_timer_proc : Bool := false
  /-- `EstRecord _gps` of `EstScheduler` (`reference/hal/est_scheduler.h:94`). -/
  _gps : EstRecord := {}
  /-- `bool _gps_pending` of `EstScheduler` (`reference/hal/est_scheduler.h:95`). -/
  _gps_pending : Bool := false
  /-- `uint16_t _imu_rate_hz` of `EstScheduler` (`reference/hal/est_scheduler.h:96`). -/
  _imu_rate_hz : UInt16 := Int16.toUInt16 (Int32.toInt16 (1200 : Int32))
  /-- `uint64_t _fed_t_us` of `EstScheduler` (`reference/hal/est_scheduler.h:97`). -/
  _fed_t_us : UInt64 := (0 : UInt64)
  /-- `uint8_t _events` of `EstScheduler` (`reference/hal/est_scheduler.h:98`). -/
  _events : UInt8 := (0 : UInt8)
  /-- `EstRecord _synth` of `EstScheduler` (`reference/hal/est_scheduler.h:100`). -/
  _synth : EstRecord := {}
deriving Inhabited

/-- C++ `uint64_t EstScheduler::clock_us() const`, `reference/hal/est_scheduler.h:64`. -/
def clock_us (s : State) : UInt64 := Id.run do
  return s._clock_us

end EstScheduler

namespace EstUART

/-- State of C++ `EstUART` (`reference/hal/est_uart.h:15-38`): its data members; base classes flattened, base first: `AP_HAL::UARTDriver`, `AP_HAL::BetterStream`. -/
structure State where
  /-- `uint32_t lock_write_key` of `AP_HAL::UARTDriver` (`AP_HAL/UARTDriver.h:246`). -/
  lock_write_key : UInt32 := (0 : UInt32)
  /-- `uint32_t lock_read_key` of `AP_HAL::UARTDriver` (`AP_HAL/UARTDriver.h:247`). -/
  lock_read_key : UInt32 := (0 : UInt32)
  /-- `uint8_t parity` of `AP_HAL::UARTDriver` (`AP_HAL/UARTDriver.h:249`). -/
  parity : UInt8 := (0 : UInt8)
  /-- `uint16_t _last_options` of `AP_HAL::UARTDriver` (`AP_HAL/UARTDriver.h:293`). -/
  _last_options : UInt16 := (0 : UInt16)
  /-- `bool initialized` of `EstUART` (`reference/hal/est_uart.h:36`). -/
  initialized : Bool := false
  /-- `uint32_t baud` of `EstUART` (`reference/hal/est_uart.h:37`). -/
  baud : UInt32 := Int32.toUInt32 (115200 : Int32)
deriving Inhabited

end EstUART

/-- C++ `const uint16_t EST_MAX_RECORDS`, `reference/hal/est_scheduler.h:27`. -/
def EST_MAX_RECORDS : UInt16 := Int16.toUInt16 (Int32.toInt16 (1024 : Int32))

namespace EstScheduler

/-- C++ `const EstRecord & EstScheduler::current() const`, `reference/hal/est_scheduler.h:66`. -/
def current (s : State) : EstRecord := Id.run do
  return s._in

end EstScheduler

/-- C++ `const uint8_t EST_MAX_IMUS`, `reference/hal/est_input.h:13`. -/
def EST_MAX_IMUS : UInt8 := Int8.toUInt8 (Int32.toInt8 (2 : Int32))

/-- C++ `const uint8_t EST_MAX_IMU_SAMPLES`, `reference/hal/est_input.h:14`. -/
def EST_MAX_IMU_SAMPLES : UInt8 := Int8.toUInt8 (Int32.toInt8 (8 : Int32))

namespace EstScheduler

/-- C++ `uint64_t EstScheduler::step_period_us() const`, `reference/hal/est_scheduler.h:65`. -/
def step_period_us (s : State) : UInt64 := Id.run do
  return s._step_period

end EstScheduler

/-- C++ `const uint8_t EST_EV_BARO_INIT`, `reference/hal/est_input.h:51`. -/
def EST_EV_BARO_INIT : UInt8 := Int8.toUInt8 (Int32.toInt8 (1 : Int32))

namespace EstScheduler

/-- C++ `void EstScheduler::note_event(uint8_t ev)`, `reference/hal/est_scheduler.h:72`. -/
def note_event (s : State) (ev : UInt8) : State := Id.run do
  let mut s := s
  s := { s with _events := Int8.toUInt8 (Int32.toInt8 (UInt32.toInt32 (UInt8.toUInt32 s._events) ||| UInt32.toInt32 (UInt8.toUInt32 ev))) }
  return s

end EstScheduler

/-- C++ `const uint8_t EST_MAX_PROCS`, `reference/hal/est_scheduler.h:28`. -/
def EST_MAX_PROCS : UInt8 := Int8.toUInt8 (Int32.toInt8 (8 : Int32))

namespace EstScheduler

/-- C++ `void EstScheduler::register_timer_process(AP_HAL::MemberProc proc)`, `reference/hal/est_scheduler.cpp:206-216`. -/
def register_timer_process (s : State) (proc : WFun) : State := Id.run do
  let mut s := s
  let t'1 : UInt8 := Int8.toUInt8 (Int32.toInt8 (0 : Int32))
  let t'2 : Int32 := UInt32.toInt32 (UInt8.toUInt32 s._num_timer)
  for i' in [0:(t'2.toInt - (Int.ofNat t'1.toNat)).toNat] do  -- C++ loop bounded by a runtime value (--runtime-loops)
    let i : UInt8 := t'1 + Nat.toUInt8 i'
    if s._timer_proc[UInt8.toNat i]! == proc then
      return s
  if UInt32.toInt32 (UInt8.toUInt32 s._num_timer) < UInt32.toInt32 (UInt8.toUInt32 Estimator_lib.EST_MAX_PROCS) then
    let t'3 := s._num_timer
    s := { s with _num_timer := s._num_timer + (1 : UInt8) }
    s := { s with _timer_proc := s._timer_proc.set! (UInt8.toNat t'3) proc }
  return s

end EstScheduler

/-- C++ `const uint8_t EST_EV_BARO_UPDATE`, `reference/hal/est_input.h:52`. -/
def EST_EV_BARO_UPDATE : UInt8 := Int8.toUInt8 (Int32.toInt8 (2 : Int32))

/-- C++ `const uint8_t EST_EV_COMPASS_INIT`, `reference/hal/est_input.h:53`. -/
def EST_EV_COMPASS_INIT : UInt8 := Int8.toUInt8 (Int32.toInt8 (4 : Int32))

namespace EstUART

/-- C++ `uint32_t EstUART::get_baud_rate() const`, `reference/hal/est_uart.h:21`. -/
def get_baud_rate (s : State) : UInt32 := Id.run do
  return s.baud

/-- C++ `void EstUART::_begin(uint32_t b, uint16_t rxSpace, uint16_t txSpace)`, `reference/hal/est_uart.cpp:5-14`. -/
def _begin (s : State) (b : UInt32) (rxSpace : UInt16) (txSpace : UInt16) : State := Id.run do
  let mut s := s
  if b == Int32.toUInt32 (0 : Int32) && UInt32.toInt32 (UInt16.toUInt32 rxSpace) == (0 : Int32) && UInt32.toInt32 (UInt16.toUInt32 txSpace) == (0 : Int32) then
    return s
  if b != Int32.toUInt32 (0 : Int32) then
    s := { s with baud := b }
  s := { s with initialized := true }
  return s

/-- C++ `void AP_HAL::UARTDriver::begin(uint32_t baud, uint16_t rxSpace, uint16_t txSpace)`, `AP_HAL/UARTDriver.cpp:7-14` (a member of `AP_HAL::UARTDriver`, translated for `EstUART`). -/
def begin_uint32_t_uint16_t2 (s : State) (baud : UInt32) (rxSpace : UInt16) (txSpace : UInt16) : State := Id.run do
  let mut s := s
  if s.lock_write_key != Int32.toUInt32 (0 : Int32) then
    return s
  s := _begin s baud rxSpace txSpace
  return s

/-- C++ `uint32_t EstUART::_available()`, `reference/hal/est_uart.h:32`. -/
def _available : UInt32 := Id.run do
  return Int32.toUInt32 (0 : Int32)

/-- C++ `uint32_t AP_HAL::UARTDriver::available()`, `AP_HAL/UARTDriver.cpp:125-131` (a member of `AP_HAL::UARTDriver`, translated for `EstUART`). -/
def available (s : State) : UInt32 := Id.run do
  if s.lock_read_key != Int32.toUInt32 (0 : Int32) then
    return Int32.toUInt32 (0 : Int32)
  return _available

/-- C++ `int16_t EstUART::read()`, `reference/hal/est_uart.h:24`. -/
def read_void : Int16 := Id.run do
  return Int32.toInt16 (-(1 : Int32))

end EstUART

namespace EstScheduler

/-- C++ `bool EstScheduler::gps_pending() const`, `reference/hal/est_scheduler.h:69`. -/
def gps_pending (s : State) : Bool := Id.run do
  return s._gps_pending

end EstScheduler

namespace EstScheduler

/-- C++ `EstRecord EstScheduler::gps_take()`, `reference/hal/est_scheduler.h:70`. -/
def gps_take (s : State) : State × EstRecord := Id.run do
  let mut s := s
  s := { s with _gps_pending := false }
  return (s, s._gps)

end EstScheduler

/-- C++ `const uint8_t EST_EV_INS_INIT`, `reference/hal/est_input.h:54`. -/
def EST_EV_INS_INIT : UInt8 := Int8.toUInt8 (Int32.toInt8 (8 : Int32))

namespace EstScheduler

/-- C++ `uint16_t EstScheduler::imu_rate_hz() const`, `reference/hal/est_scheduler.h:75`. -/
def imu_rate_hz (s : State) : UInt16 := Id.run do
  return s._imu_rate_hz

end EstScheduler

namespace EstScheduler

/-- C++ `bool EstScheduler::feed(const EstRecord & r)`, `reference/hal/est_scheduler.cpp:10-20`. -/
def feed (s : State) (r : EstRecord) : State × Bool := Id.run do
  let mut s := s
  if UInt32.toInt32 (UInt16.toUInt32 s._count) ≥ UInt32.toInt32 (UInt16.toUInt32 Estimator_lib.EST_MAX_RECORDS) then
    return (s, false)
  s := { s with _recs := s._recs.set! (Int32.toNatClampNeg ((UInt32.toInt32 (UInt16.toUInt32 s._head) + UInt32.toInt32 (UInt16.toUInt32 s._count)) % UInt32.toInt32 (UInt16.toUInt32 Estimator_lib.EST_MAX_RECORDS))) r }
  s := { s with _count := s._count + (1 : UInt16) }
  s := { s with _fed_t_us := r.t_us }
  s := { s with _exhausted := false }
  return (s, true)

/-- C++ `bool EstScheduler::feed_line(uint16_t dt_us, uint8_t n0, float ax0, float ay0, float az0, float gx0, float gy0, float gz0, float ax1, float ay1, float az1, float gx1, float gy1, float gz1, float ax2, float ay2, float az2, float gx2, float gy2, float gz2, bool baro, float pa, float degc, bool mag, float mx, float my, float mz, bool gps, double lat, double lon, double alt, double vn, double ve, double vd)`, `reference/hal/est_scheduler.cpp:22-51`. -/
def feed_line (s : State) (dt_us : UInt16) (n0 : UInt8) (ax0 : Binary32) (ay0 : Binary32) (az0 : Binary32) (gx0 : Binary32) (gy0 : Binary32) (gz0 : Binary32) (ax1 : Binary32) (ay1 : Binary32) (az1 : Binary32) (gx1 : Binary32) (gy1 : Binary32) (gz1 : Binary32) (ax2 : Binary32) (ay2 : Binary32) (az2 : Binary32) (gx2 : Binary32) (gy2 : Binary32) (gz2 : Binary32) (baro : Bool) (pa : Binary32) (degc : Binary32) (mag : Bool) (mx : Binary32) (my : Binary32) (mz : Binary32) (gps' : Bool) (lat : Binary64) (lon : Binary64) (alt : Binary64) (vn : Binary64) (ve : Binary64) (vd : Binary64) : State × Bool := Id.run do
  let mut s := s
  let mut r : EstRecord := { t_us := (0 : UInt64), imu_n := Array.replicate 2 (0 : UInt8), accel := Array.replicate 16 { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, gyro := Array.replicate 16 { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, baro := false, baro_pa := (Binary32.ofBits 0x00000000 /- 0.0 -/), baro_degc := (Binary32.ofBits 0x00000000 /- 0.0 -/), mag := false, mag_mgauss := { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, gps := false, gps_lat_deg := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_lon_deg := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_alt_m := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_vn := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_ve := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_vd := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
  let last : UInt64 := if s._fed_t_us > s._clock_us then s._fed_t_us else s._clock_us
  r := { r with t_us := last + UInt16.toUInt64 dt_us + Int64.toUInt64 (Int32.toInt64 (1 : Int32)) }
  r := { r with imu_n := r.imu_n.set! 0 (Int8.toUInt8 (Int32.toInt8 (if UInt32.toInt32 (UInt8.toUInt32 n0) > (3 : Int32) then (3 : Int32) else UInt32.toInt32 (UInt8.toUInt32 n0)))) }
  r := { r with accel := r.accel.set! 0 (Vector3f.init_float3 ax0 ay0 az0) }
  r := { r with gyro := r.gyro.set! 0 (Vector3f.init_float3 gx0 gy0 gz0) }
  r := { r with accel := r.accel.set! 1 (Vector3f.init_float3 ax1 ay1 az1) }
  r := { r with gyro := r.gyro.set! 1 (Vector3f.init_float3 gx1 gy1 gz1) }
  r := { r with accel := r.accel.set! 2 (Vector3f.init_float3 ax2 ay2 az2) }
  r := { r with gyro := r.gyro.set! 2 (Vector3f.init_float3 gx2 gy2 gz2) }
  r := { r with baro := baro }
  r := { r with baro_pa := pa }
  r := { r with baro_degc := degc }
  r := { r with mag := mag }
  r := { r with mag_mgauss := Vector3f.init_float3 mx my mz }
  r := { r with gps := gps' }
  r := { r with gps_lat_deg := lat }
  r := { r with gps_lon_deg := lon }
  r := { r with gps_alt_m := alt }
  r := { r with gps_vn := vn }
  r := { r with gps_ve := ve }
  r := { r with gps_vd := vd }
  let (t'1, t'2) := feed s r
  s := t'1
  return (s, t'2)

/-- C++ `uint16_t EstScheduler::feed_baro_lines(uint16_t n, uint8_t k, float pa, float dpa, float degc)`, `reference/hal/est_scheduler.cpp:53-69`. -/
def feed_baro_lines (s : State) (n : UInt16) (k : UInt8) (pa : Binary32) (dpa : Binary32) (degc : Binary32) : State × UInt16 := Id.run do
  let mut s := s
  let mut fed : UInt16 := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
  for i' in [0:n.toNat] do
    let i : UInt16 := Nat.toUInt16 i'
    let mut r : EstRecord := { t_us := (0 : UInt64), imu_n := Array.replicate 2 (0 : UInt8), accel := Array.replicate 16 { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, gyro := Array.replicate 16 { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, baro := false, baro_pa := (Binary32.ofBits 0x00000000 /- 0.0 -/), baro_degc := (Binary32.ofBits 0x00000000 /- 0.0 -/), mag := false, mag_mgauss := { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, gps := false, gps_lat_deg := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_lon_deg := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_alt_m := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_vn := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_ve := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_vd := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
    let last : UInt64 := if s._fed_t_us > s._clock_us then s._fed_t_us else s._clock_us
    r := { r with t_us := last + Int64.toUInt64 (Int32.toInt64 (2500 : Int32)) }
    r := { r with baro := decide (UInt32.toInt32 (UInt8.toUInt32 k) > (0 : Int32)) && UInt32.toInt32 (UInt16.toUInt32 i) % UInt32.toInt32 (UInt8.toUInt32 k) == (0 : Int32) }
    r := { r with baro_pa := pa + UInt16.toBinary32 i * dpa }
    r := { r with baro_degc := degc }
    let (t'1, t'2) := feed s r
    s := t'1
    if !t'2 then
      break
    fed := fed + (1 : UInt16)
  return (s, fed)

/-- C++ `uint16_t EstScheduler::feed_imu_lines(uint16_t n, uint8_t k, float ax, float ay, float az, float gx, float gy, float gz, float pa, float degc)`, `reference/hal/est_scheduler.cpp:71-94`. -/
def feed_imu_lines (s : State) (n : UInt16) (k : UInt8) (ax : Binary32) (ay : Binary32) (az : Binary32) (gx : Binary32) (gy : Binary32) (gz : Binary32) (pa : Binary32) (degc : Binary32) : State × UInt16 := Id.run do
  let mut s := s
  let mut fed : UInt16 := Int16.toUInt16 (Int32.toInt16 (0 : Int32))
  for i' in [0:n.toNat] do
    let i : UInt16 := Nat.toUInt16 i'
    let mut r : EstRecord := { t_us := (0 : UInt64), imu_n := Array.replicate 2 (0 : UInt8), accel := Array.replicate 16 { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, gyro := Array.replicate 16 { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, baro := false, baro_pa := (Binary32.ofBits 0x00000000 /- 0.0 -/), baro_degc := (Binary32.ofBits 0x00000000 /- 0.0 -/), mag := false, mag_mgauss := { x := (Binary32.ofBits 0x00000000 /- 0.0 -/), y := (Binary32.ofBits 0x00000000 /- 0.0 -/), z := (Binary32.ofBits 0x00000000 /- 0.0 -/) }, gps := false, gps_lat_deg := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_lon_deg := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_alt_m := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_vn := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_ve := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/), gps_vd := (Binary64.ofBits 0x0000000000000000 /- 0.0 -/) }
    let last : UInt64 := if s._fed_t_us > s._clock_us then s._fed_t_us else s._clock_us
    r := { r with t_us := last + Int64.toUInt64 (Int32.toInt64 (2500 : Int32)) }
    for m' in [0:2] do
      let m : UInt8 := Nat.toUInt8 m'
      r := { r with imu_n := r.imu_n.set! (UInt8.toNat m) (Int8.toUInt8 (Int32.toInt8 (3 : Int32))) }
      for j' in [0:3] do
        let j : UInt8 := Nat.toUInt8 j'
        r := { r with accel := r.accel.set! (Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 m) * UInt32.toInt32 (UInt8.toUInt32 Estimator_lib.EST_MAX_IMU_SAMPLES) + UInt32.toInt32 (UInt8.toUInt32 j))) (Vector3f.init_float3 ax ay az) }
        r := { r with gyro := r.gyro.set! (Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 m) * UInt32.toInt32 (UInt8.toUInt32 Estimator_lib.EST_MAX_IMU_SAMPLES) + UInt32.toInt32 (UInt8.toUInt32 j))) (Vector3f.init_float3 gx gy gz) }
    r := { r with baro := decide (UInt32.toInt32 (UInt8.toUInt32 k) > (0 : Int32)) && UInt32.toInt32 (UInt16.toUInt32 i) % UInt32.toInt32 (UInt8.toUInt32 k) == (0 : Int32) }
    r := { r with baro_pa := pa }
    r := { r with baro_degc := degc }
    let (t'1, t'2) := feed s r
    s := t'1
    if !t'2 then
      break
    fed := fed + (1 : UInt16)
  return (s, fed)

/-! Not emitted, since they have no effect in the model (they write neither the state, the
parameters nor a reference parameter; e.g. they only save parameters):
- C++ `void AP_HAL::Scheduler::boost_end()`, `AP_HAL/Scheduler.h:49` (a member of `AP_HAL::Scheduler`, translated for `EstScheduler`).
-/

end EstScheduler

end Estimator_lib
