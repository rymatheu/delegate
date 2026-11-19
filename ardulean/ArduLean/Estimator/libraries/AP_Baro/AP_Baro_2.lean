import ArduLean.Runtime.CFloat
import ArduLean.Estimator.World
import ArduLean.Estimator.libraries.AP_Math.AP_Math_2

/-!
ArduPilot `libraries/AP_Baro`, part 2 of 4. Sources: `libraries/AP_Baro/AP_Baro_SITL.h`, `libraries/AP_Baro/AP_Baro_Backend.cpp`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

namespace AP_Baro_SITL

/-- State of C++ `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:11-53`): its data members; base classes flattened, base first: `AP_Baro_Backend`. -/
structure State where
  /-- `float _mean_pressure` of `AP_Baro_Backend` (`AP_Baro/AP_Baro_Backend.h:74`). -/
  _mean_pressure : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t _error_count` of `AP_Baro_Backend` (`AP_Baro/AP_Baro_Backend.h:76`). -/
  _error_count : UInt32 := (0 : UInt32)
  /-- `uint8_t _instance` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:28`). -/
  _instance : UInt8 := (0 : UInt8)
  /-- `SITL::SIM * _sitl` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:29`). -/
  _sitl : WPtr := WPtr.null
  /-- `uint8_t _store_index` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:36`). -/
  _store_index : UInt8 := (0 : UInt8)
  /-- `uint32_t _last_store_time` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:37`). -/
  _last_store_time : UInt32 := (0 : UInt32)
  /-- `VectorN<readings_baro, _buffer_length> _buffer` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:39`). -/
  _buffer : VectorN_AP_Baro_SITL_readings_baro_50.State := VectorN_AP_Baro_SITL_readings_baro_50.init_void
  /-- `bool _has_sample` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:45`). -/
  _has_sample : Bool := false
  /-- `uint32_t _last_sample_time` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:46`). -/
  _last_sample_time : UInt32 := (0 : UInt32)
  /-- `float _recent_temp` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:47`). -/
  _recent_temp : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _recent_press` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:48`). -/
  _recent_press : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `float _last_altitude` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:49`). -/
  _last_altitude : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
  /-- `uint32_t last_drift_delta_t_ms` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:51`). -/
  last_drift_delta_t_ms : UInt32 := (0 : UInt32)
  /-- `float total_alt_drift` of `AP_Baro_SITL` (`AP_Baro/AP_Baro_SITL.h:52`). -/
  total_alt_drift : Binary32 := (Binary32.ofBits 0x00000000 /- 0.0 -/)
deriving Inhabited

end AP_Baro_SITL

namespace AP_Baro_SITL

/-- C++ `AP_Baro_Backend::AP_Baro_Backend(class AP_Baro & baro)`, `AP_Baro/AP_Baro_Backend.cpp:18-21` (a member of `AP_Baro_Backend`, translated for `AP_Baro_SITL`). -/
def AP_Baro_Backend.init (s : State) : State := Id.run do
  let mut s := s
  return s

end AP_Baro_SITL

end Estimator_lib
