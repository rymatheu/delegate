import ArduLean.Runtime.Memory

/-!
ArduPilot `libraries/AP_RTC`. Sources: `libraries/AP_RTC/JitterCorrection.cpp`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- C++ `JitterCorrection::JitterCorrection : void (uint16_t, uint16_t)`, `JitterCorrection.cpp:39-42`. -/
def JitterCorrection.JitterCorrection (this : UInt64) (_max_lag_ms : UInt16) (_convergence_loops : UInt16) : PMem.M Unit := do
  let mut _max_lag_ms := _max_lag_ms
  let mut _convergence_loops := _convergence_loops
  PMem.stU16 (this + 0) _max_lag_ms
  PMem.stU16 (this + 2) _convergence_loops
  return ()

end Vehicle_lib
