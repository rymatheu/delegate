import ArduLean.Runtime.Memory

/-!
ArduPilot `libraries/AP_NavEKF`. Sources: `libraries/AP_NavEKF/AP_Nav_Common.h`.

Items of `lean/Vehicle_lib.lean` (the vehicle translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Vehicle/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Vehicle_lib

/-- `nav_filter_status.nav_filter_status` as a pure function of its arguments (it reads and writes no memory). -/
def nav_filter_status.nav_filter_status.pure' (this : UInt64) : Id Unit := do
  return ()

/-- C++ `nav_filter_status::nav_filter_status : void () noexcept`, `AP_Nav_Common.h:?-?`. -/
def nav_filter_status.nav_filter_status (this : UInt64) : PMem.M Unit :=
  pure (_root_.Vehicle_lib.nav_filter_status.nav_filter_status.pure' this)

end Vehicle_lib
