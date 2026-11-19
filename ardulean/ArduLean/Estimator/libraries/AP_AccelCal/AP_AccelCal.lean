import ArduLean.Runtime.CFloat

/-!
ArduPilot `libraries/AP_AccelCal`. Sources: `libraries/AP_AccelCal/AccelCalibrator.h`.

Items of `lean/Estimator_lib.lean` (the estimator translation), unchanged; placed by `tools/split_modules.py` (`ArduLean/Estimator/INDEX.md`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option maxRecDepth 200000
-- AP_DAL's `const log_RISH old_RISH = _RISH;` read only by WRITE_REPLAY_BLOCK_IFCHANGED, which is `(void)old`
-- without logging (HAL_LOGGING_ENABLED 0): an unused binding, as in the C++
set_option linter.unusedVariables false

namespace Estimator_lib

/-- C++ `enum accel_cal_status_t`, `AP_AccelCal/AccelCalibrator.h:21-27`. -/
inductive accel_cal_status_t where
  | ACCEL_CAL_NOT_STARTED
  | ACCEL_CAL_WAITING_FOR_ORIENTATION
  | ACCEL_CAL_COLLECTING_SAMPLE
  | ACCEL_CAL_SUCCESS
  | ACCEL_CAL_FAILED
deriving DecidableEq, Inhabited

/-- The value of each enumerator of `accel_cal_status_t` (underlying type `uint32_t`). -/
def accel_cal_status_t.toInt : accel_cal_status_t → UInt32
  | .ACCEL_CAL_NOT_STARTED => (0 : UInt32)
  | .ACCEL_CAL_WAITING_FOR_ORIENTATION => (1 : UInt32)
  | .ACCEL_CAL_COLLECTING_SAMPLE => (2 : UInt32)
  | .ACCEL_CAL_SUCCESS => (3 : UInt32)
  | .ACCEL_CAL_FAILED => (4 : UInt32)

end Estimator_lib
