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
import ArduLean.Estimator.World_3
import ArduLean.Estimator.libraries.AP_RTC.AP_RTC_2
import ArduLean.Estimator.libraries.AP_GPS.AP_GPS_2
import ArduLean.Estimator.libraries.AP_AHRS.AP_AHRS_2
import ArduLean.Estimator.libraries.AP_NavEKF3.AP_NavEKF3_4
import ArduLean.Estimator.libraries.AP_Baro.AP_Baro_4

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

/-- The construction of the file-scope objects, in definition order (C++ static initialization). -/
def World.init : World := Id.run do
  let mut w : World := {}
  let (t's, t'w) := NavEKF3.init w
  w := { t'w with EKF3 := t's }
  w := { w with sitl := SITL.SIM.init }
  w := { w with barometer := AP_Baro.construct }
  w := { w with compass := Compass.construct }
  w := { w with ins := AP_InertialSensor.construct }
  w := { w with gps := AP_GPS.construct }
  w := { w with rtc := AP_RTC.init }
  let t's := AP_AHRS.construct w w.ahrs'inp (Int8.toUInt8 (Int32.toInt8 (0 : Int32)))
  w := { w with ahrs := t's }
  return w

end Estimator_lib
