import ParamMemory
import GCSMemory

/-!
Written by hand for cpp2lean; copied by `cpp2lean.py --param-memory` next to a translation whose configuration
names it (`imports`: the vehicle translation, `ardupilot/vehicle/Vehicle.json`). Do not edit the copies.

The two boundaries of the vehicle translation that hold no vehicle logic:

* `bridge`: a call of a function of the estimator (AP_AHRS and its back ends, NavEKF3, AP_DAL, AP_InertialSensor,
  AP_Baro, Compass, AP_GPS, AP_RTC), which stays in the value World (`Estimator_lib`); the translated call site
  records the function's name here and takes the result type's default (zero; a zeroed temporary for a record).
  `ardupilot/vehicle/bridge_calls.txt` lists every such function with its call sites: the API the bridge provides.
* `halCall`: a call of a HAL member that the configuration's boundary does not model (recorded likewise).
-/

namespace PMem

/-- A call of an estimator function (the bridge's API): recorded. -/
def bridge (name : String) : M Unit :=
  modify fun s => { s with log := s.log.push ("bridge " ++ name) }

/-- A call of a HAL member outside the modelled boundary: recorded. -/
def halCall (name : String) : M Unit :=
  modify fun s => { s with log := s.log.push ("hal " ++ name) }

end PMem
