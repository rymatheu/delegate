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

/-- `AP_SerialManager::find_serial(protocol, i)` / `find_protocol_instance` for the vehicle: GCSMemory's MAVLink ports
(SERIAL0-2) for the MAVLink protocols (1, 2), none for any other protocol (RC input, GPS, ...: no SERIALn_PROTOCOL of
the images names them) -/
def findSerialProto (proto : Int32) (inst : UInt8) : M UInt64 :=
  if proto == 1 || proto == 2 then findSerial inst else return 0

/-- The vehicle's HAL (configuration key `hal_hook`): a call of a HAL member outside the boundary, with the object's
address and the arguments as 64-bit words (floats as their bits, records by address), its result as a 64-bit word.
lockstep.cpp's semantics (reference/hal/lockstep.cpp: the scheduler's delays consuming input lines, RCInput,
RCOutput, AnalogIn, Util) are implemented by the replay driver, which can call the translated vehicle back (the IO
processes, the delay callback, the timer failsafe); the driver defines the C symbol (`@[export]`), the forward
declaration's usual pattern. -/
@[extern "cpp2lean_vehicle_hal"]
opaque halImpl : String → UInt64 → Array UInt64 → Mem → UInt64 × Mem

@[inline] def hal (name : String) (this : UInt64) (args : Array UInt64) : M UInt64 :=
  fun s => halImpl name this args s

/-- The HAL clock (`AP_HAL::micros64`): the estimator World's, which consumes the same input lines (lockstep.cpp's
clock, set from each consumed line; 1 before the first, as SITL's) -/
@[inline] def clock : M UInt64 := return (← get).w.est_scheduler._clock_us

end PMem
