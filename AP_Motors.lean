import AP_Motors.Interface
import AP_Motors.AP_Motors_Thrust_Linearization
import AP_Motors.AP_MotorsMulticopter
import AP_Motors.AP_MotorsMatrix

/-!
# `AP_Motors`

Lean port of ArduPilot `libraries/AP_Motors` (see PORT.md), quad X on the armed,
`THROTTLE_UNLIMITED` path. See the header of each submodule for the C++ line ranges mirrored and
what is left out.

- `AP_Motors.Interface`: the controller-facing inputs, `limit` flags and throttle accessors.
- `AP_Motors.AP_Motors_Thrust_Linearization`: `thrust_to_actuator`, the thrust curve, the
  compensation gain.
- `AP_Motors.AP_MotorsMulticopter`: `MOT_` parameters, throttle filter, `output_logic`
  (`THROTTLE_UNLIMITED`), `set_actuator_with_slew`, `update_throttle_hover`.
- `AP_Motors.AP_MotorsMatrix`: quad X factors, `output_armed_stabilizing`, `output_to_motors`, and
  the per-tick `AP_MotorsMatrix.output : Params → State → State × Vector ftype 4`.

`AP_Motors.MotorsCheck` (not imported) prints three cases: `lake env lean --run AP_Motors/MotorsCheck.lean`.
-/
