import AP_Math

/-!
# `Thrust_Linearization`

Mirrors, at ArduPilot 802db19de1, `libraries/AP_Motors/AP_Motors_Thrust_Linearization.h:7-64`
and `AP_Motors_Thrust_Linearization.cpp:90-133` (constructor, `thrust_to_actuator`,
`apply_thrust_curve_and_volt_scaling`), `:155-167` (`update_lift_max_from_batt_voltage`, reduced,
see below) and `:188-206` (`get_compensation_gain`).

In the Copter build the parameters are registered by `AP_MotorsMulticopter::var_info` under the
`MOT_` names (`AP_MotorsMulticopter.cpp:57` `THST_EXPO`, `:65` `SPIN_MAX`, `:74` `BAT_VOLT_MAX`,
`:83` `BAT_VOLT_MIN`, `:129` `SPIN_MIN`), with the defaults of `AP_MotorsMulticopter.h:13-22`; the
class's own table (`.cpp:38-88`) is only loaded for Heli (`.cpp:98-100`). `Params` carries those
names; `AP_MotorsMulticopter.Params` extends it.

`AP_MOTORS_DENSITY_COMP` is 1 outside `APM_BUILD_UNKNOWN` (`.cpp:11-18`), so
`get_compensation_gain` divides by the AHRS air density ratio. That ratio is an input here: in
SITL it is `1/EAS2TAS²` from the barometer, about 0.94 at the default home altitude, so the gain
is not 1 there.

Left out:
- the battery-voltage path of `update_lift_max_from_batt_voltage` (`.cpp:161`, `:169-184`). The
  port is the early exit at `:163-167`, which `MOT_BAT_VOLT_MAX ≤ 0` (the code default,
  `AP_MotorsMulticopter.h:21`) selects whatever the voltage reading is; `Faithful` states it.
  Note that SITL's `Tools/autotest/default_params/copter.parm:72-73` sets
  `MOT_BAT_VOLT_MIN 9.6`, `MOT_BAT_VOLT_MAX 12.8`, which turns compensation on; an oracle run
  must set `MOT_BAT_VOLT_MAX 0`;
- `actuator_to_thrust`, `remove_thrust_curve_and_volt_scaling` (`.cpp:110-116`, `:135-153`): used
  by `get_thrust` (tailsitter transitions, logging), not by the output path;
- `MOT_BAT_IDX`, `get_battery_index`, the private `throttle_limit` (never read), `var_info`.
-/

namespace Thrust_Linearization

open AP_Math

/-- The `Thrust_Linearization` parameters (`AP_Motors_Thrust_Linearization.h:51-56`) under their
`MOT_` names, Copter defaults (`AP_MotorsMulticopter.h:13`, `:18`, `:19`, `:21`, `:22`). -/
structure Params where
  /-- `curve_expo`. -/
  MOT_THST_EXPO : ftype := 0.65
  /-- `spin_min`. -/
  MOT_SPIN_MIN : ftype := 0.15
  /-- `spin_max`. -/
  MOT_SPIN_MAX : ftype := 0.95
  /-- `batt_voltage_max`. -/
  MOT_BAT_VOLT_MAX : ftype := 0.0
  /-- `batt_voltage_min`. -/
  MOT_BAT_VOLT_MIN : ftype := 0.0
  deriving Repr

/-- Private members (`AP_Motors_Thrust_Linearization.h:59-61`), with the constructor's values
(`.cpp:90-96`: `lift_max(1.0)`, `batt_voltage_filt.reset(1.0)`). -/
structure State where
  lift_max : ftype := 1.0
  /-- Output of the `LowPassFilterFloat batt_voltage_filt` (0.5 Hz; only its value is read here). -/
  batt_voltage_filt : ftype := 1.0
  deriving Repr

/-- The configuration under which `update_lift_max_from_batt_voltage` is the C++. -/
structure Faithful (p : Params) : Prop where
  bat_volt_max_off : p.MOT_BAT_VOLT_MAX ≤ 0

/-- `get_spin_min` (`.h:33`). -/
def get_spin_min (p : Params) : ftype := p.MOT_SPIN_MIN
/-- `get_spin_max` (`.h:36`). -/
def get_spin_max (p : Params) : ftype := p.MOT_SPIN_MAX
/-- `get_battery_min_voltage` (`.h:42`). -/
def get_battery_min_voltage (p : Params) : ftype := p.MOT_BAT_VOLT_MIN
/-- `get_lift_max` (`.h:45`). -/
def get_lift_max (s : State) : ftype := s.lift_max

/-- `apply_thrust_curve_and_volt_scaling(thrust)` (`.cpp:119-133`): inverts
`thrust = (1-e)·u + e·u²` for `u`, then applies the battery scale. -/
def apply_thrust_curve_and_volt_scaling (p : Params) (s : State) (thrust : ftype) : ftype := Id.run do
  let mut battery_scale : ftype := 1.0
  if is_positive s.batt_voltage_filt then
    battery_scale := 1.0 / s.batt_voltage_filt
  -- apply thrust curve - domain -1.0 to 1.0, range -1.0 to 1.0
  let thrust_curve_expo := constrain_float p.MOT_THST_EXPO (-1.0) 1.0
  if is_zero thrust_curve_expo then
    -- zero expo means linear, avoid floating point exception for small values
    return s.lift_max * thrust * battery_scale
  let throttle_ratio := ((thrust_curve_expo - 1.0) + safe_sqrt ((1.0 - thrust_curve_expo) * (1.0 - thrust_curve_expo) + 4.0 * thrust_curve_expo * s.lift_max * thrust)) / (2.0 * thrust_curve_expo)
  return constrain_float (throttle_ratio * battery_scale) 0.0 1.0

/-- `thrust_to_actuator(thrust_in)` (`.cpp:104-108`). -/
def thrust_to_actuator (p : Params) (s : State) (thrust_in : ftype) : ftype :=
  let thrust_in := constrain_float thrust_in 0.0 1.0
  p.MOT_SPIN_MIN + (p.MOT_SPIN_MAX - p.MOT_SPIN_MIN) * apply_thrust_curve_and_volt_scaling p s thrust_in

/-- `update_lift_max_from_batt_voltage()` (`.cpp:156-186`), the branch at `:163-167`
(`batt_voltage_filt.reset(1.0); lift_max = 1.0;`). Under `Faithful` (`MOT_BAT_VOLT_MAX ≤ 0`) the
C++ takes this branch on every call, whatever the battery reading; for `MOT_BAT_VOLT_MAX > 0` this
function is not the C++, because the battery voltage is not modelled. -/
def update_lift_max_from_batt_voltage (_p : Params) (s : State) : State :=
  { s with batt_voltage_filt := 1.0, lift_max := 1.0 }

/-- `get_compensation_gain()` (`.cpp:189-206`) with `AP_MOTORS_DENSITY_COMP == 1`;
`air_density_ratio` is `AP::ahrs().get_air_density_ratio()` (`AP_AHRS.cpp:2134-2138`). -/
def get_compensation_gain (s : State) (air_density_ratio : ftype) : ftype := Id.run do
  -- avoid divide by zero
  if get_lift_max s ≤ 0.0 then
    return 1.0
  let mut ret : ftype := 1.0 / get_lift_max s
  -- air density ratio is increasing in density / decreasing in altitude
  if air_density_ratio > 0.3 && air_density_ratio < 1.5 then
    ret := ret * (1.0 / constrain_float air_density_ratio 0.5 1.25)
  return ret

end Thrust_Linearization
