import Harness.Compose
import px4.harnesses.px4_chain.Discharges
import sim.modules.plant_sim.Module
import px4.modules.px4_sim_in.Module
import px4.modules.px4_sensors.Module
import px4.modules.px4_rate.Module
import px4.modules.px4_alloc.Module
import px4.modules.px4_sim_out.Module

/-! # px4_closed_rate: PX4's rate loop closed around the gorge simulator

The PX4 counterpart of `closed_inner`, in one tick: the simulator (`plant_sim`), the sensor bridge
(`px4_sim_in`), PX4's `sensors` (gyro to `vehicle_angular_velocity`), PX4's rate controller, PX4's
control allocator, the motor bridge (`px4_sim_out`), whose four PWMs feed the simulator at the next
tick (`prev`, 1000 at the first). Wired by name only: no `rename`. The clock `t_us` of every PX4
module is the simulator's. The rate setpoint, the thrust, the arming and mode topics remain inputs.
Rate control only: nothing commands attitude. -/

namespace Px4.Harnesses.Px4ClosedRate

open Harness Harness.Contract.Lang

def simOut (_ : Unit := ()) : Except String Node :=
  withInit (.module Px4.Modules.Px4SimOut.module)
    [("pwm0", .u32 1000), ("pwm1", .u32 1000), ("pwm2", .u32 1000), ("pwm3", .u32 1000)]

/-- plant_sim's IMU at its default full scale (`imu_acc_fs_g` = 0: 16 g, `imu_gyro_fs_dps` = 0:
2000 deg/s, sim/modules/plant_sim), in every regime of a PX4 composite with the simulator. The two
parameters came with the simulator's IMU clipping (main, 2026-11-18), after these regimes were
written; left free, a campaign could draw a 2 g accelerometer, which the flights these regimes
describe would saturate. A regime clause, not an assumption: the composite's contract still
admits every full scale plant_sim admits. -/
def imuDefaults : Clause :=
  ⟨"imu_full_scale_default", "imu_acc_fs_g" =. 0 ∧. "imu_gyro_fs_dps" =. 0⟩

/-- The system with `imuDefaults` in each of its regimes (when it has plant_sim's parameters). -/
def withImuDefaults (n : Node) : Node :=
  match n with
  | .system s =>
    if n.view.params.any (·.name == "imu_acc_fs_g") then
      .system { s with regimes := s.regimes.map fun r =>
        { r with clauses := r.clauses ++ [imuDefaults] } }
    else n
  | m => m

/-- The X500 hovering under rate control: PX4's defaults, the SITL sensor ids and the X500
airframe; armed, rate control and allocation on, a rate setpoint every tick within 0.2 rad/s and
a thrust along -z near hover; no land detector, battery, manual or failure messages; no noise. -/
def x500Hover : Regime where
  name := "x500_hover"
  doc := "X500 under PX4 rate control, armed, small rate setpoints, thrust near hover"
  clauses := Px4.Modules.Px4Sensors.sitlParams ++ Px4.Modules.Px4Rate.Ports.paramDefaults ++
    Px4.Modules.Px4Alloc.x500Params ++ [
    ⟨"no_noise", "noise_on" =. ff⟩,
    ⟨"mode", "vehicle_control_mode_updated" ∧. "vehicle_control_mode_flag_armed" ∧.
      "vehicle_control_mode_flag_control_rates_enabled" ∧.
      "vehicle_control_mode_flag_control_allocation_enabled" ∧.
      ¬. "vehicle_control_mode_flag_control_manual_enabled"⟩,
    ⟨"status", "vehicle_status_updated" ∧. "vehicle_status_vehicle_type" =. 1 ∧.
      "vehicle_status_arming_state" =. 2 ∧. ¬. "vehicle_status_is_vtol"⟩,
    ⟨"setpoint", "vehicle_rates_setpoint_updated" ∧. abs "vehicle_rates_setpoint_roll" ≤. 0.2 ∧.
      abs "vehicle_rates_setpoint_pitch" ≤. 0.2 ∧. abs "vehicle_rates_setpoint_yaw" ≤. 0.2 ∧.
      "vehicle_rates_setpoint_thrust_body_0" =. 0 ∧. "vehicle_rates_setpoint_thrust_body_1" =. 0 ∧.
      -0.7 ≤. "vehicle_rates_setpoint_thrust_body_2" ∧. "vehicle_rates_setpoint_thrust_body_2" ≤. -0.5⟩,
    ⟨"quiet", ¬. "vehicle_land_detected_updated" ∧. ¬. "battery_status_updated" ∧.
      ¬. "manual_control_setpoint_updated" ∧. ¬. "failure_detector_status_updated"⟩]

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_closed_rate"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4SimIn.module,
     .module Px4.Modules.Px4Sensors.module, .module Px4.Modules.Px4Rate.module,
     .module Px4.Modules.Px4Alloc.module, ← simOut]
  let n := Px4.Harnesses.Chain.withGlue n
  return withImuDefaults (withRegime n x500Hover)

end Px4.Harnesses.Px4ClosedRate
