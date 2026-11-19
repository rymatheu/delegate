import Harness.Compose
import ardupilot.harnesses.rate.Composed
import ardupilot.modules.mixer.Module
import sim.modules.plant_sim.Module

/-! # closed_inner: the rate loop closed around the simulator

The plant (the gorge simulator's X500, `plant_sim`), then `rate_c`, then the mixer, in one tick.
The plant's gyro of the tick feeds the rate PIDs (same tick); the mixer's four PWMs feed the
plant at the next tick (`prev`, 1000 us at the first). Rate control only: nothing commands
attitude, so the vehicle is not expected to hold it.

* Gyro: `imu2_g*`, the sample after the last physics substep of the tick. sim/fly_gorge.py
  (ArduLean repository) passes all three substep samples to the vehicle, and the rate controller
  reads `get_gyro_latest()`, the most recent one.
* Motors: ArduPilot's quad-X motors 1 to 4 (front right CCW, rear left CCW, front left CW, rear
  right CW) are the plant's slots 0 to 3 in the same order (plant_sim's input docs). -/

namespace Ardupilot.Harnesses.ClosedInner

open Harness

/-- The plant with its gyro and PWM fields named as the controller's. -/
def plant (_ : Unit := ()) : Except String Node :=
  rename (.module Sim.Modules.PlantSim.module)
    [("imu2_gx", "gyro_x"), ("imu2_gy", "gyro_y"), ("imu2_gz", "gyro_z"),
     ("pwm0", "pwm_1"), ("pwm1", "pwm_2"), ("pwm2", "pwm_3"), ("pwm3", "pwm_4")]

/-- The mixer: no feed-forward, PWM range 1000 to 2000 and PWM kept while disarmed, so that the
plant's `pwm_range` can be discharged; the PWMs start at 1000. -/
def mixer (_ : Unit := ()) : Except String Node := do
  let m ← fix (.module Ardupilot.Modules.Mixer.module)
    [("roll_ff", .f32 0), ("pitch_ff", .f32 0), ("yaw_ff", .f32 0),
     ("pwm_min", .i32 1000), ("pwm_max", .i32 2000), ("safe_disarm", .bool false)]
  let m ← rename m [("internal_errors", "mixer_internal_errors")]
  withInit m [("pwm_1", .u32 1000), ("pwm_2", .u32 1000), ("pwm_3", .u32 1000),
    ("pwm_4", .u32 1000)]

/-- The closed loop, with a regime `stock_hover`: the composite's `stock_flight` (its clauses on
the gyro, now wired from the plant, are dropped by compose, the target bounds with them) plus
small rate targets and no sensor noise. -/
def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "closed_inner" [← plant, ← Ardupilot.Harnesses.RateC.system, ← mixer]
  let some r := n.view.regimes.find? (·.name == "stock_flight")
    | throw "closed_inner: no stock_flight regime"
  let v (f : String) : Expr := .var f
  return withRegime n { r with
    name := "stock_hover", doc := "stock_flight, rate targets within 0.2 rad/s, no noise",
    clauses := r.clauses ++ [
      ⟨"hover_targets", Contract.Lang.abs (v "target_x") ≤. 0.2 ∧.
        Contract.Lang.abs (v "target_y") ≤. 0.2 ∧. Contract.Lang.abs (v "target_z") ≤. 0.2⟩,
      ⟨"no_noise", v "noise_on" =. Contract.Lang.ff⟩] }

end Ardupilot.Harnesses.ClosedInner
