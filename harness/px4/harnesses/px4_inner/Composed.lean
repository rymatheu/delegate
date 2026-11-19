import Harness.Compose
import px4.harnesses.px4_chain.Discharges
import px4.modules.px4_rate.Module
import px4.modules.px4_alloc.Module

/-! # px4_inner: PX4's rate controller, then its control allocator, composed by topic name

No renaming: the ports are uORB topic fields, so px4_rate's `vehicle_torque_setpoint_*` and
`vehicle_thrust_setpoint_*` feed px4_alloc's (same tick), px4_alloc's `control_allocator_status_*`
feeds px4_rate's (previous tick, as the allocator runs after the rate controller), and the
topics both read (`vehicle_status`, `vehicle_control_mode`) and the clock `t_us` are shared
inputs of the composite. -/

namespace Px4.Harnesses.Px4Inner

open Harness Harness.Contract.Lang

/-- The X500 in flight: px4_rate's stock flight (PX4 defaults, a gyro message every 400 Hz tick,
armed in rate control, moderate rates and setpoints) and the X500 airframe for the allocator, with
allocation enabled; the rate setpoint's thrust along -z within [0, 1]. -/
def x500Flight : Regime where
  name := "x500_inner_flight"
  doc := "PX4 defaults, X500 airframe, armed in rate control at 400 Hz"
  clauses := Px4.Modules.Px4Rate.stockFlight.clauses ++ Px4.Modules.Px4Alloc.x500Params ++ [
    ⟨"allocation_enabled", ¬. "vehicle_control_mode_updated" ∨.
      "vehicle_control_mode_flag_control_allocation_enabled"⟩,
    ⟨"armed_state", ¬. "vehicle_status_updated" ∨. "vehicle_status_arming_state" =. 2⟩,
    ⟨"vertical_thrust", "vehicle_rates_setpoint_thrust_body_0" =. 0 ∧. "vehicle_rates_setpoint_thrust_body_1" =. 0 ∧.
      -1 ≤. "vehicle_rates_setpoint_thrust_body_2" ∧. "vehicle_rates_setpoint_thrust_body_2" ≤. 0⟩]
  hints := Px4.Modules.Px4Rate.flight.hints

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_inner" [.module Px4.Modules.Px4Rate.module, .module Px4.Modules.Px4Alloc.module]
  let n := Px4.Harnesses.Chain.withGlue n
  return withRegime n x500Flight

end Px4.Harnesses.Px4Inner
