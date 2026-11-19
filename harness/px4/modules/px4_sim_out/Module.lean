import sim.modules.plant_sim.Module
import px4.modules.px4_alloc.Ports

/-! # px4_sim_out: PX4's motor setpoints as the gorge simulator's PWM inputs

The bridge from `actuator_motors` (control_allocator's output, normalized thrust per motor) to
plant_sim's four PWM inputs. Its input fields are px4_alloc's `actuator_motors_*` output fields, its
outputs plant_sim's input fields (both schemas are taken from those declarations), so it composes by
name. adapter.cpp, hand-written: it stands for PX4's output driver on the simulator, pwm_out_sim
(src/modules/simulation/pwm_out_sim with src/lib/mixer_module), configured as below.

* Motor order: plant_sim's slots are the X500's rotors in PX4's order (4001_gz_x500: rotor 0 front
  right CCW, 1 rear left CCW, 2 front left CW, 3 rear right CW; plant_sim's slots 0-3 the same), so
  PWM slot i = motor i (PWM_MAIN_FUNCi = Motor i).
* Thrust model: the simulator's thrust is proportional to a = (PWM - 1000)/1000; PX4's
  actuator_motors value is normalized thrust. With THR_MDL_FAC = 0 (PX4's default, mixer_module's
  FunctionMotors::updateValues applies no curve) PX4 outputs the value linearly between
  PWM_MAIN_MIN = 1000 and PWM_MAIN_MAX = 2000: PWM = 1000 + 1000 u, which gives a = u, thrust ∝ u.
* A NaN value (disarmed or stopped motor, ActuatorMotors.msg) is PWM_MAIN_DIS = 1000; values are
  clipped to [0, 1] (non-reversible motors); the PWM is rounded to the nearest microsecond. Before the
  first actuator_motors message every slot is 1000. -/

namespace Px4.Modules.Px4SimOut

open Harness Harness.Contract.Lang

def input : Schema := Px4.Modules.Px4Alloc.Ports.output.filter fun f =>
  f.name == "actuator_motors_updated" ||
    (List.range 4).any fun i => f.name == s!"actuator_motors_control_{i}"
def output : Schema := Sim.Modules.PlantSim.input

private def pwmRange (i : Nat) : Expr :=
  (1000 : Expr) ≤. s!"pwm{i}" ∧. Expr.var s!"pwm{i}" ≤. 2000

def contract : Contract where
  assume := []
  guarantee := [
    ⟨"pwm_in_plant_range", pwmRange 0 ∧. pwmRange 1 ∧. pwmRange 2 ∧. pwmRange 3⟩,
    ⟨"pwm_tracks_thrust", ¬. "actuator_motors_updated" ∨. ¬. finite "actuator_motors_control_0" ∨.
      "actuator_motors_control_0" <. 0 ∨. 1 <. "actuator_motors_control_0" ∨.
      abs ("pwm0" - (1000 + 1000 * "actuator_motors_control_0")) ≤. 0.5⟩]

def module : Module where
  name := "px4_sim_out"
  doc := "PX4 actuator_motors as plant_sim's PWM (hand-written bridge, pwm_out_sim as configured)"
  params := #[]
  input := input
  output := output
  contract := contract
  exe := "build/modules/px4_sim_out/px4_sim_out"
  stack := .px4

end Px4.Modules.Px4SimOut
