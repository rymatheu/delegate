import Harness.Module
import Harness.Compose
import sim.modules.plant_sim.Module

/-! # plant_formation: two X500s in one gorge

The same simulator as `plant_sim` with two vehicles (the shared simulator's `FormationPlant`, one PyBullet world:
the vehicles collide with the gorge and with each other), stepped one 400 Hz tick per protocol step for both. Its
interface is plant_sim's twice, every field prefixed `v1_` or `v2_` (the time `t_us` and the parameters are shared),
and its contract is plant_sim's for each vehicle, renamed the same way, so a stack built for plant_sim reads one
vehicle's fields after `inst` with the same prefix. One parameter more: `formation`, the formation plan of
sim/plans (1 `abreast`, 2 `staggered`: vehicle 2 rear and facing backward), which sets where each vehicle starts.
Vehicle 2's noise seed is `noise_seed + 100` (`FormationPlant.for_plan`). Same executable as plant_sim
(sim/modules/plant_sim/adapter.py, `--vehicles 2`), built by `sim/modules/plant_sim/build.sh plant_formation`. -/

namespace Sim.Modules.PlantFormation

open Harness Harness.Contract.Lang

/-- The two vehicles, in the order of the plant's arrays. -/
def vehicles : List String := ["v1", "v2"]

private def shared (n : String) : Bool := n == "t_us" || PlantSim.params.any (·.name == n)

/-- A plant_sim field name as vehicle `v`'s. -/
def vname (v n : String) : String := if shared n then n else s!"{v}_{n}"

private def perVehicle (s : Schema) : Schema :=
  (vehicles.toArray.flatMap fun v => s.filter (!shared ·.name) |>.map fun f =>
    { f with name := vname v f.name, doc := s!"vehicle {v.drop 1}: {f.doc}" })

def params : Schema := PlantSim.params ++ #[
  { name := "formation", type := .u32,
    doc := "the formation plan (sim/plans): 1 abreast, 2 staggered (vehicle 2 rear, facing backward)" }]

def input : Schema := perVehicle PlantSim.input

def output : Schema :=
  #[{ name := "t_us", type := .u32, doc := "simulated time of the state, us since init (2500 per step)" }] ++
  perVehicle PlantSim.output

private def renamed (v : String) (c : Clause) : Clause :=
  { (c.rename (vname v)) with name := s!"{c.name}_{v}" }

def contract : Contract where
  assume :=
    (PlantSim.contract.assume.filter (·.name == "pwm_range")).flatMap (fun c => vehicles.map (renamed · c)) ++
    PlantSim.contract.assume.filter (·.name != "pwm_range") ++
    [⟨"formation_range", .var "formation" =. 1 ∨. .var "formation" =. 2⟩]
  guarantee := PlantSim.contract.guarantee.flatMap fun c => vehicles.map (renamed · c)

def module : Module where
  name := "plant_formation"
  doc := "two X500s of the gorge simulator in one world (formation plan abreast or staggered), one tick per step"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/plant_formation/plant_formation"
  stack := .sim

end Sim.Modules.PlantFormation
