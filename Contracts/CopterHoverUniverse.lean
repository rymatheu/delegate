import Contracts.CopterLift
import Contracts.CopterPlant
import Contracts.CopterVertNearStep

/-!
# The closed loop of the ArduCopter port and the Crazyflie plant: one universe

The controller component `Contracts.CopterLift.Mcopter` lives on `CopterLift.CX` (sample in,
actuators out) and the plant component `Contracts.CopterPlant.Mplant` on `CopterPlant.CX` (real
state, sample out, actuators in). Here both are restated over one tick type `HX` holding the real
plant state `phys`, the sample `smp` and the actuators `act`, so that their intersection is the
closed loop:

* `McopterH P`: the hidden-state lift of `CopterLift.tick P` (the step of `runStdio`, with the
  `takeover` first-tick wrapper) from `Harness.init P`, reading `smp`, writing `act`;
* `MplantH sense32 senseP`: the visible-state lift of `CopterPlant.plant` on `phys`, reading
  `act`, writing `smp`.

**Run parameters** (`runParams`): `Copter.defaults` with the `MOT_` record of the run
(`CopterVertNearStep.runMot`: `sim/params/copter-cf2x.txt`, the linear thrust configuration
`MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`, `MOT_BAT_VOLT_MAX 0`, `MOT_HOVER_LEARN 0`,
`MOT_THST_HOVER 0.4444`) and the hover mission of `sim/params/copter-hover.txt`, one waypoint at
NED `(0, 0, -1)`.

**Initial physical state** (`phys0`): at the waypoint, level, facing north, at rest, with the
stored specific force of the actuator the harness starts from. `Copter.takeover` (with
`run.start_hover 1`) puts the motors' throttle filter at `MOT_THST_HOVER`, whose binary32 value is
`Hf = 7455795 / 2²⁴`, so the first tick's actuator is `Hf` and the specific force consistent with
it is `-2.25 g Hf` (`vertical-channel.md` section 10, step 5), not `-g`.

The closed loop has a behavior from `phys0` for every sensor (`hoverTraj_mem`): the intersection
meets the assumption, so the hover theorem is not vacuous.
-/

namespace Contracts.CopterHover

open Contracts.Lift Contracts.CopterLift Contracts.CopterPlant Copter AP_Math

noncomputable section

/-! ## The tick type -/

/-- One tick of the closed loop: the real plant state, the sample the controller reads, the
actuators it writes. -/
-- <<HX>>
structure HX where
  /-- The real rigid-body state. -/
  phys : CState
  /-- The sample the controller reads. -/
  smp : AHRS.Sample
  /-- The actuators the controller writes. -/
  act : Vector Float32 4
-- <</HX>>

/-! ## The run parameters -/

/-- The hover waypoint, NED `(0, 0, -1)` m. -/
def hoverWP : Vector3p := ⟨0, 0, -1⟩

/-- The run parameters: `Copter.defaults`, the run's `MOT_` record, the hover mission. -/
-- <<runParams>>
def runParams : Parameters :=
  { defaults with mot := CopterVertNear.runMot, mission := [hoverWP] }
-- <</runParams>>

theorem runParams_mission_ne : runParams.mission ≠ [] := by simp [runParams]

/-! ## Widening -/

/-- The C conversion `(double)x` of a `float` (`Float32.toFloat`, an opaque `extern` constant in
core Lean, like `Float.toFloat32`) is exact: the result is finite with the same value. IEEE 754
(5.4.2) requires it, since every binary32 value is a binary64 value. The navigator's stopping
points (`AC_PosControl.get_stopping_point_D_m`) widen a nonzero `float` position, so the hover
needs this beyond `ConvZero` (which covers only `±0`). -/
-- <<WidenSpec>>
structure WidenSpec : Prop where
  exact : ∀ x : Float32, x.IsFinite → (Float32.toFloat x).IsFinite ∧
    (Float32.toFloat x).toReal = x.toReal
-- <</WidenSpec>>

/-! ## The two components over `HX` -/

/-- The ArduCopter port with parameters `P`, over `HX`. -/
-- <<McopterH>>
def McopterH (P : Parameters) : Set (ℕ → HX) :=
  liftHidden (·.smp) (·.act) (tick P) (Harness.init P)
-- <</McopterH>>

/-- The plant over `HX`. -/
-- <<MplantH>>
def MplantH (sense32 : ℝ → Float32) (senseP : ℝ → Float) : Set (ℕ → HX) :=
  liftStep (·.phys) (·.act) (·.smp) (plant sense32 senseP)
-- <</MplantH>>

theorem mem_McopterH {P : Parameters} {x : ℕ → HX} :
    x ∈ McopterH P ↔ ∃ s : ℕ → Harness, s 0 = Harness.init P ∧
      ∀ t, (s (t+1), (x t).act) = tick P (s t) (x t).smp := Iff.rfl

theorem mem_MplantH {sense32 : ℝ → Float32} {senseP : ℝ → Float} {x : ℕ → HX} :
    x ∈ MplantH sense32 senseP ↔
      ∀ t, (x (t+1)).phys = dyn (x t).phys (x t).act ∧ (x t).smp = sample sense32 senseP (x t).phys := by
  simp only [MplantH, mem_liftStep, plant, Prod.mk.injEq]

/-- The restatement agrees with `CopterLift.Mcopter` on the `smp`, `act` fields. -/
theorem McopterH_iff (P : Parameters) (x : ℕ → HX) :
    x ∈ McopterH P ↔ (fun t => (⟨(x t).smp, (x t).act⟩ : CopterLift.CX)) ∈ Mcopter P := Iff.rfl

/-- The restatement agrees with `CopterPlant.Mplant` on the three fields. -/
theorem MplantH_iff (sense32 : ℝ → Float32) (senseP : ℝ → Float) (x : ℕ → HX) :
    x ∈ MplantH sense32 senseP ↔
      (fun t => (⟨(x t).phys, (x t).smp, (x t).act⟩ : CopterPlant.CX)) ∈ Mplant sense32 senseP :=
  Iff.rfl

/-! ## The assumption and the guarantee -/

/-- The binary32 value of `MOT_THST_HOVER = 0.4444`. -/
abbrev Hf : ℝ := CopterVertNear.Hf

/-- The initial physical state: at the waypoint, level, at rest, with the specific force of the
actuator `Hf` (header). -/
-- <<phys0>>
def phys0 : CState := vstate (-1) 0 (-(QuadPlant.thrust2weight * gravity * Hf))
-- <</phys0>>

/-- **Assumption**: the loop starts at `phys0`. The run parameters and the mission are fixed in
`McopterH runParams`. -/
-- <<Ahover>>
def Ahover : Set (ℕ → HX) := {x | (x 0).phys = phys0}
-- <</Ahover>>

/-- **The hover box**: altitude within `5 mm` of the waypoint, vertical speed within `1 cm/s`,
and exactly on the vertical through the waypoint, level, facing north, not rotating. -/
-- <<hoverBox>>
def hoverBox : STL.Formula CState :=
  ((STL.Formula.atom fun s => 1/200 - |s.p.z + 1|).and (.atom fun s => 1/100 - |s.v.z|)).and
    (.atom fun s => -(|s.p.x| + |s.p.y| + |s.v.x| + |s.v.y| + |s.att.roll| + |s.att.pitch| +
      |s.att.yaw| + |s.ω.x| + |s.ω.y| + |s.ω.z|))
-- <</hoverBox>>

/-- A vertical state in the box satisfies `hoverBox`. -/
theorem sat_hoverBox {x : ℕ → CState} {t : ℕ} {z w f : ℝ} (hx : x t = vstate z w f)
    (hz : |z + 1| ≤ 1/200) (hw : |w| ≤ 1/100) : STL.sat x t hoverBox := by
  simp only [hoverBox, STL.sat_and, STL.sat_atom, hx, vstate]
  refine ⟨⟨by linarith, by linarith⟩, by simp⟩

/-! ## A behavior of the closed loop -/

/-- Hidden state and plant state of the closed-loop run from `x0`. -/
def hoverRun (P : Parameters) (sense32 : ℝ → Float32) (senseP : ℝ → Float) (x0 : CState) :
    ℕ → Harness × CState
  | 0 => (Harness.init P, x0)
  | t + 1 =>
    let hc := hoverRun P sense32 senseP x0 t
    let r := tick P hc.1 (sample sense32 senseP hc.2)
    (r.1, dyn hc.2 r.2)

/-- The behavior of the closed loop from `x0`. -/
def hoverTraj (P : Parameters) (sense32 : ℝ → Float32) (senseP : ℝ → Float) (x0 : CState)
    (t : ℕ) : HX :=
  let hc := hoverRun P sense32 senseP x0 t
  ⟨hc.2, sample sense32 senseP hc.2, (tick P hc.1 (sample sense32 senseP hc.2)).2⟩

/-- **Receptiveness of the closed loop**: from every initial plant state the intersection has a
behavior. -/
-- <<hoverTraj_mem>>
theorem hoverTraj_mem (P : Parameters) (sense32 : ℝ → Float32) (senseP : ℝ → Float) (x0 : CState) :
    hoverTraj P sense32 senseP x0 ∈ McopterH P ∩ MplantH sense32 senseP ∧
      (hoverTraj P sense32 senseP x0 0).phys = x0 :=
  ⟨⟨⟨fun t => (hoverRun P sense32 senseP x0 t).1, rfl, fun _ => rfl⟩,
    mem_MplantH.2 fun _ => ⟨rfl, rfl⟩⟩, rfl⟩
-- <</hoverTraj_mem>>

/-- **Non-vacuity**: the closed loop with the run parameters meets the assumption, for every
pair of sensors. -/
-- <<hover_nonvacuous>>
theorem hover_nonvacuous (sense32 : ℝ → Float32) (senseP : ℝ → Float) :
    (McopterH runParams ∩ MplantH sense32 senseP ∩ Ahover).Nonempty :=
  ⟨_, (hoverTraj_mem runParams sense32 senseP phys0).1,
    (hoverTraj_mem runParams sense32 senseP phys0).2⟩
-- <</hover_nonvacuous>>

end

end Contracts.CopterHover
