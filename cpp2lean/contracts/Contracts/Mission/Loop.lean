import Contracts.MissionPrelude
import Vehicle

/-!
# The closed loop: the translated controller and the sampled plant on one universe

The controller is the translated vehicle of `Translated/` (`Vehicle.lean`, the harness of the
lock-step executable, over the translations of AP_MotorsMatrix, AC_AttitudeControl_Multi,
AC_PosControl, AC_WPNav and the AHRS view), unchanged. The plant is the sampled ODE of
`Contracts/Plant/Quadrotor.lean`. Both are lifted onto the universe `X` of one tick of the closed
loop: the plant's state, the sample the controller reads, and what the controller writes.

**The controller step** (`tickT`) is one input line of `VehicleMain.loop`: on the first sample the
takeover (`Vehicle.takeover`), then `Vehicle.tick`. Its hidden state is `loop`'s own
`Option World` (`none` before the first sample), so the takeover is applied exactly once, as in the
executable; a world counter such as `ticks32 = 0` would re-trigger it after `2³²` ticks. Its output is
the four actuators and the position target `AC_PosControl::get_pos_desired_NED_m` read from the world
after the tick. That is the value the executable prints as the first three `--trace` numbers
(`Vehicle.traceValues`, `traceValues_posTarget`): it is read directly from the world rather than
from the `Array Float` of `traceValues`, so that it keeps its type (`Vector3p`, three doubles) and no
array index enters the statements.

**The plant** is the plant package's `next` and `sample`, lifted with `liftStep` as in its `Mplant`,
with the sample converted field for field to the controller's `Vehicle.Sample` (`toVSample`): the
same `float`/`double` values, and the period as `UInt64`. `mem_Mplant_iff_plant` states that a
behavior is in this lift exactly when it is the image of a behavior of the plant package's `Mplant`.
-/

namespace Contracts.Mission

open Contracts Contracts.Lift

noncomputable section

/-- Points of NED space, with the Euclidean distance. -/
abbrev P3 := EuclideanSpace ℝ (Fin 3)

/-! ## The controller -/

/-- What the controller writes each tick: the four actuators, and the position target of
`AC_PosControl` after the tick (`get_pos_desired_NED_m`, the first three `--trace` numbers). -/
structure CtrlOut where
  /-- The actuators, slots 0–3, as the motors output them. -/
  act : Vector Float32 4
  /-- `AC_PosControl::_pos_desired_ned_m` after the tick (NED, m, doubles). -/
  posTarget : AC_PosControl_lib.Vector3p.State
  /-- `AC_PosControl::_vel_desired_ned_ms` after the tick (NED, m/s, floats): the velocity the
  navigator's S-curve feeds (`get_vel_desired_NED_ms`, the second three `--trace` numbers). -/
  velTarget : AC_PosControl_lib.Vector3f.State

/-- The harness's actuator array (`#[_actuator[0]!, …, _actuator[3]!]`) as a vector of four. -/
def actVec (a : Array Float32) : Vector Float32 4 := ⟨#[a[0]!, a[1]!, a[2]!, a[3]!], rfl⟩

/-- On an array of four, `actVec` keeps the array. -/
theorem actVec_toArray {a : Array Float32} (h : a.size = 4) : (actVec a).toArray = a := by
  rcases a with ⟨l⟩
  match l, h with
  | [a0, a1, a2, a3], _ => rfl

/-- **The controller step**: one input line of `VehicleMain.loop`. The state is `loop`'s
`Option World`; on `none` (the first sample) the takeover of `w₀` on that sample comes first. -/
def tickT (w₀ : Vehicle.World) (s : Option Vehicle.World) (smp : Vehicle.Sample) :
    Option Vehicle.World × CtrlOut :=
  let wa := match s with
    | some w => w
    | none => Vehicle.takeover w₀ smp
  let r := Vehicle.tick wa smp
  (some r.1, { act := actVec r.2,
               posTarget := AC_PosControl_lib.AC_PosControl.get_pos_desired_NED_m r.1.ps,
               velTarget := AC_PosControl_lib.AC_PosControl.get_vel_desired_NED_ms r.1.ps })

/-- The position target of `tickT` is what `--trace` prints first: the three doubles of
`traceValues`. -/
theorem traceValues_posTarget (w : Vehicle.World) :
    (Vehicle.traceValues w).1[0]! = (AC_PosControl_lib.AC_PosControl.get_pos_desired_NED_m w.ps).x ∧
    (Vehicle.traceValues w).1[1]! = (AC_PosControl_lib.AC_PosControl.get_pos_desired_NED_m w.ps).y ∧
    (Vehicle.traceValues w).1[2]! = (AC_PosControl_lib.AC_PosControl.get_pos_desired_NED_m w.ps).z := by
  simp [Vehicle.traceValues]

/-! ## The universe -/

/-- One tick of a behavior of the closed loop. -/
structure X where
  /-- The plant state: rigid-body state over ℝ and the held thrust fractions. -/
  phys : Plant.PState
  /-- The sample the controller reads. -/
  smp : Vehicle.Sample
  /-- What the controller writes. -/
  out : CtrlOut

/-! ## The plant on this universe -/

/-- The plant package's sample as the controller's `Vehicle.Sample`: the same values field for
field, the period as `UInt64`. -/
def toVSample (s : Plant.Sample) : Vehicle.Sample :=
  { pos := { x := s.pos.x, y := s.pos.y, z := s.pos.z }
    vel := { x := s.vel.x, y := s.vel.y, z := s.vel.z }
    acc := { x := s.accel_ef.x, y := s.accel_ef.y, z := s.accel_ef.z }
    quat := { q1 := s.quat.q1, q2 := s.quat.q2, q3 := s.quat.q3, q4 := s.quat.q4 }
    gyro := { x := s.gyro.x, y := s.gyro.y, z := s.gyro.z }
    dt_us := s.dt_us.toUInt64 }

/-- The plant package's step with its sample converted: next plant state and this tick's sample. -/
noncomputable def plantV (sense32 : ℝ → Float32) (senseP : ℝ → Float) (s : Plant.PState)
    (a : Vector Float32 4) : Plant.PState × Vehicle.Sample :=
  (Plant.next s a, toVSample (Plant.sample sense32 senseP s))

/-- **The plant component** on the loop universe: visible state `phys`, reads `out.act`, writes
`smp`. -/
def Mplant (sense32 : ℝ → Float32) (senseP : ℝ → Float) : Set (ℕ → X) :=
  liftStep (·.phys) (·.out.act) (·.smp) (plantV sense32 senseP)

/-- **The controller component**: the hidden-state lift of `tickT` from `none`, reading `smp` and
writing `out`. -/
def Mctrl (w₀ : Vehicle.World) : Set (ℕ → X) :=
  liftHidden (·.smp) (·.out) (tickT w₀) none

/-- **The closed loop.** -/
def Mloop (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) : Set (ℕ → X) :=
  Mplant sense32 senseP ∩ Mctrl w₀

/-- Membership in the plant, unfolded. -/
theorem mem_Mplant {sense32 : ℝ → Float32} {senseP : ℝ → Float} {x : ℕ → X} :
    x ∈ Mplant sense32 senseP ↔ ∀ t, (x (t + 1)).phys = Plant.next (x t).phys (x t).out.act ∧
      (x t).smp = toVSample (Plant.sample sense32 senseP (x t).phys) := by
  simp only [Mplant, mem_liftStep, plantV, Prod.mk.injEq]

/-- The plant on this universe is the plant package's `Mplant` read through the map
`⟨phys, smp, act⟩ ↦ ⟨phys, toVSample smp, act⟩`: a loop behavior is in `Mplant` exactly when some
behavior of the package's plant has the same plant states and actuators and, converted, the same
samples. -/
theorem mem_Mplant_iff_plant {sense32 : ℝ → Float32} {senseP : ℝ → Float} {x : ℕ → X} :
    x ∈ Mplant sense32 senseP ↔ ∃ y ∈ Plant.Mplant sense32 senseP,
      ∀ t, (y t).phys = (x t).phys ∧ (y t).act = (x t).out.act ∧ toVSample (y t).smp = (x t).smp := by
  constructor
  · intro hx
    refine ⟨fun t => ⟨(x t).phys, Plant.sample sense32 senseP (x t).phys, (x t).out.act⟩, ?_,
      fun t => ⟨rfl, rfl, ((mem_Mplant.1 hx) t).2.symm⟩⟩
    exact Plant.mem_Mplant.2 fun t => ⟨((mem_Mplant.1 hx) t).1, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    refine mem_Mplant.2 fun t => ⟨?_, ?_⟩
    · rw [← (hxy (t + 1)).1, ← (hxy t).1, ← (hxy t).2.1]
      exact ((Plant.mem_Mplant.1 hy) t).1
    · rw [← (hxy t).2.2, ← (hxy t).1, ((Plant.mem_Mplant.1 hy) t).2]

/-- Membership in the controller, unfolded. -/
theorem mem_Mctrl {w₀ : Vehicle.World} {x : ℕ → X} :
    x ∈ Mctrl w₀ ↔ ∃ s : ℕ → Option Vehicle.World, s 0 = none ∧
      ∀ t, (s (t + 1), (x t).out) = tickT w₀ (s t) (x t).smp := Iff.rfl

/-! ## Signals -/

/-- The vehicle's position (NED, m): the first three coordinates of the rigid-body state. -/
noncomputable def pos (x : X) : P3 := !₂[x.phys.x 0, x.phys.x 1, x.phys.x 2]

/-- The real value of the controller's position target (NED, m). -/
noncomputable def posTarget (x : X) : P3 :=
  !₂[x.out.posTarget.x.toReal, x.out.posTarget.y.toReal, x.out.posTarget.z.toReal]

/-- The tracking error: the distance from the vehicle to the position target. -/
noncomputable def err (x : X) : ℝ := dist (pos x) (posTarget x)

/-- Altitude above the takeoff point, m (minus the down coordinate). -/
def alt (x : X) : ℝ := -(x.phys.x 2)

/-- The real value of the sampled position (NED, m), as the controller reads it. -/
noncomputable def smpPos (x : X) : P3 :=
  !₂[x.smp.pos.x.toReal, x.smp.pos.y.toReal, x.smp.pos.z.toReal]

/-- The sampled tracking error: the distance from the sampled position to the target. -/
noncomputable def smpErr (x : X) : ℝ := dist (smpPos x) (posTarget x)

/-- The real value of the controller's velocity target (NED, m/s). -/
noncomputable def velTarget (x : X) : P3 :=
  !₂[x.out.velTarget.x.toReal, x.out.velTarget.y.toReal, x.out.velTarget.z.toReal]

/-- The real value of the sampled velocity (NED, m/s). -/
noncomputable def smpVel (x : X) : P3 :=
  !₂[x.smp.vel.x.toReal, x.smp.vel.y.toReal, x.smp.vel.z.toReal]

/-- The sampled velocity error: the distance from the sampled velocity to the velocity target. -/
noncomputable def smpVelErr (x : X) : ℝ := dist (smpVel x) (velTarget x)

end

end Contracts.Mission
