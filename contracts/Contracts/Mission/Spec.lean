import Contracts.Mission.Loop
import MissionData.Course
import MissionData.Params

/-!
# The mission specification

The numbers of the validation spec `sim/spec/mission-course.json` as named constants, the course
geometry (waypoints, the planned polyline, the corridor, the takeoff box, the safe set), the STL
formulas over the loop universe, the mission formula `ψmission`, the assumption `Atakeoff`, the
initial world `MissionWorld`, and the hypotheses `LibmSpec` on the C library functions.

The numbers mirror `sim/spec/mission-course.json` (version of 2026-11-05 13:30, regenerated after
the Monte Carlo validation): the takeoff box is `[-0.15, 0.15]` m north and east (an earlier `0.2`
put its corners `0.283` m from the climb axis, outside the corridor), `[-0.3, 0]` m down; the
polyline starts at the takeoff point (the origin, on the ground), then `w0` directly above it, then
`w1 … w7` (`path_ned_m`); the safe set is the corridor of radius `0.25` m around that polyline union
the box; the actuators held at tick 0 are the hover actuators (`assumption.held_actuators`), here the
plant's hover thrust fraction `1 / thrust2weight` on each motor. Every constant names its JSON path.
-/

namespace Contracts.STL

/-- The behaviours satisfying `φ` at time index `t`. -/
def lang_t {X : Type} (t : ℕ) (φ : Formula X) : Set (ℕ → X) := {x | sat x t φ}

@[simp] theorem mem_lang_t {X : Type} {t : ℕ} {φ : Formula X} {x : ℕ → X} :
    x ∈ lang_t t φ ↔ sat x t φ := Iff.rfl

end Contracts.STL

namespace Contracts.Mission

open Contracts Contracts.STL

noncomputable section

/-! ## The numbers (they mirror `sim/spec/mission-course.json`) -/

/-- Control rate, Hz (`tick_hz`). -/
def tickHz : ℕ := 400

/-- Waypoint arrival radius, m (`r_m`). -/
def rWp : ℝ := 0.1

/-- Ceiling, m above the takeoff point (`ceiling_m`). -/
def ceiling : ℝ := 2.0

/-- Corridor radius around the planned polyline, m (`corridor_radius_m`). -/
def corridor : ℝ := 0.25

/-- Half-width of the takeoff box, north and east, m (`box_ned_m.north`, `box_ned_m.east`
`= [-0.15, 0.15]`, the corrected values). -/
def boxNE : ℝ := 0.15

/-- Lower end of the takeoff box's down coordinate, m (`box_ned_m.down[0]`). -/
def boxDownLo : ℝ := -0.3

/-- Upper end of the takeoff box's down coordinate, m (`box_ned_m.down[1]`). -/
def boxDownHi : ℝ := 0

/-- Per-leg allowances, s (`allowances_s`): leg `i` ends at `wᵢ`, leg 0 starts at tick 0. -/
def allowanceSec : List ℕ := [3, 3, 3, 3, 6, 3, 3, 3]

/-- Per-leg allowances, ticks (`allowances_ticks`). -/
def allowanceTicks : List ℕ := [1200, 1200, 1200, 1200, 2400, 1200, 1200, 1200]

/-- Sum of the allowances, ticks (`total_ticks`, 27 s). -/
def totalTicks : ℕ := 10800

/-- Hold time at the last waypoint, ticks (`hold_ticks`, `hold_s = 3`). -/
def holdTicks : ℕ := 1200

/-- Horizon, ticks (`horizon_ticks`): the allowances plus the hold. -/
def horizonTicks : ℕ := 12000

/-- Nominal leg times of the run `sim/out/lean-course-1ms`, s (`nominal.leg_s`), from which the
allowances are derived (`allowance_rule`). -/
def nominalLegSec : List ℝ := [1.685, 1.933, 1.845, 1.854, 3.621, 1.852, 1.85, 1.85]

/-- `WP_RADIUS_M` of `sim/params/copter-cf2x-tuned.txt`, m: the navigator's own arrival radius. -/
def wpRadius : ℝ := 0.1

/-- The mission waypoints `w0 … w7`, NED m (`waypoints_ned_m`; the `waypoint` lines of
`sim/params/copter-cf2x.txt`). -/
def wp : Fin 8 → P3 := ![!₂[0, 0, -0.8], !₂[1.25, 1.25, -1.0], !₂[0, 2.5, -1.2], !₂[-1.25, 1.25, -1.4],
  !₂[1.25, -1.25, -1.6], !₂[0, -2.5, -1.4], !₂[-1.25, -1.25, -1.1], !₂[0, 0, -0.8]]

/-- The last waypoint, where the vehicle holds. -/
def w7 : P3 := wp 7

/-- The planned polyline's vertices, NED m (`path_ned_m`): the takeoff point, then `w0 … w7`. -/
def pathPt : Fin 9 → P3 := ![!₂[0, 0, 0], !₂[0, 0, -0.8], !₂[1.25, 1.25, -1.0], !₂[0, 2.5, -1.2],
  !₂[-1.25, 1.25, -1.4], !₂[1.25, -1.25, -1.6], !₂[0, -2.5, -1.4], !₂[-1.25, -1.25, -1.1],
  !₂[0, 0, -0.8]]

/-- The legs of the mission: each waypoint with its allowance in ticks. -/
def legs : List (P3 × ℕ) :=
  [(wp 0, 1200), (wp 1, 1200), (wp 2, 1200), (wp 3, 1200), (wp 4, 2400), (wp 5, 1200),
   (wp 6, 1200), (wp 7, 1200)]

/-- The total allowance of a list of legs. -/
def span (L : List (P3 × ℕ)) : ℕ := (L.map Prod.snd).sum

/-! ### Evaluated facts about the numbers -/

theorem legs_allowances : legs.map Prod.snd = allowanceTicks := rfl
theorem legs_waypoints : legs.map Prod.fst = List.ofFn wp := rfl
theorem allowanceTicks_eq : allowanceTicks = allowanceSec.map (· * tickHz) := by decide
theorem span_legs : span legs = totalTicks := by decide
theorem allowanceTicks_sum : allowanceTicks.sum = totalTicks := by decide
theorem holdTicks_eq : holdTicks = 3 * tickHz := by decide
theorem horizonTicks_eq : horizonTicks = totalTicks + holdTicks := by decide
theorem rWp_le_wpRadius : rWp ≤ wpRadius := le_rfl

/-- The allowances follow the JSON's `allowance_rule`: `⌈1.25 leg_i + 0.5⌉` s of the nominal leg
times. -/
theorem allowance_rule :
    nominalLegSec.map (fun l => ⌈(5 / 4 : ℝ) * l + 1 / 2⌉) = allowanceSec.map (fun n => (n : ℤ)) := by
  norm_num [nominalLegSec, allowanceSec, Int.ceil_eq_iff]

/-! ## Geometry -/

/-- Distance in coordinates. -/
theorem dist_eq3 (p q : P3) :
    dist p q = Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_three]
  simp [Real.dist_eq, sq_abs]

/-- A coordinate difference is at most the distance. -/
theorem abs_coord_le_dist (p q : P3) (i : Fin 3) : |p i - q i| ≤ dist p q := by
  rw [dist_eq3, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1),
    sq_nonneg (p 2 - q 2)]

/-- The distance is at most the sum of the coordinate differences. -/
theorem dist_le_sum_abs (p q : P3) : dist p q ≤ |p 0 - q 0| + |p 1 - q 1| + |p 2 - q 2| := by
  rw [dist_eq3, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h0 := abs_nonneg (p 0 - q 0)
  have h1 := abs_nonneg (p 1 - q 1)
  have h2 := abs_nonneg (p 2 - q 2)
  nlinarith [sq_abs (p 0 - q 0), sq_abs (p 1 - q 1), sq_abs (p 2 - q 2), mul_nonneg h0 h1,
    mul_nonneg h1 h2, mul_nonneg h0 h2]

/-- The planned polyline: the union of its eight segments. -/
def polySet : Set P3 := ⋃ i : Fin 8, segment ℝ (pathPt i.castSucc) (pathPt i.succ)

/-- Distance to the planned polyline. -/
def polyDist (p : P3) : ℝ := Metric.infDist p polySet

theorem polySet_nonempty : polySet.Nonempty :=
  ⟨pathPt 0, Set.mem_iUnion.2 ⟨0, left_mem_segment ℝ _ _⟩⟩

/-- The distance to the polyline is 1-Lipschitz. -/
theorem polyDist_le (p q : P3) : polyDist p ≤ polyDist q + dist p q :=
  Metric.infDist_le_infDist_add_dist

/-- Every vertex of the polyline is at most `1.6` m above the takeoff point. -/
theorem pathPt_down (i : Fin 9) : -1.6 ≤ pathPt i 2 := by
  fin_cases i <;> norm_num [pathPt]

/-- Every point of the polyline is at most `1.6` m above the takeoff point. -/
theorem polySet_down {y : P3} (hy : y ∈ polySet) : -1.6 ≤ y 2 := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hi
  have h1 := pathPt_down i.castSucc
  have h2 := pathPt_down i.succ
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  nlinarith

/-- **Points within the corridor are below `1.85` m**, hence below the ceiling. -/
theorem down_of_polyDist {p : P3} (h : polyDist p ≤ corridor) : -1.85 ≤ p 2 := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨y, hy, hpy⟩ := (Metric.infDist_lt_iff polySet_nonempty).1
    (show polyDist p < corridor + ε by linarith)
  have h1 := polySet_down hy
  have h2 := abs_coord_le_dist p y 2
  have h3 := neg_abs_le (p 2 - y 2)
  norm_num [corridor] at hpy ⊢
  linarith

/-- The takeoff box (`box_ned_m`). -/
def inBox (p : P3) : Prop :=
  -boxNE ≤ p 0 ∧ p 0 ≤ boxNE ∧ -boxNE ≤ p 1 ∧ p 1 ≤ boxNE ∧ boxDownLo ≤ p 2 ∧ p 2 ≤ boxDownHi

/-- The box's margin: nonnegative exactly inside the box. -/
def boxMargin (p : P3) : ℝ :=
  min (min (p 0 + boxNE) (boxNE - p 0))
    (min (min (p 1 + boxNE) (boxNE - p 1)) (min (p 2 - boxDownLo) (boxDownHi - p 2)))

theorem boxMargin_nonneg_iff (p : P3) : 0 ≤ boxMargin p ↔ inBox p := by
  simp only [boxMargin, inBox, le_min_iff, sub_nonneg]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩; exact ⟨by linarith, h2, by linarith, h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩; exact ⟨⟨by linarith, h2⟩, ⟨by linarith, h4⟩, h5, h6⟩

/-- **The safe set** `S`: the corridor around the polyline, union the takeoff box. -/
def inSafe (p : P3) : Prop := polyDist p ≤ corridor ∨ inBox p

/-- The safe set's margin: nonnegative exactly on `S`. -/
def safeMargin (p : P3) : ℝ := max (corridor - polyDist p) (boxMargin p)

theorem safeMargin_nonneg_iff (p : P3) : 0 ≤ safeMargin p ↔ inSafe p := by
  rw [safeMargin, le_max_iff, sub_nonneg, boxMargin_nonneg_iff, inSafe]

/-- The safe set is below the ceiling. -/
theorem down_of_inSafe {p : P3} (h : inSafe p) : -ceiling ≤ p 2 := by
  rcases h with h | ⟨-, -, -, -, h, -⟩
  · have := down_of_polyDist h; norm_num [ceiling] at *; linarith
  · norm_num [ceiling, boxDownLo] at *; linarith

/-! ## Formulas over the loop universe -/

/-- `true`. -/
def trueF : Formula X := .atom fun _ => 0

/-- A predicate as an atom (`0` where it holds, `-1` elsewhere). Used for the qualitative parts of
assumptions; the metric parts of the mission are atoms with their real margins. -/
def propF (P : X → Prop) : Formula X := .atom fun x => by classical exact if P x then 0 else -1

@[simp] theorem sat_propF {P : X → Prop} {x : ℕ → X} {t : ℕ} : sat x t (propF P) ↔ P (x t) := by
  classical
  simp only [propF, sat_atom]
  split_ifs with h <;> simp [h]

@[simp] theorem sat_trueF {x : ℕ → X} {t : ℕ} : sat x t trueF := by simp [trueF]

/-- `near c ρ`: the vehicle is within `ρ` of `c`. -/
def near (c : P3) (ρ : ℝ) : Formula X := .atom fun x => ρ - dist (pos x) c

/-- `nearT c ρ`: the position target is within `ρ` of `c`. -/
def nearT (c : P3) (ρ : ℝ) : Formula X := .atom fun x => ρ - dist (posTarget x) c

/-- `errLE d`: the tracking error is at most `d`. -/
def errLE (d : ℝ) : Formula X := .atom fun x => d - err x

/-- Safety at a tick: inside `S` and below the ceiling. -/
def safeF : Formula X :=
  .and (.atom fun x => safeMargin (pos x)) (.atom fun x => ceiling - alt x)

@[simp] theorem sat_near {c : P3} {ρ : ℝ} {x : ℕ → X} {t : ℕ} :
    sat x t (near c ρ) ↔ dist (pos (x t)) c ≤ ρ := by simp [near]
@[simp] theorem sat_nearT {c : P3} {ρ : ℝ} {x : ℕ → X} {t : ℕ} :
    sat x t (nearT c ρ) ↔ dist (posTarget (x t)) c ≤ ρ := by simp [nearT]
@[simp] theorem sat_errLE {d : ℝ} {x : ℕ → X} {t : ℕ} : sat x t (errLE d) ↔ err (x t) ≤ d := by
  simp [errLE]
theorem sat_safeF {x : ℕ → X} {t : ℕ} :
    sat x t safeF ↔ inSafe (pos (x t)) ∧ alt (x t) ≤ ceiling := by
  simp only [safeF, sat_and, sat_atom, safeMargin_nonneg_iff, sub_nonneg]

/-- **Implication** (`Formula.imp` of the STL library, `¬(φ ∧ ¬ψ)`) means implication. -/
theorem sat_imp_iff {x : ℕ → X} {t : ℕ} {φ ψ : Formula X} :
    sat x t (φ.imp ψ) ↔ (sat x t φ → sat x t ψ) := sat_imp

/-- Reaching a list of points in order: `◇_[0,T₁] (F w₁ ∧ ◇_[0,T₂] (F w₂ ∧ …))`. Each allowance is
counted from the previous arrival, so the nesting enforces the order. -/
def reachSeqF (F : P3 → Formula X) : List (P3 × ℕ) → Formula X
  | [] => trueF
  | (w, T) :: rest => .eventually 0 T (.and (F w) (reachSeqF F rest))

/-- The vehicle reaches the points in order, each within radius `r`. -/
def reachSeq (r : ℝ) : List (P3 × ℕ) → Formula X := reachSeqF (near · r)

/-- The position target reaches the points in order, each within radius `r`. -/
def reachSeqT (r : ℝ) : List (P3 × ℕ) → Formula X := reachSeqF (nearT · r)

/-- **The mission**: over the horizon the vehicle stays in the safe set below the ceiling; it
reaches `w0 … w7` in order, each within `r` and within its allowance after the previous one; and
within the total allowance it is within `r` of `w7` for the hold time. -/
def ψmission : Formula X :=
  .and (.always 0 horizonTicks safeF)
    (.and (reachSeq rWp legs) (.eventually 0 totalTicks (.always 0 holdTicks (near w7 rWp))))

/-! ## The assumption -/

/-- The level attitude with heading `ψ`: the rotation by `ψ` about the down axis,
`q = (cos (ψ/2), 0, 0, sin (ψ/2))` (roll and pitch zero). -/
def yawQuat (ψ : ℝ) : Plant.Quat := ⟨Real.cos (ψ / 2), 0, 0, Real.sin (ψ / 2)⟩

/-- The plant state at the start: at `p`, at rest, level with heading `ψ` (`yawQuat ψ`), no body
rates. -/
def startState (p : P3) (ψ : ℝ) : Plant.State :=
  ⟨⟨p 0, p 1, p 2⟩, ⟨0, 0, 0⟩, yawQuat ψ, ⟨0, 0, 0⟩⟩

/-- The hover thrust fraction on every motor, `1 / thrust2weight`. -/
def hoverHeld : Fin 4 → ℝ := fun _ => 1 / Plant.thrust2weight

/-- The plant state at the start: `startState p ψ`, with the hover actuators held, so that the
specific force of tick 0 is `(0, 0, -g)`, the reading of a vehicle at rest (whatever the heading). -/
def startP (p : P3) (ψ : ℝ) : Plant.PState := ⟨(startState p ψ).toX, hoverHeld⟩

/-- **The assumption of a mission flight** (`assumption` of the JSON, with the corrected box): at
tick 0 the vehicle is in the takeoff box, at rest, level with any heading, with the hover actuators
held. -/
def Atakeoff : Set (ℕ → X) := {x | ∃ p ψ, inBox p ∧ (x 0).phys = startP p ψ}

/-! ## The initial world -/

/-- A `float` is determined by its bits. -/
theorem _root_.Float32.eq_of_toBits_eq {a b : Float32} (h : a.toBits = b.toBits) : a = b := by
  rcases a with ⟨⟨ba, va⟩⟩
  rcases b with ⟨⟨bb, vb⟩⟩
  simp only [Float32.toBits] at h
  subst h
  rfl

/-- A `double` is determined by its bits. -/
theorem _root_.Float.eq_of_toBits_eq {a b : Float} (h : a.toBits = b.toBits) : a = b := by
  rcases a with ⟨⟨ba, va⟩⟩
  rcases b with ⟨⟨bb, vb⟩⟩
  simp only [Float.toBits] at h
  subst h
  rfl

/-- **The parameters the proofs read**, as equalities (`MissionData.missionParamsOk` is the same
list as a bitwise Boolean, evaluated by `mission_world_check`): the eight waypoints, the navigator's
parameters, the position controller's position gains and shaping jerk, and the attitude
controller's rate and acceleration limits and input time constant. -/
structure MissionParams (w : Vehicle.World) : Prop where
  mission_size : w.mission.size = 8
  mission : ∀ i < 8, w.mission[i]! = MissionData.missionWps[i]!
  wpp : w.wpp = MissionData.wppC
  kp_ne : w.pp._p_pos_ne_m._kp = 1.5
  kp_d : w.pp._p_pos_d_m._kp = 1
  jerk_ne : w.pp._shaping_jerk_ne_msss = 5
  rate_r : w.ap._ang_vel_roll_max_degs = 0
  rate_p : w.ap._ang_vel_pitch_max_degs = 0
  acc_r : w.ap._accel_roll_max_degss = 1800
  acc_p : w.ap._accel_pitch_max_degss = 1800
  input_tc : w.ap._input_tc = 0.05

theorem eq_of_eq32 {a b : Float32} (h : MissionData.eq32 a b = true) : a = b :=
  Float32.eq_of_toBits_eq (by simpa [MissionData.eq32] using h)

theorem eq_of_eq64 {a b : Float} (h : MissionData.eq64 a b = true) : a = b :=
  Float.eq_of_toBits_eq (by simpa [MissionData.eq64] using h)

theorem eq_of_eqP3 {a b : AC_WPNav_lib.Vector3p.State} (h : MissionData.eqP3 a b = true) : a = b := by
  simp only [MissionData.eqP3, Bool.and_eq_true] at h
  obtain ⟨⟨hx, hy⟩, hz⟩ := h
  rcases a with ⟨ax, ay, az⟩
  rcases b with ⟨bx, by_, bz⟩
  simp only at hx hy hz
  rw [eq_of_eq64 hx, eq_of_eq64 hy, eq_of_eq64 hz]

theorem eq_of_eqWpp {a b : AC_WPNav_lib.AC_WPNav.Params} (h : MissionData.eqWpp a b = true) :
    a = b := by
  simp only [MissionData.eqWpp, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  rcases a with ⟨_, _, _, _, _, _, _, _, _, _⟩
  rcases b with ⟨_, _, _, _, _, _, _, _, _, _⟩
  simp only at *
  rw [eq_of_eq32 h1, eq_of_eq32 h2, eq_of_eq32 h3, eq_of_eq32 h4, eq_of_eq32 h5, eq_of_eq32 h6,
    eq_of_eq32 h7, eq_of_eq32 h8, eq_of_eq32 h9, h10]

/-- The executed check gives the equalities. -/
theorem missionParams_of_ok {w : Vehicle.World} (h : MissionData.missionParamsOk w = true) :
    MissionParams w := by
  simp only [MissionData.missionParamsOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs, m0⟩, m1⟩, m2⟩, m3⟩, m4⟩, m5⟩, m6⟩, m7⟩, hw⟩, k1⟩, k2⟩, j⟩, r1⟩, r2⟩,
    a1⟩, a2⟩, tc⟩ := h
  refine ⟨hs, fun i hi => ?_, eq_of_eqWpp hw, eq_of_eq32 k1, eq_of_eq32 k2, eq_of_eq32 j,
    eq_of_eq32 r1, eq_of_eq32 r2, eq_of_eq32 a1, eq_of_eq32 a2, eq_of_eq32 tc⟩
  interval_cases i
  · exact eq_of_eqP3 m0
  · exact eq_of_eqP3 m1
  · exact eq_of_eqP3 m2
  · exact eq_of_eqP3 m3
  · exact eq_of_eqP3 m4
  · exact eq_of_eqP3 m5
  · exact eq_of_eqP3 m6
  · exact eq_of_eqP3 m7

/-- **The vehicle of the mission flights**: `w₀` is the booted world that `Vehicle.construct`
builds from the lines of the three course parameter files (`MissionData.courseLines`, the texts
embedded verbatim), as `VehicleMain` builds it from
`--params copter-cf2x.txt --params copter-course-speed.txt --params copter-cf2x-tuned.txt`, and
its parameters are those of `MissionParams`.

The second field is not derived from the first in Lean: the kernel cannot evaluate
`construct courseLines` (`String.splitOn` is well-founded recursion and `Vehicle.parseDecimal` a
`while` loop). It is the trusted step: `mission_world_check` evaluates
`MissionData.missionParamsOk (boot w)` (`true`), and `missionParams_of_ok` turns it into the
equalities. -/
structure MissionWorld (w₀ : Vehicle.World) : Prop where
  built : ∃ w, Vehicle.construct MissionData.courseLines = .ok w ∧ w₀ = Vehicle.boot w
  params : MissionParams w₀

/-! ## The C library -/

/-- Accuracy of the `float` libm functions assumed for the proofs, absolute, on results in
`[-π, π]`: two units in the last place at `1` (`2⁻²²`). -/
def libm32Err : ℝ := 2 ^ (-22 : ℤ)

/-- Accuracy of the `double` libm functions, absolute, on results in `[-π, π]`: `2⁻⁵¹`. -/
def libm64Err : ℝ := 2 ^ (-51 : ℤ)

/-- **What the proofs assume of the C library functions** the translation calls as externs (core's
`Float32.sin` is `sinf`, and so on; `CppLibm` declares `fmaxf`, `fminf`, `fmodf`, `fmax`, `fmin`,
`fmod`). Finite results on finite arguments in the domain, the range facts, and accuracy against the
real functions; `sqrt` and `fmax`/`fmin`/`fmod` are exact or correctly rounded in IEEE 754, the
trigonometric functions are within `libm32Err`/`libm64Err`. These are hypotheses, stated now with
what the sub-contract proofs are expected to need; they are not proved about any implementation.
The `float`/`double` conversions are opaque externs of core Lean as well (`lean_float32_to_float`,
`lean_float_to_float32`) and are specified here alongside the C library. -/
structure LibmSpec : Prop where
  sinf : ∀ a : Float32, a.IsFinite →
    (Float32.sin a).IsFinite ∧ |(Float32.sin a).toReal| ≤ 1 ∧
      |(Float32.sin a).toReal - Real.sin a.toReal| ≤ libm32Err
  cosf : ∀ a : Float32, a.IsFinite →
    (Float32.cos a).IsFinite ∧ |(Float32.cos a).toReal| ≤ 1 ∧
      |(Float32.cos a).toReal - Real.cos a.toReal| ≤ libm32Err
  /-- Correctly rounded: within half an ulp, `2⁻²⁴` relative. -/
  sqrtf : ∀ a : Float32, a.IsFinite → 0 ≤ a.toReal →
    (Float32.sqrt a).IsFinite ∧ 0 ≤ (Float32.sqrt a).toReal ∧
      |(Float32.sqrt a).toReal - Real.sqrt a.toReal| ≤ 2 ^ (-24 : ℤ) * Real.sqrt a.toReal
  /-- `atan2f y x` against the argument of `x + y i`, away from the branch cut. -/
  atan2f : ∀ y a : Float32, y.IsFinite → a.IsFinite →
    (Float32.atan2 y a).IsFinite ∧ |(Float32.atan2 y a).toReal| ≤ Real.pi + libm32Err ∧
      (¬ (y.toReal = 0 ∧ a.toReal ≤ 0) →
        |(Float32.atan2 y a).toReal - Complex.arg ⟨a.toReal, y.toReal⟩| ≤ libm32Err)
  asinf : ∀ a : Float32, a.IsFinite → |a.toReal| ≤ 1 →
    (Float32.asin a).IsFinite ∧ |(Float32.asin a).toReal - Real.arcsin a.toReal| ≤ libm32Err
  acosf : ∀ a : Float32, a.IsFinite → |a.toReal| ≤ 1 →
    (Float32.acos a).IsFinite ∧ |(Float32.acos a).toReal - Real.arccos a.toReal| ≤ libm32Err
  fmaxf : ∀ a b : Float32, a.IsFinite → b.IsFinite →
    (CppLibm.fmaxf a b).IsFinite ∧ (CppLibm.fmaxf a b).toReal = max a.toReal b.toReal
  fminf : ∀ a b : Float32, a.IsFinite → b.IsFinite →
    (CppLibm.fminf a b).IsFinite ∧ (CppLibm.fminf a b).toReal = min a.toReal b.toReal
  /-- `fmodf` is exact: `a - n b` for an integer `n`, smaller than `|b|`. -/
  fmodf : ∀ a b : Float32, a.IsFinite → b.IsFinite → b.toReal ≠ 0 →
    (CppLibm.fmodf a b).IsFinite ∧ |(CppLibm.fmodf a b).toReal| < |b.toReal| ∧
      ∃ n : ℤ, (CppLibm.fmodf a b).toReal = a.toReal - n * b.toReal
  sin : ∀ a : Float, a.IsFinite →
    (Float.sin a).IsFinite ∧ |(Float.sin a).toReal| ≤ 1 ∧
      |(Float.sin a).toReal - Real.sin a.toReal| ≤ libm64Err
  cos : ∀ a : Float, a.IsFinite →
    (Float.cos a).IsFinite ∧ |(Float.cos a).toReal| ≤ 1 ∧
      |(Float.cos a).toReal - Real.cos a.toReal| ≤ libm64Err
  sqrt : ∀ a : Float, a.IsFinite → 0 ≤ a.toReal →
    (Float.sqrt a).IsFinite ∧ 0 ≤ (Float.sqrt a).toReal ∧
      |(Float.sqrt a).toReal - Real.sqrt a.toReal| ≤ 2 ^ (-53 : ℤ) * Real.sqrt a.toReal
  fmax : ∀ a b : Float, a.IsFinite → b.IsFinite →
    (CppLibm.fmax a b).IsFinite ∧ (CppLibm.fmax a b).toReal = max a.toReal b.toReal
  fmin : ∀ a b : Float, a.IsFinite → b.IsFinite →
    (CppLibm.fmin a b).IsFinite ∧ (CppLibm.fmin a b).toReal = min a.toReal b.toReal
  /-- `(double) f` (`Float32.toFloat`, opaque in Lean ≥ 4.36): widening is exact. Added for
  `nav_contract` (the navigator widens its `float` track to the `double` target). -/
  f32ToF64 : ∀ a : Float32, a.IsFinite →
    (Float32.toFloat a).IsFinite ∧ (Float32.toFloat a).toReal = a.toReal
  /-- `(float) d` (`Float.toFloat32`, opaque): correctly rounded narrowing on the `float` range,
  relative error `2⁻²⁴` plus the subnormal half-spacing `2⁻¹⁵⁰`. Added for `nav_contract`. -/
  f64ToF32 : ∀ a : Float, a.IsFinite → |a.toReal| ≤ Float.Model.UnpackedFloat.maxFinite32 →
    (Float.toFloat32 a).IsFinite ∧
      |(Float.toFloat32 a).toReal - a.toReal| ≤ 2 ^ (-24 : ℤ) * |a.toReal| + 2 ^ (-150 : ℤ)
  /-- `(float) d` of a `double` that is a `float` value is that value (correct rounding). Added for
  `nav_contract`. -/
  f64ToF32_exact : ∀ (a : Float) (b : Float32), a.IsFinite → b.IsFinite → b.toReal = a.toReal →
    (Float.toFloat32 a).IsFinite ∧ (Float.toFloat32 a).toReal = a.toReal

end

end Contracts.Mission
