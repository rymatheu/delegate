import Contracts.FloatLoop
import FloatModel.Small

/-!
# The `Float` closed loop under IEEE-754 binary64, with no rounding hypotheses

`Contracts.FloatLoop` proves the closed loop under the hypotheses `FloatArith ε η Ω` (rounding of
`-` and `*`) and `SenseSpec δ sense` (the sensor). Here the first is discharged from Lean's bit-level
model of `Float` (`FloatModel.Add`, `FloatModel.Small`) with `ε = 2⁻⁵³`, `η = 2⁻¹⁰⁷⁵` and
`Ω = maxFinite` (`ieeeArith`), which leaves only the sensor (`loop_spec_ieee`).

Non-vacuity of what remains:

* the sensor hypothesis is met by a concrete sensor `senseNearest`, which rounds to the nearest
  multiple of `2⁻²⁰` and then to binary64 (`senseNearest_spec`, with `δ = 2⁻²⁰`); a sensor range is
  needed in `SenseSpec`, since no function into `Float` is within any `δ` of every real
  (`not_global_sense`);
* the closed loop with that sensor has a behaviour, from `z₀ = 5`, `v₀ = 0`, that meets the
  assumption `A` (`M_inter_A_nonempty`): the plant and the controller are receptive, and the
  behaviour is built tick by tick (`traj`, `traj_mem`).
-/

namespace Contracts.FloatLoopIEEE

open Contracts.FloatReal Contracts.FloatLoop Contracts.Lift
open Float.Model UnpackedFloat

/-! ## The rounding hypotheses hold of binary64 -/

/-- Lean's binary64 `-` and `*` meet `FloatArith` with unit roundoff `2⁻⁵³`, underflow error
`2⁻¹⁰⁷⁵` and overflow threshold `maxFinite`. -/
-- <<ieeeArith>>
theorem ieeeArith :
    FloatArith ((2 : ℝ) ^ (-53 : ℤ)) ((2 : ℝ) ^ (-1075 : ℤ)) UnpackedFloat.maxFinite where
  sub_err _ _ ha hb h := Float.sub_err_all ha hb h
  mul_err _ _ ha hb h := Float.mul_err_all ha hb h
-- <</ieeeArith>>

theorem maxFinite_ge : (1000 : ℝ) ≤ UnpackedFloat.maxFinite := by
  unfold UnpackedFloat.maxFinite
  have h : (1 : ℝ) ≤ 2 ^ (971 : ℤ) := one_le_zpow₀ one_le_two (by norm_num)
  calc (1000 : ℝ) ≤ (2 ^ 53 - 1) * 1 := by norm_num
    _ ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ) := mul_le_mul_of_nonneg_left h (by norm_num)

theorem u_le : (2 : ℝ) ^ (-53 : ℤ) ≤ 1/1000 := by norm_num

theorem η_le : (2 : ℝ) ^ (-1075 : ℤ) ≤ 1/1000 :=
  (zpow_le_zpow_right₀ one_le_two (by norm_num)).trans u_le

/-- **The binary64 closed loop meets the ceiling and reach-and-hold**, assuming only a sensor that
rounds within `δ ≤ 1/100` on its range. -/
-- <<loop_spec_ieee>>
theorem loop_spec_ieee {δ : ℝ} {sense : ℝ → Float} (HS : SenseSpec δ sense) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1/100) (T T₂ : ℕ) :
    M sense ⊨ ⟨A, initOn phys ((ceiling T).and (reachHold 200 T₂ (1/2)))⟩ :=
  loop_spec_concrete (Ω := UnpackedFloat.maxFinite) ⟨ieeeArith, HS⟩ (by positivity) u_le
    (by positivity) η_le hδ0 hδ (by linarith [maxFinite_ge]) T T₂
-- <</loop_spec_ieee>>

/-! ## A sensor range is necessary -/

/-- Every float, finite or not, denotes a real of magnitude at most `maxFinite`. -/
theorem abs_toReal_le_maxFinite (f : Float) : |f.toReal| ≤ UnpackedFloat.maxFinite := by
  have hmax := maxFinite_ge
  have hc := f.toModel.unpack_canonical
  rw [Float.toReal]
  generalize f.toModel.unpack = u at hc ⊢
  cases u with
  | finite s m e hm =>
    obtain ⟨-, h2, h3, -⟩ := hc
    rw [toReal_finite, abs_mul, Sign.abs_toReal, one_mul,
      abs_of_nonneg (by unfold mag; positivity), mag, UnpackedFloat.maxFinite]
    have hm' : (m : ℝ) + 1 ≤ 2 ^ 53 := by exact_mod_cast (show m + 1 ≤ 2 ^ 53 by omega)
    have he : (2 : ℝ) ^ e ≤ 2 ^ (971 : ℤ) := zpow_le_zpow_right₀ one_le_two h2
    exact mul_le_mul (by linarith) he (two_zpow_pos e).le (by linarith)
  | _ => simp only [UnpackedFloat.toReal, abs_zero]; linarith

/-- No function into `Float` is within `δ` of every real. -/
theorem not_global_sense (δ : ℝ) : ¬ ∃ sense : ℝ → Float, ∀ r, |(sense r).toReal - r| ≤ δ := by
  rintro ⟨sense, h⟩
  set r := UnpackedFloat.maxFinite + |δ| + 1
  have h1 := h r
  have h2 := abs_toReal_le_maxFinite (sense r)
  rw [abs_le] at h1 h2
  have := le_abs_self δ
  linarith [h1.1]

/-! ## A concrete sensor -/

/-- Round to the nearest multiple of `2⁻²⁰` (an integer `N` times `2⁻²⁰`), then to binary64 by the
model's own `normalize` and `pack`. -/
-- <<senseNearest>>
noncomputable def senseNearest (r : ℝ) : Float :=
  Float.ofModel (Float.Model.pack
    (normalize Format.binary64 ⌊r * 2 ^ (20 : ℕ) + 1/2⌋ (-20) .positive))
-- <</senseNearest>>

/-- `senseNearest` is finite and within `2⁻²⁰` on the sensor range. -/
-- <<senseNearest_spec>>
theorem senseNearest_spec : SenseSpec ((2 : ℝ) ^ (-20 : ℤ)) senseNearest := by
  refine ⟨fun r hr => ?_⟩
  have hfl1 := Int.floor_le (r * 2 ^ (20 : ℕ) + 1/2)
  have hfl2 := Int.lt_floor_add_one (r * 2 ^ (20 : ℕ) + 1/2)
  have hdef : senseNearest r = Float.ofModel (Float.Model.pack
      (normalize Format.binary64 ⌊r * 2 ^ (20 : ℕ) + 1/2⌋ (-20) .positive)) := rfl
  rw [hdef]
  generalize ⌊r * 2 ^ (20 : ℕ) + 1/2⌋ = N at hfl1 hfl2 ⊢
  have hfin : |(N : ℝ) * 2 ^ (-20 : ℤ)| ≤ UnpackedFloat.maxFinite := by
    have hp : (2 : ℝ) ^ (-20 : ℤ) = 1 / 1048576 := by norm_num
    have h20 : (2 : ℝ) ^ (20 : ℕ) = 1048576 := by norm_num
    obtain ⟨hr1, hr2⟩ := abs_le.1 hr
    rw [h20] at hfl1 hfl2
    rw [hp, abs_le]; constructor <;> linarith [maxFinite_ge]
  obtain ⟨hf, herr⟩ := Float.goodRound_transfer
    (goodRound_normalize_all N (-20) .positive (by norm_num) hfin)
  refine ⟨hf, ?_⟩
  generalize Float.toReal _ = fl at herr ⊢
  have hp : (2 : ℝ) ^ (-20 : ℤ) = 1 / 1048576 := by norm_num
  have h20 : (2 : ℝ) ^ (20 : ℕ) = 1048576 := by norm_num
  have hu : (2 : ℝ) ^ (-53 : ℤ) = 1 / 9007199254740992 := by norm_num
  rw [hp] at herr ⊢
  rw [hu] at herr
  rw [h20] at hfl1 hfl2
  obtain ⟨hr1, hr2⟩ := abs_le.1 hr
  generalize (N : ℝ) = n at hfl1 hfl2 herr
  have hy1 : |n * (1 / 1048576)| ≤ 101 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨he1, he2⟩ := abs_le.1 herr
  rw [abs_le]; constructor <;> nlinarith
-- <</senseNearest_spec>>

/-- The closed loop with the concrete sensor meets both properties, with no hypotheses at all. -/
-- <<loop_spec_nearest>>
theorem loop_spec_nearest (T T₂ : ℕ) :
    M senseNearest ⊨ ⟨A, initOn phys ((ceiling T).and (reachHold 200 T₂ (1/2)))⟩ :=
  loop_spec_ieee senseNearest_spec (by positivity) (by norm_num) T T₂
-- <</loop_spec_nearest>>

/-! ## The closed loop has behaviours -/

/-- The real state of the loop, tick by tick, from `s₀`. -/
noncomputable def stateSeq (sense : ℝ → Float) (s₀ : ℝ × ℝ) : ℕ → ℝ × ℝ
  | 0 => s₀
  | t + 1 =>
    let s := stateSeq sense s₀ t
    (plant sense s (ctrlF (sense s.1) (sense s.2))).1

/-- The behaviour generated by the plant and the controller from `s₀`. -/
-- <<traj>>
noncomputable def traj (sense : ℝ → Float) (s₀ : ℝ × ℝ) (t : ℕ) : X :=
  let s := stateSeq sense s₀ t
  ⟨s.1, s.2, sense s.1, sense s.2, ctrlF (sense s.1) (sense s.2)⟩
-- <</traj>>

/-- Receptiveness: from every initial state, the generated behaviour is a behaviour of the loop. -/
-- <<traj_mem>>
theorem traj_mem (sense : ℝ → Float) (s₀ : ℝ × ℝ) : traj sense s₀ ∈ M sense :=
  ⟨fun _ => rfl, fun _ => rfl⟩
-- <</traj_mem>>

/-- **Non-vacuity**: the loop with the concrete sensor has a behaviour meeting the assumption, the
one started at rest at the reference altitude. -/
-- <<M_inter_A_nonempty>>
theorem M_inter_A_nonempty : (M senseNearest ∩ A).Nonempty :=
  ⟨traj senseNearest (5, 0), traj_mem _ _, by simp [A, traj, stateSeq]⟩
-- <</M_inter_A_nonempty>>

end Contracts.FloatLoopIEEE
