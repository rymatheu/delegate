module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic

/-!
# Grönwall with a forcing term, and the integrals of the lag

**Comparison with a supersolution** (`norm_le_of_supersol`). If `‖f'‖ ≤ K ‖f‖ + g` on `[0, T)` and `B` satisfies
`B' ≥ K B + g` with `‖f 0‖ ≤ B 0`, then `‖f‖ ≤ B` on `[0, T]`. Mathlib's `gronwallBound` is the case of a constant
`g`; the forced form is what turns a time-dependent input error (the lagged thrust error grows like `1 - e^{-t/τ}`)
into a state error without replacing the forcing by its maximum.

**The integrals of the lag** (`lagM0`, …, `lagM3`): `μ(t) = 1 - e^{-t/τ}` is the fraction of a command step that a
first-order lag with time constant `τ` has passed on to its output after `t`; `lagM1`, `lagM2`, `lagM3` are its
first, second and third integrals from `0`. They are nonnegative and at most `t/τ`, `t²/(2τ)`, `t³/(6τ)`,
`t⁴/(24τ)` for `t ≥ 0` (`lagM0_le` …). Model-free.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-- **Comparison with a supersolution.** A curve whose derivative is at most `K ‖f‖ + g` stays below every
supersolution `B` (`B' ≥ K B + g`) that starts above it. -/
theorem norm_le_of_supersol {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {B B' g : ℝ → ℝ} {K T : ℝ}
    (hf : ContinuousOn f (Icc 0 T))
    (hf' : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (f' t) (Ici t) t)
    (hB : ∀ t ∈ Icc 0 T, HasDerivAt B (B' t) t)
    (h0 : ‖f 0‖ ≤ B 0)
    (hbound : ∀ t ∈ Ico 0 T, ‖f' t‖ ≤ K * ‖f t‖ + g t)
    (hsup : ∀ t ∈ Ico 0 T, K * B t + g t ≤ B' t) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ B t := by
  have key : ∀ ε > 0, ∀ t ∈ Icc 0 T, ‖f t‖ ≤ B t + ε * Real.exp ((K + 1) * t) := by
    intro ε hε
    have hE : ∀ s, HasDerivAt (fun s => ε * Real.exp ((K + 1) * s))
        (ε * (Real.exp ((K + 1) * s) * (K + 1))) s := fun s => by
      have := ((hasDerivAt_id s).const_mul (K + 1)).exp.const_mul ε
      simpa using this
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary' (f := f) (f' := f')
      (B := fun s => B s + ε * Real.exp ((K + 1) * s))
      (B' := fun s => B' s + ε * (Real.exp ((K + 1) * s) * (K + 1))) hf hf' ?_ ?_ ?_ ?_
    · simp only [mul_zero, Real.exp_zero, mul_one]; linarith
    · exact fun s hs => ((hB s hs).add (hE s)).continuousAt.continuousWithinAt
    · exact fun s hs => ((hB s (Ico_subset_Icc_self hs)).add (hE s)).hasDerivWithinAt
    · intro s hs heq
      have h1 := hbound s hs
      have h2 := hsup s hs
      have hp : 0 < ε * Real.exp ((K + 1) * s) := mul_pos hε (Real.exp_pos _)
      rw [heq] at h1
      nlinarith
  intro t ht
  by_contra hlt
  push Not at hlt
  set d := ‖f t‖ - B t
  have hd : 0 < d := by simp only [d]; linarith
  have hx := Real.exp_pos ((K + 1) * t)
  have := key (d / 2 / Real.exp ((K + 1) * t)) (by positivity) t ht
  rw [div_mul_cancel₀ _ hx.ne'] at this
  simp only [d] at this
  linarith

/-! ## The integrals of the lag -/

section lag
variable (τ : ℝ)

/-- The step response of a first-order lag, `1 - e^{-t/τ}`. -/
def lagM0 (t : ℝ) : ℝ := 1 - Real.exp (-t / τ)

/-- Its integral from `0`: `t - τ (1 - e^{-t/τ})`. -/
def lagM1 (t : ℝ) : ℝ := t - τ * (1 - Real.exp (-t / τ))

/-- Its second integral: `t²/2 - τ t + τ² (1 - e^{-t/τ})`. -/
def lagM2 (t : ℝ) : ℝ := t ^ 2 / 2 - τ * t + τ ^ 2 * (1 - Real.exp (-t / τ))

/-- Its third integral: `t³/6 - τ t²/2 + τ² t - τ³ (1 - e^{-t/τ})`. -/
def lagM3 (t : ℝ) : ℝ := t ^ 3 / 6 - τ * t ^ 2 / 2 + τ ^ 2 * t - τ ^ 3 * (1 - Real.exp (-t / τ))

variable {τ}

theorem hasDerivAt_exp_neg_div (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-s / τ)) (-(Real.exp (-t / τ) / τ)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -s / τ) (-1 / τ) t := by
    simpa using (hasDerivAt_id t).neg.div_const τ
  refine h1.exp.congr_deriv ?_
  ring

theorem hasDerivAt_lagM0 (t : ℝ) : HasDerivAt (lagM0 τ) (Real.exp (-t / τ) / τ) t := by
  refine ((hasDerivAt_exp_neg_div t).const_sub 1).congr_deriv ?_
  ring

theorem hasDerivAt_lagM1 (hτ : τ ≠ 0) (t : ℝ) : HasDerivAt (lagM1 τ) (lagM0 τ t) t := by
  refine ((hasDerivAt_id t).sub ((hasDerivAt_lagM0 t).const_mul τ)).congr_deriv ?_
  simp only [lagM0]; field_simp

theorem hasDerivAt_lagM2 (t : ℝ) : HasDerivAt (lagM2 τ) (lagM1 τ t) t := by
  refine ((((hasDerivAt_pow 2 t).div_const 2).sub ((hasDerivAt_id t).const_mul τ)).add
    ((hasDerivAt_lagM0 t).const_mul (τ ^ 2))).congr_deriv ?_
  simp only [lagM1]; field_simp; ring

theorem hasDerivAt_lagM3 (t : ℝ) : HasDerivAt (lagM3 τ) (lagM2 τ t) t := by
  refine (((((hasDerivAt_pow 3 t).div_const 6).sub
    (((hasDerivAt_pow 2 t).const_mul τ).div_const 2)).add
    ((hasDerivAt_id t).const_mul (τ ^ 2))).sub ((hasDerivAt_lagM0 t).const_mul (τ ^ 3))).congr_deriv ?_
  simp only [lagM2]; field_simp; ring

theorem lagM0_zero : lagM0 τ 0 = 0 := by simp [lagM0]
theorem lagM1_zero : lagM1 τ 0 = 0 := by simp [lagM1]
theorem lagM2_zero : lagM2 τ 0 = 0 := by simp [lagM2]
theorem lagM3_zero : lagM3 τ 0 = 0 := by simp [lagM3]

/-- A function vanishing at `0` with a nonnegative derivative on `[0, ∞)` is nonnegative there. -/
theorem nonneg_of_hasDerivAt_nonneg {F F' : ℝ → ℝ} (h0 : F 0 = 0) (hd : ∀ t, HasDerivAt F (F' t) t)
    (hpos : ∀ t, 0 ≤ t → 0 ≤ F' t) : ∀ t, 0 ≤ t → 0 ≤ F t := by
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (D := Ici 0) (convex_Ici 0) (f := F) (f' := F')
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt)
    (fun t ht => hpos t (by rw [interior_Ici] at ht; exact le_of_lt ht))
  intro t ht
  have := hm (Set.mem_Ici.2 le_rfl) ht ht
  rwa [h0] at this

theorem lagM0_nonneg (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lagM0 τ t := by
  have : Real.exp (-t / τ) ≤ 1 := Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by linarith) hτ.le)
  simp only [lagM0]; linarith

theorem lagM0_le_one (t : ℝ) : lagM0 τ t ≤ 1 := by
  have := Real.exp_pos (-t / τ); simp only [lagM0]; linarith

theorem lagM0_le (t : ℝ) : lagM0 τ t ≤ t / τ := by
  have := Real.add_one_le_exp (-t / τ)
  have e : -t / τ = -(t / τ) := neg_div _ _
  simp only [lagM0]; linarith

theorem lagM1_nonneg (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lagM1 τ t :=
  nonneg_of_hasDerivAt_nonneg lagM1_zero (hasDerivAt_lagM1 hτ.ne') (fun _ hs => lagM0_nonneg hτ hs) t ht

theorem lagM2_nonneg (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lagM2 τ t :=
  nonneg_of_hasDerivAt_nonneg lagM2_zero (hasDerivAt_lagM2) (fun _ hs => lagM1_nonneg hτ hs) t ht

theorem lagM3_nonneg (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lagM3 τ t :=
  nonneg_of_hasDerivAt_nonneg lagM3_zero (hasDerivAt_lagM3) (fun _ hs => lagM2_nonneg hτ hs) t ht

theorem lagM1_le (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) : lagM1 τ t ≤ t ^ 2 / (2 * τ) := by
  have := nonneg_of_hasDerivAt_nonneg (F := fun s => s ^ 2 / (2 * τ) - lagM1 τ s)
    (F' := fun s => s / τ - lagM0 τ s) (by simp [lagM1_zero])
    (fun s => by
      refine (((hasDerivAt_pow 2 s).div_const (2 * τ)).sub (hasDerivAt_lagM1 hτ.ne' s)).congr_deriv ?_
      field_simp; ring)
    (fun s _ => by have := lagM0_le (τ := τ) s; linarith) t ht
  linarith

theorem lagM2_le (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) : lagM2 τ t ≤ t ^ 3 / (6 * τ) := by
  have := nonneg_of_hasDerivAt_nonneg (F := fun s => s ^ 3 / (6 * τ) - lagM2 τ s)
    (F' := fun s => s ^ 2 / (2 * τ) - lagM1 τ s) (by simp [lagM2_zero])
    (fun s => by
      refine (((hasDerivAt_pow 3 s).div_const (6 * τ)).sub (hasDerivAt_lagM2 s)).congr_deriv ?_
      field_simp; ring)
    (fun s hs => by have := lagM1_le hτ hs; linarith) t ht
  linarith

theorem lagM3_le (hτ : 0 < τ) {t : ℝ} (ht : 0 ≤ t) : lagM3 τ t ≤ t ^ 4 / (24 * τ) := by
  have := nonneg_of_hasDerivAt_nonneg (F := fun s => s ^ 4 / (24 * τ) - lagM3 τ s)
    (F' := fun s => s ^ 3 / (6 * τ) - lagM2 τ s) (by simp [lagM3_zero])
    (fun s => by
      refine (((hasDerivAt_pow 4 s).div_const (24 * τ)).sub (hasDerivAt_lagM3 s)).congr_deriv ?_
      field_simp; ring)
    (fun s hs => by have := lagM2_le hτ hs; linarith) t ht
  linarith

/-- The step response is monotone in time. -/
theorem lagM0_mono (hτ : 0 < τ) {s t : ℝ} (hst : s ≤ t) : lagM0 τ s ≤ lagM0 τ t := by
  have : Real.exp (-t / τ) ≤ Real.exp (-s / τ) :=
    Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith) hτ.le)
  simp only [lagM0]; linarith

/-- `e^{-1/5} ∈ [0.8185, 0.8188]` (`Real.exp_bound` with four terms). -/
theorem exp_neg_fifth : 0.8185 ≤ Real.exp (-(1 / 5)) ∧ Real.exp (-(1 / 5)) ≤ 0.8188 := by
  have := Real.exp_bound (x := -(1 / 5)) (by norm_num [abs_of_pos]) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at this
  norm_num [abs_of_pos] at this
  rw [abs_le] at this
  constructor <;> linarith [this.1, this.2]

end lag

end

end Plant
