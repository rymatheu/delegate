module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Tactic

/-!
# Real-variable lemmas

Model-free estimates used by the plant library: products of bounded differences, derivative bounds
on an interval, and Taylor expansions with a bounded remainder. Moved here from the archive's
`Bounds.lean` (`abs_mul_sub_mul_le`, `two_abs_mul_le`), `Invariants.lean` (`abs_sub_le_of_deriv`),
`Euler.lean` (`abs_sub_le_of_deriv_Icc`) and `Sharp.lean` (`abs_sub_poly_le`, `taylor2`–`taylor4`)
with their names and proofs unchanged.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-- Difference of products: `|a b - a' b'| ≤ Ra Db + Rb Da` when `|a| ≤ Ra`, `|b'| ≤ Rb`,
`|a - a'| ≤ Da`, `|b - b'| ≤ Db`. -/
theorem abs_mul_sub_mul_le {a b a' b' Ra Rb Da Db : ℝ} (ha : |a| ≤ Ra) (hb : |b'| ≤ Rb)
    (hda : |a - a'| ≤ Da) (hdb : |b - b'| ≤ Db) : |a * b - a' * b'| ≤ Ra * Db + Rb * Da := by
  have e : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
  rw [e]
  calc |a * (b - b') + (a - a') * b'| ≤ |a| * |b - b'| + |a - a'| * |b'| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ Ra * Db + Da * Rb := by
        gcongr
        · exact (abs_nonneg _).trans ha
        · exact (abs_nonneg _).trans hda
    _ = Ra * Db + Rb * Da := by ring

/-- `2 |a b| ≤ a² + b²`. -/
theorem two_abs_mul_le (a b : ℝ) : 2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  rw [abs_mul]; nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- A real function with derivative bounded by `C` on `[0, T]` moves by at most `C t`. -/
theorem abs_sub_le_of_deriv {f g : ℝ → ℝ} {T C : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t) (hb : ∀ t ∈ Icc 0 T, |g t| ≤ C) :
    ∀ t ∈ Icc 0 T, |f t - f 0| ≤ C * t := by
  intro t ht
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := g) (C := C)
    (fun s hs => (hd s hs).hasDerivWithinAt) (fun s hs => hb s (Ico_subset_Icc_self hs)) t ht
  simpa [Real.norm_eq_abs] using this

/-- A real function with derivative bounded by `C` on `[a, b]` is `C`-Lipschitz there. -/
theorem abs_sub_le_of_deriv_Icc {f g : ℝ → ℝ} {a b C : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (g t) t) (hb : ∀ t ∈ Icc a b, |g t| ≤ C) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |f t - f s| ≤ C * |t - s| := by
  have key : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → |f t - f s| ≤ C * |t - s| := by
    intro s hs t ht hst
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := g) (C := C) (a := s)
      (b := t) (fun r hr => (hd r ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩).hasDerivWithinAt)
      (fun r hr => hb r ⟨hs.1.trans hr.1, hr.2.le.trans ht.2⟩) t ⟨hst, le_rfl⟩
    rw [Real.norm_eq_abs] at this
    rwa [abs_of_nonneg (sub_nonneg.2 hst)]
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact key s hs t ht hst
  · rw [abs_sub_comm, abs_sub_comm t]; exact key t ht s hs hts

/-- If `f' = g` on `[0, T]` and `|g - p| ≤ B'` where `P' = p`, `B' ` is the derivative of `B` and
`B 0 = 0`, then `|f t - f 0 - (P t - P 0)| ≤ B t` on `[0, T]`. -/
theorem abs_sub_poly_le {f g P p B B' : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t) (hP : ∀ t, HasDerivAt P (p t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t) (hB0 : B 0 = 0)
    (hb : ∀ t ∈ Icc 0 T, |g t - p t| ≤ B' t) :
    ∀ t ∈ Icc 0 T, |f t - f 0 - (P t - P 0)| ≤ B t := by
  intro t ht
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t => f t - f 0 - (P t - P 0)) (f' := fun t => g t - p t) (a := 0) (b := T)
    (B := B) (B' := B')
    (fun s hs => (((hf s hs).sub_const (f 0)).sub ((hP s).sub_const (P 0))).continuousAt
      |>.continuousWithinAt)
    (fun s hs => (((hf s (Ico_subset_Icc_self hs)).sub_const (f 0)).sub
      ((hP s).sub_const (P 0))).hasDerivWithinAt)
    (by simp [hB0]) hB
    (fun s hs => by rw [Real.norm_eq_abs]; exact hb s (Ico_subset_Icc_self hs)) ht
  simpa [Real.norm_eq_abs] using this

/-- Second order: `|g t - g 0| ≤ C t` gives `|f t - f 0 - t g 0| ≤ C t² / 2`. -/
theorem taylor2 {f g : ℝ → ℝ} {T C : ℝ} (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc 0 T, |g t - g 0| ≤ C * t) :
    ∀ t ∈ Icc 0 T, |f t - f 0 - t * g 0| ≤ C * t ^ 2 / 2 := by
  intro t ht
  have := abs_sub_poly_le (P := fun s => s * g 0) (p := fun _ => g 0)
    (B := fun s => C * s ^ 2 / 2) (B' := fun s => C * s) hf
    (fun s => hasDerivAt_mul_const (g 0))
    (fun s => by convert ((hasDerivAt_pow 2 s).const_mul C).div_const 2 using 1; ring)
    (by simp) hg t ht
  simpa using this

/-- Third order: `|g t - g 0 - t k| ≤ C t² / 2` gives
`|f t - f 0 - t g 0 - (t² / 2) k| ≤ C t³ / 6`. -/
theorem taylor3 {f g : ℝ → ℝ} {T C k : ℝ} (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc 0 T, |g t - g 0 - t * k| ≤ C * t ^ 2 / 2) :
    ∀ t ∈ Icc 0 T, |f t - f 0 - t * g 0 - t ^ 2 / 2 * k| ≤ C * t ^ 3 / 6 := by
  intro t ht
  have := abs_sub_poly_le (P := fun s => s * g 0 + s ^ 2 / 2 * k) (p := fun s => g 0 + s * k)
    (B := fun s => C * s ^ 3 / 6) (B' := fun s => C * s ^ 2 / 2) hf
    (fun s => by
      convert (hasDerivAt_mul_const (g 0)).add (((hasDerivAt_pow 2 s).div_const 2).mul_const k)
        using 1
      push_cast; ring)
    (fun s => by convert ((hasDerivAt_pow 3 s).const_mul C).div_const 6 using 1; push_cast; ring)
    (by simp) (fun s hs => by simpa [sub_sub] using hg s hs) t ht
  have e : f t - f 0 - (t * g 0 + t ^ 2 / 2 * k - (0 * g 0 + 0 ^ 2 / 2 * k)) =
      f t - f 0 - t * g 0 - t ^ 2 / 2 * k := by ring
  simpa only [e] using this

/-- Fourth order: `|g t - g 0 - t k₁ - (t² / 2) k₂| ≤ C t³ / 6` gives
`|f t - f 0 - t g 0 - (t² / 2) k₁ - (t³ / 6) k₂| ≤ C t⁴ / 24`. -/
theorem taylor4 {f g : ℝ → ℝ} {T C k₁ k₂ : ℝ} (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc 0 T, |g t - g 0 - t * k₁ - t ^ 2 / 2 * k₂| ≤ C * t ^ 3 / 6) :
    ∀ t ∈ Icc 0 T,
      |f t - f 0 - t * g 0 - t ^ 2 / 2 * k₁ - t ^ 3 / 6 * k₂| ≤ C * t ^ 4 / 24 := by
  intro t ht
  have := abs_sub_poly_le (P := fun s => s * g 0 + s ^ 2 / 2 * k₁ + s ^ 3 / 6 * k₂)
    (p := fun s => g 0 + s * k₁ + s ^ 2 / 2 * k₂)
    (B := fun s => C * s ^ 4 / 24) (B' := fun s => C * s ^ 3 / 6) hf
    (fun s => by
      convert ((hasDerivAt_mul_const (g 0)).add (((hasDerivAt_pow 2 s).div_const 2).mul_const k₁)).add
        (((hasDerivAt_pow 3 s).div_const 6).mul_const k₂) using 1
      push_cast; ring)
    (fun s => by convert ((hasDerivAt_pow 4 s).const_mul C).div_const 24 using 1; push_cast; ring)
    (by simp) (fun s hs => by
      have e : g s - (g 0 + s * k₁ + s ^ 2 / 2 * k₂) = g s - g 0 - s * k₁ - s ^ 2 / 2 * k₂ := by
        ring
      rw [e]; exact hg s hs) t ht
  have e : f t - f 0 - (t * g 0 + t ^ 2 / 2 * k₁ + t ^ 3 / 6 * k₂ -
      (0 * g 0 + 0 ^ 2 / 2 * k₁ + 0 ^ 3 / 6 * k₂)) =
      f t - f 0 - t * g 0 - t ^ 2 / 2 * k₁ - t ^ 3 / 6 * k₂ := by ring
  simpa only [e] using this

end

end Plant
