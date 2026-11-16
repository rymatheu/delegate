import Contracts.Track.Reach.HoverModel
import Contracts.Track.Reach.LegGains

/-!
# Decay constants of the position responses (REACH.md §8.7)

`hover_axes_s` needs, per input coordinate `j`, a constant `c_j` with
`|resp(e, m, j)| ≤ c_j λᵐ` for all `m` (`λ = 0.9997`). The Lyapunov certificates give
`c_j = √(γ P_jj)` (`respH_decay_gen`, `respV_decay_gen`); for the coordinates that carry the
measured excess these are far above the responses' peaks (`2.40` against `0.147` for the horizontal
velocity row). Two sharper constants, both from certified data:

* **vertical** (`decay_of_min`, `respV_cVd`): the vertical response decays at `λ_v = 0.998 < λ`, so
  `min(P_j, c_j λ_vᵐ) ≤ c''_j λᵐ` with `c''_j = max(P_j, c_j λ_vᴹ) / λᴹ` for a switch tick `M`:
  `1.08, 0.32, 0.0023, 1.71, 0.0077` for `ez, ev, eA, I, u` (`M = 176, 680, 1528, 872, 1176`), against
  the Lyapunov `1.452, 1.003, 0.0307, 7.448, 0.0562`;
* **horizontal velocity row** (`respH_e1`): the certified state `A_h^{1728} e₁` of the leg theorem
  (LegGainsData, checkpoint 54) bounds `V(A_h^{1728} e₁) ≤ VbE1`, so past tick 1728 the response is
  at most `√(γ_h VbE1) λ^(m − 1728)`, and before it at most the peak `PH 0 1 = 0.147`:
  `c''₁ = 1/4` (`λ^{1728} ≥ 0.595`).
-/

namespace Contracts.Track.Reach.Hover

open Matrix Finset Contracts.Track Contracts.Track.Induction Contracts.Track.Induction.Nominal
open Contracts.Track.Reach.Glue

noncomputable section

/-! ## A peak and a faster decay give a decay at `λ` -/

/-- If `|r m| ≤ P` for all `m`, `|r m| ≤ c μᵐ` with `0 ≤ μ ≤ λ`, and at a switch tick `M`
both `P` and `c μᴹ` are at most `c'' λᴹ`, then `|r m| ≤ c'' λᵐ` for all `m`. -/
theorem decay_of_min {r : ℕ → ℝ} {P c c'' μ : ℝ} (M : ℕ) (hμ0 : 0 ≤ μ) (hμ : μ ≤ lam)
    (hP : ∀ m, |r m| ≤ P) (hc : ∀ m, |r m| ≤ c * μ ^ m) (_hc0 : 0 ≤ c)
    (h1 : P ≤ c'' * lam ^ M) (h2 : c * μ ^ M ≤ c'' * lam ^ M) (m : ℕ) : |r m| ≤ c'' * lam ^ m := by
  have hl := lam_pos
  have hc'' : 0 ≤ c'' := by
    have := (abs_nonneg _).trans ((hP 0).trans h1)
    exact nonneg_of_mul_nonneg_left this (by positivity)
  rcases le_or_gt m M with hm | hm
  · refine (hP m).trans (h1.trans ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hl.le lam_le_one hm) hc''
  · obtain ⟨k, rfl⟩ : ∃ k, m = M + k := ⟨m - M, by omega⟩
    refine (hc _).trans ?_
    rw [pow_add, pow_add, ← mul_assoc, ← mul_assoc]
    exact mul_le_mul h2 (pow_le_pow_left₀ hμ0 hμ k) (by positivity) (by positivity)

/-- The vertical Lyapunov decay at `λ_v`. -/
theorem respV_decay_v (j : Fin 8) {c : ℝ} (hc : 0 ≤ c)
    (hγ : (Vertical.gamv : ℝ) * (Vertical.Pv j j : ℝ) ≤ c ^ 2) (m : ℕ) :
    |resp Vertical.AvR (outV 0) m j| ≤ c * (Vertical.lamv : ℝ) ^ m := by
  have hr : resp Vertical.AvR (outV 0) m j = ((Vertical.AvR ^ m) *ᵥ Pi.single j 1) 0 := by
    simp [resp, outV, dotProduct, Pi.single_apply]
  have h1 := Vertical.sq_ez_le ((Vertical.AvR ^ m) *ᵥ Pi.single j 1)
  have h2 := V_pow_le m (Pi.single j 1)
  rw [Vv_single_j] at h2
  have hg : (0 : ℝ) ≤ (Vertical.gamv : ℝ) := by norm_num [Vertical.gamv]
  have hx : ((Vertical.lamv : ℝ) ^ 2) ^ m = ((Vertical.lamv : ℝ) ^ m) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hl0 : (0 : ℝ) ≤ (Vertical.lamv : ℝ) := by norm_num [Vertical.lamv]
  rw [hr]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc _ ≤ (Vertical.gamv : ℝ) * Vertical.V _ := h1
    _ ≤ (Vertical.gamv : ℝ) * (((Vertical.lamv : ℝ) ^ 2) ^ m * (Vertical.Pv j j : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 hg
    _ = ((Vertical.gamv : ℝ) * (Vertical.Pv j j : ℝ)) * ((Vertical.lamv : ℝ) ^ m) ^ 2 := by
        rw [hx]; ring
    _ ≤ c ^ 2 * ((Vertical.lamv : ℝ) ^ m) ^ 2 := mul_le_mul_of_nonneg_right hγ (by positivity)
    _ = (c * (Vertical.lamv : ℝ) ^ m) ^ 2 := by ring

/-- The vertical decay constants. -/
def cVd : Fin 8 → ℝ := ![108 / 100, 32 / 100, 221 / 1000, 23 / 10000, 171 / 100, 1676 / 1000,
  77 / 10000, 1649 / 10000]

theorem lamv_nonneg : (0 : ℝ) ≤ (Vertical.lamv : ℝ) := by norm_num [Vertical.lamv]

/-- `p / q ≤ (a / b)ᴹ` from a comparison of natural numbers (kernel arithmetic). -/
theorem rat_pow_ge {a b p q : ℕ} (M : ℕ) (hb : 0 < b) (hq : 0 < q) (h : p * b ^ M ≤ a ^ M * q) :
    (p / q : ℝ) ≤ ((a : ℝ) / b) ^ M := by
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

/-- `(a / b)ᴹ ≤ p / q` from a comparison of natural numbers (kernel arithmetic). -/
theorem rat_pow_le {a b p q : ℕ} (M : ℕ) (hb : 0 < b) (hq : 0 < q) (h : a ^ M * q ≤ p * b ^ M) :
    ((a : ℝ) / b) ^ M ≤ (p / q : ℝ) := by
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

theorem lam_pow_ge (M p q : ℕ) (hq : 0 < q) (h : p * 10000 ^ M ≤ 9997 ^ M * q) :
    (p / q : ℝ) ≤ lam ^ M := by
  have := rat_pow_ge (a := 9997) (b := 10000) M (by norm_num) hq h
  simpa [lam] using this

theorem lamv_pow_le (M p q : ℕ) (hq : 0 < q) (h : 499 ^ M * q ≤ p * 500 ^ M) :
    (Vertical.lamv : ℝ) ^ M ≤ p / q := by
  have := rat_pow_le (a := 499) (b := 500) M (by norm_num) hq h
  simpa [Vertical.lamv] using this

/-- One row of the vertical decay by `decay_of_min`, with rational bounds `L ≤ λᴹ`, `λ_vᴹ ≤ U`. -/
theorem respV_row (j : Fin 8) (M : ℕ) (c L U : ℝ) (hc : 0 ≤ c)
    (hγ : (Vertical.gamv : ℝ) * (Vertical.Pv j j : ℝ) ≤ c ^ 2) (hL : L ≤ lam ^ M)
    (hU : (Vertical.lamv : ℝ) ^ M ≤ U) (hPL : PV 0 j ≤ cVd j * L) (hcU : c * U ≤ cVd j * L)
    (hcd : 0 ≤ cVd j) (m : ℕ) :
    |resp Vertical.AvR (outV 0) m j| ≤ cVd j * lam ^ m := by
  have h1 : PV 0 j ≤ cVd j * lam ^ M := hPL.trans (mul_le_mul_of_nonneg_left hL hcd)
  have h2 : c * (Vertical.lamv : ℝ) ^ M ≤ cVd j * lam ^ M :=
    (mul_le_mul_of_nonneg_left hU hc).trans (hcU.trans (mul_le_mul_of_nonneg_left hL hcd))
  exact decay_of_min (r := fun m => resp Vertical.AvR (outV 0) m j) M lamv_nonneg lamv_le
    (fun m => peakV' 0 j m) (fun m => respV_decay_v j hc hγ m) hc h1 h2 m

/-- **The vertical decay constants `cVd`** (switch ticks `176, 680, 1528, 872, 1176`; the rational
bounds of `λᴹ` and `λ_vᴹ` are comparisons of natural numbers checked by the kernel). -/
theorem respV_cVd (j : Fin 8) (m : ℕ) : |resp Vertical.AvR (outV 0) m j| ≤ cVd j * lam ^ m := by
  fin_cases j
  · exact respV_row 0 176 (1452 / 1000) (9485 / 10000) (7032 / 10000) (by norm_num)
      (by norm_num [Vertical.gamv, Vertical.Pv])
      (by exact_mod_cast lam_pow_ge 176 9485 10000 (by norm_num) (by decide +kernel))
      (by exact_mod_cast lamv_pow_le 176 7032 10000 (by norm_num) (by decide +kernel))
      (by norm_num [PV, cVd]) (by norm_num [cVd]) (by norm_num [cVd]) m
  · exact respV_row 1 680 (1003 / 1000) (8154 / 10000) (2564 / 10000) (by norm_num)
      (by norm_num [Vertical.gamv, Vertical.Pv])
      (by exact_mod_cast lam_pow_ge 680 8154 10000 (by norm_num) (by decide +kernel))
      (by exact_mod_cast lamv_pow_le 680 2564 10000 (by norm_num) (by decide +kernel))
      (by norm_num [PV, cVd]) (by norm_num [cVd]) (by norm_num [cVd]) m
  · exact respV_decay_gen 2 (by norm_num [cVd]) (by norm_num [Vertical.gamv, Vertical.Pv, cVd]) m
  · exact respV_row 3 1528 (307 / 10000) (6322 / 10000) (4694 / 100000) (by norm_num)
      (by norm_num [Vertical.gamv, Vertical.Pv])
      (by exact_mod_cast lam_pow_ge 1528 6322 10000 (by norm_num) (by decide +kernel))
      (by exact_mod_cast lamv_pow_le 1528 4694 100000 (by norm_num) (by decide +kernel))
      (by norm_num [PV, cVd]) (by norm_num [cVd]) (by norm_num [cVd]) m
  · exact respV_row 4 872 (7448 / 1000) (7697 / 10000) (1746 / 10000) (by norm_num)
      (by norm_num [Vertical.gamv, Vertical.Pv])
      (by exact_mod_cast lam_pow_ge 872 7697 10000 (by norm_num) (by decide +kernel))
      (by exact_mod_cast lamv_pow_le 872 1746 10000 (by norm_num) (by decide +kernel))
      (by norm_num [PV, cVd]) (by norm_num [cVd]) (by norm_num [cVd]) m
  · exact respV_decay_gen 5 (by norm_num [cVd]) (by norm_num [Vertical.gamv, Vertical.Pv, cVd]) m
  · exact respV_row 6 1176 (562 / 10000) (7026 / 10000) (950 / 10000) (by norm_num)
      (by norm_num [Vertical.gamv, Vertical.Pv])
      (by exact_mod_cast lam_pow_ge 1176 7026 10000 (by norm_num) (by decide +kernel))
      (by exact_mod_cast lamv_pow_le 1176 950 10000 (by norm_num) (by decide +kernel))
      (by norm_num [PV, cVd]) (by norm_num [cVd]) (by norm_num [cVd]) m
  · exact respV_decay_gen 7 (by norm_num [cVd]) (by norm_num [Vertical.gamv, Vertical.Pv, cVd]) m

/-! ## The horizontal velocity row from the certified state `A_h^{1728} e₁` -/

/-- `V x ≤ Σᵢⱼ |Pᵢⱼ| xbᵢ xbⱼ` for `|xⱼ| ≤ xbⱼ`. -/
theorem Vh_le_abs (x xb : Fin 9 → ℝ) (hx : ∀ j, |x j| ≤ xb j) :
    Horizontal.V x ≤ ∑ i, ∑ j, |(Horizontal.Ph i j : ℝ)| * (xb i * xb j) := by
  simp only [Horizontal.V, Vertical.qf, dotProduct, mulVec, Horizontal.PhR, Horizontal.castM,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have hi := hx i; have hj := hx j
  have h0i : 0 ≤ xb i := (abs_nonneg _).trans hi
  calc x i * ((Horizontal.Ph i j : ℝ) * x j) ≤ |x i * ((Horizontal.Ph i j : ℝ) * x j)| := le_abs_self _
    _ = |(Horizontal.Ph i j : ℝ)| * (|x i| * |x j|) := by rw [abs_mul, abs_mul]; ring
    _ ≤ |(Horizontal.Ph i j : ℝ)| * (xb i * xb j) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hi hj (abs_nonneg _) h0i) (abs_nonneg _)

open Contracts.Track.Reach.Leg Contracts.Track.Reach.Leg.CertGainH in
/-- The certified enclosure of `A_h^{1728} e₁` (LegGainsData, checkpoint 54). -/
def xbE1 (j : Fin 9) : ℚ := ((GainH.vec (cpE1 54).1 j).natAbs : ℚ) / SE1 + ρE1

open Contracts.Track.Reach.Leg Contracts.Track.Reach.Leg.CertGainH in
theorem stateE1 (j : Fin 9) :
    |(Horizontal.AhR ^ 1728 *ᵥ Horizontal.e1) j| ≤ ((xbE1 j : ℚ) : ℝ) :=
  stateAt Horizontal.e1 cpE1 (by norm_num [SE1]) y0E1 ρE1_check 64 64 54 1728 (by norm_num) rfl
    chkE1 j

/-- The bound of `V` at the certified state (kernel arithmetic on the stored integers). -/
def VbE1 : ℚ := 1500000000

theorem VbE1_check : ∑ i, ∑ j, |Horizontal.Ph i j| * (xbE1 i * xbE1 j) ≤ VbE1 := by
  decide +kernel

theorem V_E1 : Horizontal.V (Horizontal.AhR ^ 1728 *ᵥ Horizontal.e1) ≤ (VbE1 : ℝ) := by
  refine (Vh_le_abs _ (fun j => ((xbE1 j : ℚ) : ℝ)) stateE1).trans ?_
  have h := VbE1_check
  have h' : ((∑ i, ∑ j, |Horizontal.Ph i j| * (xbE1 i * xbE1 j) : ℚ) : ℝ) ≤ (VbE1 : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  exact h'

theorem lam_pow_1728 : (595 / 1000 : ℝ) ≤ lam ^ 1728 := by
  exact_mod_cast lam_pow_ge 1728 595 1000 (by norm_num) (by decide +kernel)

/-- **The horizontal velocity row**: `|resp(e, m, 1)| ≤ λᵐ / 4`. -/
theorem respH_e1 (m : ℕ) : |resp Horizontal.AhR (outH 0) m 1| ≤ 1 / 4 * lam ^ m := by
  have hl := lam_pos
  have h1728 := lam_pow_1728
  rcases le_or_gt m 1728 with hm | hm
  · have hp := peakH' 0 1 m
    have hP : PH 0 1 = 147 / 1000 := by simp [PH]; norm_num
    rw [hP] at hp
    have : lam ^ 1728 ≤ lam ^ m := pow_le_pow_of_le_one hl.le lam_le_one hm
    nlinarith
  · obtain ⟨k, rfl⟩ : ∃ k, m = 1728 + k := ⟨m - 1728, by omega⟩
    set x := Horizontal.AhR ^ 1728 *ᵥ Horizontal.e1
    have hr : resp Horizontal.AhR (outH 0) (1728 + k) 1 = ((Horizontal.AhR ^ k) *ᵥ x) 0 := by
      have e1 : (Pi.single 1 1 : Fin 9 → ℝ) = Horizontal.e1 := rfl
      simp only [resp, x, mulVec_mulVec, ← pow_add, add_comm k 1728, e1]
      simp [outH, dotProduct, Pi.single_apply]
    have hs := Horizontal.sq_e_le ((Horizontal.AhR ^ k) *ᵥ x)
    have hv := Vh_pow_le k x
    have hV := V_E1
    have hg : (0 : ℝ) ≤ (Horizontal.gamh : ℝ) := by norm_num [Horizontal.gamh]
    have hlk : 0 ≤ lam ^ k := by positivity
    rw [hr]
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    rw [lamh_eq] at hv
    have hx : (lam ^ 2) ^ k = (lam ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
    rw [hx] at hv
    have hVx := Horizontal.V_nonneg x
    calc _ ≤ (Horizontal.gamh : ℝ) * Horizontal.V _ := hs
      _ ≤ (Horizontal.gamh : ℝ) * ((lam ^ k) ^ 2 * (VbE1 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hv.trans (mul_le_mul_of_nonneg_left hV (by positivity))) hg
      _ = ((Horizontal.gamh : ℝ) * (VbE1 : ℝ)) * (lam ^ k) ^ 2 := by ring
      _ ≤ (1 / 4 * lam ^ 1728) ^ 2 * (lam ^ k) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (Horizontal.gamh : ℝ) * (VbE1 : ℝ) ≤ (1 / 4 * (595 / 1000)) ^ 2 := by
            norm_num [Horizontal.gamh, VbE1]
          refine this.trans ?_
          exact pow_le_pow_left₀ (by norm_num) (by linarith) 2
      _ = (1 / 4 * lam ^ (1728 + k)) ^ 2 := by rw [pow_add]; ring

/-- The horizontal decay constants. -/
def cHd : Fin 9 → ℝ := ![347 / 100, 1 / 4, 123 / 100, 66 / 1000, 133 / 100, 18 / 100, 32 / 1000,
  26 / 1000, 19 / 1000]

/-- **The horizontal decay constants `cHd`.** -/
theorem respH_cHd (j : Fin 9) (m : ℕ) : |resp Horizontal.AhR (outH 0) m j| ≤ cHd j * lam ^ m := by
  fin_cases j
  · exact respH_decay_gen 0 (by norm_num [cHd]) (by norm_num [Horizontal.gamh, Horizontal.Ph, cHd]) m
  · simpa [cHd] using respH_e1 m
  · exact respH_decay_gen 2 (by norm_num [cHd]) (by norm_num [Horizontal.gamh, Horizontal.Ph, cHd]) m
  · exact respH_decay_gen 3 (by norm_num [cHd]) (by norm_num [Horizontal.gamh, Horizontal.Ph, cHd]) m
  · exact respH_decay_gen 4 (by norm_num [cHd]) (by norm_num [Horizontal.gamh, Horizontal.Ph, cHd]) m
  · exact respH_decay_gen 5 (by norm_num [cHd]) (by norm_num [Horizontal.gamh, Horizontal.Ph, cHd]) m
  · exact respH_decay_gen 6 (by norm_num [cHd]) (by norm_num [Horizontal.gamh, Horizontal.Ph, cHd]) m
  · exact respH_decay_gen 7 (by norm_num [cHd]) (by norm_num [Horizontal.gamh, Horizontal.Ph, cHd]) m
  · exact respH_decay_gen 8 (by norm_num [cHd]) (by norm_num [Horizontal.gamh, Horizontal.Ph, cHd]) m

/-- `mH = Σ cHd κH ≤ 0.1438`, `mV = Σ cVd κV ≤ 0.0274`. -/
theorem mH_le : ∑ j, cHd j * κH j ≤ 1438 / 10000 := by
  simp [cHd, κH, Fin.sum_univ_succ]; norm_num

theorem mV_le : ∑ j, cVd j * κV j ≤ 274 / 10000 := by
  simp [cVd, κV, Fin.sum_univ_eight]; norm_num

end

end Contracts.Track.Reach.Hover
