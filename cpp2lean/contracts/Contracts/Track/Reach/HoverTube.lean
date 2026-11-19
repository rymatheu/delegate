import Contracts.Track.Reach.GlueLoop

/-!
# The hover tube with transient excess (REACH.md §8.7)

The hover campaign (REACH.md §8.7, `staging/text/hover-campaign.md`) measured the per-tick
disturbances of the readouts on displaced holds: the per-row bounds `εVh`, `εHh` of `HoverTubeGlue`
hold after the transient, but not during it. At a start in a corner of the region, the attitude
loop deviates from the lag law by up to `0.058` m/s² (the bound was `εη = 0.01`), and the tilt of
the transient couples into the vertical channel through the plant (`ρz`, `ρv`), the sampled
specific force (`ρam`) and the angle boost (`τ`): up to `9.8·10⁻⁴` per tick in the `eA` row against
`4.2·10⁻⁶`, `2.3·10⁻⁴` in the `u` row against `3.2·10⁻⁶`. The excess over the per-tick floor is
transient: it ends within 700 ticks, and its sum, weighted by `λ^(-(k+1))` (`λ = 0.9997`), is
proportional to the offset.

This file is the model-level theorem for that class of disturbances:

* `tube_exc`: the ℓ1 tube for `η' = A η + w` with `|w_k j| ≤ ε_j + s_k j`, `s ≥ 0`: the output is
  within `Σ P e₀ + Σ G ε` plus the convolution of the response with `s`;
* `exc_peak`, `exc_decay`: that convolution is at most `Σ_j P_j W_j` (peak gains) and at most
  `λᴺ Σ_j c_j W_j` (per-coordinate decay constants `c_j ≥ √(γ P_jj)` of the Lyapunov
  certificates, `respH_decay_j`, `respV_decay_j`), with `W_j = Σ_k s_k j / λ^(k+1)`;
* `HoverModelS`: the readouts follow `A_v`, `A_h` from `t₀`, start at a position offset `d` plus
  deviations within `ε0Vs`, `ε0Hs`, and, while the box `BoxS` has held, the excess of each row over
  its floor `εVs`, `εHs` has weighted sum at most `κV j · ‖d‖∞`, `κH j · ‖d‖∞`;
* `hover_box_s`: the box at every tick (strong induction, the region closes: `regionVs`,
  `regionHs`) and the position bounds per axis `hover_axes_s`.
-/

namespace Contracts.Track.Reach.Hover

open Matrix Finset Contracts.Track Contracts.Track.Induction Contracts.Track.Induction.Nominal
open Contracts.Track.Reach.Glue

noncomputable section

/-! ## The excess of a disturbance over its floor, and the weighted sum -/

/-- The excess of `w` over the floor `ε`: `max (|w| − ε) 0`. -/
def exc (w ε : ℝ) : ℝ := max (|w| - ε) 0

theorem exc_nonneg (w ε : ℝ) : 0 ≤ exc w ε := le_max_right _ _

theorem abs_le_exc (w ε : ℝ) : |w| ≤ ε + exc w ε := by
  have := le_max_left (|w| - ε) 0
  unfold exc; linarith

/-- `exc` is monotone in `|w|` and antitone in the floor. -/
theorem exc_le_of {w w' ε ε' : ℝ} (h : |w| - ε ≤ |w'| - ε') : exc w ε ≤ exc w' ε' :=
  max_le_max h le_rfl

/-- The decay factor per tick of the hover theorem, `λ = 0.9997` (`Horizontal.lamh`). -/
def lam : ℝ := 9997 / 10000

theorem lam_pos : 0 < lam := by norm_num [lam]
theorem lam_le_one : lam ≤ 1 := by norm_num [lam]
theorem lamh_eq : (Horizontal.lamh : ℝ) = lam := by norm_num [Horizontal.lamh, lam]
theorem lamv_le : (Vertical.lamv : ℝ) ≤ lam := by norm_num [Vertical.lamv, lam]

/-- The weighted sum `Σ_{k<N} s k / λ^(k+1)`. -/
def wsum (s : ℕ → ℝ) (N : ℕ) : ℝ := ∑ k ∈ range N, s k / lam ^ (k + 1)

theorem sum_le_wsum {s : ℕ → ℝ} (hs : ∀ k, 0 ≤ s k) (N : ℕ) : ∑ k ∈ range N, s k ≤ wsum s N := by
  unfold wsum
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : 0 < lam ^ (k + 1) := pow_pos lam_pos _
  have h2 : lam ^ (k + 1) ≤ 1 := pow_le_one₀ lam_pos.le lam_le_one
  rw [le_div_iff₀ h1]
  nlinarith [hs k]

/-! ## The tube with an excess -/

section Tube

variable {n : ℕ}

/-- **The tube lemma with an excess**: for `η (t + 1) = A η t + w t` from `t₀`, with
`|η t₀ j| ≤ e0 j` and `|w (t₀ + k) j| ≤ ε j + s k j` for `k < N`, the output `o` at `t₀ + N` is
within `Σ P e0 + Σ G ε` plus the convolution of the response with `s`. -/
theorem tube_exc (A : Matrix (Fin n) (Fin n) ℝ) (η w : ℕ → Fin n → ℝ) (t₀ N : ℕ)
    (hη : ∀ t, t₀ ≤ t → η (t + 1) = A *ᵥ η t + w t) (o e0 ε P G : Fin n → ℝ)
    (s : ℕ → Fin n → ℝ) (hε : ∀ j, 0 ≤ ε j) (h₀ : ∀ j, |η t₀ j| ≤ e0 j)
    (hw : ∀ k < N, ∀ j, |w (t₀ + k) j| ≤ ε j + s k j)
    (hP : ∀ j m, |resp A o m j| ≤ P j) (hG : ∀ j N, ∑ m ∈ range N, |resp A o m j| ≤ G j) :
    |o ⬝ᵥ η (t₀ + N)| ≤ ∑ j, P j * e0 j + ∑ j, G j * ε j +
      ∑ j, ∑ k ∈ range N, |resp A o (N - 1 - k) j| * s k j := by
  have he0 : ∀ j, 0 ≤ e0 j := fun j => (abs_nonneg _).trans (h₀ j)
  rw [eta_eq_sum A η w t₀ hη N, dotProduct_add, dotProduct_sum]
  have h1 : |o ⬝ᵥ ((A ^ N) *ᵥ η t₀)| ≤ ∑ j, P j * e0 j := by
    refine (abs_dot_mulVec_le A o _ e0 N h₀).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hP j N) (he0 j)
  have h2 : |∑ k ∈ range N, o ⬝ᵥ ((A ^ (N - 1 - k)) *ᵥ w (t₀ + k))| ≤
      ∑ j, G j * ε j + ∑ j, ∑ k ∈ range N, |resp A o (N - 1 - k) j| * s k j := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range N, |o ⬝ᵥ ((A ^ (N - 1 - k)) *ᵥ w (t₀ + k))|
        ≤ ∑ k ∈ range N, ∑ j, (ε j + s k j) * |resp A o (N - 1 - k) j| :=
          Finset.sum_le_sum fun k hk => abs_dot_mulVec_le A o _ _ _ (hw k (mem_range.mp hk))
      _ = ∑ j, ε j * ∑ k ∈ range N, |resp A o (N - 1 - k) j| +
            ∑ j, ∑ k ∈ range N, |resp A o (N - 1 - k) j| * s k j := by
          rw [Finset.sum_comm, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ _ := by
          refine add_le_add (Finset.sum_le_sum fun j _ => ?_) le_rfl
          rw [Finset.sum_range_reflect (fun m => |resp A o m j|) N, mul_comm (G j)]
          exact mul_le_mul_of_nonneg_left (hG j N) (hε j)
  have := abs_add_le (o ⬝ᵥ ((A ^ N) *ᵥ η t₀)) (∑ k ∈ range N, o ⬝ᵥ ((A ^ (N - 1 - k)) *ᵥ w (t₀ + k)))
  linarith

/-- The convolution with the excess, through the peak gains. -/
theorem exc_peak (A : Matrix (Fin n) (Fin n) ℝ) (o P : Fin n → ℝ) (s : ℕ → Fin n → ℝ)
    (hs : ∀ k j, 0 ≤ s k j) (hP : ∀ j m, |resp A o m j| ≤ P j) (N : ℕ) :
    ∑ j, ∑ k ∈ range N, |resp A o (N - 1 - k) j| * s k j ≤
      ∑ j, P j * wsum (fun k => s k j) N := by
  refine Finset.sum_le_sum fun j _ => ?_
  have hP0 : 0 ≤ P j := (abs_nonneg _).trans (hP j 0)
  calc ∑ k ∈ range N, |resp A o (N - 1 - k) j| * s k j ≤ ∑ k ∈ range N, P j * s k j :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hP j _) (hs k j)
    _ = P j * ∑ k ∈ range N, s k j := by rw [Finset.mul_sum]
    _ ≤ P j * wsum (fun k => s k j) N :=
        mul_le_mul_of_nonneg_left (sum_le_wsum (fun k => hs k j) N) hP0

/-- The convolution with the excess, through per-coordinate decay constants. -/
theorem exc_decay (A : Matrix (Fin n) (Fin n) ℝ) (o c : Fin n → ℝ) (s : ℕ → Fin n → ℝ)
    (hs : ∀ k j, 0 ≤ s k j) (hc : ∀ j m, |resp A o m j| ≤ c j * lam ^ m) (N : ℕ) :
    ∑ j, ∑ k ∈ range N, |resp A o (N - 1 - k) j| * s k j ≤
      lam ^ N * ∑ j, c j * wsum (fun k => s k j) N := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  unfold wsum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk := mem_range.mp hk
  have hl : 0 < lam ^ (k + 1) := pow_pos lam_pos _
  have e : lam ^ (N - 1 - k) = lam ^ N / lam ^ (k + 1) := by
    rw [eq_div_iff hl.ne', ← pow_add]; congr 1; omega
  calc |resp A o (N - 1 - k) j| * s k j ≤ c j * lam ^ (N - 1 - k) * s k j :=
        mul_le_mul_of_nonneg_right (hc j _) (hs k j)
    _ = lam ^ N * (c j * (s k j / lam ^ (k + 1))) := by
        rw [e]; field_simp

/-- **The tube around the free response of an offset, with an excess.** -/
theorem chan_tube_exc (A : Matrix (Fin n) (Fin n) ℝ) (ξ w : ℕ → Fin n → ℝ) (t₀ N : ℕ) (i₀ : Fin n)
    (d : ℝ) (hstep : ∀ t, t₀ ≤ t → ξ (t + 1) = A *ᵥ ξ t + w t) (o e0 ε P G : Fin n → ℝ)
    (s : ℕ → Fin n → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (h0 : ∀ j, |ξ t₀ j - (Pi.single i₀ d : Fin n → ℝ) j| ≤ e0 j)
    (hw : ∀ k < N, ∀ j, |w (t₀ + k) j| ≤ ε j + s k j)
    (hP : ∀ j m, |resp A o m j| ≤ P j) (hG : ∀ j N, ∑ m ∈ range N, |resp A o m j| ≤ G j) :
    |o ⬝ᵥ ξ (t₀ + N) - d * resp A o N i₀| ≤ ∑ j, P j * e0 j + ∑ j, G j * ε j +
      ∑ j, ∑ k ∈ range N, |resp A o (N - 1 - k) j| * s k j := by
  set η : ℕ → Fin n → ℝ := fun t => ξ t - (A ^ (t - t₀)) *ᵥ Pi.single i₀ d with hη
  have hη' : ∀ t, t₀ ≤ t → η (t + 1) = A *ᵥ η t + w t := by
    intro t ht
    simp only [hη, hstep t ht, mulVec_sub, mulVec_mulVec]
    rw [show t + 1 - t₀ = (t - t₀) + 1 by omega, pow_succ']
    abel
  have h0' : ∀ j, |η t₀ j| ≤ e0 j := by
    intro j; simp only [hη, Nat.sub_self, pow_zero, one_mulVec, Pi.sub_apply]; exact h0 j
  have T := tube_exc A η w t₀ N hη' o e0 ε P G s hε h0' hw hP hG
  have e1 : o ⬝ᵥ η (t₀ + N) = o ⬝ᵥ ξ (t₀ + N) - d * resp A o N i₀ := by
    simp only [hη, dotProduct_sub, Nat.add_sub_cancel_left, resp]
    congr 1
    rw [show (Pi.single i₀ d : Fin n → ℝ) = d • Pi.single i₀ 1 by
      ext j; simp [Pi.single_apply]]
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [← e1]; exact T

end Tube

/-! ## Per-coordinate decay constants of the position responses -/

theorem Vh_single_j (j : Fin 9) : Horizontal.V (Pi.single j 1) = (Horizontal.Ph j j : ℝ) := by
  simp [Horizontal.V, Horizontal.PhR, Horizontal.castM, Vertical.qf, dotProduct, mulVec,
    Pi.single_apply]

theorem Vv_single_j (j : Fin 8) : Vertical.V (Pi.single j 1) = (Vertical.Pv j j : ℝ) := by
  simp [Vertical.V, Vertical.PvR, Vertical.castM, Vertical.qf, dotProduct, mulVec, Pi.single_apply]

/-- `|resp A_h e (m) j| ≤ c λ_h^m` whenever `γ_h P_h,jj ≤ c²`. -/
theorem respH_decay_gen (j : Fin 9) {c : ℝ} (hc : 0 ≤ c)
    (hγ : (Horizontal.gamh : ℝ) * (Horizontal.Ph j j : ℝ) ≤ c ^ 2) (m : ℕ) :
    |resp Horizontal.AhR (outH 0) m j| ≤ c * lam ^ m := by
  have hr : resp Horizontal.AhR (outH 0) m j = ((Horizontal.AhR ^ m) *ᵥ Pi.single j 1) 0 := by
    simp [resp, outH, dotProduct, Pi.single_apply]
  have h1 := Horizontal.sq_e_le ((Horizontal.AhR ^ m) *ᵥ Pi.single j 1)
  have h2 := Vh_pow_le m (Pi.single j 1)
  rw [Vh_single_j] at h2
  have hg : (0 : ℝ) ≤ (Horizontal.gamh : ℝ) := by norm_num [Horizontal.gamh]
  rw [hr, ← lamh_eq]
  have hx : ((Horizontal.lamh : ℝ) ^ 2) ^ m = ((Horizontal.lamh : ℝ) ^ m) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hl0 : (0 : ℝ) ≤ (Horizontal.lamh : ℝ) := by norm_num [Horizontal.lamh]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc _ ≤ (Horizontal.gamh : ℝ) * Horizontal.V _ := h1
    _ ≤ (Horizontal.gamh : ℝ) * (((Horizontal.lamh : ℝ) ^ 2) ^ m * (Horizontal.Ph j j : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 hg
    _ = ((Horizontal.gamh : ℝ) * (Horizontal.Ph j j : ℝ)) * ((Horizontal.lamh : ℝ) ^ m) ^ 2 := by
        rw [hx]; ring
    _ ≤ c ^ 2 * ((Horizontal.lamh : ℝ) ^ m) ^ 2 := mul_le_mul_of_nonneg_right hγ (by positivity)
    _ = (c * (Horizontal.lamh : ℝ) ^ m) ^ 2 := by ring

/-- `|resp A_v ez (m) j| ≤ c λ^m` (with `λ_v ≤ λ`) whenever `γ_v P_v,jj ≤ c²`. -/
theorem respV_decay_gen (j : Fin 8) {c : ℝ} (hc : 0 ≤ c)
    (hγ : (Vertical.gamv : ℝ) * (Vertical.Pv j j : ℝ) ≤ c ^ 2) (m : ℕ) :
    |resp Vertical.AvR (outV 0) m j| ≤ c * lam ^ m := by
  have hr : resp Vertical.AvR (outV 0) m j = ((Vertical.AvR ^ m) *ᵥ Pi.single j 1) 0 := by
    simp [resp, outV, dotProduct, Pi.single_apply]
  have h1 := Vertical.sq_ez_le ((Vertical.AvR ^ m) *ᵥ Pi.single j 1)
  have h2 := V_pow_le m (Pi.single j 1)
  rw [Vv_single_j] at h2
  have hg : (0 : ℝ) ≤ (Vertical.gamv : ℝ) := by norm_num [Vertical.gamv]
  have hx : ((Vertical.lamv : ℝ) ^ 2) ^ m = ((Vertical.lamv : ℝ) ^ m) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hl0 : (0 : ℝ) ≤ (Vertical.lamv : ℝ) := by norm_num [Vertical.lamv]
  have hlm : (Vertical.lamv : ℝ) ^ m ≤ lam ^ m := pow_le_pow_left₀ hl0 lamv_le m
  rw [hr]
  refine abs_le_of_sq_le_sq ?_ (by have := lam_pos; positivity)
  calc _ ≤ (Vertical.gamv : ℝ) * Vertical.V _ := h1
    _ ≤ (Vertical.gamv : ℝ) * (((Vertical.lamv : ℝ) ^ 2) ^ m * (Vertical.Pv j j : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 hg
    _ = ((Vertical.gamv : ℝ) * (Vertical.Pv j j : ℝ)) * ((Vertical.lamv : ℝ) ^ m) ^ 2 := by
        rw [hx]; ring
    _ ≤ c ^ 2 * ((Vertical.lamv : ℝ) ^ m) ^ 2 := mul_le_mul_of_nonneg_right hγ (by positivity)
    _ ≤ c ^ 2 * (lam ^ m) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hlm 2
    _ = (c * lam ^ m) ^ 2 := by ring

end

end Contracts.Track.Reach.Hover
