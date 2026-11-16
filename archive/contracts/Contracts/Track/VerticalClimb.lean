import Contracts.Track.VerticalData
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Certified responses of the vertical channel (milestone M5, items 3)

From the kernel checks of `VerticalData.lean` to statements about the real model of
`Vertical.lean`:

* `XA`, the response of the error coordinates to a unit step of the target acceleration, and
  `XV`, `XP`, the free responses from a reference velocity / position jump, are within `10⁻¹²` of
  the stored integer trajectories (`XA_close`, `XV_close`): the floor rounding of the stored
  recurrence is a disturbance below `1/Sz` per tick, absorbed by the ISS bound of `VerticalCert`;
* `l1_gain`: for every target acceleration sequence with `|a k| ≤ 1` (and an exact reference),
  the vertical tracking error from rest stays below `0.1161 m` (the ℓ1 norm of the impulse
  response, computed to `3000` ticks, plus the certified tail);
* `bang_bound`: the error response to every bang-bang acceleration profile
  `+1 on [s, s+T₁)`, `-1 on [s+T₁+0.4, s+2T₁+0.4)` with `T₁ ∈ [213/400, 287/400]` and arbitrary
  real switching times is below `0.0875 m`;
* `scurve_bound`: the same bound for every average of such profiles over a probability measure of
  start times, which is the form of the S-curve climb (TRACK_PLAN.md 3.5.2; `VERTICAL.md`);
* `T1_mem_of_L`: the vertical legs `L ∈ [0.5, 0.8]` m have `T₁ ∈ [213/400, 287/400]`.
-/

namespace Contracts.Track.Vertical

open Matrix Finset

/-! ## From the Bool checks to equations -/

theorem trajOK_sound (st : V8 → V8 → Bool) :
    ∀ (n : ℕ) (l : List V8), trajOK st n l = true →
      ∀ i, i + 1 < n → i + 1 < l.length → st (l.getD i default) (l.getD (i + 1) default) = true := by
  intro n
  induction n with
  | zero => intro l _ i hi; omega
  | succ n ih =>
    intro l hl i hi hlen
    match l, hl, hlen with
    | x :: tl, hl, hlen =>
      simp only [trajOK, Bool.and_eq_true] at hl
      obtain ⟨h1, h2⟩ := hl
      cases i with
      | zero =>
        match tl, h1, hlen with
        | y :: _, h1, _ => simpa using h1
      | succ i =>
        have := ih tl h2 i (by omega) (by simp at hlen; omega)
        simpa using this

theorem getD_drop (l : List V8) (n i : ℕ) :
    (l.drop n).getD i default = l.getD (n + i) default := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem trajA_steps (m : ℕ) (hm : m + 1 < 3002) :
    stepA (trajA.getD m default) (trajA.getD (m + 1) default) = true := by
  have hc : m / 32 < 94 := by omega
  have h := trajOK_sound stepA 33 _ (trajA_chunks (m / 32) hc) (m % 32) (by omega)
    (by rw [List.length_drop, trajA_length]; omega)
  rw [getD_drop, getD_drop] at h
  have e1 : 32 * (m / 32) + m % 32 = m := Nat.div_add_mod m 32
  have e2 : 32 * (m / 32) + (m % 32 + 1) = m + 1 := by omega
  rwa [e1, e2] at h

theorem trajV_steps (m : ℕ) (hm : m + 1 < 801) :
    stepF (trajV.getD m default) (trajV.getD (m + 1) default) = true := by
  have hc : m / 32 < 25 := by omega
  have h := trajOK_sound stepF 33 _ (trajV_chunks (m / 32) hc) (m % 32) (by omega)
    (by rw [List.length_drop, trajV_length]; omega)
  rw [getD_drop, getD_drop] at h
  have e1 : 32 * (m / 32) + m % 32 = m := Nat.div_add_mod m 32
  have e2 : 32 * (m / 32) + (m % 32 + 1) = m + 1 := by omega
  rwa [e1, e2] at h

theorem stepRowsA_spec {x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : ℤ}
    (h : stepRowsA x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 = true) (i : Fin 8) :
    ![y0, y1, y2, y3, y4, y5, y6, y7] i =
      (∑ j, Ahat i j * ![x0, x1, x2, x3, x4, x5, x6, x7] j + bhat i) / DAz := by
  simp only [stepRowsA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    first
    | (rw [← h0]; congr 1; simp [Ahat, bhat, Fin.sum_univ_eight])
    | (rw [← h1]; congr 1; simp [Ahat, bhat, Fin.sum_univ_eight])
    | (rw [← h2]; congr 1; simp [Ahat, bhat, Fin.sum_univ_eight])
    | (rw [← h3]; congr 1; simp [Ahat, bhat, Fin.sum_univ_eight])
    | (rw [← h4]; congr 1; simp [Ahat, bhat, Fin.sum_univ_eight])
    | (rw [← h5]; congr 1; simp [Ahat, bhat, Fin.sum_univ_eight])
    | (rw [← h6]; congr 1; simp [Ahat, bhat, Fin.sum_univ_eight])
    | (rw [← h7]; congr 1; simp [Ahat, bhat, Fin.sum_univ_eight])

theorem stepRowsF_spec {x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : ℤ}
    (h : stepRowsF x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 = true) (i : Fin 8) :
    ![y0, y1, y2, y3, y4, y5, y6, y7] i =
      (∑ j, Ahat i j * ![x0, x1, x2, x3, x4, x5, x6, x7] j + 0) / DAz := by
  simp only [stepRowsF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;>
    first
    | (rw [← h0]; congr 1; simp [Ahat, Fin.sum_univ_eight])
    | (rw [← h1]; congr 1; simp [Ahat, Fin.sum_univ_eight])
    | (rw [← h2]; congr 1; simp [Ahat, Fin.sum_univ_eight])
    | (rw [← h3]; congr 1; simp [Ahat, Fin.sum_univ_eight])
    | (rw [← h4]; congr 1; simp [Ahat, Fin.sum_univ_eight])
    | (rw [← h5]; congr 1; simp [Ahat, Fin.sum_univ_eight])
    | (rw [← h6]; congr 1; simp [Ahat, Fin.sum_univ_eight])
    | (rw [← h7]; congr 1; simp [Ahat, Fin.sum_univ_eight])

/-- A checked transition with the step input, on decoded vectors. -/
theorem stepA_spec {x y : V8} (h : stepA x y = true) (i : Fin 8) :
    vecOf y i = (∑ j, Ahat i j * vecOf x j + bhat i) / DAz := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := x
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := y
  exact stepRowsA_spec h i

/-- A checked transition without input, on decoded vectors. -/
theorem stepF_spec {x y : V8} (h : stepF x y = true) (i : Fin 8) :
    vecOf y i = (∑ j, Ahat i j * vecOf x j + 0) / DAz := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := x
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := y
  exact stepRowsF_spec h i

/-! ## The stored trajectories as real vectors -/

theorem DAz_pos : (0 : ℤ) < DAz := by norm_num [DAz]
theorem Sz_pos : (0 : ℝ) < (Sz : ℝ) := by norm_num [Sz]

/-- The stored state as a real vector (scaled back by `Sz`). -/
noncomputable def yOf (v : V8) : Fin 8 → ℝ := fun i => (vecOf v i : ℝ) / Sz

theorem Ahat_real (i j : Fin 8) : (Ahat i j : ℝ) = (DAz : ℝ) * (Av i j : ℝ) := by
  have h := Ahat_spec i j
  have : ((Ahat i j : ℚ) : ℝ) = (((DAz : ℚ) * Av i j : ℚ) : ℝ) := by rw [h]
  push_cast at this; exact this

theorem bhat_real (i : Fin 8) : (bhat i : ℝ) = (DAz : ℝ) * (Sz : ℝ) * (Bv i : ℝ) := by
  have h := bhat_spec i
  have : ((bhat i : ℚ) : ℝ) = (((DAz : ℚ) * Sz * Bv i : ℚ) : ℝ) := by rw [h]
  push_cast at this; exact this

/-- Floor division by `DAz`, over `ℝ`. -/
theorem ediv_real (N : ℤ) : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
    (((N / DAz : ℤ)) : ℝ) = (N : ℝ) / DAz - r := by
  have hD := DAz_pos
  have hDr : (0 : ℝ) < DAz := by exact_mod_cast hD
  refine ⟨((N % DAz : ℤ) : ℝ) / DAz, div_nonneg (by exact_mod_cast Int.emod_nonneg N hD.ne') hDr.le,
    (div_lt_one hDr).mpr (by exact_mod_cast Int.emod_lt_of_pos N hD), ?_⟩
  have e := Int.mul_ediv_add_emod N DAz
  have e' : ((DAz * (N / DAz) + N % DAz : ℤ) : ℝ) = (N : ℝ) := by rw [e]
  push_cast at e'
  field_simp
  linarith

/-- A checked transition is the real affine step up to a rounding vector with entries in
`[0, 1/Sz)`. -/
theorem step_real {x y : V8} (u : Fin 8 → ℤ) (b : Fin 8 → ℝ)
    (hu : ∀ i, (u i : ℝ) = (DAz : ℝ) * Sz * b i)
    (h : ∀ i, vecOf y i = (∑ j, Ahat i j * vecOf x j + u i) / DAz) :
    ∃ ρ : Fin 8 → ℝ, (∀ i, |ρ i| ≤ 1 / Sz) ∧ yOf y = AvR *ᵥ yOf x + b - ρ := by
  have hDr : (0 : ℝ) < DAz := by exact_mod_cast DAz_pos
  have hS := Sz_pos
  choose r hr0 hr1 hr using fun i => ediv_real (∑ j, Ahat i j * vecOf x j + u i)
  refine ⟨fun i => r i / Sz, fun i => ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg (hr0 i) hS.le)]
    exact div_le_div_of_nonneg_right (hr1 i).le hS.le
  · ext i
    have e1 : ((∑ j, Ahat i j * vecOf x j + u i : ℤ) : ℝ) =
        (DAz : ℝ) * (∑ j, (Av i j : ℝ) * (vecOf x j : ℝ)) + (DAz : ℝ) * Sz * b i := by
      push_cast
      rw [hu i, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Ahat_real]; ring
    have e2 : (AvR *ᵥ yOf x) i = (∑ j, (Av i j : ℝ) * (vecOf x j : ℝ)) / Sz := by
      simp only [AvR, mulVec, dotProduct, map_apply, yOf]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [yOf, Pi.add_apply, Pi.sub_apply]
    rw [h i, hr i, e1, e2]
    field_simp

/-- The rounding error of a stored trajectory stays inside the `V`-ball of radius
`Cδ = Psum / Sz² / (1 - λ)²`. -/
noncomputable def Cδ : ℝ := (Psum : ℝ) / (Sz : ℝ) ^ 2 / (1 - (lamv : ℝ)) ^ 2

theorem Cδ_nonneg : 0 ≤ Cδ := by
  unfold Cδ; have : (0 : ℝ) ≤ Psum := by norm_num [Psum]
  positivity

theorem rounding_bound (X y : ℕ → Fin 8 → ℝ) (b : Fin 8 → ℝ) (N : ℕ)
    (hX : ∀ m, X (m + 1) = AvR *ᵥ X m + b)
    (hy : ∀ m, m < N → ∃ ρ : Fin 8 → ℝ, (∀ i, |ρ i| ≤ 1 / Sz) ∧ y (m + 1) = AvR *ᵥ y m + b - ρ)
    (h0 : X 0 = y 0) : ∀ m ≤ N, V (X m - y m) ≤ Cδ := by
  have hl1 : (0 : ℝ) < 1 - lamv := by linarith [lamv_lt_one]
  intro m
  induction m with
  | zero => intro _; rw [h0, sub_self]; simp [V, qf, Cδ_nonneg]
  | succ m ih =>
    intro hm
    obtain ⟨ρ, hρ, hy'⟩ := hy m (by omega)
    have e : X (m + 1) - y (m + 1) = AvR *ᵥ (X m - y m) + ρ := by
      rw [hX m, hy', mulVec_sub]; abel
    rw [e]
    have h1 := V_iss (X m - y m) ρ
    have h2 := V_le_of_abs_le ρ hρ
    have h3 := ih (by omega)
    have h4 : V ρ / (1 - lamv) ≤ (Psum : ℝ) * (1 / Sz) ^ 2 / (1 - lamv) :=
      div_le_div_of_nonneg_right h2 hl1.le
    have h5 : (lamv : ℝ) * V (X m - y m) ≤ lamv * Cδ :=
      mul_le_mul_of_nonneg_left h3 lamv_pos.le
    have e2 : (lamv : ℝ) * Cδ + (Psum : ℝ) * (1 / Sz) ^ 2 / (1 - lamv) = Cδ := by
      unfold Cδ; field_simp; ring
    linarith

/-- `γ Cδ ≤ (10⁻¹²)²`: the rounding moves `ez` by at most `10⁻¹²` m. -/
theorem gam_Cδ : (gamv : ℝ) * Cδ ≤ (1 / 10 ^ 12) ^ 2 := by
  unfold Cδ; norm_num [gamv, Psum, Sz, lamv]

theorem ez_close_of_V {d : Fin 8 → ℝ} (h : V d ≤ Cδ) : |d 0| ≤ 1 / 10 ^ 12 := by
  have h1 := sq_ez_le d
  have hg : (0 : ℝ) ≤ gamv := by norm_num [gamv]
  have h2 : d 0 ^ 2 ≤ (1 / 10 ^ 12) ^ 2 :=
    h1.trans ((mul_le_mul_of_nonneg_left h hg).trans gam_Cδ)
  exact abs_le_of_sq_le_sq' h2 (by norm_num) |> fun h => abs_le.mpr h

/-! ## The step response `XA` and the free responses `XV`, `XP` -/

/-- Response of the error coordinates (from rest) to a unit step of the target acceleration. -/
noncomputable def XA : ℕ → Fin 8 → ℝ := traj AvR 0 (fun _ => BvR)
/-- Free response from `-h e₁` (reference velocity jump of `h`). -/
noncomputable def XV : ℕ → Fin 8 → ℝ := traj AvR (-(per : ℝ) • e1) (fun _ => 0)
/-- Free response from `-(h²/2) e₀` (reference position jump of `h²/2`). -/
noncomputable def XP : ℕ → Fin 8 → ℝ := traj AvR (-((per : ℝ) ^ 2 / 2) • e0) (fun _ => 0)

noncomputable def yA (m : ℕ) : Fin 8 → ℝ := yOf (trajA.getD m default)
noncomputable def yV (m : ℕ) : Fin 8 → ℝ := yOf (trajV.getD m default)

theorem XA_V_close : ∀ m ≤ 3001, V (XA m - yA m) ≤ Cδ := by
  refine rounding_bound XA yA BvR 3001 (fun m => traj_succ _ _ _ m) (fun m hm => ?_) ?_
  · exact step_real bhat BvR (fun i => by rw [bhat_real]; simp [BvR])
      (stepA_spec (trajA_steps m (by omega)))
  · ext i; simp only [XA, yA, yOf, traj_zero]; rw [trajA_zero]; simp

theorem XV_V_close : ∀ m ≤ 800, V (XV m - yV m) ≤ Cδ := by
  refine rounding_bound XV yV 0 800 (fun m => by simp [XV, traj_succ]) (fun m hm => ?_) ?_
  · exact step_real 0 0 (fun i => by simp) (fun i => by
      simpa using stepF_spec (trajV_steps m (by omega)) i)
  · ext i
    simp only [XV, yV, yOf, traj_zero, trajV_zero]
    fin_cases i <;> simp [e1, Sz]
    norm_num [per]

theorem XA_close (m : ℕ) (hm : m ≤ 3001) : |XA m 0 - yA m 0| ≤ 1 / 10 ^ 12 := by
  simpa using ez_close_of_V (XA_V_close m hm)

theorem XV_close (m : ℕ) (hm : m ≤ 800) : |XV m 0 - yV m 0| ≤ 1 / 10 ^ 12 := by
  simpa using ez_close_of_V (XV_V_close m hm)

/-! ## Tools: casts of rational vectors, free motion, Young with `η = 1/100` -/

theorem V_cast (v : Fin 8 → ℚ) : V (fun i => (v i : ℝ)) = ((qfQ Pv v : ℚ) : ℝ) := by
  simp [V, qf, qfQ, PvR, castM, dotProduct, mulVec, Fin.sum_univ_eight]

theorem yOf_eq_cast (v : V8) : yOf v = fun i => ((vecQ v i : ℚ) : ℝ) := by
  ext i; simp [yOf, vecQ]

/-- Along the free motion `D (m+1) = Av D m`, `V` does not increase. -/
theorem V_free_le (D : ℕ → Fin 8 → ℝ) (hD : ∀ m, D (m + 1) = AvR *ᵥ D m) (M : ℕ) :
    ∀ m, M ≤ m → V (D m) ≤ V (D M) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact le_refl _
  | succ m _ ih => rw [hD m]; exact (V_A_le _).trans ih

theorem V_young (a b : Fin 8 → ℝ) : V (a + b) ≤ (101 / 100) * V a + 101 * V b := by
  have h := qf_add_le PvR PvR_symm (fun z => V_nonneg z) (η := 1 / 100) (by norm_num) a b
  have e : (1 : ℝ) + 1 / (1 / 100) = 101 := by norm_num
  rw [e] at h
  have e2 : (1 : ℝ) + 1 / 100 = 101 / 100 := by norm_num
  rw [e2] at h
  exact h

theorem abs_le_of_gamV {x : Fin 8 → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : (gamv : ℝ) * V x ≤ c ^ 2) :
    |x 0| ≤ c :=
  abs_le_of_sq_le_sq' ((sq_ez_le x).trans h) hc |> fun h => abs_le.mpr h

/-! ## The pattern sums -/

theorem allB_sound (B : ℕ) : ∀ (n : ℕ) (a b c d : List ℕ), allB B n a b c d = true →
    ∀ k, k < n → k < a.length → k < b.length → k < c.length → k < d.length →
      a.getD k 0 + d.getD k 0 ≤ b.getD k 0 + c.getD k 0 + B ∧
        b.getD k 0 + c.getD k 0 ≤ a.getD k 0 + d.getD k 0 + B := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ k hk; omega
  | succ n ih =>
    intro a b c d h k hk ha hb hc hd
    match a, b, c, d, h, ha, hb, hc, hd with
    | x :: as, y :: bs, z :: cs, w :: ds, h, ha, hb, hc, hd =>
      simp only [allB, Bool.and_eq_true, Nat.ble_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      cases k with
      | zero => simp; omega
      | succ k =>
        simp only [List.length_cons] at ha hb hc hd
        have := ih as bs cs ds h3 k (by omega) (by omega) (by omega) (by omega) (by omega)
        simpa using this

theorem getD_rep_append (G : ℕ) (E : List ℕ) (k : ℕ) :
    (List.replicate G OFFz ++ E).getD k 0 = if k < G then OFFz else E.getD (k - G) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_replicate,
    List.getElem?_replicate]
  split_ifs <;> simp_all

theorem Elist_getD (m : ℕ) : dz (Elist.getD m 0) = vecOf (trajA.getD m default) 0 := by
  simp only [Elist, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases trajA[m]? <;> rfl

theorem Elist_length : Elist.length = 3002 := by simp [Elist, trajA_length]

theorem dz_OFF : dz OFFz = 0 := by simp [dz]

/-- The integer pattern sum. -/
noncomputable def eZ (G1 G3 k : ℕ) : ℤ :=
  vecOf (trajA.getD k default) 0 - (if G1 ≤ k then vecOf (trajA.getD (k - G1) default) 0 else 0) -
    (if G1 + 160 ≤ k then vecOf (trajA.getD (k - (G1 + 160)) default) 0 else 0) +
    (if G1 + 160 + G3 ≤ k then vecOf (trajA.getD (k - (G1 + 160 + G3)) default) 0 else 0)

theorem patOK_sound {G1 G3 : ℕ} (h : patOK Bpat G1 G3 = true) (k : ℕ) (hk : k < 1736) :
    |eZ G1 G3 k| ≤ (Bpat : ℤ) := by
  have hs := allB_sound Bpat 1736 _ _ _ _ h k hk (by rw [Elist_length]; omega)
    (by simp [Elist_length]; omega) (by simp [Elist_length]; omega) (by simp [Elist_length]; omega)
  rw [getD_rep_append, getD_rep_append, getD_rep_append] at hs
  have key : eZ G1 G3 k = dz (Elist.getD k 0) -
      dz (if k < G1 then OFFz else Elist.getD (k - G1) 0) -
      dz (if k < G1 + 160 then OFFz else Elist.getD (k - (G1 + 160)) 0) +
      dz (if k < G1 + 160 + G3 then OFFz else Elist.getD (k - (G1 + 160 + G3)) 0) := by
    simp only [eZ]
    split_ifs <;> first | omega | simp only [Elist_getD, dz_OFF]
  rw [key, abs_le]
  simp only [dz] at hs ⊢
  split_ifs at hs ⊢ <;> constructor <;> omega

/-- The real pattern sum of the step response. -/
noncomputable def sumA (G1 G3 k : ℕ) : ℝ :=
  XA k 0 - (if G1 ≤ k then XA (k - G1) 0 else 0) - (if G1 + 160 ≤ k then XA (k - (G1 + 160)) 0 else 0) +
    (if G1 + 160 + G3 ≤ k then XA (k - (G1 + 160 + G3)) 0 else 0)

/-- `BA = 0.0849`: the bound of the pattern sums. -/
noncomputable def BA : ℝ := 849 / 10000

theorem sumA_head {G1 G3 : ℕ} (h : patOK Bpat G1 G3 = true) (k : ℕ) (hk : k < 1736) :
    |sumA G1 G3 k| ≤ BA := by
  have hz := patOK_sound h k hk
  have hzr : |(eZ G1 G3 k : ℝ)| ≤ (Bpat : ℝ) := by exact_mod_cast hz
  have hS := Sz_pos
  -- the stored sum, scaled back
  have e : (eZ G1 G3 k : ℝ) / Sz = yA k 0 - (if G1 ≤ k then yA (k - G1) 0 else 0) -
      (if G1 + 160 ≤ k then yA (k - (G1 + 160)) 0 else 0) +
      (if G1 + 160 + G3 ≤ k then yA (k - (G1 + 160 + G3)) 0 else 0) := by
    simp only [eZ, yA, yOf]
    split_ifs <;> push_cast
    all_goals ring
  have c0 := XA_close k (by omega)
  have c1 : |(if G1 ≤ k then XA (k - G1) 0 else 0) - (if G1 ≤ k then yA (k - G1) 0 else 0)| ≤
      1 / 10 ^ 12 := by
    split_ifs
    · exact XA_close _ (by omega)
    · simp
  have c2 : |(if G1 + 160 ≤ k then XA (k - (G1 + 160)) 0 else 0) -
      (if G1 + 160 ≤ k then yA (k - (G1 + 160)) 0 else 0)| ≤ 1 / 10 ^ 12 := by
    split_ifs
    · exact XA_close _ (by omega)
    · simp
  have c3 : |(if G1 + 160 + G3 ≤ k then XA (k - (G1 + 160 + G3)) 0 else 0) -
      (if G1 + 160 + G3 ≤ k then yA (k - (G1 + 160 + G3)) 0 else 0)| ≤ 1 / 10 ^ 12 := by
    split_ifs
    · exact XA_close _ (by omega)
    · simp
  have hy : |(eZ G1 G3 k : ℝ) / Sz| ≤ (Bpat : ℝ) / Sz := by
    rw [abs_div, abs_of_pos hS]; exact div_le_div_of_nonneg_right hzr hS.le
  rw [e] at hy
  have hB : (Bpat : ℝ) / Sz + 4 / 10 ^ 12 ≤ BA := by norm_num [Bpat, Sz, BA]
  unfold sumA
  rw [abs_le] at c0 c1 c2 c3 hy ⊢
  constructor <;> linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2, hy.1, hy.2]

/-- The steady state of the step response over `ℝ`. -/
noncomputable def XinfR : Fin 8 → ℝ := fun i => (Xinf i : ℝ)

theorem XinfR_fixed : AvR *ᵥ XinfR + BvR = XinfR := by
  have h := Xinf_fixed
  ext i
  have hi := congrFun h i
  have : (((Av *ᵥ Xinf + Bv) i : ℚ) : ℝ) = ((Xinf i : ℚ) : ℝ) := by rw [hi]
  simpa [AvR, BvR, XinfR, mulVec, dotProduct, Fin.sum_univ_eight] using this

theorem XA_sub_Xinf_succ (m : ℕ) : XA (m + 1) - XinfR = AvR *ᵥ (XA m - XinfR) := by
  have h1 : XA (m + 1) = AvR *ᵥ XA m + BvR := traj_succ _ _ _ m
  rw [h1, mulVec_sub]
  conv_lhs => rw [← XinfR_fixed]
  abel

theorem XinfR_zero : XinfR 0 = 0 := by simp [XinfR, Xinf]

/-- From tick 1000 on, `|ez|` of the step response is below `0.014`. -/
theorem XA_tail (m : ℕ) (hm : 1000 ≤ m) : |XA m 0| ≤ 14 / 1000 := by
  have hmono := V_free_le (fun m => XA m - XinfR) XA_sub_Xinf_succ 1000 m hm
  have hsplit : XA 1000 - XinfR = (yA 1000 - XinfR) + (XA 1000 - yA 1000) := by abel
  have hy : V (yA 1000 - XinfR) ≤ ((1 / gamv * (18 / 100000) : ℚ) : ℝ) := by
    have h := tailA_check
    have e : yA 1000 - XinfR = fun i => ((vecQ (trajA.getD 1000 default) - Xinf) i : ℝ) := by
      ext i; simp [yA, yOf_eq_cast, XinfR]
    rw [e, V_cast]; exact_mod_cast h
  have hd := XA_V_close 1000 (by norm_num)
  have hY := V_young (yA 1000 - XinfR) (XA 1000 - yA 1000)
  rw [← hsplit] at hY
  have hg : (0 : ℝ) < gamv := by norm_num [gamv]
  have hC := gam_Cδ
  have hb : (gamv : ℝ) * V (XA m - XinfR) ≤ (14 / 1000) ^ 2 := by
    have : (gamv : ℝ) * V (XA m - XinfR) ≤ gamv * ((101 / 100) * ((1 / gamv * (18 / 100000) : ℚ) : ℝ) + 101 * Cδ) :=
      mul_le_mul_of_nonneg_left (hmono.trans (hY.trans (by linarith))) hg.le
    refine this.trans ?_
    have e : (gamv : ℝ) * ((101 / 100) * ((1 / gamv * (18 / 100000) : ℚ) : ℝ) + 101 * Cδ) =
        (101 / 100) * (18 / 100000) + 101 * (gamv * Cδ) := by
      push_cast; field_simp
    rw [e]; nlinarith
  have := abs_le_of_gamV (by norm_num) hb
  simpa [XinfR_zero] using this

/-- **The pattern sums are bounded for all ticks** (`G1 ∈ [213, 287]`, `|G3 - G1| ≤ 1`). -/
theorem sumA_bound (G1 G3 : ℕ) (h1 : 213 ≤ G1) (h2 : G1 ≤ 287) (h3 : G1 ≤ G3 + 1) (h4 : G3 ≤ G1 + 1)
    (k : ℕ) : |sumA G1 G3 k| ≤ BA := by
  have hpat : patOK Bpat G1 G3 = true := by
    have := pat_all (G1 - 213) (by omega)
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨ha, hb⟩, hc⟩ := this
    rcases (by omega : G3 = G1 ∨ G3 = G1 + 1 ∨ G3 = G1 - 1) with e | e | e
    · rw [e]; rwa [show 213 + (G1 - 213) = G1 by omega] at ha
    · rw [e]; rwa [show 213 + (G1 - 213) = G1 by omega, show 214 + (G1 - 213) = G1 + 1 by omega] at hb
    · rw [e]; rwa [show 213 + (G1 - 213) = G1 by omega, show 212 + (G1 - 213) = G1 - 1 by omega] at hc
  by_cases hk : k < 1736
  · exact sumA_head hpat k hk
  · have t0 := XA_tail k (by omega)
    have t1 := XA_tail (k - G1) (by omega)
    have t2 := XA_tail (k - (G1 + 160)) (by omega)
    have t3 := XA_tail (k - (G1 + 160 + G3)) (by omega)
    have e : sumA G1 G3 k = XA k 0 - XA (k - G1) 0 - XA (k - (G1 + 160)) 0 + XA (k - (G1 + 160 + G3)) 0 := by
      have h1 : G1 ≤ k := by omega
      have h2 : G1 + 160 ≤ k := by omega
      have h3 : G1 + 160 + G3 ≤ k := by omega
      simp only [sumA, h1, h2, h3, ite_true]
    rw [e]
    rw [abs_le] at t0 t1 t2 t3 ⊢
    unfold BA
    constructor <;> linarith [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2]

/-! ## The free responses `XV`, `XP` -/

theorem allAbsLe_sound (B : ℕ) : ∀ (l : List ℕ), allAbsLe B l = true → ∀ k, k < l.length →
    l.getD k 0 ≤ OFFz + B ∧ OFFz ≤ l.getD k 0 + B := by
  intro l
  induction l with
  | nil => intro _ k hk; simp at hk
  | cons a tl ih =>
    intro h k hk
    simp only [allAbsLe, Bool.and_eq_true, Nat.ble_eq] at h
    cases k with
    | zero => exact h.1
    | succ k => exact ih h.2 k (by simpa using hk)

/-- `BV = 0.00064`. -/
noncomputable def BV : ℝ := 64 / 100000

theorem XV_head (m : ℕ) (hm : m ≤ 800) : |XV m 0| ≤ BV := by
  have h := allAbsLe_sound BVz _ EV_check m (by simp [trajV_length]; omega)
  have hl : (trajV.map (fun v => v.1)).getD m 0 = (trajV.getD m default).1 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases trajV[m]? <;> rfl
  rw [hl] at h
  have hz : |vecOf (trajV.getD m default) 0| ≤ (BVz : ℤ) := by
    simp only [vecOf, Matrix.cons_val_zero, dz]
    rw [abs_le]; constructor <;> omega
  have hzr : |(vecOf (trajV.getD m default) 0 : ℝ)| ≤ (BVz : ℝ) := by exact_mod_cast hz
  have hS := Sz_pos
  have hy : |yV m 0| ≤ (BVz : ℝ) / Sz := by
    simp only [yV, yOf]; rw [abs_div, abs_of_pos hS]; exact div_le_div_of_nonneg_right hzr hS.le
  have c := XV_close m hm
  have hB : (BVz : ℝ) / Sz + 1 / 10 ^ 12 ≤ BV := by norm_num [BVz, Sz, BV]
  rw [abs_le] at c hy ⊢
  constructor <;> linarith [c.1, c.2, hy.1, hy.2]

theorem XV_succ (m : ℕ) : XV (m + 1) = AvR *ᵥ XV m := by simp [XV, traj_succ]
theorem XP_succ (m : ℕ) : XP (m + 1) = AvR *ᵥ XP m := by simp [XP, traj_succ]

theorem XV_bound (m : ℕ) : |XV m 0| ≤ BV := by
  by_cases hm : m ≤ 800
  · exact XV_head m hm
  · have hmono := V_free_le XV XV_succ 800 m (by omega)
    have hsplit : XV 800 = yV 800 + (XV 800 - yV 800) := by abel
    have hy : V (yV 800) ≤ ((1 / gamv * (21 / 10 ^ 9) : ℚ) : ℝ) := by
      have e : yV 800 = fun i => ((vecQ (trajV.getD 800 default)) i : ℝ) := by
        ext i; simp [yV, yOf_eq_cast]
      rw [e, V_cast]; exact_mod_cast tailV_check
    have hY := V_young (yV 800) (XV 800 - yV 800)
    rw [← hsplit] at hY
    have hd := XV_V_close 800 le_rfl
    have hg : (0 : ℝ) < gamv := by norm_num [gamv]
    have hC := gam_Cδ
    have hb : (gamv : ℝ) * V (XV m) ≤ BV ^ 2 := by
      have : (gamv : ℝ) * V (XV m) ≤ gamv * ((101 / 100) * ((1 / gamv * (21 / 10 ^ 9) : ℚ) : ℝ) + 101 * Cδ) :=
        mul_le_mul_of_nonneg_left (hmono.trans (hY.trans (by linarith))) hg.le
      refine this.trans ?_
      have e : (gamv : ℝ) * ((101 / 100) * ((1 / gamv * (21 / 10 ^ 9) : ℚ) : ℝ) + 101 * Cδ) =
          (101 / 100) * (21 / 10 ^ 9) + 101 * (gamv * Cδ) := by
        push_cast; field_simp
      rw [e]; unfold BV; nlinarith
    exact abs_le_of_gamV (by norm_num [BV]) hb

/-- `BP = 10⁻⁵`. -/
noncomputable def BP : ℝ := 1 / 100000

theorem XP_bound (m : ℕ) : |XP m 0| ≤ BP := by
  have hmono := V_free_le XP XP_succ 0 m (Nat.zero_le m)
  have h0 : XP 0 = fun i => ((vP i : ℚ) : ℝ) := by
    ext i; fin_cases i <;> simp [XP, e0, vP]
  have hb : (gamv : ℝ) * V (XP m) ≤ BP ^ 2 := by
    have hg : (0 : ℝ) ≤ gamv := by norm_num [gamv]
    have h1 : (gamv : ℝ) * V (XP 0) ≤ 1 / 10 ^ 10 := by
      rw [h0, V_cast]
      have h2 := (Rat.cast_le (K := ℝ)).mpr EP_check
      push_cast at h2
      exact h2
    have := mul_le_mul_of_nonneg_left hmono hg
    unfold BP; nlinarith
  exact abs_le_of_gamV (by norm_num [BP]) hb

/-! ## ℓ1 gain: inputs bounded by `|a| ≤ 1 m/s²` -/

/-- Increment of the step response = impulse response: `G m = Av^m Bv`. -/
noncomputable def G (m : ℕ) : Fin 8 → ℝ := XA (m + 1) - XA m

theorem XA_succ (m : ℕ) : XA (m + 1) = AvR *ᵥ XA m + BvR := traj_succ _ _ _ m

theorem G_succ (m : ℕ) : G (m + 1) = AvR *ᵥ G m := by
  simp only [G]
  rw [XA_succ (m + 1), XA_succ m, mulVec_sub, mulVec_add]; abel

theorem G_eq_pow (m : ℕ) : G m = (AvR ^ m) *ᵥ BvR := by
  induction m with
  | zero => simp [G, XA, traj_succ]
  | succ m ih => rw [G_succ, ih, mulVec_mulVec, ← pow_succ']

theorem l1sum_eq : ∀ (n : ℕ) (l : List ℕ), n < l.length →
    l1sum n l = ∑ m ∈ range n, (max (l.getD m 0) (l.getD (m + 1) 0) - min (l.getD m 0) (l.getD (m + 1) 0)) := by
  intro n
  induction n with
  | zero => intro l _; simp [l1sum]
  | succ n ih =>
    intro l hl
    match l, hl with
    | a :: tl, hl =>
      simp only [List.length_cons] at hl
      rw [sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [← ih tl (by omega)]
      match tl, hl with
      | b :: tl', _ => simp only [l1sum, List.getD_cons_zero]; ring

theorem natDist_eq (a b : ℕ) : ((max a b - min a b : ℕ) : ℝ) = |(dz b : ℝ) - (dz a : ℝ)| := by
  simp only [dz]
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, Nat.cast_sub h]; push_cast
    rw [abs_of_nonneg (by have : (a : ℝ) ≤ b := by exact_mod_cast h
                          linarith)]; ring
  · rw [max_eq_left h, min_eq_right h, Nat.cast_sub h]; push_cast
    rw [abs_of_nonpos (by have : (b : ℝ) ≤ a := by exact_mod_cast h
                          linarith)]; ring

theorem V_neg (x : Fin 8 → ℝ) : V (-x) = V x := by
  simp [V, qf, mulVec_neg]

theorem V_add_two (a b : Fin 8 → ℝ) : V (a + b) ≤ 2 * V a + 2 * V b := by
  have h := qf_add_le PvR PvR_symm (fun z => V_nonneg z) (η := 1) (by norm_num) a b
  norm_num at h
  simpa [V] using h

/-- The computed part of the ℓ1 norm: `Σ_{m < 3000} |g m| ≤ L1z/Sz + 6·10⁻⁹`. -/
theorem l1_head : ∑ m ∈ range 3000, |G m 0| ≤ (L1z : ℝ) / Sz + 3000 * (2 / 10 ^ 12) := by
  have hS := Sz_pos
  have hl := l1sum_eq 3000 Elist (by rw [Elist_length]; norm_num)
  have hc : ((l1sum 3000 Elist : ℕ) : ℝ) ≤ (L1z : ℝ) := by exact_mod_cast l1_check
  rw [hl] at hc
  push_cast [Nat.cast_sum] at hc
  have hterm : ∀ m ∈ range 3000, |G m 0| ≤
      ((max (Elist.getD m 0) (Elist.getD (m + 1) 0) - min (Elist.getD m 0) (Elist.getD (m + 1) 0) : ℕ) : ℝ) / Sz
        + 2 / 10 ^ 12 := by
    intro m hm
    have hm := mem_range.mp hm
    rw [natDist_eq, Elist_getD, Elist_getD]
    have c0 := XA_close m (by omega)
    have c1 := XA_close (m + 1) (by omega)
    have e0 : yA (m + 1) 0 - yA m 0 =
        ((vecOf (trajA.getD (m + 1) default) 0 : ℝ) - (vecOf (trajA.getD m default) 0 : ℝ)) / Sz := by
      simp only [yA, yOf]; ring
    have e : |(vecOf (trajA.getD (m + 1) default) 0 : ℝ) - (vecOf (trajA.getD m default) 0 : ℝ)| / Sz =
        |yA (m + 1) 0 - yA m 0| := by
      rw [e0, abs_div, abs_of_pos hS]
    rw [e]
    have e2 : G m 0 = (yA (m + 1) 0 - yA m 0) + (XA (m + 1) 0 - yA (m + 1) 0) - (XA m 0 - yA m 0) := by
      simp only [G, Pi.sub_apply]; ring
    rw [e2]
    rw [abs_le] at c0 c1 ⊢
    have t := abs_le.mp (le_refl |yA (m + 1) 0 - yA m 0|)
    constructor <;> linarith [c0.1, c0.2, c1.1, c1.2, t.1, t.2, neg_abs_le (yA (m + 1) 0 - yA m 0),
      le_abs_self (yA (m + 1) 0 - yA m 0)]
  calc ∑ m ∈ range 3000, |G m 0|
      ≤ ∑ m ∈ range 3000, (((max (Elist.getD m 0) (Elist.getD (m + 1) 0) -
          min (Elist.getD m 0) (Elist.getD (m + 1) 0) : ℕ) : ℝ) / Sz + 2 / 10 ^ 12) := sum_le_sum hterm
    _ = (∑ m ∈ range 3000, ((max (Elist.getD m 0) (Elist.getD (m + 1) 0) -
          min (Elist.getD m 0) (Elist.getD (m + 1) 0) : ℕ) : ℝ)) / Sz + 3000 * (2 / 10 ^ 12) := by
        rw [sum_add_distrib, ← sum_div]
        simp
    _ ≤ (L1z : ℝ) / Sz + 3000 * (2 / 10 ^ 12) := by
        gcongr

/-- The tail of the impulse response beyond `3000` ticks. -/
theorem G_tail (t : ℕ) : |G (3000 + t) 0| ≤ (lamv : ℝ) ^ t * (21 / 10 ^ 8) := by
  have hV : ∀ t, V (G (3000 + t)) ≤ ((lamv : ℝ) ^ 2) ^ t * V (G 3000) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [← add_assoc, G_succ]
      calc V (AvR *ᵥ G (3000 + t)) ≤ (lamv : ℝ) ^ 2 * V (G (3000 + t)) := V_A _
        _ ≤ (lamv : ℝ) ^ 2 * (((lamv : ℝ) ^ 2) ^ t * V (G 3000)) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((lamv : ℝ) ^ 2) ^ (t + 1) * V (G 3000) := by ring
  have hsplit : G 3000 = (yA 3001 - yA 3000) + ((XA 3001 - yA 3001) + -(XA 3000 - yA 3000)) := by
    simp only [G]; abel
  have hy : V (yA 3001 - yA 3000) ≤ ((1 / gamv * (4 / 10 ^ 14) : ℚ) : ℝ) := by
    have e : yA 3001 - yA 3000 =
        fun i => ((vecQ (trajA.getD 3001 default) - vecQ (trajA.getD 3000 default)) i : ℝ) := by
      ext i; simp [yA, yOf_eq_cast]
    rw [e, V_cast]; exact_mod_cast tailG_check
  have hd1 := XA_V_close 3001 le_rfl
  have hd0 := XA_V_close 3000 (by norm_num)
  have hY := V_young (yA 3001 - yA 3000) ((XA 3001 - yA 3001) + -(XA 3000 - yA 3000))
  have h2 := V_add_two (XA 3001 - yA 3001) (-(XA 3000 - yA 3000))
  rw [V_neg] at h2
  rw [← hsplit] at hY
  have hg : (0 : ℝ) < gamv := by norm_num [gamv]
  have hC := gam_Cδ
  have hG : (gamv : ℝ) * V (G 3000) ≤ (21 / 10 ^ 8) ^ 2 := by
    have : (gamv : ℝ) * V (G 3000) ≤ gamv * ((101 / 100) * ((1 / gamv * (4 / 10 ^ 14) : ℚ) : ℝ) +
        101 * (4 * Cδ)) := mul_le_mul_of_nonneg_left (by linarith) hg.le
    refine this.trans ?_
    have e : (gamv : ℝ) * ((101 / 100) * ((1 / gamv * (4 / 10 ^ 14) : ℚ) : ℝ) + 101 * (4 * Cδ)) =
        (101 / 100) * (4 / 10 ^ 14) + 404 * (gamv * Cδ) := by
      push_cast; field_simp; ring
    rw [e]; nlinarith
  have hb : (gamv : ℝ) * V (G (3000 + t)) ≤ ((lamv : ℝ) ^ t * (21 / 10 ^ 8)) ^ 2 := by
    calc (gamv : ℝ) * V (G (3000 + t)) ≤ gamv * (((lamv : ℝ) ^ 2) ^ t * V (G 3000)) :=
          mul_le_mul_of_nonneg_left (hV t) hg.le
      _ = ((lamv : ℝ) ^ 2) ^ t * (gamv * V (G 3000)) := by ring
      _ ≤ ((lamv : ℝ) ^ 2) ^ t * (21 / 10 ^ 8) ^ 2 := mul_le_mul_of_nonneg_left hG (by positivity)
      _ = ((lamv : ℝ) ^ t * (21 / 10 ^ 8)) ^ 2 := by ring
  exact abs_le_of_gamV (by have := lamv_pos; positivity) hb

/-- `Σ_{j<n} |g j| ≤ 0.1161` for every `n`. -/
theorem l1_total (n : ℕ) : ∑ j ∈ range n, |G j 0| ≤ 1161 / 10000 := by
  have hh := l1_head
  have hl1 : (0 : ℝ) < 1 - lamv := by linarith [lamv_lt_one]
  have htail : ∀ T, ∑ t ∈ range T, |G (3000 + t) 0| ≤ (21 / 10 ^ 8) / (1 - lamv) := by
    intro T
    calc ∑ t ∈ range T, |G (3000 + t) 0| ≤ ∑ t ∈ range T, (lamv : ℝ) ^ t * (21 / 10 ^ 8) :=
          sum_le_sum fun t _ => G_tail t
      _ = (∑ t ∈ range T, (lamv : ℝ) ^ t) * (21 / 10 ^ 8) := by rw [sum_mul]
      _ ≤ 1 / (1 - lamv) * (21 / 10 ^ 8) := by
          gcongr
          have hm := mul_neg_geom_sum (lamv : ℝ) T
          rw [le_div_iff₀ hl1]
          nlinarith [pow_nonneg lamv_pos.le T]
      _ = (21 / 10 ^ 8) / (1 - lamv) := by ring
  have hnum : (L1z : ℝ) / Sz + 3000 * (2 / 10 ^ 12) + (21 / 10 ^ 8) / (1 - lamv) ≤ 1161 / 10000 := by
    norm_num [L1z, Sz, lamv]
  have hpos : ∀ j, 0 ≤ |G j 0| := fun j => abs_nonneg _
  by_cases hn : n ≤ 3000
  · calc ∑ j ∈ range n, |G j 0| ≤ ∑ j ∈ range 3000, |G j 0| :=
          sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hn) (fun j _ _ => hpos j)
      _ ≤ 1161 / 10000 := by have := htail 0; simp at this; linarith
  · obtain ⟨T, rfl⟩ : ∃ T, n = 3000 + T := ⟨n - 3000, by omega⟩
    rw [sum_range_add]
    have := htail T
    linarith

/-- **ℓ1 gain of the vertical loop.** For every target acceleration sequence with
`|a k| ≤ 1 m/s²` and an exact reference (no defects), the vertical tracking error from rest
satisfies `|ez n| ≤ 0.1161 m` at every tick. -/
theorem l1_gain (a : ℕ → ℝ) (ha : ∀ k, |a k| ≤ 1) (n : ℕ) :
    |traj AvR 0 (fun k => a k • BvR) n 0| ≤ 1161 / 10000 := by
  rw [traj_eq_sum]
  have e : (∑ j ∈ range n, (AvR ^ (n - 1 - j)) *ᵥ (a j • BvR)) 0 =
      ∑ j ∈ range n, a j * G (n - 1 - j) 0 := by
    rw [Finset.sum_apply]
    refine sum_congr rfl fun j _ => ?_
    rw [mulVec_smul, G_eq_pow]; rfl
  rw [e]
  calc |∑ j ∈ range n, a j * G (n - 1 - j) 0| ≤ ∑ j ∈ range n, |a j * G (n - 1 - j) 0| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range n, |G (n - 1 - j) 0| := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (ha j)
    _ = ∑ j ∈ range n, |G j 0| := sum_range_reflect (fun j => |G j 0|) n
    _ ≤ 1161 / 10000 := l1_total n

/-! ## Target sequences, the error response and the code's variables -/

/-- The forcing of the error coordinates by a target sequence `r k = (sp, vsp, asp)`. -/
noncomputable def forceOf (r : ℕ → ℝ × ℝ × ℝ) (k : ℕ) : Fin 8 → ℝ :=
  (r k).2.2 • BvR - defect₁ (r k).1 (r (k + 1)).1 (r k).2.1 (r k).2.2 • e0 -
    defect₂ (r k).2.1 (r (k + 1)).2.1 (r k).2.2 • e1

/-- The error response (from trim, zero error) of the vertical channel to a target sequence. -/
noncomputable def errResp (r : ℕ → ℝ × ℝ × ℝ) : ℕ → Fin 8 → ℝ := traj AvR 0 (forceOf r)

/-- **The error response is the code's tracking error.** If the code's variables evolve by
`absTick` with the target sequence `r`, from a state with zero error coordinates, then their error
coordinates are `errResp r`; in particular `z k - sp k = errResp r k 0`. -/
theorem errResp_eq_code (x : ℕ → VAbs) (r : ℕ → ℝ × ℝ × ℝ)
    (hx : ∀ k, x (k + 1) = absTick (x k) (r k).1 (r k).2.1 (r k).2.2)
    (h0 : errOf (x 0) (r 0).1 (r 0).2.1 = 0) (k : ℕ) :
    errOf (x k) (r k).1 (r k).2.1 = errResp r k := by
  induction k with
  | zero => simpa [errResp] using h0
  | succ k ih =>
    rw [hx k, errOf_absTick, tick_eq, ih]
    rfl

theorem traj_comb4 (u0 u1 u2 u3 : ℕ → Fin 8 → ℝ) (n : ℕ) :
    traj AvR 0 (fun k => u0 k - u1 k - u2 k + u3 k) n =
      traj AvR 0 u0 n - traj AvR 0 u1 n - traj AvR 0 u2 n + traj AvR 0 u3 n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [traj_succ, ih, mulVec_add, mulVec_sub]; abel

/-! ## Acceleration steps at real switching times -/

/-- The sampled target of a unit acceleration step at time `s`: at tick `k`, position
`(kh - s)²/2`, velocity `kh - s`, acceleration `1` once `kh ≥ s`, and zero before. -/
noncomputable def stepRef (s : ℝ) (k : ℕ) : ℝ × ℝ × ℝ :=
  if s ≤ (k : ℝ) * per then ((((k : ℝ) * per - s) ^ 2 / 2), ((k : ℝ) * per - s), 1) else (0, 0, 0)

/-- First tick at or after `s`. -/
noncomputable def Jof (s : ℝ) : ℕ := ⌈s / (per : ℝ)⌉₊
/-- Phase of `s` inside its tick: `Jof s - s/h ∈ [0, 1)`. -/
noncomputable def ψof (s : ℝ) : ℝ := (Jof s : ℝ) - s / per

theorem per_pos : (0 : ℝ) < per := by norm_num [per]

theorem Jof_le_iff (s : ℝ) (k : ℕ) : Jof s ≤ k ↔ s ≤ (k : ℝ) * per := by
  rw [Jof, Nat.ceil_le, div_le_iff₀ per_pos]

theorem ψof_nonneg (s : ℝ) : 0 ≤ ψof s := by
  have := Nat.le_ceil (s / (per : ℝ)); simp only [ψof, Jof]; linarith

theorem ψof_lt_one (s : ℝ) (hs : 0 ≤ s) : ψof s < 1 := by
  have := Nat.ceil_lt_add_one (div_nonneg hs per_pos.le); simp only [ψof, Jof]; linarith

theorem ψof_per (s : ℝ) : ψof s * per = (Jof s : ℝ) * per - s := by
  simp only [ψof]; field_simp [per_pos.ne']

theorem ψof_zero_of_J (s : ℝ) (hs : 0 ≤ s) (hJ : Jof s = 0) : ψof s = 0 := by
  have h := (Jof_le_iff s 0).mp (le_of_eq hJ)
  simp at h
  have : s = 0 := le_antisymm h hs
  rw [ψof, hJ, this]; simp

/-- The forcing of an acceleration step: a delayed constant input and, at the tick before the
switch, the jump of the sampled position and velocity. -/
theorem forceOf_stepRef (s : ℝ) (k : ℕ) :
    forceOf (stepRef s) k = (if Jof s ≤ k then BvR else 0) +
      (if k + 1 = Jof s then ψof s • (-(per : ℝ) • e1) + ψof s ^ 2 • (-((per : ℝ) ^ 2 / 2) • e0)
        else 0) := by
  have hJ1 : Jof s ≤ k + 1 ↔ s ≤ ((k : ℝ) + 1) * per := by
    rw [Jof_le_iff]; push_cast; rfl
  by_cases hA : Jof s ≤ k
  · have h1 : s ≤ (k : ℝ) * per := (Jof_le_iff s k).mp hA
    have h2 : s ≤ ((k : ℝ) + 1) * per := hJ1.mp (by omega)
    have hne : ¬ (k + 1 = Jof s) := by omega
    rw [ite_eq_left hA, ite_eq_right hne, add_zero]
    ext i
    simp [forceOf, stepRef, h1, h2, defect₁, defect₂]
    ring
  · have h1 : ¬ s ≤ (k : ℝ) * per := fun h => hA ((Jof_le_iff s k).mpr h)
    by_cases hB : k + 1 = Jof s
    · have h2 : s ≤ ((k : ℝ) + 1) * per := hJ1.mp (by omega)
      have hp : ((k : ℝ) + 1) * per - s = ψof s * per := by
        rw [ψof_per, ← hB]; push_cast; ring
      rw [ite_eq_right hA, ite_eq_left hB, zero_add]
      ext i
      simp [forceOf, stepRef, h1, h2, defect₁, defect₂, hp]
      ring
    · have h2 : ¬ s ≤ ((k : ℝ) + 1) * per := fun h => by
        have := hJ1.mpr h; omega
      rw [ite_eq_right hA, ite_eq_right hB, add_zero]
      ext i
      simp [forceOf, stepRef, h1, h2, defect₁, defect₂]

/-- Response of the free motion to an impulse at tick `J - 1`. -/
theorem traj_impulse (v : Fin 8 → ℝ) (J k : ℕ) (hJ : J = 0 → v = 0) :
    traj AvR 0 (fun j => if j + 1 = J then v else 0) k =
      if J ≤ k then traj AvR v (fun _ => 0) (k - J) else 0 := by
  rcases Nat.eq_zero_or_pos J with h | h
  · subst h
    have hv := hJ rfl
    subst hv
    have : (fun j : ℕ => if j + 1 = 0 then (0 : Fin 8 → ℝ) else 0) = fun _ => 0 := by
      funext j; simp
    rw [this, traj_zero_input]
    simp only [Nat.zero_le, ite_true, Nat.sub_zero]
    exact (traj_zero_input AvR k).symm
  · obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
    have hδ : ∀ m, traj AvR 0 (fun j => if j = 0 then v else 0) (m + 1) = traj AvR v (fun _ => 0) m := by
      intro m
      induction m with
      | zero => simp [traj_succ]
      | succ m ih => rw [traj_succ, ih, traj_succ]; simp
    have hshift := traj_shift AvR (fun j => if j = 0 then v else 0) J' k
    have e : (fun j => if j + 1 = J' + 1 then v else 0) =
        (fun j => if J' ≤ j then (fun j => if j = 0 then v else 0) (j - J') else 0) := by
      funext j
      by_cases h1 : j = J'
      · subst h1; simp
      · by_cases h2 : J' ≤ j
        · simp [h2, show j - J' ≠ 0 by omega, show j ≠ J' from h1]
        · simp [h2, show j ≠ J' from h1]
    rw [e, hshift]
    by_cases hk : J' ≤ k
    · by_cases hk' : J' + 1 ≤ k
      · rw [ite_eq_left hk, ite_eq_left hk', show k - J' = (k - (J' + 1)) + 1 by omega, hδ]
      · have : k = J' := by omega
        subst this
        simp
    · rw [ite_eq_right hk, ite_eq_right (by omega)]

theorem traj_free_comb (a b : Fin 8 → ℝ) (c d : ℝ) (m : ℕ) :
    traj AvR (c • a + d • b) (fun _ => 0) m = c • traj AvR a (fun _ => 0) m + d • traj AvR b (fun _ => 0) m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [traj_succ, ih, mulVec_add, mulVec_smul, add_zero]

/-- **Response to an acceleration step at a real time `s ≥ 0`.** -/
theorem errResp_stepRef (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    errResp (stepRef s) k =
      if Jof s ≤ k then XA (k - Jof s) + ψof s • XV (k - Jof s) + ψof s ^ 2 • XP (k - Jof s) else 0 := by
  have hf : forceOf (stepRef s) = fun j => (fun j => if Jof s ≤ j then (fun _ => BvR) (j - Jof s) else 0) j +
      (fun j => if j + 1 = Jof s then ψof s • (-(per : ℝ) • e1) + ψof s ^ 2 • (-((per : ℝ) ^ 2 / 2) • e0)
        else 0) j := by
    funext j; rw [forceOf_stepRef]
  have h2 := traj_add AvR 0 0 (fun j => if Jof s ≤ j then (fun _ => BvR) (j - Jof s) else 0)
    (fun j => if j + 1 = Jof s then ψof s • (-(per : ℝ) • e1) + ψof s ^ 2 • (-((per : ℝ) ^ 2 / 2) • e0)
        else 0) k
  rw [add_zero] at h2
  simp only [errResp, hf]
  rw [h2, traj_shift AvR (fun _ => BvR) (Jof s) k, traj_impulse _ _ _ (fun hJ => by
    rw [ψof_zero_of_J s hs hJ]; simp)]
  rw [traj_free_comb]
  split_ifs
  · simp only [XA, XV, XP]; abel
  · simp

/-! ## Bang-bang climb profiles -/

/-- The bang-bang acceleration profile `+1` on `[s, s + T₁)`, `0` on `[s + T₁, s + T₁ + 0.4)`,
`-1` on `[s + T₁ + 0.4, s + 2T₁ + 0.4)`, sampled with its exact position and velocity at the
ticks. -/
noncomputable def bangRef (s T1 : ℝ) (k : ℕ) : ℝ × ℝ × ℝ :=
  stepRef s k - stepRef (s + T1) k - stepRef (s + T1 + 2 / 5) k + stepRef (s + 2 * T1 + 2 / 5) k

theorem errResp_bangRef (s T1 : ℝ) (k : ℕ) :
    errResp (bangRef s T1) k = errResp (stepRef s) k - errResp (stepRef (s + T1)) k -
      errResp (stepRef (s + T1 + 2 / 5)) k + errResp (stepRef (s + 2 * T1 + 2 / 5)) k := by
  have hf : forceOf (bangRef s T1) = fun j => forceOf (stepRef s) j - forceOf (stepRef (s + T1)) j -
      forceOf (stepRef (s + T1 + 2 / 5)) j + forceOf (stepRef (s + 2 * T1 + 2 / 5)) j := by
    funext j; ext i
    simp only [forceOf, bangRef, defect₁, defect₂, Prod.fst_add, Prod.fst_sub, Prod.snd_add,
      Prod.snd_sub, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [errResp, hf, traj_comb4]

theorem ceil_add_ge (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : ⌈x⌉₊ + ⌊y⌋₊ ≤ ⌈x + y⌉₊ := by
  rcases Nat.eq_zero_or_pos ⌈x⌉₊ with h | h
  · rw [h, zero_add]
    have h1 := Nat.floor_le hy
    have h2 := Nat.le_ceil (x + y)
    exact_mod_cast (show (⌊y⌋₊ : ℝ) ≤ ⌈x + y⌉₊ by linarith)
  · obtain ⟨c, hc⟩ : ∃ c, ⌈x⌉₊ = c + 1 := ⟨⌈x⌉₊ - 1, by omega⟩
    have hcx : (c : ℝ) < x := Nat.lt_ceil.mp (by omega)
    have h1 := Nat.floor_le hy
    have : c + ⌊y⌋₊ < ⌈x + y⌉₊ := Nat.lt_ceil.mpr (by push_cast; linarith)
    omega

/-- The tick gap of a switch delayed by `T ∈ [213 h, 287 h]` is `⌊T/h⌋` or `⌈T/h⌉`. -/
theorem Jof_gap (a T : ℝ) (ha : 0 ≤ a) (hT1 : 213 / 400 ≤ T) (hT2 : T ≤ 287 / 400) :
    Jof a + ⌊T / per⌋₊ ≤ Jof (a + T) ∧ Jof (a + T) ≤ Jof a + ⌈T / per⌉₊ ∧
      213 ≤ ⌊T / per⌋₊ ∧ ⌈T / per⌉₊ ≤ 287 ∧ ⌈T / per⌉₊ ≤ ⌊T / per⌋₊ + 1 := by
  have hT : 0 ≤ T := by linarith
  have e : (a + T) / per = a / per + T / per := add_div _ _ _
  have hy : T / (per : ℝ) = 400 * T := by rw [per]; push_cast; field_simp
  refine ⟨?_, ?_, ?_, ?_, Nat.ceil_le_floor_add_one _⟩
  · simp only [Jof]; rw [e]; exact ceil_add_ge _ _ (div_nonneg ha per_pos.le) (div_nonneg hT per_pos.le)
  · simp only [Jof]; rw [e]; exact Nat.ceil_add_le _ _
  · exact Nat.le_floor (by rw [hy]; push_cast; linarith)
  · exact Nat.ceil_le.mpr (by rw [hy]; push_cast; linarith)

theorem Jof_add_gap (a : ℝ) (ha : 0 ≤ a) : Jof (a + 2 / 5) = Jof a + 160 := by
  simp only [Jof]
  rw [add_div, show (2 / 5 : ℝ) / per = ((160 : ℕ) : ℝ) by norm_num [per],
    Nat.ceil_add_natCast (div_nonneg ha per_pos.le)]

/-- `Bbang = BA + 4 BV + 4 BP = 0.0875`. -/
noncomputable def Bbang : ℝ := BA + 4 * BV + 4 * BP

theorem Bbang_eq : Bbang = 875 / 10000 := by norm_num [Bbang, BA, BV, BP]

theorem rest_bound (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    |(if Jof a ≤ k then ψof a * XV (k - Jof a) 0 + ψof a ^ 2 * XP (k - Jof a) 0 else 0)| ≤ BV + BP := by
  have hBV : 0 ≤ BV := by norm_num [BV]
  have hBP : 0 ≤ BP := by norm_num [BP]
  split_ifs
  · have h0 := ψof_nonneg a
    have h1 := ψof_lt_one a ha
    have hv := abs_le.mp (XV_bound (k - Jof a))
    have hp := abs_le.mp (XP_bound (k - Jof a))
    have hψ2 : ψof a ^ 2 ≤ 1 := pow_le_one₀ h0 h1.le
    have hψ2' : 0 ≤ ψof a ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor <;> nlinarith [hv.1, hv.2, hp.1, hp.2]
  · simp; linarith

/-- **Bang-bang climb bound.** For every start time `s ≥ 0` and every `T₁ ∈ [213/400, 287/400] s`
(the vertical legs of length `0.5 … 0.8 m`, `T1_mem_of_L`), with arbitrary real switching times,
the vertical tracking error of the model never exceeds `0.0875 m`. -/
theorem bang_bound (s T1 : ℝ) (hs : 0 ≤ s) (hT1 : 213 / 400 ≤ T1) (hT2 : T1 ≤ 287 / 400) (k : ℕ) :
    |errResp (bangRef s T1) k 0| ≤ Bbang := by
  have hT : 0 ≤ T1 := by linarith
  have hs1 : 0 ≤ s + T1 := by linarith
  have hs2 : 0 ≤ s + T1 + 2 / 5 := by linarith
  have hs3 : 0 ≤ s + 2 * T1 + 2 / 5 := by linarith
  have hR : ∀ a, 0 ≤ a → errResp (stepRef a) k 0 = (if Jof a ≤ k then XA (k - Jof a) 0 else 0) +
      (if Jof a ≤ k then ψof a * XV (k - Jof a) 0 + ψof a ^ 2 * XP (k - Jof a) 0 else 0) := by
    intro a ha; rw [errResp_stepRef a ha]; split_ifs
    · simp; ring
    · simp
  rw [errResp_bangRef]
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [hR s hs, hR _ hs1, hR _ hs2, hR _ hs3]
  -- the switching ticks
  obtain ⟨g1, g2, g3, g4, g5⟩ := Jof_gap s T1 hs hT1 hT2
  have hJ2 := Jof_add_gap (s + T1) hs1
  have e3 : s + 2 * T1 + 2 / 5 = (s + T1 + 2 / 5) + T1 := by ring
  obtain ⟨f1, f2, -, -, -⟩ := Jof_gap (s + T1 + 2 / 5) T1 hs2 hT1 hT2
  rw [← e3] at f1 f2
  set J0 := Jof s
  set J1 := Jof (s + T1)
  set J2 := Jof (s + T1 + 2 / 5)
  set J3 := Jof (s + 2 * T1 + 2 / 5)
  set fl := ⌊T1 / (per : ℝ)⌋₊
  set cl := ⌈T1 / (per : ℝ)⌉₊
  have hA : |(if J0 ≤ k then XA (k - J0) 0 else 0) - (if J1 ≤ k then XA (k - J1) 0 else 0) -
      (if J2 ≤ k then XA (k - J2) 0 else 0) + (if J3 ≤ k then XA (k - J3) 0 else 0)| ≤ BA := by
    by_cases hk : J0 ≤ k
    · have hsum := sumA_bound (J1 - J0) (J3 - J2) (by omega) (by omega) (by omega) (by omega) (k - J0)
      have c1 : (J1 ≤ k) = (J1 - J0 ≤ k - J0) := propext (by omega)
      have c2 : (J2 ≤ k) = (J1 - J0 + 160 ≤ k - J0) := propext (by omega)
      have c3 : (J3 ≤ k) = (J1 - J0 + 160 + (J3 - J2) ≤ k - J0) := propext (by omega)
      have d1 : k - J1 = k - J0 - (J1 - J0) := by omega
      have d2 : k - J2 = k - J0 - (J1 - J0 + 160) := by omega
      have d3 : k - J3 = k - J0 - (J1 - J0 + 160 + (J3 - J2)) := by omega
      simp only [sumA] at hsum
      rw [ite_eq_left hk]
      simp only [c1, c2, c3, d1, d2, d3]
      exact hsum
    · have h1 : ¬ J1 ≤ k := by omega
      have h2 : ¬ J2 ≤ k := by omega
      have h3 : ¬ J3 ≤ k := by omega
      rw [ite_eq_right hk, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
      simp [BA]; norm_num
  have r0 := rest_bound s hs k
  have r1 := rest_bound _ hs1 k
  have r2 := rest_bound _ hs2 k
  have r3 := rest_bound _ hs3 k
  unfold Bbang
  rw [abs_le] at hA r0 r1 r2 r3 ⊢
  constructor <;> linarith [hA.1, hA.2, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2]

/-! ## The vertical legs `L ∈ [0.5, 0.8] m` -/

/-- `T₁` of a vertical S-curve leg of length `L` at the configured limits (`WP_ACC_Z = 1`,
`WP_JERK = 5`, `tj = 0.2 s`): `SCurve::calculate_path` on `L/2` gives the constant-acceleration
time `t4 = (√(1 + 25 L) - 3)/5`, and `T₁ = 2 tj + t4` (`VERTICAL.md`). -/
noncomputable def T1ofL (L : ℝ) : ℝ := 2 / 5 + (Real.sqrt (1 + 25 * L) - 3) / 5

theorem T1_mem_of_L (L : ℝ) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) :
    213 / 400 ≤ T1ofL L ∧ T1ofL L ≤ 287 / 400 := by
  have hl : (36625 / 10000 : ℝ) ≤ Real.sqrt (1 + 25 * L) := by
    rw [Real.le_sqrt' (by norm_num)]; nlinarith
  have hu : Real.sqrt (1 + 25 * L) ≤ 45875 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  constructor <;> simp only [T1ofL] <;> linarith

/-- **The climb family**: the bang-bang profile of every vertical leg `L ∈ [0.5, 0.8] m` keeps the
model's vertical error below `0.0875 m`. -/
theorem bang_bound_L (s L : ℝ) (hs : 0 ≤ s) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (k : ℕ) :
    |errResp (bangRef s (T1ofL L)) k 0| ≤ 875 / 10000 := by
  obtain ⟨a, b⟩ := T1_mem_of_L L h1 h2
  rw [← Bbang_eq]; exact bang_bound s _ hs a b k

/-! ## Averages of profiles: the S-curve climb -/

section Average

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- **The error response commutes with averaging the target.** If the target is the
`μ`-average of a family of targets with integrable components, the error response is the average
of their error responses (and is integrable). -/
theorem errResp_integral (μ : Measure α) (R : α → ℕ → ℝ × ℝ × ℝ) (r : ℕ → ℝ × ℝ × ℝ)
    (hint : ∀ k, Integrable (fun u => (R u k).1) μ ∧ Integrable (fun u => (R u k).2.1) μ ∧
      Integrable (fun u => (R u k).2.2) μ)
    (hr : ∀ k, r k = (∫ u, (R u k).1 ∂μ, ∫ u, (R u k).2.1 ∂μ, ∫ u, (R u k).2.2 ∂μ)) :
    ∀ k i, Integrable (fun u => errResp (R u) k i) μ ∧ errResp r k i = ∫ u, errResp (R u) k i ∂μ := by
  intro k
  induction k with
  | zero => intro i; simp [errResp]
  | succ k ih =>
    intro i
    have hf : ∀ (q : ℕ → ℝ × ℝ × ℝ), errResp q (k + 1) i = ∑ l, AvR i l * errResp q k l +
        ((q k).2.2 * BvR i - ((q (k + 1)).1 - (q k).1 - (per : ℝ) * (q k).2.1 - (per : ℝ) ^ 2 / 2 * (q k).2.2) * e0 i -
          ((q (k + 1)).2.1 - (q k).2.1 - (per : ℝ) * (q k).2.2) * e1 i) := by
      intro q
      simp only [errResp, traj_succ, Pi.add_apply, mulVec, dotProduct, forceOf, defect₁, defect₂,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    obtain ⟨a1, a2, a3⟩ := hint k
    obtain ⟨b1, b2, -⟩ := hint (k + 1)
    have hsum : Integrable (fun u => ∑ l, AvR i l * errResp (R u) k l) μ :=
      integrable_finsetSum _ (fun l _ => (ih l).1.const_mul _)
    have hfo : Integrable (fun u => (R u k).2.2 * BvR i - ((R u (k + 1)).1 - (R u k).1 -
        (per : ℝ) * (R u k).2.1 - (per : ℝ) ^ 2 / 2 * (R u k).2.2) * e0 i -
        ((R u (k + 1)).2.1 - (R u k).2.1 - (per : ℝ) * (R u k).2.2) * e1 i) μ := by
      refine ((a3.mul_const _).sub ?_).sub ?_
      · exact (((b1.sub a1).sub (a2.const_mul _)).sub (a3.const_mul _)).mul_const _
      · exact ((b2.sub a2).sub (a3.const_mul _)).mul_const _
    refine ⟨?_, ?_⟩
    · simp only [hf]; exact hsum.add hfo
    · simp only [hf]
      rw [integral_add hsum hfo, integral_finsetSum _ (fun l _ => (ih l).1.const_mul _)]
      congr 1
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_const_mul, (ih l).2]
      · have hfun : (fun u => (R u k).2.2 * BvR i - ((R u (k + 1)).1 - (R u k).1 -
            (per : ℝ) * (R u k).2.1 - (per : ℝ) ^ 2 / 2 * (R u k).2.2) * e0 i -
            ((R u (k + 1)).2.1 - (R u k).2.1 - (per : ℝ) * (R u k).2.2) * e1 i) =
            fun u => (-e0 i) * (R u (k + 1)).1 + e0 i * (R u k).1 +
              ((per : ℝ) * e0 i + e1 i) * (R u k).2.1 +
              (BvR i + (per : ℝ) ^ 2 / 2 * e0 i + (per : ℝ) * e1 i) * (R u k).2.2 +
              (-e1 i) * (R u (k + 1)).2.1 := by
          funext u; ring
        rw [hfun]
        have i1 := b1.const_mul (-e0 i)
        have i2 := a1.const_mul (e0 i)
        have i3 := a2.const_mul ((per : ℝ) * e0 i + e1 i)
        have i4 := a3.const_mul (BvR i + (per : ℝ) ^ 2 / 2 * e0 i + (per : ℝ) * e1 i)
        have i5 := b2.const_mul (-e1 i)
        have j12 : Integrable (fun u => -e0 i * (R u (k + 1)).1 + e0 i * (R u k).1) μ := i1.add i2
        have j123 : Integrable (fun u => -e0 i * (R u (k + 1)).1 + e0 i * (R u k).1 +
            ((per : ℝ) * e0 i + e1 i) * (R u k).2.1) μ := j12.add i3
        have j1234 : Integrable (fun u => -e0 i * (R u (k + 1)).1 + e0 i * (R u k).1 +
            ((per : ℝ) * e0 i + e1 i) * (R u k).2.1 +
            (BvR i + (per : ℝ) ^ 2 / 2 * e0 i + (per : ℝ) * e1 i) * (R u k).2.2) μ := j123.add i4
        rw [integral_add j1234 i5, integral_add j123 i4, integral_add j12 i3, integral_add i1 i2]
        simp only [integral_const_mul, hr k, hr (k + 1)]
        ring

/-- **Averaging keeps the bound.** -/
theorem errResp_average_bound (μ : Measure α) [IsProbabilityMeasure μ] (R : α → ℕ → ℝ × ℝ × ℝ)
    (r : ℕ → ℝ × ℝ × ℝ)
    (hint : ∀ k, Integrable (fun u => (R u k).1) μ ∧ Integrable (fun u => (R u k).2.1) μ ∧
      Integrable (fun u => (R u k).2.2) μ)
    (hr : ∀ k, r k = (∫ u, (R u k).1 ∂μ, ∫ u, (R u k).2.1 ∂μ, ∫ u, (R u k).2.2 ∂μ))
    {B : ℝ} (hB : ∀ u k, |errResp (R u) k 0| ≤ B) (k : ℕ) : |errResp r k 0| ≤ B := by
  rw [(errResp_integral μ R r hint hr k 0).2]
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u => errResp (R u) k 0) (C := B)
    (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hB u k)
  simpa [Real.norm_eq_abs] using h

/-- **The S-curve climb bound.** Let the target be the average, over a probability measure of
start times `σ u ≥ 0`, of the bang-bang profiles of a vertical leg `L ∈ [0.5, 0.8] m`. This is the
form of the jerk-limited S-curve of `AC_WPNav`/`SCurve` (the raised-cosine jerk pulses are the
density of the start time, `VERTICAL.md`). Then the model's vertical tracking error never exceeds
`0.0875 m`. -/
theorem scurve_bound (μ : Measure α) [IsProbabilityMeasure μ] (σ : α → ℝ) (hσ : ∀ u, 0 ≤ σ u)
    (L : ℝ) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (r : ℕ → ℝ × ℝ × ℝ)
    (hint : ∀ k, Integrable (fun u => (bangRef (σ u) (T1ofL L) k).1) μ ∧
      Integrable (fun u => (bangRef (σ u) (T1ofL L) k).2.1) μ ∧
      Integrable (fun u => (bangRef (σ u) (T1ofL L) k).2.2) μ)
    (hr : ∀ k, r k = (∫ u, (bangRef (σ u) (T1ofL L) k).1 ∂μ, ∫ u, (bangRef (σ u) (T1ofL L) k).2.1 ∂μ,
      ∫ u, (bangRef (σ u) (T1ofL L) k).2.2 ∂μ)) (k : ℕ) :
    |errResp r k 0| ≤ 875 / 10000 :=
  errResp_average_bound μ (fun u => bangRef (σ u) (T1ofL L)) r hint hr
    (fun u k => bang_bound_L (σ u) L (hσ u) h1 h2 k) k

end Average

end Contracts.Track.Vertical
