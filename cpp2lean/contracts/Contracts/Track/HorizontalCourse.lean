import Contracts.Track.HorizontalChecks
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Field

/-!
# The certified course response of the horizontal loop (milestone M6, items 3 and 4)

From the kernel checks of `HorizontalTrajN.lean`, `HorizontalTrajE.lean` and
`HorizontalChecks.lean` to statements about the real model of `Horizontal.lean`.

The **course table** `refN`, `refE` is the target (position, velocity, acceleration) of the north
and east axes, tick by tick from the start of leg 1, of the ideal S-curve legs 1–7 of the mission
with the navigator's limits (`WP_SPD 1`, `WP_ACC 1.5`, `WP_JERK 5`, snap from `ATC_INPUT_TC`) and its
corner blends (`SCurve::advance_target_along_track` with fast waypoints), on the grid `2^-40 m`
(`HORIZONTAL.md` §3); it is at rest at `w₇ = w₀` from tick `6324` on.

* `course_norm`: the model's horizontal tracking error (both axes, from zero error at the start
  of leg 1) is at most `0.0285 m` at every tick;
* `corner_vehicle`: at each corner `w₁ … w₆`, whenever the table's target is within
  `0.1075 m` of the corner, the model's vehicle (target plus error) is within `0.0841 m` of it
  (`corner_vehicle_105`: `0.08075 m` for the window `0.105 m`; `corner_vehicle_106`: `0.0831 m`
  for `0.106 m`);
* `corner_transfer`: the transfer property T4 for any real target and vehicle within explicit
  distances of the nominal (`1 mm` and `15.9 mm`);
* `course_tube`: nominal plus tube for a disturbed trajectory with an arbitrary initial state.
-/

namespace Contracts.Track.Horizontal

open Matrix Finset
open Contracts.Track.Vertical (traj traj_succ traj_zero qf qf_add_le)

/-! ## The stored entries as a function of the tick -/

/-- The entry of tick `m` (`m ≤ Kh`; later ticks repeat the last entry). -/
def entOf (C : List (List V12)) (m : ℕ) : V12 :=
  if m < Kh then (C.getD (m / 32) []).getD (m % 32) default else (C.getD 206 []).getD 32 default

theorem trajOK_sound (st : V12 → V12 → Bool) :
    ∀ (n : ℕ) (l : List V12), trajOK st n l = true →
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

theorem Kh_eq : Kh = 6624 := rfl

/-- Every stored transition is checked. -/
theorem ent_step (C : List (List V12)) (hok : ∀ c < 207, trajOK stepH 33 (C.getD c []) = true)
    (hlen : ∀ c < 207, (C.getD c []).length = 33)
    (hlink : ∀ c < 206, v12eq ((C.getD c []).getD 32 default) ((C.getD (c + 1) []).getD 0 default) = true)
    (m : ℕ) (hm : m < Kh) : stepH (entOf C m) (entOf C (m + 1)) = true := by
  rw [Kh_eq] at hm
  have hc : m / 32 < 207 := by omega
  have h := trajOK_sound stepH 33 _ (hok _ hc) (m % 32) (by omega) (by rw [hlen _ hc]; omega)
  have e1 : entOf C m = (C.getD (m / 32) []).getD (m % 32) default := by
    simp [entOf, Kh_eq, hm]
  rw [e1]
  by_cases hi : m % 32 < 31
  · have e2 : entOf C (m + 1) = (C.getD (m / 32) []).getD (m % 32 + 1) default := by
      have h1 : m + 1 < 6624 := by omega
      have h2 : (m + 1) / 32 = m / 32 := by omega
      have h3 : (m + 1) % 32 = m % 32 + 1 := by omega
      simp [entOf, Kh_eq, h1, h2, h3]
    rw [e2]; exact h
  · have hi' : m % 32 = 31 := by omega
    rw [hi'] at h ⊢
    by_cases hc' : m / 32 < 206
    · have e2 : entOf C (m + 1) = (C.getD (m / 32 + 1) []).getD 0 default := by
        have h1 : m + 1 < 6624 := by omega
        have h2 : (m + 1) / 32 = m / 32 + 1 := by omega
        have h3 : (m + 1) % 32 = 0 := by omega
        simp [entOf, Kh_eq, h1, h2, h3]
      rw [e2, ← v12eq_spec (hlink _ hc')]
      exact h
    · have hc2 : m / 32 = 206 := by omega
      have e2 : entOf C (m + 1) = (C.getD 206 []).getD 32 default := by
        have h1 : ¬ (m + 1 < 6624) := by omega
        simp [entOf, Kh_eq, h1]
      rw [e2, ← hc2]
      exact h

/-! ## The course table and the stored states over `ℝ` -/

/-- The course table of tick `m` (position, velocity, acceleration of one axis). -/
noncomputable def refOf (C : List (List V12)) (m : ℕ) : ℝ × ℝ × ℝ :=
  ((tPos (entOf C m) : ℝ) / Sh, (tVel (entOf C m) : ℝ) / Sh, (tAcc (entOf C m) : ℝ) / Sh)

/-- The stored state as a real vector (scaled back by `Sh`). -/
noncomputable def yOf (e : V12) : Fin 9 → ℝ := fun i => (vecOf e i : ℝ) / Sh

theorem DAh_pos : (0 : ℤ) < DAh := by norm_num [DAh]
theorem Sh_pos : (0 : ℝ) < (Sh : ℝ) := by norm_num [Sh]

theorem cast_spec {q : ℤ} {r : ℚ} (h : (q : ℚ) = r) : (q : ℝ) = (r : ℝ) := by
  have : ((q : ℚ) : ℝ) = (r : ℝ) := by rw [h]
  simpa using this

theorem Ahat_real (i j : Fin 9) : (Ahat i j : ℝ) = (DAh : ℝ) * (Ah i j : ℝ) := by
  have := cast_spec (Ahat_spec i j); push_cast at this; exact this

theorem DBh_real (i : Fin 9) : (DBh i : ℝ) = (DAh : ℝ) * (Bh i : ℝ) := by
  have := cast_spec (DBh_spec i); push_cast at this; exact this

theorem Dh1_real : (Dh1 : ℝ) = (DAh : ℝ) * (per : ℝ) := by
  have := cast_spec Dh1_spec; push_cast at this; exact this

theorem Dh2_real : (Dh2 : ℝ) = (DAh : ℝ) * ((per : ℝ) ^ 2 / 2) := by
  have := cast_spec Dh2_spec; push_cast at this; exact this

/-- The scaled forcing is the forcing of the table. -/
theorem inpH_real (C : List (List V12)) (m : ℕ) (i : Fin 9) :
    (inpH (tPos (entOf C m)) (tVel (entOf C m)) (tAcc (entOf C m)) (tPos (entOf C (m + 1)))
      (tVel (entOf C (m + 1))) i : ℝ) = (DAh : ℝ) * Sh * forceOf (refOf C) m i := by
  have hS : (Sh : ℝ) ≠ 0 := Sh_pos.ne'
  simp only [inpH, forceOf, refOf, defect₁, defect₂]
  push_cast
  rw [DBh_real, Dh1_real, Dh2_real]
  fin_cases i <;> simp [e0, e1, BhR] <;> field_simp

/-- Floor division by `DAh`, over `ℝ`. -/
theorem ediv_real (N : ℤ) : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
    (((N / DAh : ℤ)) : ℝ) = (N : ℝ) / DAh - r := by
  have hD := DAh_pos
  have hDr : (0 : ℝ) < DAh := by exact_mod_cast hD
  refine ⟨((N % DAh : ℤ) : ℝ) / DAh, div_nonneg (by exact_mod_cast Int.emod_nonneg N hD.ne') hDr.le,
    (div_lt_one hDr).mpr (by exact_mod_cast Int.emod_lt_of_pos N hD), ?_⟩
  have e := Int.mul_ediv_add_emod N DAh
  have e' : ((DAh * (N / DAh) + N % DAh : ℤ) : ℝ) = (N : ℝ) := by rw [e]
  push_cast at e'
  field_simp
  linarith

/-- A checked transition is the real affine step up to a rounding vector with entries in
`[0, 1/Sh)`. -/
theorem step_real (C : List (List V12)) (m : ℕ)
    (h : stepH (entOf C m) (entOf C (m + 1)) = true) :
    ∃ ρ : Fin 9 → ℝ, (∀ i, |ρ i| ≤ 1 / Sh) ∧
      yOf (entOf C (m + 1)) = AhR *ᵥ yOf (entOf C m) + forceOf (refOf C) m - ρ := by
  have hDr : (0 : ℝ) < DAh := by exact_mod_cast DAh_pos
  have hS := Sh_pos
  set x := entOf C m
  set y := entOf C (m + 1)
  have hspec := stepH_spec h
  set u := inpH (tPos x) (tVel x) (tAcc x) (tPos y) (tVel y)
  choose r hr0 hr1 hr using fun i => ediv_real (∑ j, Ahat i j * vecOf x j + u i)
  refine ⟨fun i => r i / Sh, fun i => ?_, ?_⟩
  · rw [abs_of_nonneg (div_nonneg (hr0 i) hS.le)]
    exact div_le_div_of_nonneg_right (hr1 i).le hS.le
  · ext i
    have e1 : ((∑ j, Ahat i j * vecOf x j + u i : ℤ) : ℝ) =
        (DAh : ℝ) * (∑ j, (Ah i j : ℝ) * (vecOf x j : ℝ)) + (DAh : ℝ) * Sh * forceOf (refOf C) m i := by
      push_cast
      rw [inpH_real C m i, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Ahat_real]; ring
    have e2 : (AhR *ᵥ yOf x) i = (∑ j, (Ah i j : ℝ) * (vecOf x j : ℝ)) / Sh := by
      simp only [AhR, mulVec, dotProduct, map_apply, yOf]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [yOf, Pi.add_apply, Pi.sub_apply]
    rw [hspec i, hr i, e1, e2]
    field_simp

/-! ## Rounding -/

/-- The rounding error of a stored trajectory stays inside the `V`-ball of radius
`Cδ = Psum / Sh² / (1 - λ)²`. -/
noncomputable def Cδ : ℝ := (Psumh : ℝ) / (Sh : ℝ) ^ 2 / (1 - (lamh : ℝ)) ^ 2

theorem Cδ_nonneg : 0 ≤ Cδ := by
  unfold Cδ; have : (0 : ℝ) ≤ Psumh := by norm_num [Psumh]
  positivity

theorem rounding_bound (X y b : ℕ → Fin 9 → ℝ) (N : ℕ)
    (hX : ∀ m, X (m + 1) = AhR *ᵥ X m + b m)
    (hy : ∀ m, m < N → ∃ ρ : Fin 9 → ℝ, (∀ i, |ρ i| ≤ 1 / Sh) ∧ y (m + 1) = AhR *ᵥ y m + b m - ρ)
    (h0 : X 0 = y 0) : ∀ m ≤ N, V (X m - y m) ≤ Cδ := by
  have hl1 : (0 : ℝ) < 1 - lamh := by linarith [lamh_lt_one]
  intro m
  induction m with
  | zero => intro _; rw [h0, sub_self]; simp [V, qf, Cδ_nonneg]
  | succ m ih =>
    intro hm
    obtain ⟨ρ, hρ, hy'⟩ := hy m (by omega)
    have e : X (m + 1) - y (m + 1) = AhR *ᵥ (X m - y m) + ρ := by
      rw [hX m, hy', mulVec_sub]; abel
    rw [e]
    have h1 := V_iss (X m - y m) ρ
    have h2 := V_le_of_abs_le ρ hρ
    have h3 := ih (by omega)
    have h4 : V ρ / (1 - lamh) ≤ (Psumh : ℝ) * (1 / Sh) ^ 2 / (1 - lamh) :=
      div_le_div_of_nonneg_right h2 hl1.le
    have h5 : (lamh : ℝ) * V (X m - y m) ≤ lamh * Cδ :=
      mul_le_mul_of_nonneg_left h3 lamh_pos.le
    have e2 : (lamh : ℝ) * Cδ + (Psumh : ℝ) * (1 / Sh) ^ 2 / (1 - lamh) = Cδ := by
      unfold Cδ; field_simp; ring
    linarith

/-- `γ Cδ ≤ (10⁻⁷)²`: the rounding moves the error by at most `10⁻⁷ m`. -/
theorem gam_Cδ : (gamh : ℝ) * Cδ ≤ (1 / 10 ^ 7) ^ 2 := by
  unfold Cδ; norm_num [gamh, Psumh, Sh, lamh]

theorem abs_le_of_gamV {x : Fin 9 → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : (gamh : ℝ) * V x ≤ c ^ 2) :
    |x 0| ≤ c :=
  abs_le_of_sq_le_sq' ((sq_e_le x).trans h) hc |> fun h => abs_le.mpr h

theorem e_close_of_V {d : Fin 9 → ℝ} (h : V d ≤ Cδ) : |d 0| ≤ 1 / 10 ^ 7 := by
  have hg : (0 : ℝ) ≤ gamh := by norm_num [gamh]
  exact abs_le_of_gamV (by norm_num) ((mul_le_mul_of_nonneg_left h hg).trans gam_Cδ)

/-- The hypotheses on a chunk list that the kernel checks provide. -/
structure Checked (C : List (List V12)) : Prop where
  ok : ∀ c < 207, trajOK stepH 33 (C.getD c []) = true
  len : ∀ c < 207, (C.getD c []).length = 33
  link : ∀ c < 206, v12eq ((C.getD c []).getD 32 default) ((C.getD (c + 1) []).getD 0 default) = true
  zero : vecOf ((C.getD 0 []).getD 0 default) = 0
  rest : tVel ((C.getD 206 []).getD 32 default) = 0 ∧ tAcc ((C.getD 206 []).getD 32 default) = 0
  tail : qfQ Ph (vecQ ((C.getD 206 []).getD 32 default)) ≤ 1 / gamh * (8 / 1000) ^ 2

theorem checkedN : Checked chunksN :=
  ⟨chunksN_ok, chunksN_lengths, chunksN_link, chunksN_zero, ⟨endN.2.1, endN.2.2⟩, tailN_check⟩

theorem checkedE : Checked chunksE :=
  ⟨chunksE_ok, chunksE_lengths, chunksE_link, chunksE_zero, ⟨endE.2.1, endE.2.2⟩, tailE_check⟩

/-- The real error response stays within `V`-distance `Cδ` of the stored states. -/
theorem resp_V_close {C : List (List V12)} (hC : Checked C) :
    ∀ m ≤ Kh, V (errResp (refOf C) m - yOf (entOf C m)) ≤ Cδ := by
  refine rounding_bound (errResp (refOf C)) (fun m => yOf (entOf C m)) (forceOf (refOf C)) Kh
    (fun m => traj_succ _ _ _ m) (fun m hm => step_real C m (ent_step C hC.ok hC.len hC.link m hm)) ?_
  ext i
  have h0 : entOf C 0 = (C.getD 0 []).getD 0 default := by simp [entOf, Kh_eq]
  simp only [errResp, traj_zero, yOf, h0, hC.zero]
  simp

theorem resp_close {C : List (List V12)} (hC : Checked C) (m : ℕ) (hm : m ≤ Kh) :
    |errResp (refOf C) m 0 - (vecOf (entOf C m) 0 : ℝ) / Sh| ≤ 1 / 10 ^ 7 := by
  simpa [yOf] using e_close_of_V (resp_V_close hC m hm)

/-! ## After the course: the free motion -/

theorem entOf_ge (C : List (List V12)) (m : ℕ) (hm : Kh ≤ m) :
    entOf C m = (C.getD 206 []).getD 32 default := by
  simp [entOf, Nat.not_lt.mpr hm]

theorem forceOf_rest {C : List (List V12)} (hC : Checked C) (m : ℕ) (hm : Kh ≤ m) :
    forceOf (refOf C) m = 0 := by
  have e1 := entOf_ge C m hm
  have e2 := entOf_ge C (m + 1) (by omega)
  ext i
  simp only [forceOf, refOf, e1, e2, hC.rest.1, hC.rest.2]
  simp [defect₁, defect₂]

theorem V_young (a b : Fin 9 → ℝ) : V (a + b) ≤ (101 / 100) * V a + 101 * V b := by
  have h := qf_add_le PhR PhR_symm (fun z => V_nonneg z) (η := 1 / 100) (by norm_num) a b
  have e : (1 : ℝ) + 1 / (1 / 100) = 101 := by norm_num
  rw [e] at h
  have e2 : (1 : ℝ) + 1 / 100 = 101 / 100 := by norm_num
  rw [e2] at h
  exact h

theorem V_cast (v : Fin 9 → ℚ) : V (fun i => (v i : ℝ)) = ((qfQ Ph v : ℚ) : ℝ) := by
  simp [V, qf, qfQ, PhR, castM, dotProduct, mulVec, Fin.sum_univ_succ]

/-- From tick `Kh` on the error decays freely; it stays below `0.00805 m`. -/
theorem resp_tail {C : List (List V12)} (hC : Checked C) (m : ℕ) (hm : Kh ≤ m) :
    |errResp (refOf C) m 0| ≤ 805 / 100000 := by
  have hfree : ∀ t, errResp (refOf C) (Kh + t + 1) = AhR *ᵥ errResp (refOf C) (Kh + t) := by
    intro t
    rw [show Kh + t + 1 = (Kh + t) + 1 by ring]
    simp only [errResp, traj_succ]
    rw [show forceOf (refOf C) (Kh + t) = 0 from forceOf_rest hC _ (by omega), add_zero]
  have hmono : ∀ t, V (errResp (refOf C) (Kh + t)) ≤ V (errResp (refOf C) Kh) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [← add_assoc, hfree t]; exact (V_A_le _).trans ih
  obtain ⟨t, rfl⟩ : ∃ t, m = Kh + t := ⟨m - Kh, by omega⟩
  set yK := yOf (entOf C Kh)
  have hsplit : errResp (refOf C) Kh = yK + (errResp (refOf C) Kh - yK) := by abel
  have hy : V yK ≤ ((1 / gamh * (8 / 1000) ^ 2 : ℚ) : ℝ) := by
    have e : yK = fun i => (vecQ ((C.getD 206 []).getD 32 default) i : ℝ) := by
      ext i; simp [yK, yOf, vecQ, entOf_ge C Kh le_rfl]
    rw [e, V_cast]; exact_mod_cast hC.tail
  have hd := resp_V_close hC Kh le_rfl
  have hY := V_young yK (errResp (refOf C) Kh - yK)
  rw [← hsplit] at hY
  have hg : (0 : ℝ) < gamh := by norm_num [gamh]
  have hC2 := gam_Cδ
  have hb : (gamh : ℝ) * V (errResp (refOf C) (Kh + t)) ≤ (805 / 100000) ^ 2 := by
    have : (gamh : ℝ) * V (errResp (refOf C) (Kh + t)) ≤
        gamh * ((101 / 100) * ((1 / gamh * (8 / 1000) ^ 2 : ℚ) : ℝ) + 101 * Cδ) :=
      mul_le_mul_of_nonneg_left ((hmono t).trans (hY.trans (by linarith))) hg.le
    refine this.trans ?_
    have e : (gamh : ℝ) * ((101 / 100) * ((1 / gamh * (8 / 1000) ^ 2 : ℚ) : ℝ) + 101 * Cδ) =
        (101 / 100) * (8 / 1000) ^ 2 + 101 * (gamh * Cδ) := by
      push_cast; field_simp
    rw [e]; nlinarith
  exact abs_le_of_gamV (by norm_num) hb

/-! ## The course: the two axes -/

/-- The course table, north axis. -/
noncomputable def refN : ℕ → ℝ × ℝ × ℝ := refOf chunksN
/-- The course table, east axis. -/
noncomputable def refE : ℕ → ℝ × ℝ × ℝ := refOf chunksE

/-- The model's horizontal tracking error, north and east. -/
noncomputable def errN (k : ℕ) : ℝ := errResp refN k 0
noncomputable def errE (k : ℕ) : ℝ := errResp refE k 0

theorem normOK_sound : ∀ (a b : List V12), normOK a b = true →
    ∀ i, i < a.length → i < b.length → normOne (a.getD i default) (b.getD i default) = true := by
  intro a
  induction a with
  | nil => intro b _ i hi; simp at hi
  | cons x as ih =>
    intro b h i hi hb
    match b, h, hb with
    | y :: bs, h, hb =>
      simp only [normOK, Bool.and_eq_true] at h
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using ih bs h.2 i (by simpa using hi) (by simpa using hb)

theorem cornerOK_sound : ∀ (a b : List V12), cornerOK a b = true →
    ∀ i, i < a.length → i < b.length → cornerAll (a.getD i default) (b.getD i default) = true := by
  intro a
  induction a with
  | nil => intro b _ i hi; simp at hi
  | cons x as ih =>
    intro b h i hi hb
    match b, h, hb with
    | y :: bs, h, hb =>
      simp only [cornerOK, Bool.and_eq_true] at h
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using ih bs h.2 i (by simpa using hi) (by simpa using hb)

/-- Any per-entry test that holds on every chunk holds at every tick. -/
theorem ent_pair {P : V12 → V12 → Prop}
    (h : ∀ c < 207, ∀ i < 33, P ((chunksN.getD c []).getD i default) ((chunksE.getD c []).getD i default))
    (m : ℕ) : P (entOf chunksN m) (entOf chunksE m) := by
  by_cases hm : m < Kh
  · have h1 : entOf chunksN m = (chunksN.getD (m / 32) []).getD (m % 32) default := by simp [entOf, hm]
    have h2 : entOf chunksE m = (chunksE.getD (m / 32) []).getD (m % 32) default := by simp [entOf, hm]
    rw [h1, h2]; exact h _ (by rw [Kh_eq] at hm; omega) _ (by omega)
  · have h1 := entOf_ge chunksN m (by omega)
    have h2 := entOf_ge chunksE m (by omega)
    rw [h1, h2]; exact h 206 (by norm_num) 32 (by norm_num)

theorem normOne_all (m : ℕ) : normOne (entOf chunksN m) (entOf chunksE m) = true :=
  ent_pair (P := fun a b => normOne a b = true) (fun c hc i hi => normOK_sound _ _ (norm_all c hc) i (by rw [chunksN_lengths c hc]; exact hi)
    (by rw [chunksE_lengths c hc]; exact hi)) m

theorem cornerAll_all (m : ℕ) : cornerAll (entOf chunksN m) (entOf chunksE m) = true :=
  ent_pair (P := fun a b => cornerAll a b = true) (fun c hc i hi => cornerOK_sound _ _ (corner_all c hc) i (by rw [chunksN_lengths c hc]; exact hi)
    (by rw [chunksE_lengths c hc]; exact hi)) m

/-- The stored error of tick `m`, in meters. -/
noncomputable def sN (m : ℕ) : ℝ := (vecOf (entOf chunksN m) 0 : ℝ) / Sh
noncomputable def sE (m : ℕ) : ℝ := (vecOf (entOf chunksE m) 0 : ℝ) / Sh

theorem stored_norm (m : ℕ) : sN m ^ 2 + sE m ^ 2 ≤ (2845 / 100000) ^ 2 := by
  have h := normOne_all m
  simp only [normOne, decide_eq_true_eq] at h
  have h' : ((100000 * vecOf (entOf chunksN m) 0) ^ 2 + (100000 * vecOf (entOf chunksE m) 0) ^ 2 : ℝ) ≤
      ((2845 * Sh) ^ 2 : ℝ) := by exact_mod_cast h
  have hS := Sh_pos
  simp only [sN, sE]
  rw [div_pow, div_pow, ← add_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- The model error is within `10⁻⁷ m` of the stored error, on each axis, up to tick `Kh`. -/
theorem close_N (m : ℕ) (hm : m ≤ Kh) : |errN m - sN m| ≤ 1 / 10 ^ 7 := resp_close checkedN m hm
theorem close_E (m : ℕ) (hm : m ≤ Kh) : |errE m - sE m| ≤ 1 / 10 ^ 7 := resp_close checkedE m hm

theorem tail_N (m : ℕ) (hm : Kh ≤ m) : |errN m| ≤ 805 / 100000 := resp_tail checkedN m hm
theorem tail_E (m : ℕ) (hm : Kh ≤ m) : |errE m| ≤ 805 / 100000 := resp_tail checkedE m hm

/-! ## Item 3: the bound on the horizontal error over the course -/

/-- **The horizontal error over the course (milestone M6, item 3).** For the ideal S-curve legs
1–7 with their corner blends, from zero horizontal error at the start of leg 1, the model's
horizontal tracking error `√(eN² + eE²)` is at most `0.0285 m` at every tick. -/
theorem course_norm (k : ℕ) : errN k ^ 2 + errE k ^ 2 ≤ (285 / 10000) ^ 2 := by
  by_cases hk : k ≤ Kh
  · have h1 := abs_le.mp (close_N k hk)
    have h2 := abs_le.mp (close_E k hk)
    have h3 := stored_norm k
    have hN : |sN k| ≤ 2845 / 100000 := abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (sE k)]) (by norm_num)
      |> fun h => abs_le.mpr h
    have hE : |sE k| ≤ 2845 / 100000 := abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (sN k)]) (by norm_num)
      |> fun h => abs_le.mpr h
    have hN' := abs_le.mp hN
    have hE' := abs_le.mp hE
    nlinarith [sq_nonneg (errN k - sN k), sq_nonneg (errE k - sE k)]
  · have h1 := abs_le.mp (tail_N k (by omega))
    have h2 := abs_le.mp (tail_E k (by omega))
    nlinarith

theorem course_N (k : ℕ) : |errN k| ≤ 285 / 10000 :=
  abs_le_of_sq_le_sq' (by nlinarith [course_norm k, sq_nonneg (errE k)]) (by norm_num) |> fun h => abs_le.mpr h

theorem course_E (k : ℕ) : |errE k| ≤ 285 / 10000 :=
  abs_le_of_sq_le_sq' (by nlinarith [course_norm k, sq_nonneg (errN k)]) (by norm_num) |> fun h => abs_le.mpr h

/-! ## Item 4: the corner property -/

/-- Euclidean length of a planar vector. -/
noncomputable def hyp (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

theorem hyp_add_le (a b c d : ℝ) : hyp (a + c) (b + d) ≤ hyp a b + hyp c d := by
  unfold hyp
  have hX : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hY : 0 ≤ c ^ 2 + d ^ 2 := by positivity
  have hcs : a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
    rw [← Real.sqrt_mul hX]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg (a * d - b * c)]))
  rw [Real.sqrt_le_left]
  · nlinarith [Real.sq_sqrt hX, Real.sq_sqrt hY]
  · positivity

theorem hyp_le_of_sq {a b r : ℝ} (hr : 0 ≤ r) (h : a ^ 2 + b ^ 2 ≤ r ^ 2) : hyp a b ≤ r := by
  unfold hyp; rw [Real.sqrt_le_left hr]; exact h

theorem sq_le_of_hyp {a b r : ℝ} (h : hyp a b ≤ r) : a ^ 2 + b ^ 2 ≤ r ^ 2 := by
  unfold hyp at h
  have h0 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have := Real.sq_sqrt h0
  have hs := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
  nlinarith

theorem hyp_nonneg (a b : ℝ) : 0 ≤ hyp a b := Real.sqrt_nonneg _

/-- The corners `w₁ … w₆` relative to `w₀`, north and east (m). -/
noncomputable def cN : Fin 6 → ℝ := ![5 / 4, 0, -(5 / 4), 5 / 4, 0, -(5 / 4)]
noncomputable def cE : Fin 6 → ℝ := ![5 / 4, 5 / 2, 5 / 4, -(5 / 4), -(5 / 2), -(5 / 4)]
/-- The same in units `2^-40`. -/
def cNi : Fin 6 → ℤ := ![1374389534720, 0, -1374389534720, 1374389534720, 0, -1374389534720]
def cEi : Fin 6 → ℤ := ![1374389534720, 2748779069440, 1374389534720, -1374389534720,
  -2748779069440, -1374389534720]

theorem cNi_real (i : Fin 6) : (cNi i : ℝ) = cN i * Sh := by
  fin_cases i <;> norm_num [cNi, cN, Sh]
theorem cEi_real (i : Fin 6) : (cEi i : ℝ) = cE i * Sh := by
  fin_cases i <;> norm_num [cEi, cE, Sh]

theorem cornerAll_one {eN eE : V12} (h : cornerAll eN eE = true) (i : Fin 6) :
    cornerOne (cNi i) (cEi i) eN eE = true := by
  simp only [cornerAll, Bool.and_eq_true] at h
  fin_cases i <;> simp [cNi, cEi] <;> tauto

/-- The table's target position of tick `m`, north and east. -/
noncomputable def tN (m : ℕ) : ℝ := (refN m).1
noncomputable def tE (m : ℕ) : ℝ := (refE m).1

/-- The corner test, over `ℝ`, on the stored error. -/
theorem stored_corner (i : Fin 6) (m : ℕ)
    (hw : (tN m - cN i) ^ 2 + (tE m - cE i) ^ 2 ≤ (106 / 1000) ^ 2) :
    (tN m + sN m - cN i) ^ 2 + (tE m + sE m - cE i) ^ 2 ≤ (83 / 1000) ^ 2 := by
  have h := cornerAll_one (cornerAll_all m) i
  simp only [cornerOne, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  have hS := Sh_pos
  have eN : tN m = (tPos (entOf chunksN m) : ℝ) / Sh := rfl
  have eE : tE m = (tPos (entOf chunksE m) : ℝ) / Sh := rfl
  rcases h with h | h
  · exfalso; apply h
    have hw' : ((1000 * (tPos (entOf chunksN m) - cNi i)) ^ 2 + (1000 * (tPos (entOf chunksE m) - cEi i)) ^ 2 : ℝ)
        ≤ ((106 * Sh) ^ 2 : ℝ) := by
      rw [cNi_real, cEi_real]
      rw [eN, eE] at hw
      have e1 : (tPos (entOf chunksN m) : ℝ) / Sh - cN i = ((tPos (entOf chunksN m) : ℝ) - cN i * Sh) / Sh := by
        field_simp
      have e2 : (tPos (entOf chunksE m) : ℝ) / Sh - cE i = ((tPos (entOf chunksE m) : ℝ) - cE i * Sh) / Sh := by
        field_simp
      rw [e1, e2, div_pow, div_pow, ← add_div, div_le_iff₀ (by positivity)] at hw
      nlinarith
    exact_mod_cast hw'
  · have h' : ((1000 * (tPos (entOf chunksN m) + vecOf (entOf chunksN m) 0 - cNi i)) ^ 2 +
        (1000 * (tPos (entOf chunksE m) + vecOf (entOf chunksE m) 0 - cEi i)) ^ 2 : ℝ) ≤ ((83 * Sh) ^ 2 : ℝ) := by
      exact_mod_cast h
    rw [cNi_real, cEi_real] at h'
    simp only [sN, sE]
    rw [eN, eE]
    have e1 : (tPos (entOf chunksN m) : ℝ) / Sh + (vecOf (entOf chunksN m) 0 : ℝ) / Sh - cN i =
        ((tPos (entOf chunksN m) : ℝ) + vecOf (entOf chunksN m) 0 - cN i * Sh) / Sh := by field_simp
    have e2 : (tPos (entOf chunksE m) : ℝ) / Sh + (vecOf (entOf chunksE m) 0 : ℝ) / Sh - cE i =
        ((tPos (entOf chunksE m) : ℝ) + vecOf (entOf chunksE m) 0 - cE i * Sh) / Sh := by field_simp
    rw [e1, e2, div_pow, div_pow, ← add_div, div_le_iff₀ (by positivity)]
    nlinarith

theorem tN_rest (m : ℕ) (hm : Kh ≤ m) : tN m = 0 := by
  simp only [tN, refN, refOf, entOf_ge chunksN m hm, endN.1]; simp
theorem tE_rest (m : ℕ) (hm : Kh ≤ m) : tE m = 0 := by
  simp only [tE, refE, refOf, entOf_ge chunksE m hm, endE.1]; simp

/-- The corner property with window `0.106 m` and bound `0.0831 m` (used by `corner_transfer`). -/
theorem corner_vehicle_106 (i : Fin 6) (m : ℕ) (hw : hyp (tN m - cN i) (tE m - cE i) ≤ 106 / 1000) :
    hyp (tN m + errN m - cN i) (tE m + errE m - cE i) ≤ 831 / 10000 := by
  have hw2 := sq_le_of_hyp hw
  by_cases hm : m ≤ Kh
  · have hs := hyp_le_of_sq (by norm_num) (stored_corner i m hw2)
    have hd : hyp (errN m - sN m) (errE m - sE m) ≤ 2 / 10 ^ 7 := by
      apply hyp_le_of_sq (by norm_num)
      have h1 := abs_le.mp (close_N m hm)
      have h2 := abs_le.mp (close_E m hm)
      nlinarith
    have := hyp_add_le (tN m + sN m - cN i) (tE m + sE m - cE i) (errN m - sN m) (errE m - sE m)
    have e1 : tN m + sN m - cN i + (errN m - sN m) = tN m + errN m - cN i := by ring
    have e2 : tE m + sE m - cE i + (errE m - sE m) = tE m + errE m - cE i := by ring
    rw [e1, e2] at this
    linarith
  · exfalso
    rw [tN_rest m (by omega), tE_rest m (by omega)] at hw2
    fin_cases i <;> norm_num [cN, cE] at hw2

theorem cornerOKP_sound : ∀ (a b : List V12), cornerOKP a b = true →
    ∀ i, i < a.length → i < b.length → cornerAllP (a.getD i default) (b.getD i default) = true := by
  intro a
  induction a with
  | nil => intro b _ i hi; simp at hi
  | cons x as ih =>
    intro b h i hi hb
    match b, h, hb with
    | y :: bs, h, hb =>
      simp only [cornerOKP, Bool.and_eq_true] at h
      cases i with
      | zero => simpa using h.1
      | succ i => simpa using ih bs h.2 i (by simpa using hi) (by simpa using hb)

/-- The per-corner bounds of the kernel check (units `10⁻⁵ m`): window `0.1075` (`BA`) and
window `0.105` (`BB`). -/
def BA : Fin 6 → ℤ := ![8143, 8240, 8300, 8409, 8258, 8280]
def BB : Fin 6 → ℤ := ![7841, 7948, 7990, 8074, 7960, 7933]

theorem cornerAllP_one {eN eE : V12} (h : cornerAllP eN eE = true) (i : Fin 6) :
    cornerOneR 10750 (BA i) (cNi i) (cEi i) eN eE = true ∧
      cornerOneR 10500 (BB i) (cNi i) (cEi i) eN eE = true := by
  simp only [cornerAllP, Bool.and_eq_true] at h
  fin_cases i <;> simp [cNi, cEi, BA, BB] <;> tauto

theorem cornerP_ent (m : ℕ) : cornerAllP (entOf chunksN m) (entOf chunksE m) = true :=
  ent_pair (P := fun a b => cornerAllP a b = true)
    (fun c hc j hj => cornerOKP_sound _ _ (cornerP_all c hc) j (by rw [chunksN_lengths c hc]; exact hj)
      (by rw [chunksE_lengths c hc]; exact hj)) m

/-- A corner test with window `R · 10⁻⁵` and bound `B · 10⁻⁵`, over `ℝ`, on the stored error. -/
theorem stored_cornerR {R B : ℤ} (i : Fin 6) (m : ℕ)
    (hent : cornerOneR R B (cNi i) (cEi i) (entOf chunksN m) (entOf chunksE m) = true)
    (hw : (tN m - cN i) ^ 2 + (tE m - cE i) ^ 2 ≤ ((R : ℝ) / 100000) ^ 2) :
    (tN m + sN m - cN i) ^ 2 + (tE m + sE m - cE i) ^ 2 ≤ ((B : ℝ) / 100000) ^ 2 := by
  have h := hent
  simp only [cornerOneR, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  have hS := Sh_pos
  have eN : tN m = (tPos (entOf chunksN m) : ℝ) / Sh := rfl
  have eE : tE m = (tPos (entOf chunksE m) : ℝ) / Sh := rfl
  rcases h with h | h
  · exfalso; apply h
    have hw' : ((100000 * (tPos (entOf chunksN m) - cNi i)) ^ 2 +
        (100000 * (tPos (entOf chunksE m) - cEi i)) ^ 2 : ℝ) ≤ ((R * Sh) ^ 2 : ℝ) := by
      rw [cNi_real, cEi_real]
      rw [eN, eE] at hw
      have e1 : (tPos (entOf chunksN m) : ℝ) / Sh - cN i = ((tPos (entOf chunksN m) : ℝ) - cN i * Sh) / Sh := by
        field_simp
      have e2 : (tPos (entOf chunksE m) : ℝ) / Sh - cE i = ((tPos (entOf chunksE m) : ℝ) - cE i * Sh) / Sh := by
        field_simp
      rw [e1, e2, div_pow, div_pow, ← add_div, div_le_iff₀ (by positivity), div_pow] at hw
      have : (((tPos (entOf chunksN m) : ℝ) - cN i * Sh) ^ 2 + ((tPos (entOf chunksE m) : ℝ) - cE i * Sh) ^ 2) * 100000 ^ 2
          ≤ (R : ℝ) ^ 2 * Sh ^ 2 := by
        have h5 := hw; field_simp at h5; nlinarith
      nlinarith
    exact_mod_cast hw'
  · have h' : ((100000 * (tPos (entOf chunksN m) + vecOf (entOf chunksN m) 0 - cNi i)) ^ 2 +
        (100000 * (tPos (entOf chunksE m) + vecOf (entOf chunksE m) 0 - cEi i)) ^ 2 : ℝ) ≤
        ((B * Sh) ^ 2 : ℝ) := by
      exact_mod_cast h
    rw [cNi_real, cEi_real] at h'
    simp only [sN, sE]
    rw [eN, eE]
    have e1 : (tPos (entOf chunksN m) : ℝ) / Sh + (vecOf (entOf chunksN m) 0 : ℝ) / Sh - cN i =
        ((tPos (entOf chunksN m) : ℝ) + vecOf (entOf chunksN m) 0 - cN i * Sh) / Sh := by field_simp
    have e2 : (tPos (entOf chunksE m) : ℝ) / Sh + (vecOf (entOf chunksE m) 0 : ℝ) / Sh - cE i =
        ((tPos (entOf chunksE m) : ℝ) + vecOf (entOf chunksE m) 0 - cE i * Sh) / Sh := by field_simp
    rw [e1, e2, div_pow, div_pow, ← add_div, div_le_iff₀ (by positivity), div_pow]
    field_simp
    nlinarith

/-- The corner property for a checked window `R` and bound `B` (units `10⁻⁵ m`), up to the
rounding `2·10⁻⁷`. -/
theorem corner_vehicleR {R B : ℤ} (i : Fin 6)
    (hent : ∀ m, cornerOneR R B (cNi i) (cEi i) (entOf chunksN m) (entOf chunksE m) = true)
    (hR : 0 ≤ R) (hR1 : R ≤ 100000) (hB : 0 ≤ B) (m : ℕ)
    (hw : hyp (tN m - cN i) (tE m - cE i) ≤ (R : ℝ) / 100000) :
    hyp (tN m + errN m - cN i) (tE m + errE m - cE i) ≤ (B : ℝ) / 100000 + 2 / 10 ^ 7 := by
  have hRr : (0 : ℝ) ≤ R := by exact_mod_cast hR
  have hRr1 : (R : ℝ) ≤ 100000 := by exact_mod_cast hR1
  have hBr : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hw2 := sq_le_of_hyp hw
  by_cases hm : m ≤ Kh
  · have hs := hyp_le_of_sq (by positivity) (stored_cornerR i m (hent m) hw2)
    have hd : hyp (errN m - sN m) (errE m - sE m) ≤ 2 / 10 ^ 7 := by
      apply hyp_le_of_sq (by norm_num)
      have h1 := abs_le.mp (close_N m hm)
      have h2 := abs_le.mp (close_E m hm)
      nlinarith
    have := hyp_add_le (tN m + sN m - cN i) (tE m + sE m - cE i) (errN m - sN m) (errE m - sE m)
    have e1 : tN m + sN m - cN i + (errN m - sN m) = tN m + errN m - cN i := by ring
    have e2 : tE m + sE m - cE i + (errE m - sE m) = tE m + errE m - cE i := by ring
    rw [e1, e2] at this
    linarith
  · exfalso
    rw [tN_rest m (by omega), tE_rest m (by omega)] at hw2
    have hq : ((R : ℝ) / 100000) ^ 2 ≤ 1 := by
      rw [div_pow]; rw [div_le_one (by positivity)]; nlinarith
    fin_cases i <;> norm_num [cN, cE] at hw2 <;> linarith

/-- **Per-corner bounds.** Whenever the course table's target is within `0.1075 m`
(`= 0.105 m + 2.5 mm`, one tick at 1 m/s) of `wᵢ`, the model's vehicle is within
`BA i · 10⁻⁵ + 2·10⁻⁷ m` of it: `0.08143, 0.08240, 0.08300, 0.08409, 0.08258, 0.08280` (plus the
rounding) for `w₁ … w₆`. -/
theorem corner_vehicle_per (i : Fin 6) (m : ℕ)
    (hw : hyp (tN m - cN i) (tE m - cE i) ≤ 1075 / 10000) :
    hyp (tN m + errN m - cN i) (tE m + errE m - cE i) ≤ (BA i : ℝ) / 100000 + 2 / 10 ^ 7 :=
  corner_vehicleR i (fun m => (cornerAllP_one (cornerP_ent m) i).1)
    (by norm_num) (by norm_num) (by fin_cases i <;> norm_num [BA]) m (by norm_num; linarith)

/-- **Per-corner bounds, window `0.105 m`**: `BB i · 10⁻⁵ + 2·10⁻⁷`, that is
`0.07841, 0.07948, 0.07990, 0.08074, 0.07960, 0.07933` (plus the rounding). -/
theorem corner_vehicle_per_105 (i : Fin 6) (m : ℕ)
    (hw : hyp (tN m - cN i) (tE m - cE i) ≤ 105 / 1000) :
    hyp (tN m + errN m - cN i) (tE m + errE m - cE i) ≤ (BB i : ℝ) / 100000 + 2 / 10 ^ 7 :=
  corner_vehicleR i (fun m => (cornerAllP_one (cornerP_ent m) i).2)
    (by norm_num) (by norm_num) (by fin_cases i <;> norm_num [BB]) m (by norm_num; linarith)

/-- **The corner property of the model (milestone M6, item 4).** At each corner `w₁ … w₆`,
whenever the course table's target is within `0.1075 m = 0.105 m + 2.5 mm` (one tick of travel at
1 m/s) of the corner, the model's vehicle (the target plus the certified error response) is within
`0.0841 m` of the corner (kernel check: `0.08409` at `w₄`, plus `2·10⁻⁷` rounding). -/
theorem corner_vehicle (i : Fin 6) (m : ℕ) (hw : hyp (tN m - cN i) (tE m - cE i) ≤ 1075 / 10000) :
    hyp (tN m + errN m - cN i) (tE m + errE m - cE i) ≤ 841 / 10000 := by
  have h := corner_vehicle_per i m hw
  have hb : (BA i : ℝ) ≤ 8409 := by fin_cases i <;> norm_num [BA]
  linarith

/-- The same with the window `0.105 m`: the model's vehicle is within `0.08075 m` (kernel check:
`0.08074` at `w₄`). -/
theorem corner_vehicle_105 (i : Fin 6) (m : ℕ) (hw : hyp (tN m - cN i) (tE m - cE i) ≤ 105 / 1000) :
    hyp (tN m + errN m - cN i) (tE m + errE m - cE i) ≤ 8075 / 100000 := by
  have h := corner_vehicle_per_105 i m hw
  have hb : (BB i : ℝ) ≤ 8074 := by fin_cases i <;> norm_num [BB]
  linarith

/-- **The transfer property T4 at `w₁ … w₆` (milestone M6, item 4).** Let `q` be the real
target and `x` the real vehicle position at a tick `m` of the course (both in the horizontal
plane, relative to `w₀`). If the target is within `1 mm` of the course table and the vehicle's
error `x - q` is within `15.9 mm` of the model's error response, then the vehicle is within
`r = 0.1` of the corner whenever the target is within `rPass = 0.105` of it. -/
theorem corner_transfer (i : Fin 6) (m : ℕ) (qN qE xN xE : ℝ)
    (hq : hyp (qN - tN m) (qE - tE m) ≤ 1 / 1000)
    (hx : hyp (xN - qN - errN m) (xE - qE - errE m) ≤ 159 / 10000)
    (hw : hyp (qN - cN i) (qE - cE i) ≤ 105 / 1000) :
    hyp (xN - cN i) (xE - cE i) ≤ 1 / 10 := by
  have h1 : hyp (tN m - cN i) (tE m - cE i) ≤ 106 / 1000 := by
    have := hyp_add_le (qN - cN i) (qE - cE i) (tN m - qN) (tE m - qE)
    have e1 : qN - cN i + (tN m - qN) = tN m - cN i := by ring
    have e2 : qE - cE i + (tE m - qE) = tE m - cE i := by ring
    rw [e1, e2] at this
    have : hyp (tN m - qN) (tE m - qE) = hyp (qN - tN m) (qE - tE m) := by
      unfold hyp; congr 1; ring
    linarith
  have h2 := corner_vehicle_106 i m h1
  have h3 := hyp_add_le (tN m + errN m - cN i) (tE m + errE m - cE i) (qN - tN m) (qE - tE m)
  have h4 := hyp_add_le (tN m + errN m - cN i + (qN - tN m)) (tE m + errE m - cE i + (qE - tE m))
    (xN - qN - errN m) (xE - qE - errE m)
  have e1 : tN m + errN m - cN i + (qN - tN m) + (xN - qN - errN m) = xN - cN i := by ring
  have e2 : tE m + errE m - cE i + (qE - tE m) + (xE - qE - errE m) = xE - cE i := by ring
  rw [e1, e2] at h4
  linarith

/-! ## Nominal plus tube -/

/-- **Nominal plus tube.** If one horizontal axis follows `ξ (k+1) = Ah ξ k + forceOf r k + w k`
(the course table `r`; `w` collects the float error `β`, the deviation of the attitude loop from
the lag interface, the plant remainder and the yaw coupling) with `V (w k) ≤ c`, then its
position error is the certified response plus `√(γ (λᵏ V (ξ 0) + c / (1 - λ)²))`; an initial
horizontal state at the start of leg 1 enters through `V (ξ 0)`. -/
theorem course_tube (r : ℕ → ℝ × ℝ × ℝ) (ξ w : ℕ → Fin 9 → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hξ : ∀ k, ξ (k + 1) = AhR *ᵥ ξ k + forceOf r k + w k) (hw : ∀ k, V (w k) ≤ c) (k : ℕ) :
    |ξ k 0 - errResp r k 0| ≤
      Real.sqrt ((gamh : ℝ) * ((lamh : ℝ) ^ k * V (ξ 0) + c / (1 - lamh) ^ 2)) := by
  have h := errOf_traj_dist ξ r w hξ k
  have h2 := e_traj_le_const (traj AhR (ξ 0) w) w hc (fun k => traj_succ _ _ _ k) hw k
  rw [traj_zero] at h2
  have : ξ k 0 - errResp r k 0 = traj AhR (ξ 0) w k 0 := by rw [← h]; rfl
  rw [this]; exact h2

end Contracts.Track.Horizontal
