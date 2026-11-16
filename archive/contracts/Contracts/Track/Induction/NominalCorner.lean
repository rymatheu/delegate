import Contracts.Track.Induction.NominalVTab

/-!
# M9, certified nominal: the vertical error at the corners `w₁ … w₆`

Signed bounds of the leg-0 tail (windowed pattern sums of the certified step response of
VerticalData.lean, the phase terms, the S-curve average) and of the legs 1–7 part (`VTab`), and
their combination `vz_w1 … vz_w6` (NOMINAL.md §3).
-/

namespace Contracts.Track.Induction.Nominal

open Matrix Finset

noncomputable section


/-! ## The vertical nominal at the corners `w₁ … w₆`

The vertical reference of the ideal course near the corners is the leg-0 climb (the S-curve family
of `VerticalSCurve.lean`, `L ∈ [0.5, 0.8]`, any phase, with the sign of a climb: `-scurveRef`)
plus the vertical part of legs 1–7 (the table `VTab.vt`, started `D1` ticks later). By
superposition the model's vertical error is the sum of the two responses. Their signs differ at
`w₁` (the leg-0 tail is `+0.0087 … +0.0254` m there, the legs 1–7 part `-0.0059 … -0.0056`), so
both are bounded **signed** on the corner windows:

* the leg-0 tail by windowed signed pattern sums of the certified step response
  (`patOK`-style kernel checks on `Elist`, `sumA_win`) and the sub-tick phase terms (`XV`, `XP`);
* the legs 1–7 part by a kernel-checked forced trajectory of the vertical model driven by the
  table (`VTab`).
-/

namespace Corner

open Vertical MeasureTheory Set

/-! ### Tails of the free and step responses -/

/-- The first components of the stored free response `XV`. -/
def EVlist : List ℕ := trajV.map (fun v => v.1)

/-- `|XV m| ≤ 2.85·10⁻⁴` for `m ∈ [413, 800]`: the stored values. -/
theorem EV413_check : allAbsLe 3132000000000 (EVlist.drop 413) = true := by decide +kernel

theorem XV_ge800 (m : ℕ) (hm : 800 ≤ m) : |XV m 0| ≤ 146 / 10 ^ 6 := by
  have hmono := V_free_le XV XV_succ 800 m hm
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
  have hb : (gamv : ℝ) * V (XV m) ≤ (146 / 10 ^ 6) ^ 2 := by
    have : (gamv : ℝ) * V (XV m) ≤ gamv * ((101 / 100) * ((1 / gamv * (21 / 10 ^ 9) : ℚ) : ℝ) + 101 * Cδ) :=
      mul_le_mul_of_nonneg_left (hmono.trans (hY.trans (by linarith))) hg.le
    refine this.trans ?_
    have e : (gamv : ℝ) * ((101 / 100) * ((1 / gamv * (21 / 10 ^ 9) : ℚ) : ℝ) + 101 * Cδ) =
        (101 / 100) * (21 / 10 ^ 9) + 101 * (gamv * Cδ) := by
      push_cast; field_simp
    rw [e]; nlinarith
  exact abs_le_of_gamV (by norm_num) hb

theorem XV_ge413 (m : ℕ) (hm : 413 ≤ m) : |XV m 0| ≤ 285 / 10 ^ 6 := by
  by_cases h8 : 800 ≤ m
  · exact (XV_ge800 m h8).trans (by norm_num)
  · have hlen : EVlist.length = 801 := by simp [EVlist, trajV_length]
    have h := allAbsLe_sound _ _ EV413_check (m - 413) (by simp [hlen]; omega)
    have hl : (EVlist.drop 413).getD (m - 413) 0 = (trajV.getD m default).1 := by
      simp only [EVlist, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map]
      rw [show 413 + (m - 413) = m by omega]
      cases trajV[m]? <;> rfl
    rw [hl] at h
    have hz : |vecOf (trajV.getD m default) 0| ≤ (3132000000000 : ℤ) := by
      simp only [vecOf, Matrix.cons_val_zero, dz]
      rw [abs_le]; constructor <;> omega
    have hzr : |(vecOf (trajV.getD m default) 0 : ℝ)| ≤ (3132000000000 : ℝ) := by exact_mod_cast hz
    have hS := Sz_pos
    have hy : |yV m 0| ≤ (3132000000000 : ℝ) / Sz := by
      simp only [yV, yOf]; rw [abs_div, abs_of_pos hS]; exact div_le_div_of_nonneg_right hzr hS.le
    have c := XV_close m (by omega)
    have hB : (3132000000000 : ℝ) / Sz + 1 / 10 ^ 12 ≤ 285 / 10 ^ 6 := by norm_num [Sz]
    rw [abs_le] at c hy ⊢
    constructor <;> linarith [c.1, c.2, hy.1, hy.2]

/-- The step response near its steady state at tick 3001. -/
theorem tailA3001_check :
    qfQ Pv (vecQ (trajA.getD 3001 default) - Xinf) ≤ 1 / gamv * (52 / 10 ^ 10) := by
  decide +kernel

theorem XA_ge3001 (m : ℕ) (hm : 3001 ≤ m) : |XA m 0| ≤ 73 / 10 ^ 6 := by
  have hmono := V_free_le (fun m => XA m - XinfR) XA_sub_Xinf_succ 3001 m hm
  have hsplit : XA 3001 - XinfR = (yA 3001 - XinfR) + (XA 3001 - yA 3001) := by abel
  have hy : V (yA 3001 - XinfR) ≤ ((1 / gamv * (52 / 10 ^ 10) : ℚ) : ℝ) := by
    have e : yA 3001 - XinfR = fun i => ((vecQ (trajA.getD 3001 default) - Xinf) i : ℝ) := by
      ext i; simp [yA, yOf_eq_cast, XinfR]
    rw [e, V_cast]; exact_mod_cast tailA3001_check
  have hd := XA_V_close 3001 le_rfl
  have hY := V_young (yA 3001 - XinfR) (XA 3001 - yA 3001)
  rw [← hsplit] at hY
  have hg : (0 : ℝ) < gamv := by norm_num [gamv]
  have hC := gam_Cδ
  have hb : (gamv : ℝ) * V (XA m - XinfR) ≤ (73 / 10 ^ 6) ^ 2 := by
    have : (gamv : ℝ) * V (XA m - XinfR) ≤
        gamv * ((101 / 100) * ((1 / gamv * (52 / 10 ^ 10) : ℚ) : ℝ) + 101 * Cδ) :=
      mul_le_mul_of_nonneg_left (hmono.trans (hY.trans (by linarith))) hg.le
    refine this.trans ?_
    have e : (gamv : ℝ) * ((101 / 100) * ((1 / gamv * (52 / 10 ^ 10) : ℚ) : ℝ) + 101 * Cδ) =
        (101 / 100) * (52 / 10 ^ 10) + 101 * (gamv * Cδ) := by
      push_cast; field_simp
    rw [e]; nlinarith
  have := abs_le_of_gamV (by norm_num) hb
  simpa [XinfR_zero] using this

/-! ### Windowed signed pattern sums -/

/-- `lo ≤ a - b - c + d ≤ hi` on the first `n` entries (offsets cancel). -/
def allS (lo hi : ℤ) : ℕ → List ℕ → List ℕ → List ℕ → List ℕ → Bool
  | n + 1, a :: as, b :: bs, c :: cs, d :: ds =>
      (decide (lo ≤ (a : ℤ) - b - c + d) && decide ((a : ℤ) - b - c + d ≤ hi)) && allS lo hi n as bs cs ds
  | _, _, _, _, _ => true

theorem allS_sound (lo hi : ℤ) : ∀ (n : ℕ) (a b c d : List ℕ), allS lo hi n a b c d = true →
    ∀ k, k < n → k < a.length → k < b.length → k < c.length → k < d.length →
      lo ≤ (a.getD k 0 : ℤ) - b.getD k 0 - c.getD k 0 + d.getD k 0 ∧
        (a.getD k 0 : ℤ) - b.getD k 0 - c.getD k 0 + d.getD k 0 ≤ hi := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ k hk; omega
  | succ n ih =>
    intro a b c d h k hk ha hb hc hd
    match a, b, c, d with
    | x :: as, y :: bs, z :: cs, w :: ds =>
      simp only [allS, Bool.and_eq_true, decide_eq_true_eq] at h
      cases k with
      | zero => simpa using h.1
      | succ k =>
        simp only [List.length_cons] at ha hb hc hd
        simpa using ih as bs cs ds h.2 k (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The pattern `(G1, 160, G3)` signed on the window `k ∈ [lo, lo + n)`. -/
def patW (L H : ℤ) (lo n G1 G3 : ℕ) : Bool :=
  allS L H n (Elist.drop lo) (Elist.drop (lo - G1)) (Elist.drop (lo - (G1 + 160)))
    (Elist.drop (lo - (G1 + 160 + G3)))

/-- The three patterns of a gap `G1` (`G3 ∈ {G1, G1 + 1, G1 - 1}`). -/
def patG (L H : ℤ) (lo n G1 : ℕ) : Bool :=
  patW L H lo n G1 G1 && patW L H lo n G1 (G1 + 1) && patW L H lo n G1 (G1 - 1)

theorem patW_sound {L H : ℤ} {lo n G1 G3 : ℕ} (h : patW L H lo n G1 G3 = true)
    (hlo : G1 + 160 + G3 ≤ lo) (hn : lo + n ≤ 3002) (k : ℕ) (hk1 : lo ≤ k) (hk2 : k < lo + n) :
    L ≤ vecOf (trajA.getD k default) 0 - vecOf (trajA.getD (k - G1) default) 0 -
        vecOf (trajA.getD (k - (G1 + 160)) default) 0 + vecOf (trajA.getD (k - (G1 + 160 + G3)) default) 0 ∧
      vecOf (trajA.getD k default) 0 - vecOf (trajA.getD (k - G1) default) 0 -
        vecOf (trajA.getD (k - (G1 + 160)) default) 0 + vecOf (trajA.getD (k - (G1 + 160 + G3)) default) 0 ≤ H := by
  have hlen := Elist_length
  have hs := allS_sound L H n _ _ _ _ h (k - lo) (by omega) (by simp [hlen]; omega)
    (by simp [hlen]; omega) (by simp [hlen]; omega) (by simp [hlen]; omega)
  have gd : ∀ j i, (Elist.drop j).getD i 0 = Elist.getD (j + i) 0 := by
    intro j i; simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have e : ∀ m, (Elist.getD m 0 : ℤ) = vecOf (trajA.getD m default) 0 + OFFz := by
    intro m; have := Elist_getD m; simp only [dz] at this; linarith
  obtain ⟨h1, h2⟩ := hs
  simp only [gd] at h1 h2
  rw [show lo + (k - lo) = k by omega, show lo - G1 + (k - lo) = k - G1 by omega,
    show lo - (G1 + 160) + (k - lo) = k - (G1 + 160) by omega,
    show lo - (G1 + 160 + G3) + (k - lo) = k - (G1 + 160 + G3) by omega, e, e, e, e] at h1 h2
  constructor <;> linarith

/-- **Signed pattern sums on a window.** -/
theorem sumA_win {L H : ℤ} {lo n : ℕ} (hP : ∀ G1, 213 ≤ G1 → G1 ≤ 287 → patG L H lo n G1 = true)
    (hlo : 735 ≤ lo) (hn : lo + n ≤ 3002) (G1 G3 : ℕ) (h1 : 213 ≤ G1) (h2 : G1 ≤ 287)
    (h3 : G1 ≤ G3 + 1) (h4 : G3 ≤ G1 + 1) (k : ℕ) (hk1 : lo ≤ k) (hk2 : k < lo + n) :
    (L : ℝ) / Sz - 4 / 10 ^ 12 ≤ sumA G1 G3 k ∧ sumA G1 G3 k ≤ (H : ℝ) / Sz + 4 / 10 ^ 12 := by
  have hW : patW L H lo n G1 G3 = true := by
    have := hP G1 h1 h2
    simp only [patG, Bool.and_eq_true] at this
    obtain ⟨⟨ha, hb⟩, hc⟩ := this
    rcases (by omega : G3 = G1 ∨ G3 = G1 + 1 ∨ G3 = G1 - 1) with e | e | e <;> rw [e] <;> assumption
  obtain ⟨z1, z2⟩ := patW_sound hW (by omega) hn k hk1 hk2
  have hS := Sz_pos
  have ha : G1 ≤ k := by omega
  have hb : G1 + 160 ≤ k := by omega
  have hc : G1 + 160 + G3 ≤ k := by omega
  have e : sumA G1 G3 k = XA k 0 - XA (k - G1) 0 - XA (k - (G1 + 160)) 0 + XA (k - (G1 + 160 + G3)) 0 := by
    simp only [sumA, ha, hb, hc, ite_true]
  have c0 := XA_close k (by omega)
  have c1 := XA_close (k - G1) (by omega)
  have c2 := XA_close (k - (G1 + 160)) (by omega)
  have c3 := XA_close (k - (G1 + 160 + G3)) (by omega)
  set Y := vecOf (trajA.getD k default) 0 - vecOf (trajA.getD (k - G1) default) 0 -
      vecOf (trajA.getD (k - (G1 + 160)) default) 0 + vecOf (trajA.getD (k - (G1 + 160 + G3)) default) 0
  have ey : (Y : ℝ) / Sz = yA k 0 - yA (k - G1) 0 - yA (k - (G1 + 160)) 0 + yA (k - (G1 + 160 + G3)) 0 := by
    simp only [Y, yA, yOf]; push_cast; ring
  have y1 : (L : ℝ) / Sz ≤ (Y : ℝ) / Sz := div_le_div_of_nonneg_right (by exact_mod_cast z1) hS.le
  have y2 : (Y : ℝ) / Sz ≤ (H : ℝ) / Sz := div_le_div_of_nonneg_right (by exact_mod_cast z2) hS.le
  rw [ey] at y1 y2
  rw [e]
  rw [abs_le] at c0 c1 c2 c3
  constructor <;> linarith [c0.1, c0.2, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2]

/-- Far tails of the pattern sums: `|sumA| ≤ 4 · 73·10⁻⁶` once every term is past tick 3001. -/
theorem sumA_far (G1 G3 : ℕ) (h2 : G1 ≤ 287) (h4 : G3 ≤ G1 + 1) (k : ℕ) (hk : 3736 ≤ k) :
    -(292 / 10 ^ 6) ≤ sumA G1 G3 k ∧ sumA G1 G3 k ≤ 292 / 10 ^ 6 := by
  have ha : G1 ≤ k := by omega
  have hb : G1 + 160 ≤ k := by omega
  have hc : G1 + 160 + G3 ≤ k := by omega
  have e : sumA G1 G3 k = XA k 0 - XA (k - G1) 0 - XA (k - (G1 + 160)) 0 + XA (k - (G1 + 160 + G3)) 0 := by
    simp only [sumA, ha, hb, hc, ite_true]
  have t0 := XA_ge3001 k (by omega)
  have t1 := XA_ge3001 (k - G1) (by omega)
  have t2 := XA_ge3001 (k - (G1 + 160)) (by omega)
  have t3 := XA_ge3001 (k - (G1 + 160 + G3)) (by omega)
  rw [e]
  rw [abs_le] at t0 t1 t2 t3
  constructor <;> linarith [t0.1, t0.2, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2]

/-- The sub-tick phase term of one switch, once it is `M` ticks past. -/
theorem rest_le (a : ℝ) (ha : 0 ≤ a) (k M : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hV : ∀ m, M ≤ m → |XV m 0| ≤ c) (hk : Jof a + M ≤ k) :
    |(if Jof a ≤ k then ψof a * XV (k - Jof a) 0 + ψof a ^ 2 * XP (k - Jof a) 0 else 0)| ≤ c + BP := by
  have hBP : 0 ≤ BP := by norm_num [BP]
  have hk' : Jof a ≤ k := by omega
  simp only [hk', ↓reduceIte]
  have h0 := ψof_nonneg a
  have h1 := ψof_lt_one a ha
  have hv := abs_le.mp (hV (k - Jof a) (by omega))
  have hp := abs_le.mp (XP_bound (k - Jof a))
  have hψ2 : ψof a ^ 2 ≤ 1 := pow_le_one₀ h0 h1.le
  have hψ2' : 0 ≤ ψof a ^ 2 := sq_nonneg _
  rw [abs_le]
  constructor <;> nlinarith [hv.1, hv.2, hp.1, hp.2]

/-- **Signed bang-bang bound on a window.** If the pattern sums are in `[lo, hi]` for the window
`k - J₀ ∈ [klo, khi]` and the phase terms past `klo - 734 …` are bounded by `c₀ … c₃`, the
bang-bang member's response is in `[lo - c, hi + c]`, `c = Σ cᵢ + 4 BP`. -/
theorem bang_win (s T1 : ℝ) (hs : 0 ≤ s) (hT1 : 213 / 400 ≤ T1) (hT2 : T1 ≤ 287 / 400)
    (klo khi : ℕ) (hklo : 734 ≤ klo) {lo hi c0 c1 c2 c3 : ℝ}
    (hA : ∀ G1 G3, 213 ≤ G1 → G1 ≤ 287 → G1 ≤ G3 + 1 → G3 ≤ G1 + 1 → ∀ k', klo ≤ k' → k' ≤ khi →
      lo ≤ sumA G1 G3 k' ∧ sumA G1 G3 k' ≤ hi)
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hV0 : ∀ m, klo ≤ m → |XV m 0| ≤ c0) (hV1 : ∀ m, klo ≤ m + 287 → |XV m 0| ≤ c1)
    (hV2 : ∀ m, klo ≤ m + 447 → |XV m 0| ≤ c2) (hV3 : ∀ m, klo ≤ m + 734 → |XV m 0| ≤ c3)
    (k : ℕ) (hk1 : Jof s + klo ≤ k) (hk2 : k ≤ Jof s + khi) :
    lo - (c0 + c1 + c2 + c3 + 4 * BP) ≤ errResp (bangRef s T1) k 0 ∧
      errResp (bangRef s T1) k 0 ≤ hi + (c0 + c1 + c2 + c3 + 4 * BP) := by
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
  have hsum := hA (J1 - J0) (J3 - J2) (by omega) (by omega) (by omega) (by omega) (k - J0) (by omega)
    (by omega)
  have hAe : (if J0 ≤ k then XA (k - J0) 0 else 0) - (if J1 ≤ k then XA (k - J1) 0 else 0) -
      (if J2 ≤ k then XA (k - J2) 0 else 0) + (if J3 ≤ k then XA (k - J3) 0 else 0) =
      sumA (J1 - J0) (J3 - J2) (k - J0) := by
    have a0 : J0 ≤ k := by omega
    have a1 : J1 ≤ k := by omega
    have a2 : J2 ≤ k := by omega
    have a3 : J3 ≤ k := by omega
    have b1 : J1 - J0 ≤ k - J0 := by omega
    have b2 : J1 - J0 + 160 ≤ k - J0 := by omega
    have b3 : J1 - J0 + 160 + (J3 - J2) ≤ k - J0 := by omega
    simp only [sumA, a0, a1, a2, a3, b1, b2, b3, ite_true]
    rw [show k - J0 - (J1 - J0) = k - J1 by omega, show k - J0 - (J1 - J0 + 160) = k - J2 by omega,
      show k - J0 - (J1 - J0 + 160 + (J3 - J2)) = k - J3 by omega]
  have r0 := rest_le s hs k klo hc0 hV0 (by omega)
  have r1 := rest_le _ hs1 k (klo - 287) hc1 (fun m hm => hV1 m (by omega)) (by omega)
  have r2 := rest_le _ hs2 k (klo - 447) hc2 (fun m hm => hV2 m (by omega)) (by omega)
  have r3 := rest_le _ hs3 k (klo - 734) hc3 (fun m hm => hV3 m (by omega)) (by omega)
  rw [abs_le] at r0 r1 r2 r3
  have key : ∀ (a0 a1 a2 a3 p0 p1 p2 p3 : ℝ), (a0 + p0) - (a1 + p1) - (a2 + p2) + (a3 + p3) =
      (a0 - a1 - a2 + a3) + (p0 - p1 - p2 + p3) := fun _ _ _ _ _ _ _ _ => by ring
  rw [key, hAe]
  constructor <;> linarith [hsum.1, hsum.2, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2]

/-- **Signed S-curve bound on a window**: averaging over the start of the jerk pulse. -/
theorem scurve_win (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (klo khi : ℕ)
    {lo hi : ℝ}
    (hb : ∀ s T1, 0 ≤ s → 213 / 400 ≤ T1 → T1 ≤ 287 / 400 → ∀ k, Jof s + klo ≤ k → k ≤ Jof s + khi →
      lo ≤ errResp (bangRef s T1) k 0 ∧ errResp (bangRef s T1) k 0 ≤ hi)
    (k : ℕ) (hk1 : Jof s₀ + 160 + klo ≤ k) (hk2 : k ≤ Jof s₀ + khi) :
    lo ≤ errResp (scurveRef s₀ L) k 0 ∧ errResp (scurveRef s₀ L) k 0 ≤ hi := by
  obtain ⟨t1, t2⟩ := T1_mem_of_L L h1 h2
  have hT : 0 ≤ T1ofL L := by linarith
  have hle : (0 : ℝ) ≤ 2 / 5 := by norm_num
  set μ := volume.restrict (Ioc (0 : ℝ) (2 / 5))
  set R : ℝ → ℕ → ℝ × ℝ × ℝ := fun u j => pulse u • bangRef (s₀ + u) (T1ofL L) j
  have hint : ∀ j, Integrable (fun u => (R u j).1) μ ∧ Integrable (fun u => (R u j).2.1) μ ∧
      Integrable (fun u => (R u j).2.2) μ := by
    intro j
    simp only [R, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    refine ⟨integrable_pulse_mul s₀ _ j (fun x => x.1) measurable_fst _ (fun u hu =>
        (bangRef_bound _ _ (by linarith) hT j).1),
      integrable_pulse_mul s₀ _ j (fun x => x.2.1) (measurable_fst.comp measurable_snd) _
        (fun u hu => (bangRef_bound _ _ (by linarith) hT j).2.1),
      integrable_pulse_mul s₀ _ j (fun x => x.2.2) (measurable_snd.comp measurable_snd) _
        (fun u hu => (bangRef_bound _ _ (by linarith) hT j).2.2)⟩
  have hr : ∀ j, scurveRef s₀ L j = (∫ u, (R u j).1 ∂μ, ∫ u, (R u j).2.1 ∂μ, ∫ u, (R u j).2.2 ∂μ) := by
    intro j
    simp only [R, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, scurveRef,
      intervalIntegral.integral_of_le hle]
    rfl
  obtain ⟨hI, hE⟩ := errResp_integral μ R (scurveRef s₀ L) hint hr k 0
  have e : (fun u => errResp (R u) k 0) = fun u => pulse u * errResp (bangRef (s₀ + u) (T1ofL L)) k 0 := by
    funext u; simp only [R]; rw [errResp_smul]; rfl
  rw [e] at hI hE
  have hwi : Integrable pulse μ :=
    (continuous_pulse.integrableOn_Icc (a := 0) (b := 2 / 5)).mono_set Ioc_subset_Icc_self
  have hw1 : ∫ u, pulse u ∂μ = 1 := by
    rw [← intervalIntegral.integral_of_le hle, integral_pulse]
  have hmem : ∀ u ∈ Ioc (0 : ℝ) (2 / 5), lo ≤ errResp (bangRef (s₀ + u) (T1ofL L)) k 0 ∧
      errResp (bangRef (s₀ + u) (T1ofL L)) k 0 ≤ hi := by
    intro u hu
    have j1 : Jof s₀ ≤ Jof (s₀ + u) := Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith [hu.1])
      per_pos.le)
    have j2 : Jof (s₀ + u) ≤ Jof s₀ + 160 := by
      rw [← Jof_add_gap s₀ hs]
      exact Nat.ceil_mono (div_le_div_of_nonneg_right (by linarith [hu.2]) per_pos.le)
    exact hb (s₀ + u) (T1ofL L) (by linarith [hu.1]) t1 t2 k (by omega) (by omega)
  have hae : ∀ᵐ u ∂μ, u ∈ Ioc (0 : ℝ) (2 / 5) := ae_restrict_mem measurableSet_Ioc
  rw [hE]
  constructor
  · have hlo : ∫ u, pulse u * lo ∂μ ≤ ∫ u, pulse u * errResp (bangRef (s₀ + u) (T1ofL L)) k 0 ∂μ :=
      integral_mono_ae (hwi.mul_const lo) hI (hae.mono fun u hu =>
        mul_le_mul_of_nonneg_left (hmem u hu).1 (pulse_nonneg u))
    rwa [integral_mul_const, hw1, one_mul] at hlo
  · have hhi : ∫ u, pulse u * errResp (bangRef (s₀ + u) (T1ofL L)) k 0 ∂μ ≤ ∫ u, pulse u * hi ∂μ :=
      integral_mono_ae hI (hwi.mul_const hi) (hae.mono fun u hu =>
        mul_le_mul_of_nonneg_left (hmem u hu).2 (pulse_nonneg u))
    rwa [integral_mul_const, hw1, one_mul] at hhi

/-! ### Combining the two parts -/

theorem errResp_shift (r : ℕ → ℝ × ℝ × ℝ) (hr0 : r 0 = 0) (D k : ℕ) :
    errResp (fun j => if D ≤ j then r (j - D) else 0) k = if D ≤ k then errResp r (k - D) else 0 := by
  have hf : forceOf (fun j => if D ≤ j then r (j - D) else 0) =
      fun j => if D ≤ j then forceOf r (j - D) else 0 := by
    funext j
    by_cases h : D ≤ j
    · have h' : D ≤ j + 1 := by omega
      simp only [forceOf, h, h', ite_true]
      rw [show j + 1 - D = j - D + 1 by omega]
    · simp only [h, ite_false]
      by_cases h1 : D = j + 1
      · ext i
        simp [forceOf, defect₁, defect₂, h1, hr0]
      · have h1' : ¬ D ≤ j + 1 := by omega
        ext i
        simp [forceOf, defect₁, defect₂, h, h1']
  simp only [errResp, hf]
  exact traj_shift AvR (forceOf r) D k

theorem vtRef_zero : VTab.vtRef 0 = 0 := by
  simp [VTab.vtRef, VTab.vt_zero]

/-- **The combination**: the vertical model's error under the leg-0 climb `-scurveRef s₀ L` plus
the legs 1–7 table started after `D1` ticks is bounded by `vz`, given the signed bounds of the
two parts at the tick. -/
theorem vz_comb (s₀ L : ℝ) (D1 k : ℕ) (hD : D1 ≤ k) {lo0 hi0 loZ hiZ vz : ℝ}
    (h0 : lo0 ≤ errResp (scurveRef s₀ L) k 0 ∧ errResp (scurveRef s₀ L) k 0 ≤ hi0)
    (hZ : loZ ≤ errResp VTab.vtRef (k - D1) 0 ∧ errResp VTab.vtRef (k - D1) 0 ≤ hiZ)
    (hv1 : hiZ - lo0 ≤ vz) (hv2 : hi0 - loZ ≤ vz) :
    |errResp (fun j => (-1 : ℝ) • scurveRef s₀ L j + (if D1 ≤ j then VTab.vtRef (j - D1) else 0)) k 0| ≤ vz := by
  rw [errResp_add, errResp_smul, errResp_shift _ vtRef_zero]
  simp only [hD, ↓reduceIte]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [abs_le]; constructor <;> linarith [h0.1, h0.2, hZ.1, hZ.2]

/-- The legs 1–7 part on a window, from the window check. -/
theorem legs_win (a b c0 nc : ℕ) (lo hi : ℤ) (hc : c0 + nc ≤ 169) (h0 : 32 * c0 ≤ a)
    (h1 : b < 32 * (c0 + nc)) (hW : allOK (VTab.chkW a b lo hi) nc c0 = true) (i : ℕ) (hi1 : a ≤ i)
    (hi2 : i ≤ b) :
    (lo : ℝ) / 2 ^ 64 - 1 / 10 ^ 13 ≤ errResp VTab.vtRef i 0 ∧
      errResp VTab.vtRef i 0 ≤ (hi : ℝ) / 2 ^ 64 + 1 / 10 ^ 13 := by
  obtain ⟨w1, w2⟩ := VTab.window a b lo hi c0 nc hc h0 h1 hW i hi1 hi2
  have hc := abs_le.mp (VTab.resp_close i)
  have e1 : (lo : ℝ) / 2 ^ 64 ≤ ((VTab.Xf i).1 : ℝ) / 2 ^ 64 :=
    div_le_div_of_nonneg_right (by exact_mod_cast w1) (by positivity)
  have e2 : ((VTab.Xf i).1 : ℝ) / 2 ^ 64 ≤ (hi : ℝ) / 2 ^ 64 :=
    div_le_div_of_nonneg_right (by exact_mod_cast w2) (by positivity)
  constructor <;> linarith [hc.1, hc.2]


set_option maxHeartbeats 0 in
theorem pat1_0 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_1 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_2 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_3 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_4 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 20 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_5 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 25 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_6 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 30 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_7 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 35 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_8 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 40 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_9 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 45 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_10 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 50 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_11 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 55 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_12 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 60 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_13 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 65 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat1_14 : allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 70 = true := by
  decide +kernel

theorem pat1 : ∀ G1, 213 ≤ G1 → G1 ≤ 287 → patG (-279041140053448) (-96166496776758) 1148 275 G1 = true := by
  intro G1 h1 h2
  have key : ∀ g < 15, allOK (fun j => patG (-279041140053448) (-96166496776758) 1148 275 (213 + j)) 5 (5 * g) = true := by
    intro g hg
    match g, hg with
    | 0, _ => exact pat1_0
    | 1, _ => exact pat1_1
    | 2, _ => exact pat1_2
    | 3, _ => exact pat1_3
    | 4, _ => exact pat1_4
    | 5, _ => exact pat1_5
    | 6, _ => exact pat1_6
    | 7, _ => exact pat1_7
    | 8, _ => exact pat1_8
    | 9, _ => exact pat1_9
    | 10, _ => exact pat1_10
    | 11, _ => exact pat1_11
    | 12, _ => exact pat1_12
    | 13, _ => exact pat1_13
    | 14, _ => exact pat1_14
  have := allOK_spec _ 5 (5 * ((G1 - 213) / 5)) (key _ (by omega)) ((G1 - 213) % 5) (Nat.mod_lt _ (by norm_num))
  rwa [show 213 + (5 * ((G1 - 213) / 5) + (G1 - 213) % 5) = G1 by omega] at this

/-- The leg-0 climb at the window of `w1`: `k - ⌈s₀/h⌉ ∈ [1308, 1422]`. -/
theorem leg0_w1 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (k : ℕ)
    (hk1 : Jof s₀ + 1308 ≤ k) (hk2 : k ≤ Jof s₀ + 1422) :
    ((-279041140053448 : ℤ) : ℝ) / Sz - 4 / 10 ^ 12 - ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (285 / 10 ^ 6 : ℝ) + (285 / 10 ^ 6 : ℝ) + 4 * BP) ≤ errResp (scurveRef s₀ L) k 0 ∧
      errResp (scurveRef s₀ L) k 0 ≤ ((-96166496776758 : ℤ) : ℝ) / Sz + 4 / 10 ^ 12 + ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (285 / 10 ^ 6 : ℝ) + (285 / 10 ^ 6 : ℝ) + 4 * BP) :=
  scurve_win s₀ L hs h1 h2 1148 1422
    (fun s T1 hs hT1 hT2 k hk1 hk2 => bang_win s T1 hs hT1 hT2 1148 1422 (by norm_num)
      (fun G1 G3 a1 a2 a3 a4 k' hk1 hk2 => sumA_win pat1 (by norm_num) (by norm_num) G1 G3 a1 a2 a3 a4 k' hk1 (by omega))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge413 m (by omega)) (fun m hm => XV_ge413 m (by omega)) k hk1 hk2) k (by omega) hk2

/-- **The vertical nominal at `w1`** (ideal course; table window `937 … 975` = `k - D1 - 1`,
target within `0.1075` m of `w1` in the plane): `|ez| ≤ 517 / 25000`. -/
theorem vz_w1 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (D1 k : ℕ) (hD : D1 ≤ k)
    (hw1 : 938 ≤ k - D1) (hw2 : k - D1 ≤ 976) (hk1 : Jof s₀ + 1308 ≤ k) (hk2 : k ≤ Jof s₀ + 1422) :
    |errResp (fun j => (-1 : ℝ) • scurveRef s₀ L j + (if D1 ≤ j then VTab.vtRef (j - D1) else 0)) k 0| ≤
      517 / 25000 := by
  refine vz_comb s₀ L D1 k hD (leg0_w1 s₀ L hs h1 h2 k hk1 hk2)
    (legs_win 938 976 29 2 (-108824675257520125) (-103414957182250598) (by norm_num) (by norm_num) (by norm_num) VTab.win1 _ hw1 hw2) ?_ ?_
  · norm_num [Sz, BP]
  · norm_num [Sz, BP]


set_option maxHeartbeats 0 in
theorem pat2_0 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_1 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_2 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_3 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_4 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 20 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_5 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 25 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_6 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 30 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_7 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 35 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_8 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 40 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_9 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 45 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_10 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 50 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_11 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 55 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_12 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 60 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_13 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 65 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat2_14 : allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 70 = true := by
  decide +kernel

theorem pat2 : ∀ G1, 213 ≤ G1 → G1 ≤ 287 → patG (-7980202533308) (-1654056079498) 1888 275 G1 = true := by
  intro G1 h1 h2
  have key : ∀ g < 15, allOK (fun j => patG (-7980202533308) (-1654056079498) 1888 275 (213 + j)) 5 (5 * g) = true := by
    intro g hg
    match g, hg with
    | 0, _ => exact pat2_0
    | 1, _ => exact pat2_1
    | 2, _ => exact pat2_2
    | 3, _ => exact pat2_3
    | 4, _ => exact pat2_4
    | 5, _ => exact pat2_5
    | 6, _ => exact pat2_6
    | 7, _ => exact pat2_7
    | 8, _ => exact pat2_8
    | 9, _ => exact pat2_9
    | 10, _ => exact pat2_10
    | 11, _ => exact pat2_11
    | 12, _ => exact pat2_12
    | 13, _ => exact pat2_13
    | 14, _ => exact pat2_14
  have := allOK_spec _ 5 (5 * ((G1 - 213) / 5)) (key _ (by omega)) ((G1 - 213) % 5) (Nat.mod_lt _ (by norm_num))
  rwa [show 213 + (5 * ((G1 - 213) / 5) + (G1 - 213) % 5) = G1 by omega] at this

/-- The leg-0 climb at the window of `w2`: `k - ⌈s₀/h⌉ ∈ [2048, 2162]`. -/
theorem leg0_w2 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (k : ℕ)
    (hk1 : Jof s₀ + 2048 ≤ k) (hk2 : k ≤ Jof s₀ + 2162) :
    ((-7980202533308 : ℤ) : ℝ) / Sz - 4 / 10 ^ 12 - ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) ≤ errResp (scurveRef s₀ L) k 0 ∧
      errResp (scurveRef s₀ L) k 0 ≤ ((-1654056079498 : ℤ) : ℝ) / Sz + 4 / 10 ^ 12 + ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) :=
  scurve_win s₀ L hs h1 h2 1888 2162
    (fun s T1 hs hT1 hT2 k hk1 hk2 => bang_win s T1 hs hT1 hT2 1888 2162 (by norm_num)
      (fun G1 G3 a1 a2 a3 a4 k' hk1 hk2 => sumA_win pat2 (by norm_num) (by norm_num) G1 G3 a1 a2 a3 a4 k' hk1 (by omega))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) k hk1 hk2) k (by omega) hk2

/-- **The vertical nominal at `w2`** (ideal course; table window `1677 … 1715` = `k - D1 - 1`,
target within `0.1075` m of `w2` in the plane): `|ez| ≤ 57 / 25000`. -/
theorem vz_w2 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (D1 k : ℕ) (hD : D1 ≤ k)
    (hw1 : 1678 ≤ k - D1) (hw2 : k - D1 ≤ 1716) (hk1 : Jof s₀ + 2048 ≤ k) (hk2 : k ≤ Jof s₀ + 2162) :
    |errResp (fun j => (-1 : ℝ) • scurveRef s₀ L j + (if D1 ≤ j then VTab.vtRef (j - D1) else 0)) k 0| ≤
      57 / 25000 := by
  refine vz_comb s₀ L D1 k hD (leg0_w2 s₀ L hs h1 h2 k hk1 hk2)
    (legs_win 1678 1716 52 2 (-33188653472739181) (-32050604292117536) (by norm_num) (by norm_num) (by norm_num) VTab.win2 _ hw1 hw2) ?_ ?_
  · norm_num [Sz, BP]
  · norm_num [Sz, BP]


set_option maxHeartbeats 0 in
theorem pat3_0 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 0 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_1 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 5 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_2 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_3 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 15 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_4 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 20 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_5 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 25 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_6 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 30 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_7 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 35 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_8 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 40 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_9 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 45 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_10 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 50 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_11 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 55 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_12 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 60 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_13 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 65 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pat3_14 : allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 70 = true := by
  decide +kernel

theorem pat3 : ∀ G1, 213 ≤ G1 → G1 ≤ 287 → patG (-5277420862450) (-784283185864) 2628 277 G1 = true := by
  intro G1 h1 h2
  have key : ∀ g < 15, allOK (fun j => patG (-5277420862450) (-784283185864) 2628 277 (213 + j)) 5 (5 * g) = true := by
    intro g hg
    match g, hg with
    | 0, _ => exact pat3_0
    | 1, _ => exact pat3_1
    | 2, _ => exact pat3_2
    | 3, _ => exact pat3_3
    | 4, _ => exact pat3_4
    | 5, _ => exact pat3_5
    | 6, _ => exact pat3_6
    | 7, _ => exact pat3_7
    | 8, _ => exact pat3_8
    | 9, _ => exact pat3_9
    | 10, _ => exact pat3_10
    | 11, _ => exact pat3_11
    | 12, _ => exact pat3_12
    | 13, _ => exact pat3_13
    | 14, _ => exact pat3_14
  have := allOK_spec _ 5 (5 * ((G1 - 213) / 5)) (key _ (by omega)) ((G1 - 213) % 5) (Nat.mod_lt _ (by norm_num))
  rwa [show 213 + (5 * ((G1 - 213) / 5) + (G1 - 213) % 5) = G1 by omega] at this

/-- The leg-0 climb at the window of `w3`: `k - ⌈s₀/h⌉ ∈ [2788, 2904]`. -/
theorem leg0_w3 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (k : ℕ)
    (hk1 : Jof s₀ + 2788 ≤ k) (hk2 : k ≤ Jof s₀ + 2904) :
    ((-5277420862450 : ℤ) : ℝ) / Sz - 4 / 10 ^ 12 - ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) ≤ errResp (scurveRef s₀ L) k 0 ∧
      errResp (scurveRef s₀ L) k 0 ≤ ((-784283185864 : ℤ) : ℝ) / Sz + 4 / 10 ^ 12 + ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) :=
  scurve_win s₀ L hs h1 h2 2628 2904
    (fun s T1 hs hT1 hT2 k hk1 hk2 => bang_win s T1 hs hT1 hT2 2628 2904 (by norm_num)
      (fun G1 G3 a1 a2 a3 a4 k' hk1 hk2 => sumA_win pat3 (by norm_num) (by norm_num) G1 G3 a1 a2 a3 a4 k' hk1 (by omega))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) k hk1 hk2) k (by omega) hk2

/-- **The vertical nominal at `w3`** (ideal course; table window `2417 … 2457` = `k - D1 - 1`,
target within `0.1075` m of `w3` in the plane): `|ez| ≤ 219 / 50000`. -/
theorem vz_w3 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (D1 k : ℕ) (hD : D1 ≤ k)
    (hw1 : 2418 ≤ k - D1) (hw2 : k - D1 ≤ 2458) (hk1 : Jof s₀ + 2788 ≤ k) (hk2 : k ≤ Jof s₀ + 2904) :
    |errResp (fun j => (-1 : ℝ) • scurveRef s₀ L j + (if D1 ≤ j then VTab.vtRef (j - D1) else 0)) k 0| ≤
      219 / 50000 := by
  refine vz_comb s₀ L D1 k hD (leg0_w3 s₀ L hs h1 h2 k hk1 hk2)
    (legs_win 2418 2458 75 2 (-70467772597766588) (-55100942503994685) (by norm_num) (by norm_num) (by norm_num) VTab.win3 _ hw1 hw2) ?_ ?_
  · norm_num [Sz, BP]
  · norm_num [Sz, BP]


/-- The leg-0 climb at the window of `w4`: `k - ⌈s₀/h⌉ ∈ [4235, 4352]`. -/
theorem leg0_w4 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (k : ℕ)
    (hk1 : Jof s₀ + 4235 ≤ k) (hk2 : k ≤ Jof s₀ + 4352) :
    -(292 / 10 ^ 6 : ℝ) - ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) ≤ errResp (scurveRef s₀ L) k 0 ∧
      errResp (scurveRef s₀ L) k 0 ≤ (292 / 10 ^ 6 : ℝ) + ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) :=
  scurve_win s₀ L hs h1 h2 4075 4352
    (fun s T1 hs hT1 hT2 k hk1 hk2 => bang_win s T1 hs hT1 hT2 4075 4352 (by norm_num)
      (fun G1 G3 a1 a2 a3 a4 k' hk1 hk2 => sumA_far G1 G3 a2 a4 k' (by omega))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) k hk1 hk2) k (by omega) hk2

/-- **The vertical nominal at `w4`** (ideal course; table window `3864 … 3905` = `k - D1 - 1`,
target within `0.1075` m of `w4` in the plane): `|ez| ≤ 99 / 12500`. -/
theorem vz_w4 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (D1 k : ℕ) (hD : D1 ≤ k)
    (hw1 : 3865 ≤ k - D1) (hw2 : k - D1 ≤ 3906) (hk1 : Jof s₀ + 4235 ≤ k) (hk2 : k ≤ Jof s₀ + 4352) :
    |errResp (fun j => (-1 : ℝ) • scurveRef s₀ L j + (if D1 ≤ j then VTab.vtRef (j - D1) else 0)) k 0| ≤
      99 / 12500 := by
  refine vz_comb s₀ L D1 k hD (leg0_w4 s₀ L hs h1 h2 k hk1 hk2)
    (legs_win 3865 3906 120 3 (-129053058191910744) (-84976960978898954) (by norm_num) (by norm_num) (by norm_num) VTab.win4 _ hw1 hw2) ?_ ?_
  · norm_num [Sz, BP]
  · norm_num [Sz, BP]


/-- The leg-0 climb at the window of `w5`: `k - ⌈s₀/h⌉ ∈ [4977, 5092]`. -/
theorem leg0_w5 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (k : ℕ)
    (hk1 : Jof s₀ + 4977 ≤ k) (hk2 : k ≤ Jof s₀ + 5092) :
    -(292 / 10 ^ 6 : ℝ) - ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) ≤ errResp (scurveRef s₀ L) k 0 ∧
      errResp (scurveRef s₀ L) k 0 ≤ (292 / 10 ^ 6 : ℝ) + ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) :=
  scurve_win s₀ L hs h1 h2 4817 5092
    (fun s T1 hs hT1 hT2 k hk1 hk2 => bang_win s T1 hs hT1 hT2 4817 5092 (by norm_num)
      (fun G1 G3 a1 a2 a3 a4 k' hk1 hk2 => sumA_far G1 G3 a2 a4 k' (by omega))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) k hk1 hk2) k (by omega) hk2

/-- **The vertical nominal at `w5`** (ideal course; table window `4606 … 4645` = `k - D1 - 1`,
target within `0.1075` m of `w5` in the plane): `|ez| ≤ 767 / 100000`. -/
theorem vz_w5 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (D1 k : ℕ) (hD : D1 ≤ k)
    (hw1 : 4607 ≤ k - D1) (hw2 : k - D1 ≤ 4646) (hk1 : Jof s₀ + 4977 ≤ k) (hk2 : k ≤ Jof s₀ + 5092) :
    |errResp (fun j => (-1 : ℝ) • scurveRef s₀ L j + (if D1 ≤ j then VTab.vtRef (j - D1) else 0)) k 0| ≤
      767 / 100000 := by
  refine vz_comb s₀ L D1 k hD (leg0_w5 s₀ L hs h1 h2 k hk1 hk2)
    (legs_win 4607 4646 143 3 (101449892410077667) (124484111246185194) (by norm_num) (by norm_num) (by norm_num) VTab.win5 _ hw1 hw2) ?_ ?_
  · norm_num [Sz, BP]
  · norm_num [Sz, BP]


/-- The leg-0 climb at the window of `w6`: `k - ⌈s₀/h⌉ ∈ [5718, 5832]`. -/
theorem leg0_w6 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (k : ℕ)
    (hk1 : Jof s₀ + 5718 ≤ k) (hk2 : k ≤ Jof s₀ + 5832) :
    -(292 / 10 ^ 6 : ℝ) - ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) ≤ errResp (scurveRef s₀ L) k 0 ∧
      errResp (scurveRef s₀ L) k 0 ≤ (292 / 10 ^ 6 : ℝ) + ((146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + (146 / 10 ^ 6 : ℝ) + 4 * BP) :=
  scurve_win s₀ L hs h1 h2 5558 5832
    (fun s T1 hs hT1 hT2 k hk1 hk2 => bang_win s T1 hs hT1 hT2 5558 5832 (by norm_num)
      (fun G1 G3 a1 a2 a3 a4 k' hk1 hk2 => sumA_far G1 G3 a2 a4 k' (by omega))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) (fun m hm => XV_ge800 m (by omega)) k hk1 hk2) k (by omega) hk2

/-- **The vertical nominal at `w6`** (ideal course; table window `5347 … 5385` = `k - D1 - 1`,
target within `0.1075` m of `w6` in the plane): `|ez| ≤ 143 / 25000`. -/
theorem vz_w6 (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (D1 k : ℕ) (hD : D1 ≤ k)
    (hw1 : 5348 ≤ k - D1) (hw2 : k - D1 ≤ 5386) (hk1 : Jof s₀ + 5718 ≤ k) (hk2 : k ≤ Jof s₀ + 5832) :
    |errResp (fun j => (-1 : ℝ) • scurveRef s₀ L j + (if D1 ≤ j then VTab.vtRef (j - D1) else 0)) k 0| ≤
      143 / 25000 := by
  refine vz_comb s₀ L D1 k hD (leg0_w6 s₀ L hs h1 h2 k hk1 hk2)
    (legs_win 5348 5386 167 2 (86843609401351666) (88596607834143619) (by norm_num) (by norm_num) (by norm_num) VTab.win6 _ hw1 hw2) ?_ ?_
  · norm_num [Sz, BP]
  · norm_num [Sz, BP]


end Corner

end

end Contracts.Track.Induction.Nominal
