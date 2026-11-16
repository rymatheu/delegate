import Contracts.Track.Induction.Step

/-!
# M9, part 5: `ψtrack` from the invariant, and `track_contract` from the pieces

`ψtrack_of_inv`: the invariant at every tick gives each conjunct of `ψtrack`:

* **T1** `err ≤ δ`: the nominal (`nom_T1`) plus the 3D tube `τ3`;
* **T2** the envelope: positions from the target box (`nav_bounds`) and T1, velocities from the
  velocity target and the boxes, rates from the attitude invariant (`att_rates`);
* **T3** the climb-out bound: `nom_climbout` plus the tube;
* **T4** the transfer: at `w0 = w7` from `nom_w07`, at `w₁ … w₆` from `nom_corner`, each plus the
  3D tube;
* **T6** the rest condition: `nom_rest` plus the velocity tube and the `float` sensing;
* **T5** the reach chain, by M8's `Pacing.pacing_course`: `Pace` from the code facts
  (`pace_run`, by `Pacing.pace_of`), the phase bounds from P-1 (`phase_r`: `Pacing.rawScaler_ge`
  with the along-track errors of the nominal, `nom_along`, plus the tubes), the vehicle's window at
  `w0` (`nom_win0` plus the tube), the target's windows (`pace_win`), the escape and the gaps;
* **the hold**, by `Pacing.hold_course` (the loiter, `loiter_nav`, with the completion state from
  `nom_complete`, the tubes and the estimates) or, without completion in the horizon,
  `Pacing.hold_formula` with `pace_end` and the S-curve time's leak (`q_leak`).

`track_contract_of_pieces` is the contract of `Sub.lean` from `Pieces`.
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission Matrix Finset

noncomputable section

variable {sense32 : ℝ → Float32} {senseP : ℝ → Float} {w₀ : Vehicle.World}

/-! ## Geometry -/

theorem hyp_le_dist (p q : P3) : Horizontal.hyp (p 0 - q 0) (p 1 - q 1) ≤ dist p q := by
  rw [dist_eq3, Horizontal.hyp]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (p 2 - q 2)])

theorem hyp_le_abs (a b : ℝ) : Horizontal.hyp a b ≤ |a| + |b| := by
  have h := Horizontal.hyp_add_le a 0 0 b
  simp only [add_zero, zero_add] at h
  refine h.trans (le_of_eq ?_)
  simp [Horizontal.hyp, Real.sqrt_sq_eq_abs]

theorem dist_le_of_parts {p w : P3} {Bp Bv r : ℝ} (hr : 0 ≤ r)
    (hp : Horizontal.hyp (p 0 - w 0) (p 1 - w 1) ≤ Bp) (hv : |p 2 - w 2| ≤ Bv)
    (h : Bp ^ 2 + Bv ^ 2 ≤ r ^ 2) : dist p w ≤ r := by
  have h1 := Horizontal.sq_le_of_hyp hp
  have h2 := sq_le_sq' (abs_le.1 hv).1 (abs_le.1 hv).2
  rw [dist_eq3, Real.sqrt_le_left hr]
  nlinarith

theorem wp_cIdx (c : Fin 6) :
    wp (cIdx c) 0 = Horizontal.cN c ∧ wp (cIdx c) 1 = Horizontal.cE c := by
  fin_cases c <;> simp [wp, cIdx, Horizontal.cN, Horizontal.cE] <;> norm_num

theorem rPass_cIdx (c : Fin 6) : rPass (wp (cIdx c)) = rPassMid :=
  rPass_mid _ (fun h => by have := congrArg Fin.val h; simp [cIdx] at this)
    (fun h => by have := congrArg Fin.val h; simp [cIdx] at this; omega)

/-! ## The invariant over the horizon, unpacked -/

section Unpack

variable (P : Pieces sense32 senseP w₀) {x : ℕ → Mission.X}
  (hInv : ∀ t ≤ horizonTicks, Inv P.toIface w₀ x t)
include hInv

theorem inv1 (t : ℕ) (ht : t ≤ horizonTicks) : Inv1 P.toIface w₀ x t := hInv t ht t le_rfl

theorem pre_at (t : ℕ) (ht : t ≤ horizonTicks) : Pre P.toIface w₀ x t := pre_of_inv (hInv t ht)

end Unpack

/-! ## The conjuncts at one tick -/

section Tick

variable (P : Pieces sense32 senseP w₀) (hS : Plant.CopterSense sense32 senseP)
  {x : ℕ → Mission.X} (hx : Beh sense32 senseP w₀ x)
  (hInv : ∀ t ≤ horizonTicks, Inv P.toIface w₀ x t)
include hx hInv

theorem vel_bound (t : ℕ) (ht : t ≤ horizonTicks) (i : Fin 3) : |vel (x t) i| ≤ 2 :=
  vel_bound_of P hx (inv1 P hInv t ht).region i

theorem env_at (t : ℕ) (ht : t ≤ horizonTicks) : physEnv (x t) := by
  have R := (inv1 P hInv t ht).region
  have hp : ∀ i : Fin 3, |(x t).phys.x (pIx i)| ≤ 10 := by
    intro i
    have := pos_bound P hx (hInv t ht) i
    have e : pos (x t) i = (x t).phys.x (pIx i) := by fin_cases i <;> simp [pos, pIx]
    rw [e] at this; norm_num [δ] at this; linarith
  have hv : ∀ i : Fin 3, |(x t).phys.x (vIx i)| ≤ 2 := by
    intro i
    have := vel_bound P hx hInv t ht i
    have e : vel (x t) i = (x t).phys.x (vIx i) := by fin_cases i <;> simp [vel, vIx]
    rwa [e] at this
  obtain ⟨w0, w1, w2⟩ := P.att_rates x hx t R.att
  refine ⟨⟨hp 0, hp 1, hp 2⟩, ⟨hv 0, hv 1, hv 2⟩, ⟨?_, ?_, ?_⟩⟩
  · exact w0.trans (by norm_num)
  · exact w1.trans (by norm_num)
  · exact w2.trans (by norm_num)

/-- T4 at a corner `w₁ … w₆`: the nominal (`nom_corner`) plus the 3D tube. -/
theorem prox_corner (t : ℕ) (ht : t ≤ horizonTicks) (c : Fin 6) (hw : dist (posTarget (x t)) (wp (cIdx c)) ≤ rPassMid) :
    dist (pos (x t)) (wp (cIdx c)) ≤ rWp :=
  (dist_pos_le P.toIface w₀ (inv1 P hInv t ht).tube _).trans
    (P.nom_corner x hx t (pre_at P hInv t ht) c hw)

include hS in
/-- The conjunct `errLE δ ∧ envF ∧ takeoffF ∧ proxAllF ∧ restF` at tick `t`. -/
theorem always_at (t : ℕ) (ht : t ≤ horizonTicks) :
    sat x t (.and (errLE δ) (.and envF (.and takeoffF (.and proxAllF restF)))) := by
  have I1 := inv1 P hInv t ht
  have hpre := pre_at P hInv t ht
  have herr := err_le_nom P.toIface w₀ I1.tube
  refine ⟨sat_errLE.2 (err_le P hx (hInv t ht)), sat_propF.2 (env_at P hx hInv t ht), ?_, ?_, ?_⟩
  · -- T3
    rw [takeoffF, sat_imp_iff]
    rintro ⟨hc, hn⟩
    simp only [inColumnT, sat_propF] at hc
    simp only [nearPolyT, sat_not, sat_atom, sub_nonneg, not_le] at hn
    exact sat_errLE.2 (herr.trans (P.nom_climbout x hx t hpre hc hn))
  · -- T4
    rw [proxAllF, sat_allF]
    intro φ hφ
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hφ
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
    rw [proxF, sat_imp_iff, sat_nearT, sat_near]
    intro hT
    have w07 : ∀ j : Fin 8, wp j = w7 → dist (posTarget (x t)) (wp j) ≤ rPass (wp j) →
        dist (pos (x t)) (wp j) ≤ rWp := by
      intro j hj hT'
      rw [hj] at hT' ⊢
      rw [rPass_w7] at hT'
      exact (dist_pos_le P.toIface w₀ I1.tube w7).trans (P.nom_w07 x hx t hpre hT')
    fin_cases i
    · exact w07 0 w0_eq_w7 hT
    · rw [show (⟨1, by omega⟩ : Fin 8) = cIdx 0 from rfl] at hT ⊢
      exact prox_corner P hx hInv t ht 0 (by rwa [rPass_cIdx] at hT)
    · rw [show (⟨2, by omega⟩ : Fin 8) = cIdx 1 from rfl] at hT ⊢
      exact prox_corner P hx hInv t ht 1 (by rwa [rPass_cIdx] at hT)
    · rw [show (⟨3, by omega⟩ : Fin 8) = cIdx 2 from rfl] at hT ⊢
      exact prox_corner P hx hInv t ht 2 (by rwa [rPass_cIdx] at hT)
    · rw [show (⟨4, by omega⟩ : Fin 8) = cIdx 3 from rfl] at hT ⊢
      exact prox_corner P hx hInv t ht 3 (by rwa [rPass_cIdx] at hT)
    · rw [show (⟨5, by omega⟩ : Fin 8) = cIdx 4 from rfl] at hT ⊢
      exact prox_corner P hx hInv t ht 4 (by rwa [rPass_cIdx] at hT)
    · rw [show (⟨6, by omega⟩ : Fin 8) = cIdx 5 from rfl] at hT ⊢
      exact prox_corner P hx hInv t ht 5 (by rwa [rPass_cIdx] at hT)
    · exact w07 7 rfl hT
  · -- T6
    rw [restF, sat_imp_iff]
    rintro ⟨hn, hv⟩
    rw [sat_nearT] at hn
    simp only [sat_atom, sub_nonneg] at hv ⊢
    have hr := P.nom_rest x hx t hpre hn hv
    have hc := smpVel_close hS hx.1.1 t fun i => (vel_bound P hx hInv t ht i).trans (by norm_num)
    have hV : dist (vel (x t)) (velTarget (x t)) ≤ ‖nomV3 P.toIface w₀ x t‖ + τ3v := by
      rw [vel_eq P.toIface w₀ x t, V3_eq, dist_eq_norm, add_sub_cancel_left]
      exact (norm_add_le _ _).trans (by linarith [η3v_le P.toIface w₀ I1.tube])
    rw [smpVelErr]
    have := dist_triangle (smpVel (x t)) (vel (x t)) (velTarget (x t))
    linarith

end Tick

/-! ## The reach chain and the hold, by M8's `pacing_course` and `hold_course` -/

theorem dot3_eq (a b : AC_WPNav_lib.Vector3f.State) : Pacing.dot3 a b = inner ℝ (v3 a) (v3 b) := by
  simp [Pacing.dot3, v3, PiLp.inner_apply, Fin.sum_univ_three]; ring

theorem len3_eq (a : AC_WPNav_lib.Vector3f.State) : Pacing.len3 a = ‖v3 a‖ := by
  rw [norm_eq3, Pacing.len3]; simp [v3]

theorem cPace : (1 / 10 ^ 7 : ℝ) / Pacing.α₀ ≤ 1 / 10 ^ 4 := by norm_num [Pacing.α₀]

/-! ### The pacing sequences, extended past the horizon

M8's `Pace` is a statement about all ticks; the invariant covers the horizon. Past it the
sequences are continued by the ideal filter with raw scaler `1` (`rE`, `sE`, `qE`); on the horizon
they are the run's. -/

/-- The raw scaler, `1` past the horizon. -/
def rE (I : Iface) (x : ℕ → Mission.X) (t : ℕ) : ℝ := if t ≤ horizonTicks then I.r x t else 1

/-- The filtered scaler, continued by the exact filter past the horizon. -/
def sE (I : Iface) (x : ℕ → Mission.X) : ℕ → ℝ
  | 0 => I.sc x 0
  | t + 1 => if t + 1 ≤ horizonTicks then I.sc x (t + 1)
      else sE I x t + (rE I x (t + 1) - sE I x t) * Pacing.α₀

/-- The S-curve time, continued exactly past the horizon. -/
def qE (I : Iface) (x : ℕ → Mission.X) : ℕ → ℝ
  | 0 => I.q x 0
  | t + 1 => if t + 1 ≤ horizonTicks then I.q x (t + 1) else qE I x t + sE I x (t + 1)

theorem rE_eq (I : Iface) (x : ℕ → Mission.X) {t : ℕ} (ht : t ≤ horizonTicks) : rE I x t = I.r x t := by
  simp [rE, ht]

theorem sE_eq (I : Iface) (x : ℕ → Mission.X) {t : ℕ} (ht : t ≤ horizonTicks) : sE I x t = I.sc x t := by
  cases t with
  | zero => rfl
  | succ t => simp [sE, ht]

theorem qE_eq (I : Iface) (x : ℕ → Mission.X) {t : ℕ} (ht : t ≤ horizonTicks) : qE I x t = I.q x t := by
  cases t with
  | zero => rfl
  | succ t => simp [qE, ht]

/-- **`hesc` from the hypothesis `ClimbEscape`**: with `q` and `τ_v` the navigator's (`q_nav`,
`τv_nav`), the escape of `Pacing.pacing_course` is `ClimbEscape` read at `x`. -/
theorem pace_esc_of (P : Pieces sense32 senseP w₀) (hE : ClimbEscape sense32 senseP w₀)
    {x : ℕ → Mission.X} (hx : Beh sense32 senseP w₀ x) :
    0 ≤ P.τv x ∧ ∃ t ≤ 350, P.τv x ≤ P.q x t := by
  obtain ⟨t, ht, h⟩ := hE x ⟨hx.1, hx.2⟩
  refine ⟨?_, t, ht, ?_⟩
  · rw [P.τv_nav x hx, climbTau]
    exact mul_nonneg (by norm_num) (Real.sInf_nonneg fun _ ⟨_, _, _, h0, _⟩ => h0)
  · rw [P.τv_nav x hx, P.q_nav x hx t ht]
    exact h

section Reach

set_option linter.unusedSectionVars false

variable (P : Pieces sense32 senseP w₀) {x : ℕ → Mission.X} (hx : Beh sense32 senseP w₀ x)
  (hInv : ∀ t ≤ horizonTicks, Inv P.toIface w₀ x t)
include hx hInv

/-- The filtered scaler stays in `[−c, 1 + c]` over the horizon, `c = 10⁻⁷/α₀` (as
`Pacing.filter_bounds`, with the filter step of each tick from `pace_filter`). -/
theorem sc_bounds (t : ℕ) (ht : t ≤ horizonTicks) :
    -((1 / 10 ^ 7) / Pacing.α₀) ≤ P.sc x t ∧ P.sc x t ≤ 1 + (1 / 10 ^ 7) / Pacing.α₀ := by
  have hα : (0 : ℝ) < Pacing.α₀ := by norm_num [Pacing.α₀]
  have hα1 : Pacing.α₀ ≤ 1 := by norm_num [Pacing.α₀]
  have hc : Pacing.α₀ * ((1 / 10 ^ 7) / Pacing.α₀) = 1 / 10 ^ 7 := by field_simp
  have hcp := cPace
  induction t with
  | zero => exact P.pace_s0 x hx
  | succ t ih =>
    have ih := ih (by omega)
    have h := abs_le.1 (P.pace_filter x hx t (inv1 P hInv (t + 1) ht).region
      (by linarith [ih.1]) (by linarith [ih.2]))
    obtain ⟨r0, r1⟩ := P.pace_raw x hx (t + 1)
    constructor <;> nlinarith [ih.1, ih.2]

/-- **The pacing facts of the run** (`Pacing.Pace`, extended past the horizon), by
`Pacing.pace_of`. -/
theorem pace_run :
    Pacing.Pace (sE P.toIface x) (rE P.toIface x) (qE P.toIface x) Pacing.α₀ (1 / 10 ^ 7) (1 / 10 ^ 7) := by
  have hcp := cPace
  have hα : (0 : ℝ) < Pacing.α₀ := by norm_num [Pacing.α₀]
  refine Pacing.pace_of (fun t => ?_) (fun t => ?_) ?_ (fun t => ?_) ?_
  · by_cases ht : t + 1 ≤ horizonTicks
    · rw [sE_eq _ _ ht, sE_eq _ _ (by omega : t ≤ horizonTicks), rE_eq _ _ ht]
      have hb := sc_bounds P hx hInv t (by omega)
      exact P.pace_filter x hx t (inv1 P hInv (t + 1) ht).region (by linarith [hb.1]) (by linarith [hb.2])
    · simp only [sE, ht, if_false, sub_self, abs_zero]; norm_num
  · by_cases ht : t ≤ horizonTicks
    · rw [rE_eq _ _ ht]; exact P.pace_raw x hx t
    · simp [rE, ht]
  · exact P.pace_s0 x hx
  · by_cases ht : t + 1 ≤ horizonTicks
    · rw [qE_eq _ _ ht, qE_eq _ _ (by omega : t ≤ horizonTicks), sE_eq _ _ ht]
      exact P.pace_q x hx t (inv1 P hInv (t + 1) ht).region
    · simp only [qE, ht, if_false]; ring_nf; norm_num
  · exact P.pace_q0 x hx

/-- **P-1 on the phases**: on a phase where the S-curve speed is at least `v_min`, the raw scaler of
the next tick is at least `ρ`, from `Pacing.rawScaler_ge` with the along-track bounds of the nominal
(`nom_along`) and the tubes. -/
theorem phase_r (t : ℕ) (ht : t + 1 ≤ horizonTicks) {vmin ρ : ℝ} (hvmin : 1 / 10 ≤ vmin)
    (hρ : ρ ≤ min 1 (21 / 20 - (55 / 1000 + 3 / 2 * (3 / 100)) / vmin - 1 / 1000))
    (hsp : vmin ≤ ‖velTarget (x t)‖) (h1 : P.τv x - 1 ≤ P.q x t) (h2 : P.q x t < P.ar x 7) :
    ρ ≤ P.r x (t + 1) := by
  obtain ⟨vT, pe, ve, kP, hr, hkf, hk, hvT, hpe, hve, eV, dve, dpe⟩ :=
    P.pace_scaler x hx t (fun k hk => inv1 P hInv k (by omega))
  obtain ⟨av, ae⟩ := P.nom_along x hx t (pre_at P hInv (t + 1) ht) h1 h2
  set V := velTarget (x t)
  have T1 := inv1 P hInv (t + 1) ht
  have hη := η3_le P.toIface w₀ T1.tube
  have hηv := η3v_le P.toIface w₀ T1.tube
  have hvel := vel_eq P.toIface w₀ x (t + 1)
  rw [V3_eq] at hvel
  have hpos := pos_eq P.toIface w₀ x (t + 1)
  rw [E3_eq] at hpos
  have hL : Pacing.len3 vT = ‖V‖ := by rw [len3_eq, eV]
  have hv : Pacing.dot3 vT vT - Pacing.dot3 ve vT ≤ 55 / 1000 * Pacing.len3 vT := by
    rw [dot3_eq, dot3_eq, eV, hL, real_inner_comm V (v3 ve), ← inner_sub_right]
    have e : V - v3 ve = (V - (velTarget (x (t + 1)) + nomV3 P.toIface w₀ x (t + 1))) -
        η3v P.toIface w₀ x (t + 1) + (vel (x (t + 1)) - v3 ve) := by rw [hvel]; abel
    rw [e, inner_add_right, inner_sub_right]
    have c1 := real_inner_le_norm V (vel (x (t + 1)) - v3 ve)
    have c2 := abs_real_inner_le_norm V (η3v P.toIface w₀ x (t + 1))
    rw [← dist_eq_norm, dist_comm] at c1
    have hn := norm_nonneg V
    nlinarith [abs_le.1 c2, mul_le_mul_of_nonneg_left dve hn, mul_le_mul_of_nonneg_left hηv hn]
  have he : Pacing.dot3 pe vT ≤ 3 / 100 * Pacing.len3 vT := by
    rw [dot3_eq, eV, hL, real_inner_comm V (v3 pe)]
    have e : v3 pe = (posTarget (x t) - (posTarget (x (t + 1)) + nomE3 P.toIface w₀ x (t + 1))) -
        η3 P.toIface w₀ x (t + 1) + (v3 pe - (posTarget (x t) - pos (x (t + 1)))) := by
      rw [hpos]; abel
    rw [e, inner_add_right, inner_sub_right]
    have c1 := real_inner_le_norm V (v3 pe - (posTarget (x t) - pos (x (t + 1))))
    have c2 := abs_real_inner_le_norm V (η3 P.toIface w₀ x (t + 1))
    rw [← dist_eq_norm] at c1
    have hn := norm_nonneg V
    nlinarith [abs_le.1 c2, mul_le_mul_of_nonneg_left dpe hn, mul_le_mul_of_nonneg_left hη hn]
  have hg := Pacing.rawScaler_ge vT pe ve kP hkf hk hvT hpe hve hvmin (hL ▸ hsp) (by norm_num) hv he
  rw [hr]
  exact hρ.trans hg

/-- The windows are ordered (`pace_gaps`). -/
theorem ar_order :
    P.τv x + 242 ≤ P.ar x 1 ∧ P.ar x 1 ≤ P.ar x 2 ∧ P.ar x 2 ≤ P.ar x 3 ∧ P.ar x 3 ≤ P.ar x 4 ∧
      P.ar x 4 ≤ P.ar x 5 ∧ P.ar x 5 ≤ P.ar x 6 ∧ P.ar x 6 ≤ P.ar x 7 := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := P.pace_gaps x hx
  refine ⟨by linarith [g0.1, g1.1], by linarith [g2.1], by linarith [g3.1], by linarith [g4.1],
    by linarith [g5.1], by linarith [g6.1], by linarith [g7.1]⟩

/-- **T5, the reach chain**, by `Pacing.pacing_course`. -/
theorem reach_chain (hE : ClimbEscape sense32 senseP w₀) :
    sat x 0 (.eventually 0 1200 (.and (near (wp 0) rWp)
      (reachSeqF (fun w => nearT w (rPass w)) legs.tail))) ∧
      ∃ t ≤ 10800, P.ar x 7 ≤ qE P.toIface x t := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := ar_order P hx hInv
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := P.pace_gaps x hx
  obtain ⟨hτ, t0, ht0, hesc⟩ := pace_esc_of P hE hx
  obtain ⟨rL, rM, rE'⟩ := Pacing.rho_course
  have hN : horizonTicks = 12000 := rfl
  refine Pacing.pacing_course (pace_run P hx hInv) x (P.ar x) hτ
    ⟨t0, ht0, by rw [qE_eq _ _ (by rw [hN]; omega)]; exact hesc⟩ g0 g1 g2 g3 g4 g5 g6 g7 ?_ ?_ ?_ ?_ ?_
  · intro t ht h1 h2
    rw [qE_eq _ _ (by rw [hN]; omega)] at h1 h2
    rw [rE_eq _ _ (by rw [hN]; omega)]
    exact phase_r P hx hInv t (by rw [hN]; omega) (by norm_num) rL
      ((P.pace_speed x hx t (inv1 P hInv t (by rw [hN]; omega)).region.nav).1 h1 h2) h1 (by linarith)
  · intro i hi2 hi6 t ht h1 h2
    rw [qE_eq _ _ (by rw [hN]; omega)] at h1 h2
    rw [rE_eq _ _ (by rw [hN]; omega)]
    have hsp := (P.pace_speed x hx t (inv1 P hInv t (by rw [hN]; omega)).region.nav).2.1 i hi2 hi6 h1 h2
    have hb : P.τv x - 1 ≤ P.q x t ∧ P.q x t < P.ar x 7 := by
      fin_cases i <;> simp at hi2 hi6 h1 h2 ⊢ <;> constructor <;> linarith
    exact phase_r P hx hInv t (by rw [hN]; omega) (by norm_num) rM hsp hb.1 hb.2
  · intro t ht h1 h2
    rw [qE_eq _ _ (by rw [hN]; omega)] at h1 h2
    rw [rE_eq _ _ (by rw [hN]; omega)]
    exact phase_r P hx hInv t (by rw [hN]; omega) (by norm_num) rE'
      ((P.pace_speed x hx t (inv1 P hInv t (by rw [hN]; omega)).region.nav).2.2 h1 h2) (by linarith) h2
  · intro t ht h1 h2
    rw [qE_eq _ _ (by rw [hN]; omega)] at h1 h2
    rw [sat_near]
    exact (dist_pos_le P.toIface w₀ (inv1 P hInv t (by rw [hN]; omega)).tube (wp 0)).trans
      (P.nom_win0 x hx t (pre_at P hInv t (by rw [hN]; omega)) h1 h2)
  · intro i hi t ht h1 h2
    rw [qE_eq _ _ (by rw [hN]; omega)] at h1 h2
    rw [sat_nearT]
    exact P.pace_win x hx i hi t (inv1 P hInv t (by rw [hN]; omega)).region.nav h1 h2

/-- The S-curve time loses less than one tick over the hold (the leak `c + ε_q` of `Pace`). -/
theorem q_leak {t₀ t : ℕ} (h : t₀ ≤ t) (hd : t ≤ t₀ + 1200) :
    qE P.toIface x t₀ - 1 ≤ qE P.toIface x t := by
  have Pc := pace_run P hx hInv
  have hcp := cPace
  have key : ∀ d, qE P.toIface x t₀ - d * (1 / 10 ^ 4 + 1 / 10 ^ 7) ≤ qE P.toIface x (t₀ + d) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 := abs_le.1 (Pc.prog (t₀ + d))
      have h2 := (Pc.sb (t₀ + d + 1)).1
      rw [show t₀ + (d + 1) = t₀ + d + 1 by omega]
      push_cast
      nlinarith
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have := key d
  have hd' : (d : ℝ) ≤ 1200 := by exact_mod_cast (by omega : d ≤ 1200)
  nlinarith

/-- **The hold**, by `Pacing.hold_course` (completion within the horizon) or `Pacing.hold_formula`. -/
theorem hold (hE : ClimbEscape sense32 senseP w₀) (hL : LibmSpec) :
    sat x 0 (.eventually 0 totalTicks (.always 0 holdTicks (nearT w7 (rPass w7)))) := by
  classical
  have hN : horizonTicks = 12000 := rfl
  obtain ⟨-, ht7⟩ := reach_chain P hx hInv hE
  by_cases hc : ∃ k, k ≤ 12000 ∧ complete w₀ x k
  · have hex : ∃ k, complete w₀ x k := ⟨_, hc.choose_spec.2⟩
    set tc := Nat.find hex
    have htc : complete w₀ x tc := Nat.find_spec hex
    have hfirst : ∀ k < tc, ¬ complete w₀ x k := fun k hk => Nat.find_min hex hk
    have htcN : tc ≤ horizonTicks := by
      have h1 := Nat.find_min' hex hc.choose_spec.2
      have h2 := hc.choose_spec.1
      rw [hN]; omega
    obtain ⟨p, s, hH, hpe, hve, hloit⟩ :=
      P.loiter_nav x hx tc (fun k hk => inv1 P hInv k (hk.trans htcN)) htc hfirst
    obtain ⟨cd, cv⟩ := P.nom_complete x hx tc (pre_at P hInv tc htcN) htc hfirst
    have I1 := inv1 P hInv tc htcN
    have hd : dist (pos (x tc)) w7 ≤ dist (posTarget (x tc) + nomE3 P.toIface w₀ x tc) w7 + τ3 :=
      dist_pos_le P.toIface w₀ I1.tube w7
    have hv : ‖vel (x tc)‖ ≤ ‖velTarget (x tc) + nomV3 P.toIface w₀ x tc‖ + τ3v := by
      rw [vel_eq P.toIface w₀ x tc, V3_eq, ← add_assoc]
      exact (norm_add_le _ _).trans (by linarith [η3v_le P.toIface w₀ I1.tube])
    have hn1 : ‖estVel s‖ ≤ ‖vel (x tc)‖ + 1 / 10 ^ 6 := by
      have := norm_sub_norm_le (estVel s) (vel (x tc))
      rw [← dist_eq_norm] at this
      linarith
    have hd1 : dist (estPos s) w7 ≤ dist (pos (x tc)) w7 + 1 / 10 ^ 6 := by
      linarith [dist_triangle (estPos s) (pos (x tc)) w7]
    exact Pacing.hold_course hL (pace_run P hx hInv) x ht7
      (fun t ht htc' h7 => by
        rw [qE_eq _ _ (by rw [hN]; omega)] at h7
        exact P.pace_end x hx t (inv1 P hInv t (by rw [hN]; omega)).region.nav (hfirst t htc') h7)
      p s (fun t ht htc' => hloit t htc' (fun k hk => inv1 P hInv k (by rw [hN]; omega)))
      hH.hkp hH.hacc hH.hvm hH.hkpd hH.haccd hH.hpox hH.hpoy hH.hpoz hH.hvox hH.hvoy hH.hvoz
      hH.hpx hH.hpy hH.hpz hH.hvx hH.hvy hH.hvz (by linarith) (by linarith)
  · push Not at hc
    obtain ⟨t7, ht7a, ht7b⟩ := ht7
    have e1 : totalTicks = 10800 := rfl
    have e2 : holdTicks = 1200 := rfl
    rw [e1, e2]
    refine Pacing.hold_formula x ht7a fun t h1 h2 => ?_
    rw [sat_nearT]
    have hq := q_leak P hx hInv h1 h2
    rw [qE_eq (t := t) _ _ (by rw [hN]; omega)] at hq
    exact P.pace_end x hx t (inv1 P hInv t (by rw [hN]; omega)).region.nav (hc t (by omega))
      (by linarith)

end Reach

/-! ## The guarantee -/

/-- **`ψtrack` from the invariant over the horizon.** -/
theorem ψtrack_of_inv (P : Pieces sense32 senseP w₀) (hS : Plant.CopterSense sense32 senseP)
    (hL : LibmSpec) {x : ℕ → Mission.X} (hx : Beh sense32 senseP w₀ x)
    (hInv : ∀ t ≤ horizonTicks, Inv P.toIface w₀ x t) (hE : ClimbEscape sense32 senseP w₀) :
    x ∈ lang_t 0 ψtrack := by
  rw [mem_lang_t, ψtrack]
  refine ⟨?_, (reach_chain P hx hInv hE).1, hold P hx hInv hE hL⟩
  rw [sat_always]
  intro τ _ hτ
  exact always_at P hS hx hInv τ (by simpa using hτ)

/-- **`track_contract` from the pieces.** -/
theorem track_contract_of_pieces (sense32 : ℝ → Float32) (senseP : ℝ → Float)
    (w₀ : Vehicle.World) (P : Pieces sense32 senseP w₀) (hM : MissionWorld w₀)
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec) (hE : ClimbEscape sense32 senseP w₀) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψtrack⟩ := by
  rintro x ⟨hloop, hA⟩
  have hx : Beh sense32 senseP w₀ x := ⟨hloop, hA⟩
  exact ψtrack_of_inv P hS hL hx (inv_all P hM hS hL hx) hE

end

end Contracts.Track.Induction
