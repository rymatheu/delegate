import Contracts.Track.Induction.Pieces
import Contracts.Track.Induction.PlantRow

/-!
# M9, part 4: the induction

* `world_all`: the world facts at every tick, from the finished M1 (`tick_actOK`), M2
  (`intOK_tick`, `intOK_takeover`) and Q5 (`mission_in_order`) — no induction hypothesis needed;
* `err_le`, `smpErr_le`: the tracking error from the nominal and the tubes;
* `inv_zero`: the takeoff assumption gives `Inv 0`;
* `inv_succ`: `Inv t → Inv (t + 1)` for `t + 1 ≤ horizonTicks`. The navigator's step (`nav_step`, needing the sampled error at
  `t`) comes first, so that the certified nominal may be read at `t + 1` (`Pre`); then the tubes at `t + 1` by `tube_out` from the
  per-tick disturbance bounds of all ticks `2 … t` (`wV_bound` from `vglue` and the C-series'
  `CtrlV.vertical_tick_split`; `wHβ_bound` from
  `ne_glue`, `plant_rows` and M6's `horizontal_tick_eq_D`; `attitude_tracks`) and the gains; then the boxes (`nom_box` plus the tubes); then the commands of
  tick `t` (from the box at `t + 1`), and the attitude, heading and code invariants;
* `inv_all`: `Inv t` for every `t` of the horizon (12000 ticks; the region includes `t ≤ 12000`,
  so no step piece is asked about ticks past the span of `ψtrack`).
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission Matrix Finset

noncomputable section

/-! ## Reading the tubes -/

section Read

variable (I : Iface) (w₀ : Vehicle.World)

theorem outV_dot (o : Fin 5) (v : Fin 8 → ℝ) :
    outV o ⬝ᵥ v = ![v 0, v 1, v 4, v 5, v 6] o := by
  fin_cases o <;> simp [outV, single_dotProduct]

theorem outH_dot (o : Fin 5) (v : Fin 9 → ℝ) :
    outH o ⬝ᵥ v = ![v 0, v 1, v 4, v 6, v 6 - v 7] o := by
  fin_cases o <;> simp [outH, single_dotProduct, sub_dotProduct]

/-- The 3D tube vector. -/
def η3 (x : ℕ → Mission.X) (t : ℕ) : P3 :=
  !₂[ηH I w₀ x t 0 0, ηH I w₀ x t 1 0, ηV I w₀ x t 0]

/-- The 3D velocity tube vector. -/
def η3v (x : ℕ → Mission.X) (t : ℕ) : P3 :=
  !₂[ηH I w₀ x t 0 1, ηH I w₀ x t 1 1, ηV I w₀ x t 1]

theorem E3_eq (x : ℕ → Mission.X) (t : ℕ) : E3 I w₀ x t = nomE3 I w₀ x t + η3 I w₀ x t := by
  ext i; fin_cases i <;> simp [E3, nomE3, η3, ηH, ηV]

theorem V3_eq (x : ℕ → Mission.X) (t : ℕ) : V3 I w₀ x t = nomV3 I w₀ x t + η3v I w₀ x t := by
  ext i; fin_cases i <;> simp [V3, nomV3, η3v, ηH, ηV]

/-- The vehicle is the target plus the 3D error. -/
theorem pos_eq (x : ℕ → Mission.X) (t : ℕ) : pos (x t) = posTarget (x t) + E3 I w₀ x t := by
  ext i; fin_cases i <;> simp [pos, E3, ξH_zero, ξV_zero, ph, pIx]

/-- The vehicle's velocity is the velocity target plus the 3D velocity error. -/
theorem vel_eq (x : ℕ → Mission.X) (t : ℕ) : vel (x t) = velTarget (x t) + V3 I w₀ x t := by
  ext i; fin_cases i <;> simp [vel, V3, ξH_one, ξV_one, ph, vIx]

theorem norm3_le {v : P3} {a b c : ℝ} (h0 : |v 0| ≤ a) (h1 : |v 1| ≤ a) (h2 : |v 2| ≤ b)
    (hc : 0 ≤ c) (h : 2 * a ^ 2 + b ^ 2 ≤ c ^ 2) : ‖v‖ ≤ c := by
  rw [norm_eq3, Real.sqrt_le_left]
  · have e0 := sq_le_sq' (abs_le.1 h0).1 (abs_le.1 h0).2
    have e1 := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
    have e2 := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
    nlinarith
  · exact hc

theorem η3_le {x : ℕ → Mission.X} {t : ℕ} (h : TubeOK I w₀ x t) : ‖η3 I w₀ x t‖ ≤ τ3 := by
  have a0 := h.h 0 0; have a1 := h.h 1 0; have b := h.v 0
  rw [outH_dot] at a0 a1; rw [outV_dot] at b
  exact norm3_le (by simpa [η3] using a0) (by simpa [η3] using a1) (by simpa [η3] using b)
    (by norm_num [τ3]) τ3_spec

theorem η3v_le {x : ℕ → Mission.X} {t : ℕ} (h : TubeOK I w₀ x t) : ‖η3v I w₀ x t‖ ≤ τ3v := by
  have a0 := h.h 0 1; have a1 := h.h 1 1; have b := h.v 1
  rw [outH_dot] at a0 a1; rw [outV_dot] at b
  exact norm3_le (by simpa [η3v] using a0) (by simpa [η3v] using a1) (by simpa [η3v] using b)
    (by norm_num [τ3v]) τ3v_spec

theorem err_eq (x : ℕ → Mission.X) (t : ℕ) : err (x t) = ‖E3 I w₀ x t‖ := by
  rw [err, pos_eq I w₀ x t, dist_eq_norm, add_sub_cancel_left]

/-- The error is at most the nominal error plus the tube. -/
theorem err_le_nom {x : ℕ → Mission.X} {t : ℕ} (h : TubeOK I w₀ x t) :
    err (x t) ≤ ‖nomE3 I w₀ x t‖ + τ3 := by
  rw [err_eq, E3_eq]
  exact (norm_add_le _ _).trans (by linarith [η3_le I w₀ h])

/-- Distance of the vehicle to a point, from the nominal and the tube. -/
theorem dist_pos_le {x : ℕ → Mission.X} {t : ℕ} (h : TubeOK I w₀ x t) (c : P3) :
    dist (pos (x t)) c ≤ dist (posTarget (x t) + nomE3 I w₀ x t) c + τ3 := by
  rw [pos_eq I w₀ x t, E3_eq, ← add_assoc]
  refine (dist_triangle _ (posTarget (x t) + nomE3 I w₀ x t) c).trans ?_
  rw [dist_eq_norm, add_sub_cancel_left, add_comm]
  linarith [η3_le I w₀ h]

end Read

variable {sense32 : ℝ → Float32} {senseP : ℝ → Float} {w₀ : Vehicle.World}

/-! ## The world facts -/

theorem world_all (P : Pieces sense32 senseP w₀) (hM : MissionWorld w₀) (hL : LibmSpec)
    {x : ℕ → Mission.X} (hx : x ∈ Mctrl w₀) (t : ℕ) : WorldOK w₀ x t := by
  have hact : ∀ t, ActOK (run w₀ x t).ms._actuator := by
    intro t
    induction t with
    | zero => exact actOK_takeover w₀ _ (actOK_missionWorld hM)
    | succ t ih => exact (tick_actOK _ _ ih).1
  have hint : ∀ t, IntOK (run w₀ x t) := by
    intro t
    induction t with
    | zero => exact intOK_takeover hL w₀ _ P.init_world
    | succ t ih => exact intOK_tick _ _ ih
  refine ⟨hact t, hint t, fun ht => ?_⟩
  obtain ⟨s, hs0, hs⟩ := mem_Mctrl.1 hx
  obtain ⟨w, hw, rfl⟩ := hM.built
  obtain ⟨h0, hz⟩ := Quick.mission_start_of_construct hw
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  obtain ⟨v, hv, hI⟩ := (Quick.mission_in_order _ h0 hz hs0 hs).1 t'
  rw [(hidden_run hs0 hs t').1, Option.some.injEq] at hv
  rw [hv]; exact hI


/-! ## Sensing -/

theorem smpPos_close (hS : Plant.CopterSense sense32 senseP) {x : ℕ → Mission.X}
    (hx : x ∈ Mplant sense32 senseP) (t : ℕ) (hb : ∀ i : Fin 3, |pos (x t) i| ≤ 100) :
    dist (smpPos (x t)) (pos (x t)) ≤ 3 / 10 ^ 9 := by
  have hs := (mem_Mplant.1 hx t).2
  refine (dist_le_sum_abs _ _).trans ?_
  have e0 := senseP_close hS (hb 0); have e1 := senseP_close hS (hb 1)
  have e2 := senseP_close hS (hb 2)
  simp only [smpPos, pos, hs] at e0 e1 e2 ⊢
  simp only [toVSample, Plant.sample, Plant.State.ofX] at e0 e1 e2 ⊢
  simp at e0 e1 e2 ⊢
  linarith

theorem smpVel_close (hS : Plant.CopterSense sense32 senseP) {x : ℕ → Mission.X}
    (hx : x ∈ Mplant sense32 senseP) (t : ℕ) (hb : ∀ i : Fin 3, |vel (x t) i| ≤ 100) :
    dist (smpVel (x t)) (vel (x t)) ≤ 3 / 10 ^ 5 := by
  have hs := (mem_Mplant.1 hx t).2
  refine (dist_le_sum_abs _ _).trans ?_
  have e0 := sense32_close hS (hb 0); have e1 := sense32_close hS (hb 1)
  have e2 := sense32_close hS (hb 2)
  simp only [smpVel, vel, hs] at e0 e1 e2 ⊢
  simp only [toVSample, Plant.sample, Plant.State.ofX] at e0 e1 e2 ⊢
  simp at e0 e1 e2 ⊢
  linarith

/-! ## Tracking at a tick -/

theorem pre_of_inv {I : Iface} {x : ℕ → Mission.X} {t : ℕ} (h : Inv I w₀ x t) : Pre I w₀ x t :=
  ⟨fun k hk => h k hk.le, (h t le_rfl).region.nav⟩

theorem err_le (P : Pieces sense32 senseP w₀) {x : ℕ → Mission.X}
    (hx : Beh sense32 senseP w₀ x) {t : ℕ} (h : Inv P.toIface w₀ x t) : err (x t) ≤ δ :=
  (err_le_nom P.toIface w₀ (h t le_rfl).tube).trans (P.nom_T1 x hx t (pre_of_inv h))

theorem pos_bound (P : Pieces sense32 senseP w₀) {x : ℕ → Mission.X}
    (hx : Beh sense32 senseP w₀ x) {t : ℕ} (h : Inv P.toIface w₀ x t) (i : Fin 3) :
    |pos (x t) i| ≤ 3 + δ := by
  have he := err_le P hx h
  rw [err_eq] at he
  have hc : |E3 P.toIface w₀ x t i| ≤ ‖E3 P.toIface w₀ x t‖ := by
    simpa using abs_coord_le_dist (E3 P.toIface w₀ x t) 0 i
  have hT := (P.nav_bounds x hx t (h t le_rfl).region.nav i).1
  rw [pos_eq P.toIface w₀ x t, PiLp.add_apply]
  linarith [abs_add_le (posTarget (x t) i) (E3 P.toIface w₀ x t i)]

theorem vel_bound_of (P : Pieces sense32 senseP w₀) {x : ℕ → Mission.X}
    (hx : Beh sense32 senseP w₀ x) {t : ℕ} (R : Region P.toIface w₀ x t) (i : Fin 3) :
    |vel (x t) i| ≤ 2 := by
  have hT := (P.nav_bounds x hx t R.nav i).2
  rw [vel_eq P.toIface w₀ x t, PiLp.add_apply]
  have hV : |V3 P.toIface w₀ x t i| ≤ 1 / 2 := by
    fin_cases i
    · have := R.boxH 0 1; rw [outH_dot] at this; simpa [V3, bH] using this
    · have := R.boxH 1 1; rw [outH_dot] at this; simpa [V3, bH] using this
    · have := R.boxV 1; rw [outV_dot] at this; simpa [V3, bV] using this
  linarith [abs_add_le (velTarget (x t) i) (V3 P.toIface w₀ x t i)]

theorem smpErr_le (P : Pieces sense32 senseP w₀) (hS : Plant.CopterSense sense32 senseP)
    {x : ℕ → Mission.X} (hx : Beh sense32 senseP w₀ x) {t : ℕ} (h : Inv P.toIface w₀ x t) :
    smpErr (x t) ≤ δs := by
  have hc := smpPos_close hS hx.1.1 t fun i => (pos_bound P hx h i).trans (by norm_num [δ])
  have he := err_le P hx h
  rw [smpErr]
  refine (dist_triangle _ (pos (x t)) _).trans ?_
  rw [err] at he
  norm_num [δ, δs] at he ⊢
  linarith

/-! ## The base case -/

/-- **Base case**: from the takeoff assumption, the invariant holds at tick 0. -/
theorem inv_zero (P : Pieces sense32 senseP w₀) (hM : MissionWorld w₀) (hL : LibmSpec)
    {x : ℕ → Mission.X} (hx : Beh sense32 senseP w₀ x) : Inv P.toIface w₀ x 0 := by
  intro k hk
  obtain rfl : k = 0 := by omega
  obtain ⟨ha, hy, hn, hc⟩ := P.init x hx
  have hpre : Pre P.toIface w₀ x 0 := ⟨fun k hk => absurd hk (Nat.not_lt_zero _), hn⟩
  have hT := (P.init_tube x hx).1 0 (by norm_num)
  obtain ⟨nV, nH⟩ := P.nom_box x hx 0 hpre
  refine ⟨⟨Nat.zero_le _, world_all P hM hL hx.1.2 0, fun o => ?_, fun a o => ?_, ha, hy, hn, hc⟩, hT⟩
  · have e : ξv P.toIface w₀ x 0 = nomV P.toIface w₀ x 0 + ηV P.toIface w₀ x 0 := by
      simp [ηV]
    rw [e, dotProduct_add]
    linarith [abs_add_le (outV o ⬝ᵥ nomV P.toIface w₀ x 0) (outV o ⬝ᵥ ηV P.toIface w₀ x 0),
      nV o, hT.v o]
  · have e : ξH w₀ x 0 a = nomH P.toIface w₀ x a 0 + ηH P.toIface w₀ x 0 a := by
      simp [ηH]
    rw [e, dotProduct_add]
    linarith [abs_add_le (outH o ⬝ᵥ nomH P.toIface w₀ x a 0) (outH o ⬝ᵥ ηH P.toIface w₀ x 0 a),
      nH a o, hT.h a o]

/-! ## The step -/

/-- The tubes at `t + 1`, from the disturbance bounds of the ticks `2 … t`. -/
theorem tube_succ (P : Pieces sense32 senseP w₀) (hS : Plant.CopterSense sense32 senseP)
    (hL : LibmSpec) {x : ℕ → Mission.X} (hx : Beh sense32 senseP w₀ x) {t : ℕ} (h : Inv P.toIface w₀ x t) :
    TubeOK P.toIface w₀ x (t + 1) := by
  by_cases ht : t + 1 ≤ 2
  · exact (P.init_tube x hx).1 (t + 1) ht
  obtain ⟨-, h0V, h0H⟩ := P.init_tube x hx
  obtain ⟨N, hN⟩ : ∃ N, t + 1 = 2 + N := ⟨t - 1, by omega⟩
  rw [hN]
  refine ⟨fun o => ?_, fun a o => ?_⟩
  · refine (tube_out Vertical.AvR (ηV P.toIface w₀ x) (wV P.toIface w₀ x) 2 N
      (fun s _ => ηV_succ P.toIface w₀ x s) (outV o) ε0V εV (PV o) (GV o) εV_nonneg h0V
      (fun k hk j => by
        have hR := (h (2 + k) (by omega)).region
        have hv := vel_bound_of P hx hR 2
        have hp := pos_bound P hx (t := 2 + k) (fun i hi => h i (by omega)) 2
        simp [vel, pos, δ] at hv hp; norm_num at hp
        exact wV_bound hL hL.pi32 hS hx.1 (2 + k) hR.world.act
          (P.vglue x hx (2 + k) (by omega) hR) (by simp [ph]; linarith) (by simpa [ph] using hv)
          P.toIface (P.wVs_def x (2 + k)) j)
      (P.peakV o) (P.gainV o)).trans (τV_spec o)
  · refine (tube_out Horizontal.AhR (fun s => ηH P.toIface w₀ x s a) (fun s => wH P.toIface w₀ x s a)
      2 N (fun s _ => ηH_succ P.toIface w₀ x s a) (outH o) ε0H εH (PH o) (GH o) εH_nonneg (h0H a)
      (fun k hk j => ?_) (P.peakH o) (P.gainH o)).trans (τH_spec o)
    have hR := (h (2 + k) (by omega)).region
    have hv : ∀ b : Fin 2, |ph x (2 + k) (vIx b.castSucc)| ≤ 2 := fun b => by
      have := vel_bound_of P hx hR b.castSucc
      fin_cases b <;> simpa [vel, ph, vIx] using this
    have hp : ∀ b : Fin 2, |ph x (2 + k) (pIx b.castSucc)| ≤ 4 := fun b => by
      have := pos_bound P hx (t := 2 + k) (fun i hi => h i (by omega)) b.castSucc
      fin_cases b <;> simp [pos, ph, pIx, δ] at this ⊢ <;> norm_num at this <;> linarith
    have hb := wHβ_bound hL hS hx.1.1 (2 + k) (P.ne_glue x hx (2 + k) (by omega) hR)
      (prow_le hx.1.1 hx.2 (2 + k) (P.att_rates x hx (2 + k) hR.att)) hv hp a j
    have he := P.attitude_tracks x hx (2 + k) (by omega) hR a
    have hs := εH_spec j
    simp only [wH, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    nlinarith [abs_nonneg (eAcc j), abs_nonneg (etaA w₀ x (2 + k) a - P.etaHat x (2 + k) a)]

theorem cmdAgo_succ_one (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) :
    cmdAgo w₀ x (t + 1) 1 a = cmd w₀ x t a := by
  simp [cmdAgo]

theorem cmdAgo_succ_two (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) :
    cmdAgo w₀ x (t + 1) 2 a = cmdAgo w₀ x t 1 a := by
  unfold cmdAgo
  by_cases h : 1 ≤ t
  · simp only [show 2 ≤ t + 1 by omega, h, ite_true]; congr 1
  · simp only [show ¬ 2 ≤ t + 1 by omega, h, ite_false]

theorem cmdOK_of_box {x : ℕ → Mission.X} {t : ℕ} (h : BoxH w₀ x (t + 1)) : CmdOK w₀ x t := by
  intro a
  have h3 := h a 3; have h4 := h a 4
  rw [outH_dot] at h3 h4
  simp only [ξH, Horizontal.errOf, habs, Matrix.cons_val] at h3 h4
  simp [bH, cmdAgo_succ_one, cmdAgo_succ_two] at h3 h4
  exact ⟨by linarith, by linarith⟩

/-- **The step**: `Inv t → Inv (t + 1)`. -/
theorem inv_succ (P : Pieces sense32 senseP w₀) (hM : MissionWorld w₀)
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec) {x : ℕ → Mission.X}
    (hx : Beh sense32 senseP w₀ x) {t : ℕ} (h : Inv P.toIface w₀ x t) (ht : t + 1 ≤ horizonTicks) :
    Inv P.toIface w₀ x (t + 1) := by
  intro k hk
  rcases Nat.lt_or_ge k (t + 1) with hk' | hk'
  · exact h k (by omega)
  obtain rfl : k = t + 1 := by omega
  have R := (h t le_rfl).region
  -- the navigator
  have hnav := P.nav_step x hx t R (smpErr_le P hS hx h)
  have hpre : Pre P.toIface w₀ x (t + 1) := ⟨fun k hk => h k (by omega), hnav⟩
  -- the tubes and the boxes
  have hT := tube_succ P hS hL hx h
  obtain ⟨nV, nH⟩ := P.nom_box x hx (t + 1) hpre
  have hbV : BoxV P.toIface w₀ x (t + 1) := by
    intro o
    have e : ξv P.toIface w₀ x (t + 1) = nomV P.toIface w₀ x (t + 1) + ηV P.toIface w₀ x (t + 1) := by
      simp [ηV]
    rw [e, dotProduct_add]
    linarith [abs_add_le (outV o ⬝ᵥ nomV P.toIface w₀ x (t + 1))
      (outV o ⬝ᵥ ηV P.toIface w₀ x (t + 1)), nV o, hT.v o]
  have hbH : BoxH w₀ x (t + 1) := by
    intro a o
    have e : ξH w₀ x (t + 1) a = nomH P.toIface w₀ x a (t + 1) + ηH P.toIface w₀ x (t + 1) a := by
      simp [ηH]
    rw [e, dotProduct_add]
    linarith [abs_add_le (outH o ⬝ᵥ nomH P.toIface w₀ x a (t + 1))
      (outH o ⬝ᵥ ηH P.toIface w₀ x (t + 1) a), nH a o, hT.h a o]
  -- the subsystem invariants
  exact ⟨⟨ht, world_all P hM hL hx.1.2 (t + 1), hbV, hbH,
    P.att_step x hx t R (cmdOK_of_box hbH), P.yaw_step x hx t R, hnav, P.ctrl_step x hx t R⟩, hT⟩

/-- **The induction**: the invariant at every tick of the horizon. -/
theorem inv_all (P : Pieces sense32 senseP w₀) (hM : MissionWorld w₀)
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec) {x : ℕ → Mission.X}
    (hx : Beh sense32 senseP w₀ x) : ∀ t ≤ horizonTicks, Inv P.toIface w₀ x t := by
  intro t
  induction t with
  | zero => exact fun _ => inv_zero P hM hL hx
  | succ t ih => exact fun ht => inv_succ P hM hS hL hx (ih (by omega)) ht

end

end Contracts.Track.Induction
