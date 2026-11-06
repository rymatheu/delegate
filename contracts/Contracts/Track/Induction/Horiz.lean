import Contracts.Track.Induction.Inv
import Contracts.Track.CtrlHorizontalTick

/-!
# M9: the horizontal tick from M6's `horizontal_tick_eq_D`

`NEGlue w₀ x t` is what the tick glue (C15) has to establish at tick `t`: inside `Vehicle.tick`
of `run w₀ x t`, the position controller runs `NE_update_controller p s inp` on its region
(`HCtl.NERegion`), then `D_update_controller` with the vertical controller active, and the values
it reads and writes are the readouts of `Run.lean` (the sampled position and velocity, the targets,
the PID states of `habs`, the command `cmd`).

`wHβ_bound` derives the per-tick bound of `wHβ` (the field `horizontal_tick_eq` of the earlier
form) from `NEGlue`, the plant's position row and the `float` sensing, with M6's finished
`HCtl.horizontal_tick_eq_D`. The attitude interface of that theorem (`a' = a + αL (c₃ - a) + η`) is
used with `η = 0`: here `a` is the exact lag law `aLag`, and the realized deviation `etaA` enters the
plant rows (`ρp`, `ρv`), as HORIZONTAL.md §7 states it.
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission Matrix Finset AC_PosControl_lib AC_PosControl

noncomputable section

/-! ## Sensing -/

section Sense

variable {sense32 : ℝ → Float32} {senseP : ℝ → Float}

theorem senseP_close (hS : Plant.CopterSense sense32 senseP) {r : ℝ} (hr : |r| ≤ 100) :
    |(senseP r).toReal - r| ≤ 1 / 10 ^ 9 := by
  obtain ⟨-, he⟩ := hS.pos.err r (hr.trans (by norm_num))
  refine he.trans ?_
  have h53 : (2 : ℝ) ^ (-53 : ℤ) ≤ 1 / 10 ^ 13 := by norm_num
  have h75 : (2 : ℝ) ^ (-1075 : ℤ) ≤ 1 / 10 ^ 10 :=
    (zpow_le_zpow_right₀ one_le_two (by norm_num : (-1075 : ℤ) ≤ -40)).trans (by norm_num)
  nlinarith [abs_nonneg r, mul_le_mul h53 hr (abs_nonneg r) (by norm_num)]

theorem sense32_close (hS : Plant.CopterSense sense32 senseP) {r : ℝ} (hr : |r| ≤ 100) :
    |(sense32 r).toReal - r| ≤ 1 / 10 ^ 5 := by
  obtain ⟨-, he⟩ := hS.f32.err r hr
  refine he.trans ?_
  have h24 : (2 : ℝ) ^ (-24 : ℤ) ≤ 1 / 10 ^ 7 := by norm_num
  have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 10 ^ 10 :=
    (zpow_le_zpow_right₀ one_le_two (by norm_num : (-150 : ℤ) ≤ -40)).trans (by norm_num)
  nlinarith [abs_nonneg r, mul_le_mul h24 hr (abs_nonneg r) (by norm_num)]

theorem sense32_close3 (hS : Plant.CopterSense sense32 senseP) {r : ℝ} (hr : |r| ≤ 3) :
    |(sense32 r).toReal - r| ≤ 2 / 10 ^ 7 := by
  obtain ⟨-, he⟩ := hS.f32.err r (hr.trans (by norm_num))
  refine he.trans ?_
  have h24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 10 ^ 10 :=
    (zpow_le_zpow_right₀ one_le_two (by norm_num : (-150 : ℤ) ≤ -40)).trans (by norm_num)
  rw [h24]
  nlinarith [abs_nonneg r]

/-- The sampled horizontal position and velocity are the ports of the plant state. -/
theorem smp_ne {x : ℕ → Mission.X} (hx : x ∈ Mplant sense32 senseP) (t : ℕ) :
    smpPos (x t) 0 = (senseP ((x t).phys.x 0)).toReal ∧
    smpPos (x t) 1 = (senseP ((x t).phys.x 1)).toReal ∧
    smpVel (x t) 0 = (sense32 ((x t).phys.x 3)).toReal ∧
    smpVel (x t) 1 = (sense32 ((x t).phys.x 4)).toReal := by
  have hs := (mem_Mplant.1 hx t).2
  simp only [smpPos, smpVel, hs]
  simp [toVSample, Plant.sample, Plant.State.ofX]

end Sense

/-- **The horizontal tick glue at tick `t`** (C15): the call of `NE_update_controller`, its
region, the active vertical controller after it, and the readouts. -/
def NEGlue (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : Prop :=
  ∃ (p : Params) (s : State) (inp : Inputs) (pD : Params) (o : Outputs) (inpD : Inputs),
    HCtl.NERegion p s inp ∧
    D_is_active (D_handle_ekf_reset (NE_update_controller p s inp) inpD) inpD = true ∧
    HCtl.axisX s = ⟨posTarget (x t) 0, smpPos (x t) 0, velTarget (x t) 0, smpVel (x t) 0,
      (habs w₀ x t 0).E, (habs w₀ x t 0).D, (habs w₀ x t 0).I, accDes w₀ x t 0⟩ ∧
    HCtl.axisY s = ⟨posTarget (x t) 1, smpPos (x t) 1, velTarget (x t) 1, smpVel (x t) 1,
      (habs w₀ x t 1).E, (habs w₀ x t 1).D, (habs w₀ x t 1).I, accDes w₀ x t 1⟩ ∧
    (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1._pid_vel_ne_m._error.x.toReal =
      (habs w₀ x (t + 1) 0).E ∧
    (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1._pid_vel_ne_m._derivative.x.toReal =
      (habs w₀ x (t + 1) 0).D ∧
    (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1._pid_vel_ne_m._integrator.x.toReal =
      (habs w₀ x (t + 1) 0).I ∧
    (get_thrust_vector (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1).x.toReal =
      cmd w₀ x t 0 ∧
    (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1._pid_vel_ne_m._error.y.toReal =
      (habs w₀ x (t + 1) 1).E ∧
    (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1._pid_vel_ne_m._derivative.y.toReal =
      (habs w₀ x (t + 1) 1).D ∧
    (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1._pid_vel_ne_m._integrator.y.toReal =
      (habs w₀ x (t + 1) 1).I ∧
    (get_thrust_vector (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1).y.toReal =
      cmd w₀ x t 1

/-- The plant's position row over one period, against the realized mean acceleration (P4,
`Plant/Sharp.lean`): `p' = p + h v + h²/2 aReal + ρ`. -/
def prow (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) : ℝ :=
  ph x (t + 1) (pIx a.castSucc) - ph x t (pIx a.castSucc) - Plant.h * ph x t (vIx a.castSucc) -
    Plant.h ^ 2 / 2 * aReal x t a

/-! ## The algebra of one axis -/

/-- `A_h` applied to a vector supported on the first two coordinates. -/
theorem AhR_mulVec_two (d0 d1 : ℝ) (j : Fin 9) :
    (Horizontal.AhR *ᵥ ![d0, d1, 0, 0, 0, 0, 0, 0, 0]) j =
      Horizontal.AhR j 0 * d0 + Horizontal.AhR j 1 * d1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_succ]

/-- The first two columns of `A_h`, bounded. -/
theorem AhR_col (j : Fin 9) :
    |Horizontal.AhR j 0| ≤ ![1, 0, 11 / 100, 32 / 10, 3 / 10000, 0, 225 / 100, 0, 0] j ∧
      |Horizontal.AhR j 1| ≤ ![1 / 400, 1, 74 / 1000, 213 / 100, 2 / 10000, 0, 150 / 100, 0, 0] j := by
  fin_cases j <;>
    simp [Horizontal.AhR, Horizontal.Ah, Horizontal.rowEp, Horizontal.rowEv, Horizontal.rowE,
      Horizontal.rowD, Horizontal.rowI, Horizontal.rowC, Horizontal.rowA, Horizontal.αE,
      Horizontal.kpPos, Horizontal.dtf, Horizontal.ki, Horizontal.kp, Horizontal.kd,
      Horizontal.per] <;>
    norm_num [abs_le]

set_option maxHeartbeats 1000000 in
/-- **One axis, one tick, in this file's coordinates.** M6's form `xiNext = A_h xiOf + forcing + w`
(with the attitude deviation in the plant rows, `η = 0`) gives the deviation of the code's tick
from `A_h ξ + forcing + (aR − a) eAcc` in the plant coordinates: row 0 is the plant's position
row, row 1 is `0`, rows 2, 3, 4, 6 are `w` plus the sensing difference through `A_h`. -/
theorem axis_dev (A : HCtl.AxisIn) (aN aN' c₁ c₂ c₃ pNN vNN spNN vspNN : ℝ)
    (E' D' I' acc : Float32) (w : Fin 9 → ℝ) (P V P' V' aR : ℝ)
    (hE : HCtl.xiNext pNN vNN spNN vspNN E' D' I' acc aN' c₁ c₂ =
      Horizontal.AhR *ᵥ HCtl.xiOf A aN c₁ c₂ c₃ + (A.asp • Horizontal.BhR -
        Horizontal.defect₁ A.sp spNN A.vsp A.asp • Horizontal.e0 -
        Horizontal.defect₂ A.vsp vspNN A.asp • Horizontal.e1) + w)
    (hW : HCtl.WBound (pNN - (A.p + (Horizontal.per : ℝ) * A.v + (Horizontal.per : ℝ) ^ 2 / 2 * aN))
      (vNN - (A.v + (Horizontal.per : ℝ) * aN)) 0 w)
    (hd0 : |A.p - P| ≤ 1 / 10 ^ 9) (hd1 : |A.v - V| ≤ 2 / 10 ^ 7)
    (hrow : |P' - P - Plant.h * V - Plant.h ^ 2 / 2 * aR| ≤ 18 / 10 ^ 8)
    (haR : aR = (V' - V) / Plant.h) (j : Fin 9) :
    |Horizontal.errOf ⟨P', V', E'.toReal, D'.toReal, I'.toReal, aN', acc.toReal, c₁, c₂⟩ spNN vspNN j -
      ((Horizontal.AhR *ᵥ Horizontal.errOf ⟨P, V, A.E, A.D, A.I, aN, c₁, c₂, c₃⟩ A.sp A.vsp) j +
        (A.asp • Horizontal.BhR - Horizontal.defect₁ A.sp spNN A.vsp A.asp • Horizontal.e0 -
          Horizontal.defect₂ A.vsp vspNN A.asp • Horizontal.e1) j + (aR - aN) * eAcc j)| ≤ εHβ j := by
  have hper : (Horizontal.per : ℝ) = Plant.h := Horizontal.per_eq
  have hh : Plant.h = 1 / 400 := rfl
  -- the vector identity
  set F := A.asp • Horizontal.BhR - Horizontal.defect₁ A.sp spNN A.vsp A.asp • Horizontal.e0 -
    Horizontal.defect₂ A.vsp vspNN A.asp • Horizontal.e1
  set ξ := Horizontal.errOf ⟨P, V, A.E, A.D, A.I, aN, c₁, c₂, c₃⟩ A.sp A.vsp
  set ξ' := Horizontal.errOf ⟨P', V', E'.toReal, D'.toReal, I'.toReal, aN', acc.toReal, c₁, c₂⟩ spNN vspNN
  have hΔ : HCtl.xiOf A aN c₁ c₂ c₃ - ξ = ![A.p - P, A.v - V, 0, 0, 0, 0, 0, 0, 0] := by
    ext k; fin_cases k <;> simp [HCtl.xiOf, ξ, Horizontal.errOf]
  have hΔ' : ξ' - HCtl.xiNext pNN vNN spNN vspNN E' D' I' acc aN' c₁ c₂ =
      ![P' - pNN, V' - vNN, 0, 0, 0, 0, 0, 0, 0] := by
    ext k; fin_cases k <;> simp [HCtl.xiNext, ξ', Horizontal.errOf]
  have key : ξ' j - ((Horizontal.AhR *ᵥ ξ) j + F j + (aR - aN) * eAcc j) =
      w j + (Horizontal.AhR j 0 * (A.p - P) + Horizontal.AhR j 1 * (A.v - V)) +
        ![P' - pNN, V' - vNN, 0, 0, 0, 0, 0, 0, 0] j - (aR - aN) * eAcc j := by
    rw [← AhR_mulVec_two, ← hΔ, ← hΔ', mulVec_sub]
    have := congrFun hE j
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    linarith
  rw [key]
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8⟩ := hW
  by_cases hj : 2 ≤ j.val
  · -- rows 2 … 8: `w` plus the sensing difference
    obtain ⟨c0, c1⟩ := AhR_col j
    have p0 := mul_le_mul c0 hd0 (abs_nonneg _) ((abs_nonneg _).trans c0)
    have p1 := mul_le_mul c1 hd1 (abs_nonneg _) ((abs_nonneg _).trans c1)
    rw [← abs_mul] at p0 p1
    have hb := (abs_add_le (w j) _).trans (add_le_add le_rfl ((abs_add_le _ _).trans (add_le_add p0 p1)))
    fin_cases j
    all_goals first | exact absurd hj (by decide) | skip
    all_goals
      norm_num [eAcc, εHβ] at hb w2 w3 w4 w5 w6 w7 w8 ⊢
    all_goals first
      | linarith
      | (rw [w5] at hb; norm_num at hb ⊢; linarith)
      | (rw [w7] at hb; norm_num at hb ⊢; linarith)
      | (rw [w8] at hb; norm_num at hb ⊢; linarith)
  · have hj' : j = 0 ∨ j = 1 := by
      rcases j with ⟨_ | _ | k, hk⟩
      · left; rfl
      · right; rfl
      · simp at hj
    rcases hj' with rfl | rfl
    · -- the position row
      have e00 : Horizontal.AhR 0 0 = 1 := by simp [Horizontal.AhR, Horizontal.Ah, Horizontal.rowEp]
      have e01 : Horizontal.AhR 0 1 = Plant.h := by
        simp [Horizontal.AhR, Horizontal.Ah, Horizontal.rowEp, ← hper]
      rw [w0, e00, e01, hper]
      simp only [eAcc, εHβ, Matrix.cons_val_zero]
      have : pNN - (A.p + Plant.h * A.v + Plant.h ^ 2 / 2 * aN) + (1 * (A.p - P) + Plant.h * (A.v - V)) +
          (P' - pNN) - (aR - aN) * (Plant.h ^ 2 / 2) = P' - P - Plant.h * V - Plant.h ^ 2 / 2 * aR := by
        ring
      rw [this]; refine hrow.trans (by norm_num)
    · -- the velocity row
      have e10 : Horizontal.AhR 1 0 = 0 := by simp [Horizontal.AhR, Horizontal.Ah, Horizontal.rowEv]
      have e11 : Horizontal.AhR 1 1 = 1 := by simp [Horizontal.AhR, Horizontal.Ah, Horizontal.rowEv]
      rw [w1, e10, e11, hper, haR]
      simp only [eAcc, εHβ, Matrix.cons_val_one, Matrix.cons_val_zero]
      have : vNN - (A.v + Plant.h * aN) + (0 * (A.p - P) + 1 * (A.v - V)) + (V' - vNN) -
          ((V' - V) / Plant.h - aN) * Plant.h = 0 := by rw [hh]; field_simp; ring
      rw [this]; simp

/-- **The horizontal disturbance of one tick**, from the glue, the plant's position row and the
sensing, by M6's `HCtl.horizontal_tick_eq_D` and `axis_dev`. -/
theorem wHβ_bound {sense32 : ℝ → Float32} {senseP : ℝ → Float} {w₀ : Vehicle.World}
    (hL : LibmSpec) (hS : Plant.CopterSense sense32 senseP) {x : ℕ → Mission.X}
    (hx : x ∈ Mplant sense32 senseP) (t : ℕ) (hg : NEGlue w₀ x t)
    (hrow : ∀ a, |prow x t a| ≤ 18 / 10 ^ 8)
    (hv : ∀ a : Fin 2, |ph x t (vIx a.castSucc)| ≤ 2) (hp : ∀ a : Fin 2, |ph x t (pIx a.castSucc)| ≤ 4) :
    ∀ a j, |wHβ w₀ x t a j| ≤ εHβ j := by
  obtain ⟨p, s, inp, pD, o, inpD, R, hact, hX, hY, eEx, eDx, eIx, eTx, eEy, eDy, eIy, eTy⟩ := hg
  obtain ⟨sp0, sp1, sv0, sv1⟩ := smp_ne hx t
  have d0x : |(HCtl.axisX s).p - ph x t 0| ≤ 1 / 10 ^ 9 := by
    rw [hX]; simp only; rw [sp0]; exact senseP_close hS ((hp 0).trans (by norm_num))
  have d0y : |(HCtl.axisY s).p - ph x t 1| ≤ 1 / 10 ^ 9 := by
    rw [hY]; simp only; rw [sp1]; exact senseP_close hS ((hp 1).trans (by norm_num))
  have d1x : |(HCtl.axisX s).v - ph x t 3| ≤ 2 / 10 ^ 7 := by
    rw [hX]; simp only; rw [sv0]; exact sense32_close3 hS ((hv 0).trans (by norm_num))
  have d1y : |(HCtl.axisY s).v - ph x t 4| ≤ 2 / 10 ^ 7 := by
    rw [hY]; simp only; rw [sv1]; exact sense32_close3 hS ((hv 1).trans (by norm_num))
  obtain ⟨⟨wN, hEN, hWN⟩, ⟨wE, hEE, hWE⟩, -⟩ := HCtl.horizontal_tick_eq_D hL p s inp R pD o inpD hact
    (aLag w₀ x 0 t) (aLag w₀ x 0 (t + 1)) (cmdAgo w₀ x t 1 0) (cmdAgo w₀ x t 2 0) (cmdAgo w₀ x t 3 0) 0
    (smpPos (x (t + 1)) 0) (smpVel (x (t + 1)) 0) (posTarget (x (t + 1)) 0) (velTarget (x (t + 1)) 0)
    (smpPos (x (t + 1)) 0 - ((HCtl.axisX s).p + (Horizontal.per : ℝ) * (HCtl.axisX s).v +
      (Horizontal.per : ℝ) ^ 2 / 2 * aLag w₀ x 0 t))
    (smpVel (x (t + 1)) 0 - ((HCtl.axisX s).v + (Horizontal.per : ℝ) * aLag w₀ x 0 t))
    (aLag w₀ x 1 t) (aLag w₀ x 1 (t + 1)) (cmdAgo w₀ x t 1 1) (cmdAgo w₀ x t 2 1) (cmdAgo w₀ x t 3 1) 0
    (smpPos (x (t + 1)) 1) (smpVel (x (t + 1)) 1) (posTarget (x (t + 1)) 1) (velTarget (x (t + 1)) 1)
    (smpPos (x (t + 1)) 1 - ((HCtl.axisY s).p + (Horizontal.per : ℝ) * (HCtl.axisY s).v +
      (Horizontal.per : ℝ) ^ 2 / 2 * aLag w₀ x 1 t))
    (smpVel (x (t + 1)) 1 - ((HCtl.axisY s).v + (Horizontal.per : ℝ) * aLag w₀ x 1 t))
    (by ring) (by ring) (by simp [aLag]) (by ring) (by ring) (by simp [aLag])
  intro a j
  have hc1 : ∀ b : Fin 2, cmdAgo w₀ x (t + 1) 1 b = cmd w₀ x t b := by intro b; simp [cmdAgo]
  have hcs : ∀ (b : Fin 2) d, cmdAgo w₀ x (t + 1) (d + 1) b = cmdAgo w₀ x t d b := by
    intro b d; unfold cmdAgo
    by_cases h : d ≤ t
    · rw [if_pos (by omega), if_pos h]; congr 1; omega
    · rw [if_neg (by omega), if_neg h]
  fin_cases a
  · show |wHβ w₀ x t 0 j| ≤ εHβ j
    set s'' := (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1
    have hA : ξH w₀ x t 0 = Horizontal.errOf ⟨ph x t 0, ph x t 3, (HCtl.axisX s).E, (HCtl.axisX s).D,
        (HCtl.axisX s).I, aLag w₀ x 0 t, cmdAgo w₀ x t 1 0, cmdAgo w₀ x t 2 0, cmdAgo w₀ x t 3 0⟩
        (HCtl.axisX s).sp (HCtl.axisX s).vsp := by
      rw [hX]; ext k; fin_cases k <;> simp [ξH, habs, Horizontal.errOf, refH, refAx, pIx, vIx, ph]
    have hA' : ξH w₀ x (t + 1) 0 = Horizontal.errOf ⟨ph x (t + 1) 0, ph x (t + 1) 3,
        s''._pid_vel_ne_m._error.x.toReal, s''._pid_vel_ne_m._derivative.x.toReal,
        s''._pid_vel_ne_m._integrator.x.toReal, aLag w₀ x 0 (t + 1), (get_thrust_vector s'').x.toReal,
        cmdAgo w₀ x t 1 0, cmdAgo w₀ x t 2 0⟩ (posTarget (x (t + 1)) 0) (velTarget (x (t + 1)) 0) := by
      rw [eEx, eDx, eIx, eTx, ← hc1, ← hcs 0 1, ← hcs 0 2]
      ext k; fin_cases k <;> simp [ξH, habs, Horizontal.errOf, refH, refAx, pIx, vIx, ph]
    have hF : Horizontal.forceOf (refH w₀ x 0) t = (HCtl.axisX s).asp • Horizontal.BhR -
        Horizontal.defect₁ (HCtl.axisX s).sp (posTarget (x (t + 1)) 0) (HCtl.axisX s).vsp
          (HCtl.axisX s).asp • Horizontal.e0 -
        Horizontal.defect₂ (HCtl.axisX s).vsp (velTarget (x (t + 1)) 0) (HCtl.axisX s).asp •
          Horizontal.e1 := by
      rw [hX]; simp [Horizontal.forceOf, refH, refAx]
    have key := axis_dev (HCtl.axisX s) _ _ _ _ _ _ _ _ _ _ _ _ _ wN (ph x t 0) (ph x t 3)
      (ph x (t + 1) 0) (ph x (t + 1) 3) (aReal x t 0) hEN hWN d0x d1x
      (by simpa [prow, pIx, vIx] using hrow 0) (by simp [aReal, vIx, ph]) j
    have e : wHβ w₀ x t 0 j = Horizontal.errOf ⟨ph x (t + 1) 0, ph x (t + 1) 3,
        s''._pid_vel_ne_m._error.x.toReal, s''._pid_vel_ne_m._derivative.x.toReal,
        s''._pid_vel_ne_m._integrator.x.toReal, aLag w₀ x 0 (t + 1), (get_thrust_vector s'').x.toReal,
        cmdAgo w₀ x t 1 0, cmdAgo w₀ x t 2 0⟩ (posTarget (x (t + 1)) 0) (velTarget (x (t + 1)) 0) j -
        ((Horizontal.AhR *ᵥ Horizontal.errOf ⟨ph x t 0, ph x t 3, (HCtl.axisX s).E, (HCtl.axisX s).D,
          (HCtl.axisX s).I, aLag w₀ x 0 t, cmdAgo w₀ x t 1 0, cmdAgo w₀ x t 2 0, cmdAgo w₀ x t 3 0⟩
          (HCtl.axisX s).sp (HCtl.axisX s).vsp) j +
        ((HCtl.axisX s).asp • Horizontal.BhR -
          Horizontal.defect₁ (HCtl.axisX s).sp (posTarget (x (t + 1)) 0) (HCtl.axisX s).vsp
            (HCtl.axisX s).asp • Horizontal.e0 -
          Horizontal.defect₂ (HCtl.axisX s).vsp (velTarget (x (t + 1)) 0) (HCtl.axisX s).asp •
            Horizontal.e1) j + (aReal x t 0 - aLag w₀ x 0 t) * eAcc j) := by
      simp only [wHβ, hA, hA', hF, etaA, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]; exact key
  · show |wHβ w₀ x t 1 j| ≤ εHβ j
    set s'' := (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1
    have hA : ξH w₀ x t 1 = Horizontal.errOf ⟨ph x t 1, ph x t 4, (HCtl.axisY s).E, (HCtl.axisY s).D,
        (HCtl.axisY s).I, aLag w₀ x 1 t, cmdAgo w₀ x t 1 1, cmdAgo w₀ x t 2 1, cmdAgo w₀ x t 3 1⟩
        (HCtl.axisY s).sp (HCtl.axisY s).vsp := by
      rw [hY]; ext k; fin_cases k <;> simp [ξH, habs, Horizontal.errOf, refH, refAx, pIx, vIx, ph]
    have hA' : ξH w₀ x (t + 1) 1 = Horizontal.errOf ⟨ph x (t + 1) 1, ph x (t + 1) 4,
        s''._pid_vel_ne_m._error.y.toReal, s''._pid_vel_ne_m._derivative.y.toReal,
        s''._pid_vel_ne_m._integrator.y.toReal, aLag w₀ x 1 (t + 1), (get_thrust_vector s'').y.toReal,
        cmdAgo w₀ x t 1 1, cmdAgo w₀ x t 2 1⟩ (posTarget (x (t + 1)) 1) (velTarget (x (t + 1)) 1) := by
      rw [eEy, eDy, eIy, eTy, ← hc1, ← hcs 1 1, ← hcs 1 2]
      ext k; fin_cases k <;> simp [ξH, habs, Horizontal.errOf, refH, refAx, pIx, vIx, ph]
    have hF : Horizontal.forceOf (refH w₀ x 1) t = (HCtl.axisY s).asp • Horizontal.BhR -
        Horizontal.defect₁ (HCtl.axisY s).sp (posTarget (x (t + 1)) 1) (HCtl.axisY s).vsp
          (HCtl.axisY s).asp • Horizontal.e0 -
        Horizontal.defect₂ (HCtl.axisY s).vsp (velTarget (x (t + 1)) 1) (HCtl.axisY s).asp •
          Horizontal.e1 := by
      rw [hY]; simp [Horizontal.forceOf, refH, refAx]
    have key := axis_dev (HCtl.axisY s) _ _ _ _ _ _ _ _ _ _ _ _ _ wE (ph x t 1) (ph x t 4)
      (ph x (t + 1) 1) (ph x (t + 1) 4) (aReal x t 1) hEE hWE d0y d1y
      (by simpa [prow, pIx, vIx] using hrow 1) (by simp [aReal, vIx, ph]) j
    have e : wHβ w₀ x t 1 j = Horizontal.errOf ⟨ph x (t + 1) 1, ph x (t + 1) 4,
        s''._pid_vel_ne_m._error.y.toReal, s''._pid_vel_ne_m._derivative.y.toReal,
        s''._pid_vel_ne_m._integrator.y.toReal, aLag w₀ x 1 (t + 1), (get_thrust_vector s'').y.toReal,
        cmdAgo w₀ x t 1 1, cmdAgo w₀ x t 2 1⟩ (posTarget (x (t + 1)) 1) (velTarget (x (t + 1)) 1) j -
        ((Horizontal.AhR *ᵥ Horizontal.errOf ⟨ph x t 1, ph x t 4, (HCtl.axisY s).E, (HCtl.axisY s).D,
          (HCtl.axisY s).I, aLag w₀ x 1 t, cmdAgo w₀ x t 1 1, cmdAgo w₀ x t 2 1, cmdAgo w₀ x t 3 1⟩
          (HCtl.axisY s).sp (HCtl.axisY s).vsp) j +
        ((HCtl.axisY s).asp • Horizontal.BhR -
          Horizontal.defect₁ (HCtl.axisY s).sp (posTarget (x (t + 1)) 1) (HCtl.axisY s).vsp
            (HCtl.axisY s).asp • Horizontal.e0 -
          Horizontal.defect₂ (HCtl.axisY s).vsp (velTarget (x (t + 1)) 1) (HCtl.axisY s).asp •
            Horizontal.e1) j + (aReal x t 1 - aLag w₀ x 1 t) * eAcc j) := by
      simp only [wHβ, hA, hA', hF, etaA, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]; exact key

end

end Contracts.Track.Induction
