import Contracts.Track.Induction.Horiz
import Contracts.Track.CtrlVertical

/-!
# M9: the vertical tick from the C-series join `CtrlV.vertical_tick_split`

`VGlue w₀ x t` is what the tick glue has to establish at tick `t` for the vertical join:
* the hypotheses `CtrlV.VTickHyp` of one tick at the region's magnitudes (`vMag`);
* the navigator's targets read by `D_update_controller` are the targets of `Run.lean`;
* the thrust command and the integrator within `3` and `2`.

`wSv` is the structured vertical disturbance of the tick, `CtrlV.wS` of the tick's values: the plant
residuals, the tilt coupling of the sampled specific force through the acceleration filter, and the
angle boost's deviation. An `Iface` whose `wVs` is `wSv` carries it in the certified nominal.

`wV_bound`: then the vertical disturbance `wV` of `Inv.lean` is within `εV` per coordinate. The
proof:
* reads `ξV` before and after the tick as `CtrlV.vstate` (the trim is the run's hover);
* reads the held mean as the tick's `meanAct`, since the actuators are in `[0, 1]`;
* reads the model's `tick` as `A_v ξ + forceOf`;
* bounds the code's `βcode` by `εV` at the magnitudes (`βcode_le`).
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission Matrix Finset

noncomputable section

/-- The mean held actuator at tick `t` (the plant's `held`). -/
def heldM (x : ℕ → Mission.X) (t : ℕ) : ℝ :=
  ((x t).phys.held 0 + (x t).phys.held 1 + (x t).phys.held 2 + (x t).phys.held 3) / 4

/-- The vertical values of tick `t` (`CtrlV.vvOf`): the plant before and after, the next targets. -/
def vvals (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : CtrlV.VVals :=
  CtrlV.vvOf (run w₀ x t) (x t).smp (heldM x t) (ph x t 2) (ph x t 5) (ph x (t + 1) 2)
    (ph x (t + 1) 5) (posTarget (x (t + 1)) 2) (velTarget (x (t + 1)) 2)

/-- **The structured vertical disturbance** of tick `t`. -/
def wSv (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : Fin 8 → ℝ := CtrlV.wS (vvals w₀ x t)

/-- **The vertical tick glue at tick `t`**: the join's hypotheses at the region's magnitudes
(position error `0.11`, velocity error `0.6`, target speed `2`, target acceleration `3`,
acceleration error `5`, signal scales `16`, `cos θ ≥ 0.9`, mixer mean `3·10⁻⁷`, which is
`Mixer.tick_output_spec`'s per-actuator bound, averaged with `Σ RF = Σ PF = Σ YF = 0`), the targets, and the
thrust command and integrator within `3` and `2`. -/
def VGlue (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : Prop :=
  CtrlV.VTickHyp (run w₀ x t) (x t).smp (11 / 100) (6 / 10) 2 3 5 16 16 (9 / 10) (3 / 10 ^ 7) ∧
  (CtrlV.navOf (run w₀ x t) (x t).smp).ps._pos_desired_ned_m.z.toReal = posTarget (x t) 2 ∧
  (CtrlV.navOf (run w₀ x t) (x t).smp).ps._vel_desired_ned_ms.z.toReal = velTarget (x t) 2 ∧
  (CtrlV.navOf (run w₀ x t) (x t).smp).ps._accel_desired_ned_mss.z.toReal = accDes w₀ x t 2 ∧
  |(vvals w₀ x t).thr| ≤ 3 ∧ |(run w₀ x t).ps._pid_accel_d_m._integrator.toReal| ≤ 2

/-- **The code's `β`s at the region's magnitudes are within `εV`.** -/
theorem βcode_le {K I thr εs : ℝ} (hK : K ≤ 2) (hI : |I| ≤ 2) (hthr : |thr| ≤ 3) (hs0 : 0 ≤ εs)
    (hs : εs ≤ 3 / 10 ^ 7) (j : Fin 8) :
    CtrlV.βcode (CtrlV.veOf (11 / 100) (6 / 10) 2 3 5 16 16 K I thr (9 / 10) (3 / 10 ^ 7) εs) j ≤
      εV j := by
  have hu : u32 = 1 / 16777216 := by norm_num [u32]
  have he : η32 ≤ 1 / 10 ^ 40 := by
    rw [η32]; exact (zpow_le_zpow_right₀ one_le_two (by norm_num : (-149 : ℤ) ≤ -140)).trans (by norm_num)
  have he0 : 0 ≤ η32 := by rw [η32]; positivity
  have hI0 := abs_nonneg I
  have ht0 := abs_nonneg thr
  fin_cases j <;>
    simp only [CtrlV.βcode, CtrlV.veOf, CtrlV.VErr.W2, CtrlV.VErr.W3c, CtrlV.VErr.W4c, CtrlV.MeV,
      εV, hu, Matrix.cons_val, Fin.reduceFinMk, Fin.isValue] <;>
    norm_num [Vertical.per, Vertical.amax, Vertical.tw, Vertical.grav, Vertical.αV, Vertical.αA,
      Vertical.kiDt, Vertical.kpAcc, CtrlV.αVr, CtrlV.αAr, CtrlV.αTr] <;>
    nlinarith

/-- The mean held actuator after a tick is the tick's `meanAct` (the actuators are in `[0, 1]`). -/
theorem heldM_succ {sense32 : ℝ → Float32} {senseP : ℝ → Float} {w₀ : Vehicle.World}
    {x : ℕ → Mission.X} (hx : x ∈ Mloop sense32 senseP w₀) (t : ℕ)
    (hA : ActOK (run w₀ x t).ms._actuator) :
    heldM x (t + 1) = CtrlV.meanAct (Vehicle.tick (run w₀ x t) (x t).smp).2 := by
  have hn := (mem_Mplant.1 hx.1 t).1
  have ha := act_run hx.2 t
  have hb := (tick_actOK _ (x t).smp hA).2
  have c : ∀ i : ℕ, Plant.clip01 ((Vehicle.tick (run w₀ x t) (x t).smp).2[i]!).toReal =
      ((Vehicle.tick (run w₀ x t) (x t).smp).2[i]!).toReal := by
    intro i
    obtain ⟨-, h0, h1⟩ := hb i
    simp only [Plant.clip01, min_eq_right h1, max_eq_right h0]
  simp only [heldM, hn, Plant.next, Plant.nextR, Plant.act, ha, CtrlV.meanAct, actVec]
  simp [c]

/-- **The vertical disturbance of one tick**, from the glue, by `CtrlV.vertical_tick_split`. -/
theorem wV_bound {sense32 : ℝ → Float32} {senseP : ℝ → Float} {w₀ : Vehicle.World}
    (hL : LibmSpec) (hpi : CtrlV.PiF32) (hS : Plant.CopterSense sense32 senseP)
    {x : ℕ → Mission.X} (hx : x ∈ Mloop sense32 senseP w₀) (t : ℕ)
    (hA : ActOK (run w₀ x t).ms._actuator) (hg : VGlue w₀ x t)
    (hp : |ph x t 2| ≤ 4) (hv : |ph x t 5| ≤ 2) (I : Iface) (hI : I.wVs x t = wSv w₀ x t) :
    ∀ j, |wV I w₀ x t j| ≤ εV j := by
  obtain ⟨H, esp, evsp, easp, hthr, hIb⟩ := hg
  have T := CtrlV.vertical_tick_split hL hpi (run w₀ x t) (x t).smp (heldM x t) (ph x t 2)
    (ph x t 5) (ph x (t + 1) 2) (ph x (t + 1) 5) (posTarget (x (t + 1)) 2) (velTarget (x (t + 1)) 2) H
  -- the sample's vertical position and velocity
  have hs := (mem_Mplant.1 hx.1 t).2
  have szp : (x t).smp.pos.z.toReal = (senseP ((x t).phys.x 2)).toReal := by
    rw [hs]; simp [toVSample, Plant.sample, Plant.State.ofX]
  have svz : (x t).smp.vel.z.toReal = (sense32 ((x t).phys.x 5)).toReal := by
    rw [hs]; simp [toVSample, Plant.sample, Plant.State.ofX]
  have dz : |ph x t 2 - (x t).smp.pos.z.toReal| ≤ 1 / 10 ^ 9 := by
    rw [szp, abs_sub_comm]; exact senseP_close hS (hp.trans (by norm_num))
  have dv : |ph x t 5 - (x t).smp.vel.z.toReal| ≤ 2 / 10 ^ 7 := by
    rw [svz, abs_sub_comm]; exact sense32_close3 hS (hv.trans (by norm_num))
  -- the vectors
  set v := vvals w₀ x t with hvdef
  have hvsp : v.sp = posTarget (x t) 2 := esp
  have hvvsp : v.vsp = velTarget (x t) 2 := evsp
  have hvasp : v.asp = accDes w₀ x t 2 := easp
  have hhov : hoverT = 1 / (9 / 4) := by norm_num [hoverT, Plant.thrust2weight]
  have e1 : ξV w₀ x (t + 1) = CtrlV.vstate (Vehicle.tick (run w₀ x t) (x t).smp).1 (ph x (t + 1) 2)
      (ph x (t + 1) 5) (CtrlV.meanAct (Vehicle.tick (run w₀ x t) (x t).smp).2)
      (posTarget (x (t + 1)) 2) (velTarget (x (t + 1)) 2) := by
    rw [← heldM_succ hx t hA]
    ext k; fin_cases k <;> simp [ξV, Vertical.errOf, vabs, refV, refAx, CtrlV.vstate, run, hov,
      CtrlV.hovF, heldM, ph, hhov]
  have e2 : ξV w₀ x t = CtrlV.vstate (run w₀ x t) (ph x t 2) (ph x t 5) (heldM x t) v.sp v.vsp := by
    rw [hvsp, hvvsp]
    ext k; fin_cases k <;> simp [ξV, Vertical.errOf, vabs, refV, refAx, CtrlV.vstate, hov,
      CtrlV.hovF, heldM, ph, hhov]
  have e3 : Vertical.forceOf (refV w₀ x) t = v.asp • Vertical.BvR -
      Vertical.defect₁ v.sp (posTarget (x (t + 1)) 2) v.vsp v.asp • Vertical.e0 -
      Vertical.defect₂ v.vsp (velTarget (x (t + 1)) 2) v.asp • Vertical.e1 := by
    rw [hvsp, hvvsp, hvasp]; simp [Vertical.forceOf, refV, refAx]
  have key : wV I w₀ x t = CtrlV.vstate (Vehicle.tick (run w₀ x t) (x t).smp).1 (ph x (t + 1) 2)
      (ph x (t + 1) 5) (CtrlV.meanAct (Vehicle.tick (run w₀ x t) (x t).smp).2)
      (posTarget (x (t + 1)) 2) (velTarget (x (t + 1)) 2) -
      Vertical.tick (CtrlV.vstate (run w₀ x t) (ph x t 2) (ph x t 5) (heldM x t) v.sp v.vsp) v.asp
        (Vertical.defect₁ v.sp (posTarget (x (t + 1)) 2) v.vsp v.asp)
        (Vertical.defect₂ v.vsp (velTarget (x (t + 1)) 2) v.asp) - CtrlV.wS v := by
    rw [Vertical.tick_eq, ← e1, ← e2, ← e3, wV, hI, wSv]
    simp only [ξv]
    abel
  intro j
  rw [key]
  refine (T j).trans (βcode_le H.hp.aimx' hIb hthr (by positivity) ?_ j)
  linarith

end

end Contracts.Track.Induction
