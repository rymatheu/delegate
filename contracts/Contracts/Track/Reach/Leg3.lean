import Contracts.Track.Reach.Leg3Gains
import Contracts.Track.Reach.LegHold

/-!
# The 3D leg theorem: waypoint reachability from hover at `PSC_D_ACC_P = 0.25` (REACH.md §10)

```
theorem waypoint_reach (sense32 senseP w₀) (p₀ : P3) (w' : Vector3p.State) (ψ₀ : ℝ)
    (hP : LegParams3 w₀) (hmin : 1/100 ≤ dist p₀ (wpt w')) (hR : dist p₀ (wpt w') ≤ 36/10)
    (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : LegFacts3 sense32 senseP w₀ p₀ w' ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, lang_t 0 (.eventually 0 6000 (.always 0 1200 (near (wpt w') (1/10))))⟩
```

From a hover at `p₀` (any heading `ψ₀`), one waypoint `w'` in any direction between 1 cm and 3.6 m
away, in the world with `PSC_D_ACC_P 0.25`: within 6000 ticks (15 s) the vehicle is within 0.1 m of
`w'` for 1200 consecutive ticks. The `eventually` bound is 6000, not the plan's 4800: the vertical
loop at `PSC_D_ACC_P 0.25` has a slow mode (`λ = 0.99901`, the acceleration integrator), and the
tail of its response to the vertical target acceleration needs `Mt3 = 2624` ticks to fall below the
hold budget (§10.2).

`LegFacts3` is the one named hypothesis: per behavior, the start, the per-tick rows and reference
limits while the box holds (`tick`, `TickBounds3`), the defect sums over the run (`d2sum`), and the
navigator's phases (`LegPhase3`). Everything above the facts is proved (Leg3Tube, Leg3Nav,
Leg3Hold). The horizontal channel is that of the horizontal theorem (`Leg`), the vertical channel is
`VerticalHi`.
-/

namespace Contracts.Track.Reach.Leg3

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue Contracts.Track.Reach.Leg

noncomputable section

/-- **The vertical disturbance of tick `t`** against the model at `PSC_D_ACC_P = 0.25`. -/
def legWV3 (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) : Fin 8 → ℝ :=
  ξV w₀ x (t + 1) - (VerticalHi.AvR *ᵥ ξV w₀ x t + VerticalHi.forceOf (refV w₀ x) t)

/-- **The navigator's phases of one 3D behavior** (`Tc`: the completion tick; `Tl`: the end of the
loiter S-curve). Measured side: the coordinator's 3D campaign at `PSC_D_ACC_P 0.25` (426 legs,
0.05–3.6 m, elevations −90°…90°, `reach-legs3d-campaign.csv`, the traces read per tick, REACH.md
§10.3). -/
structure LegPhase3 (w₀ : Vehicle.World) (w' : P3) (x : ℕ → X) (Tc Tl : ℕ) : Prop where
  /-- The completion after the first two ticks; the loiter S-curve lasts at most 450 ticks
  (measured `≤ 434`). -/
  order : ts ≤ Tc ∧ Tc ≤ Tl ∧ Tl ≤ Tc + 450
  /-- **The target is held after the loiter**: the position target constant, the velocity and
  acceleration targets `≤ 10⁻⁶` on every axis (measured `4.2·10⁻⁸`, `4.9·10⁻⁷`). -/
  hold : ∀ t, Tl ≤ t → posTarget (x t) = posTarget (x Tl) ∧
    ∀ i, |velTarget (x t) i| ≤ 1 / 10 ^ 6 ∧ |accDes w₀ x t i| ≤ 1 / 10 ^ 6
  /-- **The leg S-curve has finished by tick 2200** (measured `≤ 2105`), and from then to the
  completion the target is at `w'` within `10⁻³` (measured `8.6·10⁻⁷`) and at rest on all three
  axes: acceleration `≤ 10⁻⁶`, defects `≤ 10⁻⁸`, `3·10⁻⁶` (measured `1.0·10⁻⁷`, `2.2·10⁻¹⁰`,
  `8.6·10⁻⁸`); the completion test. -/
  arrive : ∃ Te, ts ≤ Te ∧ Te ≤ 2200 ∧
    (∀ t, Te ≤ t → t < Tc → dist (posTarget (x t)) w' ≤ 1 / 1000 ∧
      (∀ a, |aH w₀ x t a| ≤ 1 / 10 ^ 6 ∧ |d1H w₀ x t a| ≤ 1 / 10 ^ 8 ∧
        |d2H w₀ x t a| ≤ 3 / 10 ^ 6) ∧
      |aZ w₀ x t| ≤ 1 / 10 ^ 6 ∧ |d1Z w₀ x t| ≤ 1 / 10 ^ 8 ∧ |d2Z w₀ x t| ≤ 3 / 10 ^ 6) ∧
    ∀ t, Te ≤ t → t < Tc → dist (pos (x t)) w' ≤ 99 / 1000 → Tc ≤ t + 1
  /-- **The state at completion**: distance plus speed `≤ 0.08` (measured `≤ 0.0698`). -/
  atComplete : dist (pos (x Tc)) w' + ‖vel (x Tc)‖ ≤ 8 / 100
  /-- **The loiter target** (`loiter_dest_bound`): within `dist + ‖v‖ + 10⁻³` of `w'` (measured
  within the bound). -/
  loiter : dist (posTarget (x Tl)) w' ≤ dist (pos (x Tc)) w' + ‖vel (x Tc)‖ + 1 / 1000

/-- **The per-tick facts of one 3D behavior.** -/
structure LegRun3 (w₀ : Vehicle.World) (w' : P3) (x : ℕ → X) : Prop where
  /-- **The start** (tick 2): the readouts within `ε0VL`, `ε0HL` (LegTube.lean, measured values
  there), the target accelerations `≤ 10⁻³` (measured `≤ 7.6·10⁻⁵` horizontal, `7.0·10⁻⁵` vertical),
  the horizontal velocity defect `≤ 10⁻⁶` (measured `1.2·10⁻⁷`). **Repaired 2026-11-06**: the
  vertical start asked `|ev| ≤ 10⁻⁶` and `|eA| ≤ 10⁻⁵`, false on every run (the trim
  `MOT_THST_HOVER 0.4444` against `1/2.25` sinks the vehicle at `9.80·10⁻⁴` m/s²: `ev` measured
  `5.03·10⁻⁶`, `eA` computed `2.34·10⁻⁴`); `ε0VL` now has `10⁻⁵` and `2·10⁻³` there. -/
  init : (∀ j, |ξV w₀ x ts j| ≤ ε0VL j) ∧ (∀ a j, |ξH w₀ x ts a j| ≤ ε0HL j) ∧
    (∀ a, |aH w₀ x ts a| ≤ 1 / 1000) ∧ |aZ w₀ x ts| ≤ 1 / 1000 ∧ ∀ a, |d2H w₀ x ts a| ≤ 1 / 10 ^ 6
  /-- **The tick glue and the reference limits while the box `BoxL3` holds** (`TickBounds3`):
  the rows `legWV3 ≤ εVL3` (the `u` row `4·10⁻⁶` at `PSC_D_ACC_P 0.25`; `vglue` at the vertical box
  `|ez| ≤ 0.2`, the code's `βcode` at `E = 0.21`: `1.1·10⁻⁷, 3.9·10⁻⁶, 3.9·10⁻⁶` in the rows `eV`,
  `eA`, `u`) and `legWH ≤ εHL` (the horizontal theorem's); horizontal reference per axis:
  acceleration `≤ 1.501` (measured `1.5000002`), change `≤ 0.013` (`0.0125`), defects
  `≤ 1.3·10⁻⁴`, `8·10⁻⁴` (`1.258·10⁻⁴`, `7.68·10⁻⁴`), change of `d₂` `≤ 1.1·10⁻⁵` (`1.007·10⁻⁵`);
  vertical: acceleration `≤ 1.001` (`WP_ACC_Z 1`: `1.0000001`), change `≤ 0.013` (`0.0125`),
  defects `≤ 1.3·10⁻⁴`, `8·10⁻⁴` (`6.9·10⁻⁵`, `4.0·10⁻⁴`). -/
  tick : ∀ t, ts ≤ t → t < hzn3 → (∀ k, ts ≤ k → k ≤ t → BoxL3 (ξV w₀ x) (ξH w₀ x) k) →
    TickBounds3 (ξV w₀ x) (legWV3 w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) t
  /-- **The velocity defects summed over the run**, per axis `≤ 1/4` (measured `0.2389`
  horizontal, `0.1134` vertical). -/
  d2sum : ∀ N, ts + N ≤ hzn3 → (∀ k, ts ≤ k → k ≤ ts + N → BoxL3 (ξV w₀ x) (ξH w₀ x) k) →
    (∀ a, ∑ k ∈ Finset.range N, |d2H w₀ x (ts + k) a| ≤ 1 / 4) ∧
      ∑ k ∈ Finset.range N, |d2Z w₀ x (ts + k)| ≤ 1 / 4
  /-- The navigator's phases. -/
  phase : ∃ Tc Tl : ℕ, LegPhase3 w₀ w' x Tc Tl

/-- **The facts of the 3D leg** (the one named hypothesis of `waypoint_reach`). -/
structure LegFacts3 (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p₀ : P3)
    (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) : Prop where
  run : ∀ x ∈ Mloop sense32 senseP w₀ ∩ Reach.Ahover p₀ ψ₀, LegRun3 w₀ (wpt w') x

/-! ## The parameters -/

open AC_PosControl_lib AC_PosControl in
/-- **The vertical controllers at `PSC_D_ACC_P 0.25`** (`CtrlV.DPar2` with the acceleration loop's
proportional gain `0.25`). -/
structure DPar3 (p : Params) : Prop where
  kpP : p._p_pos_d_m._kp.IsFinite
  kpPv : p._p_pos_d_m._kp.toReal = 1
  vkp : p._pid_vel_d_m._kp.IsFinite
  vkpv : p._pid_vel_d_m._kp.toReal = 5
  vki : p._pid_vel_d_m._ki.IsFinite
  vkiv : p._pid_vel_d_m._ki.toReal = 0
  vkd : p._pid_vel_d_m._kd.IsFinite
  vkdv : p._pid_vel_d_m._kd.toReal = 0
  vkff : p._pid_vel_d_m._kff.IsFinite
  vkffv : p._pid_vel_d_m._kff.toReal = 0
  vfE : p._pid_vel_d_m._filt_E_hz = 5.0
  vfD : p._pid_vel_d_m._filt_D_hz = 5.0
  akp : p._pid_accel_d_m._kp.IsFinite
  akpv : p._pid_accel_d_m._kp.toReal = 1 / 4
  aki : p._pid_accel_d_m._ki.IsFinite
  akiv : p._pid_accel_d_m._ki.toReal = CtrlV.kiA
  akd : p._pid_accel_d_m._kd.IsFinite
  akdv : p._pid_accel_d_m._kd.toReal = 0
  akff : p._pid_accel_d_m._kff.IsFinite
  akffv : p._pid_accel_d_m._kff.toReal = 0
  akdff : p._pid_accel_d_m._kdff.IsFinite
  akdffv : p._pid_accel_d_m._kdff.toReal = 0
  apd : p._pid_accel_d_m._kpdmax.IsFinite
  apdv : p._pid_accel_d_m._kpdmax.toReal = 0
  asr : p._pid_accel_d_m._slew_rate_max.IsFinite
  asrv : p._pid_accel_d_m._slew_rate_max.toReal = 0
  afT : p._pid_accel_d_m._filt_T_hz.IsFinite
  afTv : p._pid_accel_d_m._filt_T_hz.toReal = 0
  afE : p._pid_accel_d_m._filt_E_hz = 20.0
  afD : p._pid_accel_d_m._filt_D_hz.IsFinite
  afDv : p._pid_accel_d_m._filt_D_hz.toReal = 0
  aimx : p._pid_accel_d_m._kimax.IsFinite
  aimx' : p._pid_accel_d_m._kimax.toReal ≤ 2

/-- **The parameters of the 3D leg's models**: `LegParams` with the vertical part `DPar3`. -/
structure LegParams3 (w : Vehicle.World) : Prop where
  hover : w.mp._throttle_hover = 0.4444
  hover_learn : w.mp._throttle_hover_learn = 0
  expo : w.mp.thr_lin.curve_expo = 0
  spin_min : w.mp.thr_lin.spin_min = 0
  spin_max : w.mp.thr_lin.spin_max = 1
  batt : w.mp.thr_lin.batt_voltage_max = 0
  ang_r : w.ap._p_angle_roll._kp = 9
  ang_p : w.ap._p_angle_pitch._kp = 9
  ne_kp : w.pp._pid_vel_ne_m._kp = 6
  ne_ki : w.pp._pid_vel_ne_m._ki = 1
  ne_kd : w.pp._pid_vel_ne_m._kd = 0.5
  ne_kff : w.pp._pid_vel_ne_m._kff = 0
  ne_fE : w.pp._pid_vel_ne_m._filt_E_hz = 5
  ne_fD : w.pp._pid_vel_ne_m._filt_D_hz = 5
  vert : DPar3 w.pp

/-- The goal: within 6000 ticks, 1200 consecutive ticks within `0.1` of `w'`. -/
def legGoal3 (w' : P3) : Formula X := .eventually 0 6000 (.always 0 1200 (near w' (1 / 10)))

/-- **Nonvacuity**: the loop has behaviors from every hover. -/
theorem waypoint_reach_nonvacuous (sense32 : ℝ → Float32) (senseP : ℝ → Float)
    (w₀ : Vehicle.World) (p₀ : P3) (ψ₀ : ℝ) :
    (Mloop sense32 senseP w₀ ∩ Ahover p₀ ψ₀).Nonempty :=
  Leg.waypoint_reach_h_nonvacuous sense32 senseP w₀ p₀ ψ₀

end

end Contracts.Track.Reach.Leg3
