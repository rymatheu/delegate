import Contracts.Track.CtrlHorizontalSpec

/-!
# `horizontal_tick_eq`: one tick of the code is the horizontal model plus `w` (milestone M6)

`HORIZONTAL.md` §7 asks the controller lemmas for the rows of `Horizontal.tick` on the code's
values. With them, one tick of one horizontal axis, in the error coordinates
`ξ = (p - sp, v - vsp, E, D, I, a, c₁, c₂, c₃)` of `Horizontal.lean`, is

  `ξ⁺ = A_h ξ + (asp B_h - d₁ e₀ - d₂ e₁) + w`

(the form `Horizontal.errOf_traj_dist` and `course_tube` take), where

* the controller rows of `w` are the distances of the code's `float` state from the ideal law,
  bounded by `ne_spec`: `|w₂| ≤ 3.6·10⁻⁶` (`E`), `|w₃| ≤ 2.3·10⁻⁴` (`D`), `|w₄| ≤ 6.1·10⁻⁷`
  (`I`), `|w₆| ≤ 1.6·10⁻⁴` (the command `_accel_target_ned_mss`, which is the horizontal part of
  `get_thrust_vector`: `thrust_xy`);
* `w₀ = ρp`, `w₁ = ρv` are the plant remainders (the plant interface, `PLANT.md`, a hypothesis);
* `w₅ = η` is the deviation of the realized acceleration from the lag law (the attitude interface,
  M4, a hypothesis, as `Horizontal.lean` parameterizes it);
* `w₇ = w₈ = 0` (the command history shifts).

The samples the controller reads are the plant state exactly (C1, `estimates_ne`).

* `axis_tick`: the real composition for one axis, from `NEAxis`;
* `horizontal_tick_eq`: both axes, from `ne_spec` on `NERegion`.
-/

namespace Contracts.Track.HCtl

open AC_PosControl_lib Contracts.Quick Contracts.Mission Float.Model UnpackedFloat Matrix
open AC_PosControl
open Contracts.Track.Horizontal

noncomputable section

/-! ## C1 and the thrust vector -/

/-- **C1, horizontal rows**: `update_estimates` stores the sample's horizontal position (`double`)
and velocity (`float`) unchanged, whatever the vertical branches do. -/
theorem estimates_ne (s : State) (inp : Inputs) (hv : Bool) :
    (update_estimates s inp hv)._pos_estimate_ned_m.x = inp.get_relative_position_NED_origin_vec.x ∧
    (update_estimates s inp hv)._pos_estimate_ned_m.y = inp.get_relative_position_NED_origin_vec.y ∧
    (update_estimates s inp hv)._vel_estimate_ned_ms.x = inp.get_velocity_NED_vec.x ∧
    (update_estimates s inp hv)._vel_estimate_ned_ms.y = inp.get_velocity_NED_vec.y := by
  unfold update_estimates
  simp only [Id.run]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- C1 on the vehicle's inputs: the sample of the world. -/
theorem estimates_ne_world (w : Vehicle.World) (s : State) :
    (update_estimates s (Vehicle.posInputs w) false)._pos_estimate_ned_m.x = w.sample.pos.x ∧
    (update_estimates s (Vehicle.posInputs w) false)._pos_estimate_ned_m.y = w.sample.pos.y ∧
    (update_estimates s (Vehicle.posInputs w) false)._vel_estimate_ned_ms.x = w.sample.vel.x ∧
    (update_estimates s (Vehicle.posInputs w) false)._vel_estimate_ned_ms.y = w.sample.vel.y :=
  estimates_ne s _ false

/-- The horizontal part of the thrust vector is the acceleration target; its vertical part is
`-g`. -/
theorem thrust_xy (s : State) :
    (get_thrust_vector s).x = s._accel_target_ned_mss.x ∧
    (get_thrust_vector s).y = s._accel_target_ned_mss.y ∧
    (get_thrust_vector s).z = -(9.80665016 : Float32) := ⟨rfl, rfl, rfl⟩

/-! ## One axis -/

/-- The error coordinates before the tick. -/
def xiOf (A : AxisIn) (a c₁ c₂ c₃ : ℝ) : Fin 9 → ℝ :=
  ![A.p - A.sp, A.v - A.vsp, A.E, A.D, A.I, a, c₁, c₂, c₃]

/-- The error coordinates after the tick: the next sample against the next target, the code's new
filter states and command, the realized acceleration. -/
def xiNext (pN vN spN vspN : ℝ) (E' D' I' acc : Float32) (a' c₁ c₂ : ℝ) : Fin 9 → ℝ :=
  ![pN - spN, vN - vspN, E'.toReal, D'.toReal, I'.toReal, a', acc.toReal, c₁, c₂]

/-- The disturbance of one tick: plant remainders, controller rounding, attitude deviation. -/
def wOf (A : AxisIn) (ρp ρv η : ℝ) (E' D' I' acc : Float32) : Fin 9 → ℝ :=
  ![ρp, ρv, E'.toReal - lawE A.sp A.p A.vsp A.v A.E, D'.toReal - lawD A.sp A.p A.vsp A.v A.E A.D,
    I'.toReal - lawI A.sp A.p A.vsp A.v A.E A.I, η,
    acc.toReal - lawC A.sp A.p A.vsp A.v A.E A.D A.I A.asp, 0, 0]

/-- The bounds of `w` (`HORIZONTAL.md` §7, the rows of the controller). -/
def WBound (ρp ρv η : ℝ) (w : Fin 9 → ℝ) : Prop :=
  w 0 = ρp ∧ w 1 = ρv ∧ |w 2| ≤ 36 / 10 ^ 7 ∧ |w 3| ≤ 23 / 10 ^ 5 ∧ |w 4| ≤ 61 / 10 ^ 8 ∧
    w 5 = η ∧ |w 6| ≤ 16 / 10 ^ 5 ∧ w 7 = 0 ∧ w 8 = 0

set_option maxHeartbeats 1000000 in
/-- **One axis, one tick**: from `NEAxis` (the code's controller on its region), the plant rows and
the attitude interface, the error coordinates map as `A_h ξ + forcing + w` with `w = wOf …`
within `WBound`. -/
theorem axis_tick (A : AxisIn) {vt E' D' I' out acc : Float32} (hA : NEAxis A vt E' D' I' out acc)
    (a a' c₁ c₂ c₃ η pN vN spN vspN ρp ρv : ℝ)
    (hp : pN = A.p + (per : ℝ) * A.v + (per : ℝ) ^ 2 / 2 * a + ρp)
    (hv : vN = A.v + (per : ℝ) * a + ρv)
    (ha : a' = a + (αL : ℝ) * (c₃ - a) + η) :
    xiNext pN vN spN vspN E' D' I' acc a' c₁ c₂ =
        AhR *ᵥ xiOf A a c₁ c₂ c₃ + (A.asp • BhR - defect₁ A.sp spN A.vsp A.asp • e0 -
          defect₂ A.vsp vspN A.asp • e1) + wOf A ρp ρv η E' D' I' acc ∧
      WBound ρp ρv η (wOf A ρp ρv η E' D' I' acc) := by
  obtain ⟨hvt, ⟨hE, hD, hI, hO, -⟩, hacc⟩ := hA
  have c := rows_compose hvt.2 hE.2 hD.2 hI.2 hO.2 hacc.2
  refine ⟨?_, rfl, rfl, c.1, c.2.1, c.2.2.1, rfl, c.2.2.2, rfl, rfl⟩
  rw [← tick_eq]
  ext i
  fin_cases i <;>
    simp [xiNext, xiOf, wOf, tick, defect₁, defect₂, lawE, lawD, lawI, lawC, lawVt, hp, hv, ha] <;>
    ring

/-! ## Both axes -/

set_option maxHeartbeats 1000000 in
/-- **`horizontal_tick_eq`** (`HORIZONTAL.md` §7): on `NERegion` (one call of
`NE_update_controller`, `s ↦ s'`), with the plant rows `pN = p + h v + h²/2 a + ρp`,
`vN = v + h a + ρv` and the attitude interface `a' = a + αL (c₃ - a) + η` of each axis, the error
coordinates of each axis (`xiOf` of the values before, `xiNext` of the next sample and target and of
`s'`) map as `A_h ξ + (asp B_h - d₁ e₀ - d₂ e₁) + w`, with `w` within `WBound`: the plant and
attitude terms as given, the controller terms below `3.6·10⁻⁶`, `2.3·10⁻⁴`, `6.1·10⁻⁷`,
`1.6·10⁻⁴`. The command row is the new `_accel_target_ned_mss`, i.e. the horizontal part of
`get_thrust_vector s'`; the new `_pid_vel_ne_m` stays in the filter branch and the limit vector is
zero, as the next tick's region needs. -/
theorem horizontal_tick_eq (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs)
    (R : NERegion p s inp)
    (aN aN' cN₁ cN₂ cN₃ ηN pNN vNN spNN vspNN ρpN ρvN : ℝ)
    (aE aE' cE₁ cE₂ cE₃ ηE pNE vNE spNE vspNE ρpE ρvE : ℝ)
    (hpN : pNN = (axisX s).p + (per : ℝ) * (axisX s).v + (per : ℝ) ^ 2 / 2 * aN + ρpN)
    (hvN : vNN = (axisX s).v + (per : ℝ) * aN + ρvN)
    (haN : aN' = aN + (αL : ℝ) * (cN₃ - aN) + ηN)
    (hpE : pNE = (axisY s).p + (per : ℝ) * (axisY s).v + (per : ℝ) ^ 2 / 2 * aE + ρpE)
    (hvE : vNE = (axisY s).v + (per : ℝ) * aE + ρvE)
    (haE : aE' = aE + (αL : ℝ) * (cE₃ - aE) + ηE) :
    let s' := NE_update_controller p s inp
    (∃ w, xiNext pNN vNN spNN vspNN s'._pid_vel_ne_m._error.x s'._pid_vel_ne_m._derivative.x
        s'._pid_vel_ne_m._integrator.x (get_thrust_vector s').x aN' cN₁ cN₂ =
        AhR *ᵥ xiOf (axisX s) aN cN₁ cN₂ cN₃ + ((axisX s).asp • BhR -
          defect₁ (axisX s).sp spNN (axisX s).vsp (axisX s).asp • e0 -
          defect₂ (axisX s).vsp vspNN (axisX s).asp • e1) + w ∧ WBound ρpN ρvN ηN w) ∧
    (∃ w, xiNext pNE vNE spNE vspNE s'._pid_vel_ne_m._error.y s'._pid_vel_ne_m._derivative.y
        s'._pid_vel_ne_m._integrator.y (get_thrust_vector s').y aE' cE₁ cE₂ =
        AhR *ᵥ xiOf (axisY s) aE cE₁ cE₂ cE₃ + ((axisY s).asp • BhR -
          defect₁ (axisY s).sp spNE (axisY s).vsp (axisY s).asp • e0 -
          defect₂ (axisY s).vsp vspNE (axisY s).asp • e1) + w ∧ WBound ρpE ρvE ηE w) ∧
    s'._pid_vel_ne_m._reset_filter = false ∧
    s'._limit_vector_ned.x = Int32.toFloat32 0 ∧ s'._limit_vector_ned.y = Int32.toFloat32 0 := by
  intro s'
  obtain ⟨hX, hY, hr, hlx, hly⟩ := ne_spec hL p s inp R
  rw [(thrust_xy s').1, (thrust_xy s').2.1]
  exact ⟨⟨_, axis_tick (axisX s) hX aN aN' cN₁ cN₂ cN₃ ηN pNN vNN spNN vspNN ρpN ρvN hpN hvN haN⟩,
    ⟨_, axis_tick (axisY s) hY aE aE' cE₁ cE₂ cE₃ ηE pNE vNE spNE vspNE ρpE ρvE hpE hvE haE⟩,
    hr, hlx, hly⟩

/-! ## The vertical controller leaves the horizontal fields alone -/

/-- The horizontal fields `D_update_controller` leaves alone. -/
structure HFrame (s t : State) : Prop where
  acc : t._accel_target_ned_mss.x = s._accel_target_ned_mss.x ∧
    t._accel_target_ned_mss.y = s._accel_target_ned_mss.y
  lim : t._limit_vector_ned.x = s._limit_vector_ned.x ∧ t._limit_vector_ned.y = s._limit_vector_ned.y
  pid : t._pid_vel_ne_m = s._pid_vel_ne_m

section
variable (p : Params) (s : State) (inp : Inputs)
theorem doff_fr : HFrame s (D_update_offsets s inp) := by
  unfold D_update_offsets; simp only [Id.run]; (try split_ifs) <;> exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
theorem dter_fr : HFrame s (update_terrain s) := by
  unfold update_terrain; simp only [Id.run]; (try split_ifs) <;> exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
theorem dekf_fr : HFrame s (D_handle_ekf_reset s inp) := by
  unfold D_handle_ekf_reset; simp only [Id.run]; (try split_ifs) <;> (try split) <;>
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
theorem gtv_fr : HFrame s (get_throttle_with_vibration_override p s inp).1 := by
  unfold get_throttle_with_vibration_override; simp only [Id.run]; (try split_ifs) <;>
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
end

theorem HFrame.trans {a b c : State} (h1 : HFrame a b) (h2 : HFrame b c) : HFrame a c :=
  ⟨⟨h2.acc.1.trans h1.acc.1, h2.acc.2.trans h1.acc.2⟩, ⟨h2.lim.1.trans h1.lim.1,
    h2.lim.2.trans h1.lim.2⟩, h2.pid.trans h1.pid⟩

theorem d_frame (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (hact : D_is_active (D_handle_ekf_reset s inp) inp = true) :
    HFrame s (D_update_controller p s o inp).2.1 := by
  have f1 := dekf_fr s inp
  unfold D_update_controller
  simp (config := { maxSteps := 2000000 }) only [Id.run, hact, Bool.not_true, Bool.false_eq_true,
    ite_false]
  generalize D_handle_ekf_reset s inp = s1 at f1 ⊢
  have f2 := doff_fr { s1 with _last_update_d_ticks := inp.ticks32 } inp
  generalize D_update_offsets { s1 with _last_update_d_ticks := inp.ticks32 } inp = s2 at f2 ⊢
  have f3 := dter_fr s2
  generalize update_terrain s2 = s3 at f3 ⊢
  have fm : HFrame s1 { s1 with _last_update_d_ticks := inp.ticks32 } :=
    ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  have f23 : HFrame s s3 := f1.trans (fm.trans (f2.trans f3))
  split_ifs <;> first
    | exact ⟨f23.acc, f23.lim, f23.pid⟩
    | exact ⟨⟨(gtv_fr _ _ _).acc.1.trans f23.acc.1, (gtv_fr _ _ _).acc.2.trans f23.acc.2⟩,
        ⟨(gtv_fr _ _ _).lim.1.trans f23.lim.1, (gtv_fr _ _ _).lim.2.trans f23.lim.2⟩,
        (gtv_fr _ _ _).pid.trans f23.pid⟩

/-- The thrust vector the attitude controller receives (`wp_run`: `D_update_controller`, then
`get_thrust_vector`) has the horizontal part `NE_update_controller` wrote. -/
theorem thrust_after_D (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (hact : D_is_active (D_handle_ekf_reset s inp) inp = true) :
    (get_thrust_vector (D_update_controller p s o inp).2.1).x = s._accel_target_ned_mss.x ∧
    (get_thrust_vector (D_update_controller p s o inp).2.1).y = s._accel_target_ned_mss.y :=
  (d_frame p s o inp hact).acc

set_option maxHeartbeats 1000000 in
/-- **`horizontal_tick_eq` through the vertical controller**: the same statement with the command
row read from the thrust vector after `D_update_controller` (the vector `wp_run` hands to
`input_thrust_vector_heading`) and the PID state and limit vector after it. -/
theorem horizontal_tick_eq_D (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs)
    (R : NERegion p s inp) (pD : Params) (o : Outputs) (inpD : Inputs)
    (hact : D_is_active (D_handle_ekf_reset (NE_update_controller p s inp) inpD) inpD = true)
    (aN aN' cN₁ cN₂ cN₃ ηN pNN vNN spNN vspNN ρpN ρvN : ℝ)
    (aE aE' cE₁ cE₂ cE₃ ηE pNE vNE spNE vspNE ρpE ρvE : ℝ)
    (hpN : pNN = (axisX s).p + (per : ℝ) * (axisX s).v + (per : ℝ) ^ 2 / 2 * aN + ρpN)
    (hvN : vNN = (axisX s).v + (per : ℝ) * aN + ρvN)
    (haN : aN' = aN + (αL : ℝ) * (cN₃ - aN) + ηN)
    (hpE : pNE = (axisY s).p + (per : ℝ) * (axisY s).v + (per : ℝ) ^ 2 / 2 * aE + ρpE)
    (hvE : vNE = (axisY s).v + (per : ℝ) * aE + ρvE)
    (haE : aE' = aE + (αL : ℝ) * (cE₃ - aE) + ηE) :
    let s'' := (D_update_controller pD (NE_update_controller p s inp) o inpD).2.1
    (∃ w, xiNext pNN vNN spNN vspNN s''._pid_vel_ne_m._error.x s''._pid_vel_ne_m._derivative.x
        s''._pid_vel_ne_m._integrator.x (get_thrust_vector s'').x aN' cN₁ cN₂ =
        AhR *ᵥ xiOf (axisX s) aN cN₁ cN₂ cN₃ + ((axisX s).asp • BhR -
          defect₁ (axisX s).sp spNN (axisX s).vsp (axisX s).asp • e0 -
          defect₂ (axisX s).vsp vspNN (axisX s).asp • e1) + w ∧ WBound ρpN ρvN ηN w) ∧
    (∃ w, xiNext pNE vNE spNE vspNE s''._pid_vel_ne_m._error.y s''._pid_vel_ne_m._derivative.y
        s''._pid_vel_ne_m._integrator.y (get_thrust_vector s'').y aE' cE₁ cE₂ =
        AhR *ᵥ xiOf (axisY s) aE cE₁ cE₂ cE₃ + ((axisY s).asp • BhR -
          defect₁ (axisY s).sp spNE (axisY s).vsp (axisY s).asp • e0 -
          defect₂ (axisY s).vsp vspNE (axisY s).asp • e1) + w ∧ WBound ρpE ρvE ηE w) ∧
    s''._pid_vel_ne_m._reset_filter = false ∧
    s''._limit_vector_ned.x = Int32.toFloat32 0 ∧ s''._limit_vector_ned.y = Int32.toFloat32 0 := by
  intro s''
  have F := d_frame pD (NE_update_controller p s inp) o inpD hact
  have H := horizontal_tick_eq hL p s inp R aN aN' cN₁ cN₂ cN₃ ηN pNN vNN spNN vspNN ρpN ρvN
    aE aE' cE₁ cE₂ cE₃ ηE pNE vNE spNE vspNE ρpE ρvE hpN hvN haN hpE hvE haE
  simp only at H
  have tx : (get_thrust_vector s'').x = (get_thrust_vector (NE_update_controller p s inp)).x :=
    F.acc.1
  have ty : (get_thrust_vector s'').y = (get_thrust_vector (NE_update_controller p s inp)).y :=
    F.acc.2
  rw [tx, ty, F.pid, F.lim.1, F.lim.2]
  exact H

end

end Contracts.Track.HCtl
