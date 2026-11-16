import Contracts.Track.Reach.GlueTick
import Contracts.Track.CtrlVerticalNav
import Contracts.Track.CtrlAttitudeMixer

/-!
# The glue of hover, part (2): the mixer mean `hmix` of `VTickHyp` from `Mixer.tick_output_spec`

INDUCTION.md §"Tick glue", `hmix`: `VTickHyp.hmix` is
`|meanAct (Vehicle.tick w smp).2 − (Vehicle.tick w smp).1.ms._throttle_filter.output.toReal| ≤ εmix`.
`Mixer.tick_output_spec` (CtrlAttitudeMixer.lean) is stated at the world where `Vehicle.tick` calls
`AP_MotorsMulticopter::output`, which is `preMotS w smp` (`GlueTick.tick_split`). This file does the
rest of the glue:

* the actuators the tick returns are the `_actuator[0…3]` that `output` stores (`act_tick`);
* the stored throttle filter after the whole tick is the one `update_throttle_filter` stores inside
  `output` (`filt_tick`: no later call of the tick touches its output; `applyPos_filt`, `nf_navW`,
  `nf_mission_update`, `finW_ms`), which is the `float` update `F = f + (u − f)·α` when it is in
  `[0, 1]` (`CtrlV.utf_eq`);
* `Σ RF = Σ PF = Σ YF = 0`, so the mean of the four actuators is within `3·10⁻⁷` of `F`
  (`hmix_of_spec`).

So `εmix = 3·10⁻⁷` holds on every tick after the first whose output call meets the hypotheses of
`tick_output_spec` (the mixer region: `f, u ∈ [0.301, 0.619]`, `|roll|, |pitch|, |yaw| ≤ 0.15`, the
frame facts).
-/

namespace Contracts.Track.Reach.Glue

open Vehicle Contracts.Track.CtrlV Contracts.Mission

noncomputable section

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
/-- The position controller's events leave the motors' throttle filter output alone. -/
theorem applyPos_filt (w : World) (evs : AC_PosControl_lib.Outputs) :
    (applyPos w evs).ms._throttle_filter.output = w.ms._throttle_filter.output := by
  frame_gen World (fun w' : World => w'.ms._throttle_filter.output = w.ms._throttle_filter.output)
      (applyPos w evs)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [withMotors_ms, applyAtt_filt]; with_reducible assumption)

theorem postD_filt (w : World) : (postD w).ms._throttle_filter.output = w.ms._throttle_filter.output := by
  unfold postD
  rcases AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w) with
    ⟨pp, ps, evs⟩
  exact applyPos_filt _ _

/-- `ModeAuto::run`'s mission part leaves the throttle filter alone (after the start). -/
theorem missionW_filt (w : World) (hws : w.au.waiting_to_start = false) :
    (missionW w).ms._throttle_filter = w.ms._throttle_filter := by
  unfold missionW
  rw [hws]
  exact (nf_mission_update w).1

/-- **The stored filter after the tick is the one `output` stores** (after the first tick, the
mission started). -/
theorem filt_tick (w : World) (smp : Sample) (hin : w.in_auto = true)
    (hws : w.au.waiting_to_start = false) :
    (Vehicle.tick w smp).1.ms._throttle_filter.output =
      (AP_Motors_lib.AP_MotorsMatrix.update_throttle_filter (preMotS w smp).ms
        (motorsInputs (preMotS w smp)))._throttle_filter.output := by
  rw [tick_split]
  have hau := preNav_au w smp hin
  have h1 : (preNav w smp).au.waiting_to_start = false := by rw [hau]; exact hws
  rw [finW_ms, postD_filt, (nf_navW _).1, missionW_filt _ h1, preNav_def, modeW_auto w smp hin]
  show (postMot (preMotS w smp)).ms._throttle_filter.output = _
  simp only [postMot, filt_output]

/-- **The actuators the tick returns** are those `output` stores. -/
theorem act_tick (w : World) (smp : Sample) (i : ℕ) (hi : i < 4) :
    (Vehicle.tick w smp).2[i]! =
      (AP_Motors_lib.AP_MotorsMatrix.output (preMotS w smp).mp (preMotS w smp).ms #[]
        (motorsInputs (preMotS w smp))).2.1._actuator[i]! := by
  rw [tick_split]
  simp only [actOf, postMot]
  interval_cases i <;> rfl

theorem sum_RF : Mixer.RF 0 + Mixer.RF 1 + Mixer.RF 2 + Mixer.RF 3 = 0 := by
  simp [Mixer.RF]; norm_num
theorem sum_PF : Mixer.PF 0 + Mixer.PF 1 + Mixer.PF 2 + Mixer.PF 3 = 0 := by
  simp [Mixer.PF]; norm_num
theorem sum_YF : Mixer.YF 0 + Mixer.YF 1 + Mixer.YF 2 + Mixer.YF 3 = 0 := by
  simp [Mixer.YF]; norm_num

open AP_Motors_lib AP_MotorsMatrix in
/-- **`hmix` from the mixer's per-actuator spec at the tick's output call**: if, at
`W = preMotS w smp`, the filter update `F` is within `2·10⁻⁷` of `f + a (u − f)` with
`f, u ∈ [0.301, 0.619]`, `a ∈ [0, 1]` (so the clamps to `[0, 1]` are inactive), and each actuator
`output` stores is within `3·10⁻⁷` of `F + RF i r + PF i q + YF i y` (the two first conclusions of
`Mixer.tick_output_spec hL W …`), then the tick's mean actuator is within `3·10⁻⁷` of the stored
filter output. -/
theorem hmix_of_spec (w : World) (smp : Sample) (hin : w.in_auto = true)
    (hws : w.au.waiting_to_start = false)
    (harm : (preMotS w smp).ms._armed = true)
    (hinit : (preMotS w smp).ms._throttle_filter.initialised = true)
    {f u a r q y : ℝ} (hf0 : 301 / 1000 ≤ f) (hf1 : f ≤ 619 / 1000) (hu0 : 301 / 1000 ≤ u)
    (hu1 : u ≤ 619 / 1000) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hF : A32 ((preMotS w smp).ms._throttle_filter.output + ((preMotS w smp).ms._throttle_in -
        (preMotS w smp).ms._throttle_filter.output) *
        calc_lowpass_alpha_dt (preMotS w smp).ms._dt_s (preMotS w smp).ms._throttle_filter.cutoff_freq)
        (f + a * (u - f)) (2 / 10 ^ 7))
    (hact : ∀ i < 4, A32 (output (preMotS w smp).mp (preMotS w smp).ms #[]
        (motorsInputs (preMotS w smp))).2.1._actuator[i]!
        (((preMotS w smp).ms._throttle_filter.output + ((preMotS w smp).ms._throttle_in -
          (preMotS w smp).ms._throttle_filter.output) *
          calc_lowpass_alpha_dt (preMotS w smp).ms._dt_s
            (preMotS w smp).ms._throttle_filter.cutoff_freq).toReal +
          Mixer.RF i * r + Mixer.PF i * q + Mixer.YF i * y) (3 / 10 ^ 7)) :
    |meanAct (Vehicle.tick w smp).2 - (Vehicle.tick w smp).1.ms._throttle_filter.output.toReal| ≤
      3 / 10 ^ 7 := by
  set s := (preMotS w smp).ms with hs
  set F := s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
    calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq with hFdef
  have hv0 : 3 / 10 ≤ f + a * (u - f) := by nlinarith
  have hv1 : f + a * (u - f) ≤ 62 / 100 := by nlinarith
  obtain ⟨hFf, hFb⟩ := hF
  rw [abs_le] at hFb
  have h0 : ¬ (F < 0.0) := by
    rw [Float32.lt_iff_toReal_lt hFf Float32.isFinite_lit_zero, Float32.toReal_lit_zero, not_lt]
    linarith
  have h1 : ¬ (F > 1.0) := by
    rw [gt_iff_lt, Float32.lt_iff_toReal_lt Float32.isFinite_lit_one hFf, Float32.toReal_lit_one,
      not_lt]
    linarith
  have hfilt : (Vehicle.tick w smp).1.ms._throttle_filter.output = F := by
    rw [filt_tick w smp hin hws]
    exact utf_eq s _ harm hinit h0 h1
  rw [hfilt]
  simp only [meanAct]
  rw [act_tick w smp 0 (by norm_num), act_tick w smp 1 (by norm_num), act_tick w smp 2 (by norm_num),
    act_tick w smp 3 (by norm_num)]
  have a0 := (hact 0 (by norm_num)).2
  have a1 := (hact 1 (by norm_num)).2
  have a2 := (hact 2 (by norm_num)).2
  have a3 := (hact 3 (by norm_num)).2
  have eR : Mixer.RF 0 * r + Mixer.RF 1 * r + Mixer.RF 2 * r + Mixer.RF 3 * r = 0 := by
    rw [← add_mul, ← add_mul, ← add_mul, sum_RF, zero_mul]
  have eP : Mixer.PF 0 * q + Mixer.PF 1 * q + Mixer.PF 2 * q + Mixer.PF 3 * q = 0 := by
    rw [← add_mul, ← add_mul, ← add_mul, sum_PF, zero_mul]
  have eY : Mixer.YF 0 * y + Mixer.YF 1 * y + Mixer.YF 2 * y + Mixer.YF 3 * y = 0 := by
    rw [← add_mul, ← add_mul, ← add_mul, sum_YF, zero_mul]
  rw [abs_le] at a0 a1 a2 a3 ⊢
  constructor <;> linarith [a0.1, a0.2, a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

/-! ## `NavV` of `VTickHyp` on a hold tick -/

/-- **The navigator's frame `NavV` on a steady hold tick** (`VTickHyp.hnav`): the mission update is
the identity and `update_wpnav` logs only `set_pos_terrain_target_D_m 0`,
`set_pos_vel_accel_NED_m` and `NE_update_controller`, none of which re-initializes the vertical
controller (`navV_of_logs`). -/
theorem navV_hold (w : World) (smp : Sample) (hin : w.in_auto = true)
    (hst : w.au.state ≠ .RUNNING)
    (hS : Contracts.Track.Induction.TG.SpeedSteady (preNav w smp).wpp (preNav w smp).wps)
    (hT : (preNav w smp).wps._is_terrain_alt = false) :
    NavV (preAuto (postMot (preMot w smp)) smp) (navOf w smp) := by
  have hX := preNav_eq w smp hin
  have hau := preNav_au w smp hin
  have h2 : (preNav w smp).au.state ≠ .RUNNING := by rw [hau]; exact hst
  rw [hX] at h2 hS hT
  have hm := mission_update_idle _ h2
  refine navV_of_logs w smp (by rw [hm]) ?_
  rw [hm]
  obtain ⟨-, P, V, A, hl⟩ := Contracts.Track.Induction.TG.update_wpnav_steady
    (wpInputs (navPre (preAuto (postMot (preMot w smp)) smp))) hS hT
  have : navLog (preAuto (postMot (preMot w smp)) smp) =
      ((((#[] : AC_WPNav_lib.Outputs).push (AC_WPNav_lib.Output.set_pos_terrain_target_D_m 0.0)).push
        (AC_WPNav_lib.Output.set_pos_vel_accel_NED_m P V A)).push
        AC_WPNav_lib.Output.NE_update_controller) := hl
  rw [this]
  intro ev hev
  simp only [Array.toList_push, List.mem_append, List.mem_singleton,
    List.nil_append] at hev
  rcases hev with ((h | h) | h) <;> subst h <;> simp

end

end Contracts.Track.Reach.Glue
