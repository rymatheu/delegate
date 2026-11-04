import Contracts.CopterHoverUniverse
import Contracts.CopterZeroPos

/-!
# `D_update_controller` at the hover: the composition of `vert_tick`

`Contracts.CopterVertNear.vert_tick` analyzes the vertical path of one tick as an explicit
composition of `AC_P_1D.update_all`, `AC_PID_Basic.update_all`, `get_accel_ef().z + GRAVITY_MSS`,
`AC_PID.update_all` and the hover offset. This file shows that `AC_PosControl.D_update_controller`
with the run parameters computes exactly that composition, once the controller is active, the
motors report no throttle limit, `MOT_THST_HOVER = 0.4444` and the RAM `PSC_D_ACC_IMAX` is at its
default `0.8`:

* the vertical offsets (`DOffZ`) and the terrain terms (`TerrZ`) are zeros and stay zeros:
  `D_update_offsets_Z` (with or without the 3 s offset-target timeout) and `update_terrain_Z`;
* frames: `D_update_offsets` writes only the `z` components of the six offset vectors
  (`D_update_offsets_frame`; the `x`, `y` components are untouched), `update_terrain` writes only
  `_pos_terrain_d_m`, `_vel_terrain_d_ms`, `_accel_terrain_d_mss` (`update_terrain_frame`), and
  neither reads `_last_update_d_ticks` (`D_update_offsets_ticks`, `update_terrain_ticks`);
* `D_update_controller_hover`: the state `s1` after the offsets and terrain differs from `s` only
  in those fields, the position target is `tgt = desired + offset + terrain` formed from `s1`, and
  the call returns `set_throttle_out(thr, true, POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)` with `thr` the
  throttle of `vert_tick`, and a state `s'` that is `s1` with exactly the ten fields the controller
  writes replaced. The `IMAX` raise is not taken (`get_throttle_hover() = 0.4444 < 0.8`), so the
  acceleration PID runs with the gains `CopterVertNear.pa`. The corollaries in the statement: the
  `x`, `y` components of the position target, the desired position, the velocity target and the
  acceleration target are those of `s`; the new position target's `z` is `P1.2.1` (the returned
  target of `AC_P_1D.update_all`, equal to `tgt` when no error clamp applies, `p1d_near`); `tgt` has
  the value of `_pos_desired_ned_m.z`; the new `_pos_desired_ned_m.z` has the value of `P1.2.1`.

The hypotheses on the limits that the offsets and terrain read are collected in `DLim`: a finite
`dt` with `|dt| ≤ 10¹⁸`, finite vertical speed limits, a finite acceleration limit with
`|a| ≤ 10¹⁸` and a finite jerk limit with `|j| ≤ 10¹¹` (the bounds of `shape_pos_vel_accel_Z`). The
limit vector and the position and velocity errors passed to `update_pos_vel_accel` are not
constrained: with zero velocity and acceleration every branch gives a zero.
-/

open Float.Model UnpackedFloat AP_Math AC_PosControl Contracts.CopterZero

namespace Contracts.CopterHover

/-! ## The zero predicates -/

/-- The vertical components of the six offset vectors are zeros (position in binary64). -/
-- <<DOffZ>>
def DOffZ (s : AC_PosControl.State) : Prop :=
  ZD s._pos_offset_target_ned_m.z ∧ ZD s._pos_offset_ned_m.z ∧ Z s._vel_offset_target_ned_ms.z ∧
    Z s._vel_offset_ned_ms.z ∧ Z s._accel_offset_target_ned_mss.z ∧ Z s._accel_offset_ned_mss.z
-- <</DOffZ>>

/-- The four terrain terms are zeros. -/
-- <<TerrZ>>
def TerrZ (s : AC_PosControl.State) : Prop :=
  Z s._pos_terrain_target_d_m ∧ Z s._pos_terrain_d_m ∧ Z s._vel_terrain_d_ms ∧
    Z s._accel_terrain_d_mss
-- <</TerrZ>>

/-- The limits that `D_update_offsets` and `update_terrain` read are finite and bounded. -/
-- <<DLim>>
structure DLim (s : AC_PosControl.State) : Prop where
  dt : s._dt_s.IsFinite
  dtb : |s._dt_s.toReal| ≤ 1e18
  up : s._vel_max_up_ms.IsFinite
  down : s._vel_max_down_ms.IsFinite
  amax : s._accel_max_d_mss.IsFinite
  amaxb : |s._accel_max_d_mss.toReal| ≤ 1e18
  jmax : s._jerk_max_d_msss.IsFinite
  jmaxb : |s._jerk_max_d_msss.toReal| ≤ 1e11
-- <</DLim>>

/-- The `double` literal `0.0` is a zero. -/
theorem ZD_lit0 : ZD (0.0 : Float) := by
  have h : (0.0 : Float).toModel.unpack = .zero .positive := by rfl
  refine ⟨by rw [Float.isFinite_iff, h]; rfl, ?_⟩
  rw [Float.toReal, h]; rfl

/-- `a - 0 = a` in value (binary64). -/
theorem sub_ZD_right {a b : Float} (ha : a.IsFinite) (hb : ZD b) :
    (a - b).IsFinite ∧ (a - b).toReal = a.toReal :=
  sub_exact_d ha hb.1 ha (by rw [hb.2, sub_zero])

/-- The loop period `dtF` satisfies the `dt` bounds of `DLim`. -/
theorem dtF_bound : CopterVertNear.dtF.IsFinite ∧ |CopterVertNear.dtF.toReal| ≤ 1e18 := by
  obtain ⟨h1, h2⟩ := litPos CopterVertNear.dtF_unpack
  refine ⟨h1, ?_⟩
  rw [h2, abs_of_nonneg (by positivity)]
  rw [zpow_neg]; norm_num

/-! ## `update_pos_vel_accel` at zero -/

/-- `update_pos_vel_accel` with zero position, velocity and acceleration returns a zero position
and a zero velocity, whatever the limit and the errors (`|dt| ≤ 10¹⁸`). -/
theorem update_pos_vel_accel_Z (C : ConvZero) {pos : postype} {vel accel dt : Float32}
    (hp : ZD pos) (hv : Z vel) (ha : Z accel) (hdt : dt.IsFinite) (hdtb : |dt.toReal| ≤ 1e18)
    (limit pos_error vel_error : Float32) :
    ZD (update_pos_vel_accel pos vel accel dt limit pos_error vel_error).1 ∧
      Z (update_pos_vel_accel pos vel accel dt limit pos_error vel_error).2 := by
  have hsq : (AP_Math.sq dt).IsFinite :=
    fin_mul hdt hdt (by rw [abs_mul]; nlinarith [abs_nonneg dt.toReal])
  have hd : Z (vel * dt + accel * 0.5 * AP_Math.sq dt) :=
    Z_add (Z_mul_left hv hdt) (Z_mul_left (Z_mul_left ha lit_half.1) hsq)
  have hdv : Z (accel * dt) := Z_mul_left ha hdt
  have hva := Z_abs hv
  have hvn := Z_neg hva
  unfold update_pos_vel_accel update_vel_accel
  refine ⟨ZD_add hp (C.toFloat_zero _ ?_), Z_add hv ?_⟩
  · split
    · exact Z_lit0
    · exact hd
  · split
    · split
      · exact constrain_Z hdv hvn.1 hva.1 hvn.2.le hva.2.ge
      · exact Z_lit0
    · exact hdv

/-! ## Frames -/

/-- `D_update_offsets` writes only the `z` components of the six offset vectors. -/
theorem D_update_offsets_frame (s : AC_PosControl.State) (clock : Clock) :
    D_update_offsets s clock = { s with
      _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with
        z := (D_update_offsets s clock)._pos_offset_target_ned_m.z },
      _pos_offset_ned_m := { s._pos_offset_ned_m with
        z := (D_update_offsets s clock)._pos_offset_ned_m.z },
      _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with
        z := (D_update_offsets s clock)._vel_offset_target_ned_ms.z },
      _vel_offset_ned_ms := { s._vel_offset_ned_ms with
        z := (D_update_offsets s clock)._vel_offset_ned_ms.z },
      _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with
        z := (D_update_offsets s clock)._accel_offset_target_ned_mss.z },
      _accel_offset_ned_mss := { s._accel_offset_ned_mss with
        z := (D_update_offsets s clock)._accel_offset_ned_mss.z } } := by
  unfold D_update_offsets
  simp only [Id.run, pure]
  split <;> rfl

/-- `update_terrain` writes only `_pos_terrain_d_m`, `_vel_terrain_d_ms`, `_accel_terrain_d_mss`. -/
theorem update_terrain_frame (s : AC_PosControl.State) :
    update_terrain s = { s with
      _pos_terrain_d_m := (update_terrain s)._pos_terrain_d_m,
      _vel_terrain_d_ms := (update_terrain s)._vel_terrain_d_ms,
      _accel_terrain_d_mss := (update_terrain s)._accel_terrain_d_mss } := rfl

/-- `D_update_offsets` does not read `_last_update_d_ticks`. -/
theorem D_update_offsets_ticks (s : AC_PosControl.State) (clock : Clock) (t : UInt32) :
    D_update_offsets { s with _last_update_d_ticks := t } clock =
      { D_update_offsets s clock with _last_update_d_ticks := t } := by
  unfold D_update_offsets
  simp only [Id.run, pure]
  split <;> rfl

/-- `update_terrain` does not read `_last_update_d_ticks`. -/
theorem update_terrain_ticks (s : AC_PosControl.State) (t : UInt32) :
    update_terrain { s with _last_update_d_ticks := t } =
      { update_terrain s with _last_update_d_ticks := t } := rfl

/-! ## The offsets and the terrain stay zero -/

/-- **`D_update_offsets` keeps zero vertical offsets**, with or without the timeout reset of the
targets. -/
theorem D_update_offsets_Z (C : ConvZero) (s : AC_PosControl.State) (clock : Clock)
    (h : DOffZ s) (hl : DLim s) : DOffZ (D_update_offsets s clock) := by
  obtain ⟨hpt, hpo, hvt, hvo, hat, hao⟩ := h
  have hup := (Float32.isFinite_neg _).2 hl.up
  have ham := (Float32.isFinite_neg _).2 hl.amax
  unfold D_update_offsets DOffZ
  simp only [Id.run, pure]
  split
  · have B := update_pos_vel_accel_Z C hpo hvo hao hl.dt hl.dtb (MIN s._limit_vector_ned.z 0.0)
      (AC_P_1D.get_error s._p_pos_d_m) (AC_PID_Basic.get_error s._pid_vel_d_m)
    have A := update_pos_vel_accel_Z C ZD_lit0 Z_lit0 Z_lit0 hl.dt hl.dtb 0.0 0.0 0.0
    exact ⟨A.1, B.1, A.2, B.2, Z_lit0,
      shape_pos_vel_accel_Z (C.toFloat32_zero _ (ZD_sub ZD_lit0 B.1)) Z_lit0 Z_lit0 B.2 hao
        hup hl.down ham hl.amax hl.jmax hl.dt hl.jmaxb hl.amaxb hl.dtb false⟩
  · have B := update_pos_vel_accel_Z C hpo hvo hao hl.dt hl.dtb (MIN s._limit_vector_ned.z 0.0)
      (AC_P_1D.get_error s._p_pos_d_m) (AC_PID_Basic.get_error s._pid_vel_d_m)
    have A := update_pos_vel_accel_Z C hpt hvt hat hl.dt hl.dtb 0.0 0.0 0.0
    exact ⟨A.1, B.1, A.2, B.2, hat,
      shape_pos_vel_accel_Z (C.toFloat32_zero _ (ZD_sub hpt B.1)) hvt hat B.2 hao
        hup hl.down ham hl.amax hl.jmax hl.dt hl.jmaxb hl.amaxb hl.dtb false⟩

/-- **`update_terrain` keeps zero terrain terms.** -/
theorem update_terrain_Z (C : ConvZero) (s : AC_PosControl.State) (h : TerrZ s) (hl : DLim s) :
    TerrZ (update_terrain s) := by
  obtain ⟨htt, htp, htv, hta⟩ := h
  have hup := (Float32.isFinite_neg _).2 hl.up
  have ham := (Float32.isFinite_neg _).2 hl.amax
  have B := update_pos_vel_accel_Z C (C.toFloat_zero _ htp) htv hta hl.dt hl.dtb
    (MIN s._limit_vector_ned.z 0.0) (AC_P_1D.get_error s._p_pos_d_m)
    (AC_PID_Basic.get_error s._pid_vel_d_m)
  have P := C.toFloat32_zero _ B.1
  unfold update_terrain TerrZ
  simp only [Id.run, pure]
  exact ⟨htt, P, B.2, shape_pos_vel_accel_Z
    (C.toFloat32_zero _ (ZD_sub (C.toFloat_zero _ htt) (C.toFloat_zero _ P))) Z_lit0 Z_lit0 B.2 hta
    hup hl.down ham hl.amax hl.jmax hl.dt hl.jmaxb hl.amaxb hl.dtb false⟩

/-! ## The position target with zero offsets and terrain -/

/-- With zero offsets and terrain, the position target `desired + offset + terrain` has the value
of the desired position. -/
theorem tgt_val (C : ConvZero) {s1 : AC_PosControl.State} (hoff : DOffZ s1) (hter : TerrZ s1)
    (hpd : s1._pos_desired_ned_m.z.IsFinite) :
    (s1._pos_desired_ned_m.z + s1._pos_offset_ned_m.z + topostype s1._pos_terrain_d_m).IsFinite ∧
      (s1._pos_desired_ned_m.z + s1._pos_offset_ned_m.z +
        topostype s1._pos_terrain_d_m).toReal = s1._pos_desired_ned_m.z.toReal := by
  have h1 := add_ZD_right hpd hoff.2.1
  have h2 := add_ZD_right h1.1 (C.toFloat_zero _ hter.2.1)
  exact ⟨h2.1, h2.2.trans h1.2⟩

/-- With zero offsets and terrain, the new desired position `target - (offset + terrain)` has the
value of the target. -/
theorem desired_val (C : ConvZero) {s1 : AC_PosControl.State} (hoff : DOffZ s1) (hter : TerrZ s1)
    {y : Float} (hy : y.IsFinite) :
    (y - (s1._pos_offset_ned_m.z + topostype s1._pos_terrain_d_m)).IsFinite ∧
      (y - (s1._pos_offset_ned_m.z + topostype s1._pos_terrain_d_m)).toReal = y.toReal :=
  sub_ZD_right hy (ZD_add hoff.2.1 (C.toFloat_zero _ hter.2.1))

/-! ## The controller -/

/-- **`D_update_controller` at the hover is the composition of `vert_tick`.** With the controller
active, no throttle limit, `MOT_THST_HOVER = 0.4444`, the RAM `IMAX` at `0.8`, zero vertical offsets
and terrain and the limits of `DLim`: the offsets and terrain give a state `s1` that differs from
`s` only in their fields and keeps them zero; the call returns `set_throttle_out(thr, true, 2 Hz)`
with `thr` built from the position P controller on `tgt`, the velocity PID `pv`, the acceleration
PID `pa` and the hover offset, wired as in `vert_tick`, and the new state `s'` is `s1` with the ten
fields the controller writes replaced (header). -/
theorem D_update_controller_hover (C : ConvZero) (s : AC_PosControl.State)
    (ahrs : AC_PosControl.AHRSInputs) (motors : AP_Motors.Inputs)
    (att : AC_PosControl.AttitudeControlInputs) (clock : AC_PosControl.Clock)
    (hact : AC_PosControl.D_is_active s clock = true)
    (hlo : motors.limit.throttle_lower = false) (hup : motors.limit.throttle_upper = false)
    (hhov : motors._throttle_hover = CopterVertNear.hoverF)
    (hkimax : s._pid_accel_d_m_kimax = AC_PosControl.POSCONTROL_D_ACC_IMAX)
    (hoff : DOffZ s) (hter : TerrZ s) (hl : DLim s) :
    ∃ s1 : AC_PosControl.State, DOffZ s1 ∧ TerrZ s1 ∧
      s1 = { s with
        _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with
          z := s1._pos_offset_target_ned_m.z },
        _pos_offset_ned_m := { s._pos_offset_ned_m with z := s1._pos_offset_ned_m.z },
        _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with
          z := s1._vel_offset_target_ned_ms.z },
        _vel_offset_ned_ms := { s._vel_offset_ned_ms with z := s1._vel_offset_ned_ms.z },
        _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with
          z := s1._accel_offset_target_ned_mss.z },
        _accel_offset_ned_mss := { s._accel_offset_ned_mss with z := s1._accel_offset_ned_mss.z },
        _pos_terrain_d_m := s1._pos_terrain_d_m,
        _vel_terrain_d_ms := s1._vel_terrain_d_ms,
        _accel_terrain_d_mss := s1._accel_terrain_d_mss } ∧
      let tgt := s1._pos_desired_ned_m.z + s1._pos_offset_ned_m.z +
        AP_Math.topostype s1._pos_terrain_d_m
      let P1 := AC_P_1D.update_all ⟨AC_PosControl.POSCONTROL_D_POS_P⟩ s._p_pos_d_m tgt
        s._pos_estimate_ned_m.z
      let scZ := ahrs.get_control_gain_scaler_Z
      let vt := P1.2.2 * scZ + (s1._vel_desired_ned_ms.z + s1._vel_offset_ned_ms.z +
        s1._vel_terrain_d_ms)
      let rv := AC_PID_Basic.update_all CopterVertNear.pv s._pid_vel_d_m vt
        s._vel_estimate_ned_ms.z s._dt_s false false
      let atg := rv.2 * scZ + (s1._accel_desired_ned_mss.z + s1._accel_offset_ned_mss.z +
        s1._accel_terrain_d_mss)
      let ra := AC_PID.update_all CopterVertNear.pa s._pid_accel_d_m atg
        (ahrs.get_accel_ef.z + GRAVITY_MSS) s._dt_s false
      let thr := -(ra.2 + AC_PID.get_ff ra.1 - AP_Motors.get_throttle_hover motors)
      ∃ s' : AC_PosControl.State,
        AC_PosControl.D_update_controller runParams.psc s ahrs motors att clock =
          (s', ⟨thr, true, AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ⟩) ∧
        s' = { s1 with
          _last_update_d_ticks := clock.ticks32,
          _p_pos_d_m := P1.1,
          _pos_target_ned_m := { s1._pos_target_ned_m with z := P1.2.1 },
          _vel_target_ned_ms := { s1._vel_target_ned_ms with z := vt },
          _pos_desired_ned_m := { s1._pos_desired_ned_m with
            z := P1.2.1 - (s1._pos_offset_ned_m.z + AP_Math.topostype s1._pos_terrain_d_m) },
          _pid_vel_d_m := rv.1,
          _accel_target_ned_mss := { s1._accel_target_ned_mss with z := atg },
          _pid_accel_d_m := ra.1,
          _vel_d_control_ratio := AP_Math.constrain_float (s1._vel_d_control_ratio +
            s1._dt_s * 0.1 * (0.5 - AC_PID_Basic.get_error rv.1 / s1._vel_max_down_ms)) 0.0 2.0,
          _limit_vector_ned := { s1._limit_vector_ned with z := 0.0 } } ∧
        s'._pid_vel_d_m = rv.1 ∧ s'._pid_accel_d_m = ra.1 ∧ s'._p_pos_d_m = P1.1 ∧
        s'._pos_target_ned_m.z = P1.2.1 ∧
        s'._pos_desired_ned_m.z = P1.2.1 - (s1._pos_offset_ned_m.z +
          AP_Math.topostype s1._pos_terrain_d_m) ∧
        s'._vel_target_ned_ms.z = vt ∧ s'._accel_target_ned_mss.z = atg ∧
        s'._last_update_d_ticks = clock.ticks32 ∧
        s'._pid_accel_d_m_kimax = s._pid_accel_d_m_kimax ∧
        s'._limit_vector_ned.z = 0.0 ∧ DOffZ s' ∧ TerrZ s' ∧
        s'._pos_target_ned_m.x = s._pos_target_ned_m.x ∧
        s'._pos_target_ned_m.y = s._pos_target_ned_m.y ∧
        s'._pos_desired_ned_m.x = s._pos_desired_ned_m.x ∧
        s'._pos_desired_ned_m.y = s._pos_desired_ned_m.y ∧
        s'._vel_target_ned_ms.x = s._vel_target_ned_ms.x ∧
        s'._vel_target_ned_ms.y = s._vel_target_ned_ms.y ∧
        s'._accel_target_ned_mss.x = s._accel_target_ned_mss.x ∧
        s'._accel_target_ned_mss.y = s._accel_target_ned_mss.y ∧
        (s._pos_desired_ned_m.z.IsFinite →
          tgt.IsFinite ∧ tgt.toReal = s._pos_desired_ned_m.z.toReal) ∧
        (P1.2.1.IsFinite →
          s'._pos_desired_ned_m.z.IsFinite ∧ s'._pos_desired_ned_m.z.toReal = P1.2.1.toReal) := by
  have hpa : ∀ X : AC_PosControl.State,
      X._pid_accel_d_m_kimax = AC_PosControl.POSCONTROL_D_ACC_IMAX →
      pid_accel_d_m_params runParams.psc X = CopterVertNear.pa :=
    fun X h => CopterVertNear.pa_eq X h
  have hno : ¬ (AP_Motors.get_throttle_hover motors > AC_PID.imax CopterVertNear.pa) := by
    rw [CopterVertNear.throttle_hover_eq motors hhov]; decide
  obtain ⟨a, b, c, d, e, f, hD⟩ : ∃ (a b : Float) (c d e f : Float32),
      D_update_offsets s clock = { s with
        _pos_offset_target_ned_m := { s._pos_offset_target_ned_m with z := a },
        _pos_offset_ned_m := { s._pos_offset_ned_m with z := b },
        _vel_offset_target_ned_ms := { s._vel_offset_target_ned_ms with z := c },
        _vel_offset_ned_ms := { s._vel_offset_ned_ms with z := d },
        _accel_offset_target_ned_mss := { s._accel_offset_target_ned_mss with z := e },
        _accel_offset_ned_mss := { s._accel_offset_ned_mss with z := f } } :=
    ⟨_, _, _, _, _, _, D_update_offsets_frame s clock⟩
  have hO := D_update_offsets_Z C s clock hoff hl
  rw [hD] at hO
  have hT := update_terrain_Z C (D_update_offsets s clock) (by rw [hD]; exact hter)
    (by rw [hD]; exact ⟨hl.1, hl.2, hl.3, hl.4, hl.5, hl.6, hl.7, hl.8⟩)
  have hO1 : DOffZ (update_terrain (D_update_offsets s clock)) := by rw [hD]; exact hO
  refine ⟨update_terrain (D_update_offsets s clock), hO1, hT, by rw [hD]; rfl, ?_⟩
  rw [hD] at hO1 hT ⊢
  intro tgt P1 scZ vt rv atg ra thr
  refine ⟨_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hO1, hT, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, fun hpd => tgt_val C hO1 hT hpd, fun hy => desired_val C hO1 hT hy⟩
  unfold D_update_controller
  simp only [Id.run, pure, hact, Bool.not_true, Bool.false_eq_true, if_false, hlo, hup,
    D_update_offsets_ticks, hD]
  rw [hpa _ ?_, if_neg hno]
  · rfl
  · exact hkimax

end Contracts.CopterHover
