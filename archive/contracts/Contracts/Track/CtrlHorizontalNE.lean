import Contracts.Track.CtrlHorizontalP
import Contracts.Track.CtrlHorizontalPID

/-!
# C-series, `AC_PosControl::NE_update_controller` (milestone M6)

The composition of the horizontal controller (`AC_PosControl.cpp:697-788`) on the region of
`HORIZONTAL.md` §7:

* no EKF reset (`NE_handle_ekf_reset` is the identity), `NE_is_active`;
* the offsets zero after `NE_update_offsets` (`OffZero`), the disturbances zero, the scale factors
  `1` (`get_control_gain_scaler_XY`, `_ne_control_scale_factor`);
* the position P controller in its linear zone (`p_spec`), the velocity PID in its region
  (`pid_spec`), `limit_accel_xy` inactive (`limit_accel_xy_inactive`).

The state of the code is reached through explicit names for the intermediate values (`nS3`, the
state after `NE_update_offsets`; `nPosTgt`, `nCombPos`, `nP`, `nVelT`, `nCombVel`, `nPID`, `nAcc`,
`nAmax`, `nVnorm`), and the field lemmas `ne_pid`, `ne_accel_x`, `ne_accel_y`, `ne_limit_x`,
`ne_limit_y` read the result of `NE_update_controller` through them (each one `rfl` per branch).

`ne_spec`: per axis (`NEAxis`), with `sp, p, vsp, v, asp` the values of `_pos_desired_ned_m`,
`_pos_estimate_ned_m`, `_vel_desired_ned_ms`, `_vel_estimate_ned_ms`, `_accel_desired_ned_mss` and
`E, D, I` those of `_pid_vel_ne_m` before the call:

* `⟦vt⟧ = kpPos (sp - p) + vsp + β`, `|β| ≤ 5·10⁻⁷` (`_vel_target_ned_ms`);
* the velocity PID rows of `PIDAxis` with target `⟦vt⟧` and measurement `v`;
* `⟦accel_target⟧ = ⟦out⟧ + asp + β`, `|β| ≤ 6·10⁻⁶`;

and the new `_pid_vel_ne_m` is the PID's (filter branch, `_reset_filter = false`), the new
`_limit_vector_ned.xy` is zero (the limiter did not act), so the region's limit condition holds on
the next tick.
-/

namespace Contracts.Track.HCtl

open AC_PosControl_lib Contracts.Quick Contracts.Mission Float.Model UnpackedFloat
open AC_PosControl

noncomputable section

/-! ## Frames -/

theorem ekf_noop (s : State) (inp : Inputs)
    (h : inp.get_position_NE_reset_count = s._ahrs_position_NE_reset_count) :
    NE_handle_ekf_reset s inp = s := by
  unfold NE_handle_ekf_reset
  simp [Id.run, h]

section
variable (s : State) (inp : Inputs)
theorem cy_p : (calculate_yaw_and_rate_yaw s inp)._p_pos_ne_m = s._p_pos_ne_m := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_pid : (calculate_yaw_and_rate_yaw s inp)._pid_vel_ne_m = s._pid_vel_ne_m := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_acc : (calculate_yaw_and_rate_yaw s inp)._accel_target_ned_mss =
    s._accel_target_ned_mss := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_lim : (calculate_yaw_and_rate_yaw s inp)._limit_vector_ned = s._limit_vector_ned := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_vt : (calculate_yaw_and_rate_yaw s inp)._vel_target_ned_ms = s._vel_target_ned_ms := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl

theorem off_p : (NE_update_offsets s inp)._p_pos_ne_m = s._p_pos_ne_m := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_pid : (NE_update_offsets s inp)._pid_vel_ne_m = s._pid_vel_ne_m := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_posd : (NE_update_offsets s inp)._pos_desired_ned_m = s._pos_desired_ned_m := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_pose : (NE_update_offsets s inp)._pos_estimate_ned_m = s._pos_estimate_ned_m := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_veld : (NE_update_offsets s inp)._vel_desired_ned_ms = s._vel_desired_ned_ms := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_vele : (NE_update_offsets s inp)._vel_estimate_ned_ms = s._vel_estimate_ned_ms := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_accd : (NE_update_offsets s inp)._accel_desired_ned_mss = s._accel_desired_ned_mss := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_dp : (NE_update_offsets s inp)._disturb_pos_ne_m = s._disturb_pos_ne_m := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_dv : (NE_update_offsets s inp)._disturb_vel_ne_ms = s._disturb_vel_ne_ms := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_sc : (NE_update_offsets s inp)._ne_control_scale_factor = s._ne_control_scale_factor := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_dt : (NE_update_offsets s inp)._dt_s = s._dt_s := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_lim : (NE_update_offsets s inp)._limit_vector_ned = s._limit_vector_ned := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
theorem off_amo : (NE_update_offsets s inp)._angle_max_override_rad = s._angle_max_override_rad := by
  unfold NE_update_offsets; simp only [Id.run]; split_ifs <;> rfl
end

/-! ## The intermediate values of `NE_update_controller` -/

/-- The state after `NE_update_offsets` (no EKF reset, active). -/
def nS3 (s : State) (inp : Inputs) : State :=
  NE_update_offsets { s with _last_update_ne_ticks := inp.ticks32 } inp

/-- `_pos_target_ned_m.xy = _pos_desired_ned_m.xy + _pos_offset_ned_m.xy`. -/
def nPosTgt (s3 : State) : Vector2p.State :=
  Vector2p.op_add ({ x := s3._pos_desired_ned_m.x, y := s3._pos_desired_ned_m.y } : Vector2p.State)
    (Vector3p.xy s3._pos_offset_ned_m)

/-- `_pos_estimate_ned_m.xy + _disturb_pos_ne_m`. -/
def nCombPos (s3 : State) : Vector2p.State :=
  (Vector2p.op_add_assign (Vector3p.xy s3._pos_estimate_ned_m)
    (Vector2f.todouble s3._disturb_pos_ne_m)).1

/-- The position P controller's call. -/
def nP (p : Params) (s3 : State) : AC_P_2D.State × Vector2p.State × Vector2f.State :=
  AC_P_2D.update_all p._p_pos_ne_m s3._p_pos_ne_m
    ({ x := (nPosTgt s3).x, y := (nPosTgt s3).y } : Vector2p.State) (nCombPos s3)

/-- The P output scaled. -/
def nVelP (p : Params) (s3 : State) (inp : Inputs) : Vector2f.State :=
  (Vector2f.op_mul_assign (Vector2f.op_mul_assign (nP p s3).2.2
    inp.get_control_gain_scaler_XY).1 s3._ne_control_scale_factor).1

/-- `_vel_target_ned_ms.xy`: the scaled P output plus `_vel_desired + _vel_offset`. -/
def nVelT (p : Params) (s3 : State) (inp : Inputs) : Vector2f.State :=
  (Vector2f.op_add_assign ({ x := (nVelP p s3 inp).x, y := (nVelP p s3 inp).y } : Vector2f.State)
    (Vector2f.op_add ({ x := s3._vel_desired_ned_ms.x, y := s3._vel_desired_ned_ms.y } :
      Vector2f.State) (Vector3f.xy s3._vel_offset_ned_ms))).1

/-- `_vel_estimate_ned_ms.xy + _disturb_vel_ne_ms`. -/
def nCombVel (s3 : State) : Vector2f.State :=
  (Vector2f.op_add_assign (Vector3f.xy s3._vel_estimate_ned_ms) s3._disturb_vel_ne_ms).1

/-- The velocity PID's call. -/
def nPID (p : Params) (s3 : State) (inp : Inputs) : AC_PID_2D.State × Vector2f.State :=
  AC_PID_2D.update_all_Vector2f2_float_Vector2f p._pid_vel_ne_m s3._pid_vel_ne_m
    (Vector3f.xy ({ s3._vel_target_ned_ms with x := (nVelT p s3 inp).x, y := (nVelT p s3 inp).y }))
    (nCombVel s3) s3._dt_s (Vector3f.xy s3._limit_vector_ned)

/-- The PID output scaled. -/
def nAccP (p : Params) (s3 : State) (inp : Inputs) : Vector2f.State :=
  (Vector2f.op_mul_assign (Vector2f.op_mul_assign (nPID p s3 inp).2
    inp.get_control_gain_scaler_XY).1 s3._ne_control_scale_factor).1

/-- `_accel_target_ned_mss.xy` before the limiter: the scaled PID output plus
`_accel_desired + _accel_offset`. -/
def nAcc (p : Params) (s3 : State) (inp : Inputs) : Vector2f.State :=
  (Vector2f.op_add_assign ({ x := (nAccP p s3 inp).x, y := (nAccP p s3 inp).y } : Vector2f.State)
    (Vector2f.op_add ({ x := s3._accel_desired_ned_mss.x, y := s3._accel_desired_ned_mss.y } :
      Vector2f.State) (Vector3f.xy s3._accel_offset_ned_mss))).1

/-- The acceleration limit `g tan(min(althold lean max, lean max))`. -/
def nAmax (p : Params) (s : State) (inp : Inputs) : Float32 :=
  angle_rad_to_accel_mss (MIN_float2 inp.get_althold_lean_angle_max_rad
    (get_lean_angle_max_rad p s inp))

/-- `_vel_desired_ned_ms.xy`. -/
def nVdes (s3 : State) : Vector2f.State :=
  { x := s3._vel_desired_ned_ms.x, y := s3._vel_desired_ned_ms.y }

/-- The limiter's reference velocity. -/
def nVnorm (s3 : State) : Vector2f.State :=
  if is_positive_float s3._vel_max_ne_ms = true then
    Vector2f.op_div (nVdes s3) s3._vel_max_ne_ms
  else Vector2f.init_void

/-! ## The fields of the result -/

section
variable (p : Params) (s : State) (inp : Inputs)
  (h : inp.get_position_NE_reset_count = s._ahrs_position_NE_reset_count)
  (ha : NE_is_active s inp = true)
include h ha

theorem ne_pid : (NE_update_controller p s inp)._pid_vel_ne_m = (nPID p (nS3 s inp) inp).1 := by
  unfold NE_update_controller
  simp only [Id.run, ekf_noop s inp h, ha, Bool.not_true, Bool.false_eq_true, ite_false, cy_pid]
  split <;> split <;> rfl

/-- The limiter's result and flag, read through the explicit names. -/
theorem ne_raw :
    (NE_update_controller p s inp)._accel_target_ned_mss.x =
      (limit_accel_xy (nVnorm (nS3 s inp)) (nAcc p (nS3 s inp) inp)
        (nAmax p (nS3 s inp) inp)).1.x ∧
    (NE_update_controller p s inp)._accel_target_ned_mss.y =
      (limit_accel_xy (nVnorm (nS3 s inp)) (nAcc p (nS3 s inp) inp)
        (nAmax p (nS3 s inp) inp)).1.y ∧
    ((limit_accel_xy (nVnorm (nS3 s inp)) (nAcc p (nS3 s inp) inp)
        (nAmax p (nS3 s inp) inp)).2 = false →
      (NE_update_controller p s inp)._limit_vector_ned.x = Int32.toFloat32 0 ∧
      (NE_update_controller p s inp)._limit_vector_ned.y = Int32.toFloat32 0) := by
  by_cases hv : is_positive_float (nS3 s inp)._vel_max_ne_ms = true
  · have hn : nVnorm (nS3 s inp) = Vector2f.op_div (nVdes (nS3 s inp)) (nS3 s inp)._vel_max_ne_ms :=
      if_pos hv
    rw [hn]
    simp only [nS3] at hv
    unfold NE_update_controller
    simp only [Id.run, ekf_noop s inp h, ha, Bool.not_true, Bool.false_eq_true, ite_false, cy_acc,
      cy_lim, hv, ite_true]
    split
    · exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
    · rename_i hb
      refine ⟨rfl, rfl, fun hl => absurd ?_ hb⟩
      rw [Bool.not_eq_true']
      exact hl
  · have hn : nVnorm (nS3 s inp) = Vector2f.init_void := if_neg hv
    rw [hn]
    simp only [nS3] at hv
    unfold NE_update_controller
    simp only [Id.run, ekf_noop s inp h, ha, Bool.not_true, Bool.false_eq_true, ite_false, cy_acc,
      cy_lim, hv]
    split
    · exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩
    · rename_i hb
      refine ⟨rfl, rfl, fun hl => absurd ?_ hb⟩
      rw [Bool.not_eq_true']
      exact hl

theorem ne_out (HL : ∀ v, limit_accel_xy v (nAcc p (nS3 s inp) inp) (nAmax p (nS3 s inp) inp) =
      (nAcc p (nS3 s inp) inp, false)) :
    (NE_update_controller p s inp)._accel_target_ned_mss.x = (nAcc p (nS3 s inp) inp).x ∧
    (NE_update_controller p s inp)._accel_target_ned_mss.y = (nAcc p (nS3 s inp) inp).y ∧
    (NE_update_controller p s inp)._limit_vector_ned.x = Int32.toFloat32 0 ∧
    (NE_update_controller p s inp)._limit_vector_ned.y = Int32.toFloat32 0 := by
  obtain ⟨h1, h2, h3⟩ := ne_raw p s inp h ha
  rw [HL] at h1 h2 h3
  exact ⟨h1, h2, h3 rfl⟩
end

/-! ## Values of the intermediate quantities -/

open Contracts.Track.Horizontal (αE dtf kpPos kp ki kd)

/-- `double` addition of a zero is exact. -/
theorem F64.add_zero_val {a z : Float} (ha : a.IsFinite) (hz : z.IsFinite) (h0 : z.toReal = 0) :
    (a + z).IsFinite ∧ (a + z).toReal = a.toReal := by
  have hm : |a.toReal + z.toReal| ≤ maxFinite := by
    rw [h0, add_zero]; exact Float.abs_toReal_le_maxFinite a
  obtain ⟨b1, b2⟩ := Float.add_bracket ha hz hm ha
  exact ⟨(Float.add_err_all ha hz hm).1, le_antisymm (b2 (by rw [h0, add_zero]))
    (b1 (by rw [h0, add_zero]))⟩

/-- The offsets after `NE_update_offsets` are zero (`HORIZONTAL.md` §7: offsets zero). -/
structure OffZero (s3 : State) : Prop where
  px : s3._pos_offset_ned_m.x.IsFinite ∧ s3._pos_offset_ned_m.x.toReal = 0
  py : s3._pos_offset_ned_m.y.IsFinite ∧ s3._pos_offset_ned_m.y.toReal = 0
  vx : s3._vel_offset_ned_ms.x.IsFinite ∧ s3._vel_offset_ned_ms.x.toReal = 0
  vy : s3._vel_offset_ned_ms.y.IsFinite ∧ s3._vel_offset_ned_ms.y.toReal = 0
  ax : s3._accel_offset_ned_mss.x.IsFinite ∧ s3._accel_offset_ned_mss.x.toReal = 0
  ay : s3._accel_offset_ned_mss.y.IsFinite ∧ s3._accel_offset_ned_mss.y.toReal = 0

/-- The ideal real law of one tick from the values before it (`Horizontal.absTick`'s controller
rows): `vt`, `E⁺`, `D⁺`, `I⁺` and the command `c`. -/
def lawVt (sp p vsp : ℝ) : ℝ := (kpPos : ℝ) * (sp - p) + vsp
def lawE (sp p vsp v E : ℝ) : ℝ := E + (αE : ℝ) * ((lawVt sp p vsp - v) - E)
def lawD (sp p vsp v E D : ℝ) : ℝ := D + (αE : ℝ) * ((lawE sp p vsp v E - E) / (dtf : ℝ) - D)
def lawI (sp p vsp v E I : ℝ) : ℝ := I + (ki : ℝ) * (dtf : ℝ) * lawE sp p vsp v E
def lawC (sp p vsp v E D I asp : ℝ) : ℝ :=
  (kp : ℝ) * lawE sp p vsp v E + lawI sp p vsp v E I + (kd : ℝ) * lawD sp p vsp v E D + asp

/-- **Composition of the row errors**: the per-step bounds of the float rows give the distance of
the new state and command from the ideal law of the old state. These are the components of `w` in
`horizontal_tick_eq`. -/
theorem rows_compose {sp p vsp v E D I asp vt E' D' I' out acc : ℝ}
    (hvt : |vt - lawVt sp p vsp| ≤ 5 / 10 ^ 7)
    (hE : |E' - (E + (αE : ℝ) * ((vt - v) - E))| ≤ 35 / 10 ^ 7)
    (hD : |D' - (D + (αE : ℝ) * ((E' - E) / (dtf : ℝ) - D))| ≤ 12 / 10 ^ 5)
    (hI : |I' - (I + (ki : ℝ) * (dtf : ℝ) * E')| ≤ 6 / 10 ^ 7)
    (hO : |out - ((kp : ℝ) * E' + I' + (kd : ℝ) * D')| ≤ 3 / 2 / 10 ^ 5)
    (hA : |acc - (out + asp)| ≤ 6 / 10 ^ 6) :
    |E' - lawE sp p vsp v E| ≤ 36 / 10 ^ 7 ∧ |D' - lawD sp p vsp v E D| ≤ 23 / 10 ^ 5 ∧
      |I' - lawI sp p vsp v E I| ≤ 61 / 10 ^ 8 ∧ |acc - lawC sp p vsp v E D I asp| ≤ 16 / 10 ^ 5 := by
  have hα : ((αE : ℚ) : ℝ) = 4886901 / 67108864 := by norm_num [αE]
  have hdt : ((dtf : ℚ) : ℝ) = 5368709 / 2147483648 := by norm_num [dtf]
  have hki : ((ki : ℚ) : ℝ) = 1 := by norm_num [ki]
  have hkp : ((kp : ℚ) : ℝ) = 6 := by norm_num [kp]
  have hkd : ((kd : ℚ) : ℝ) = 1 / 2 := by norm_num [kd]
  have hkpp : ((kpPos : ℚ) : ℝ) = 3 / 2 := by norm_num [kpPos]
  simp only [lawC, lawI, lawD, lawE, lawVt] at hvt ⊢
  simp only [hα, hdt, hki, hkp, hkd, hkpp] at hvt hE hD hI hO ⊢
  set V := 3 / 2 * (sp - p) + vsp
  set E0 := E + 4886901 / 67108864 * (V - v - E)
  have e1 : E' - E0 = (E' - (E + 4886901 / 67108864 * (vt - v - E))) +
      4886901 / 67108864 * (vt - V) := by simp only [E0]; ring
  have wE : |E' - E0| ≤ 36 / 10 ^ 7 := by
    rw [e1]
    calc _ ≤ |E' - (E + 4886901 / 67108864 * (vt - v - E))| + |4886901 / 67108864 * (vt - V)| :=
          abs_add_le _ _
      _ ≤ 35 / 10 ^ 7 + 4886901 / 67108864 * (5 / 10 ^ 7) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4886901 / 67108864)]
          gcongr
      _ ≤ 36 / 10 ^ 7 := by norm_num
  set D0 := D + 4886901 / 67108864 * ((E0 - E) / (5368709 / 2147483648) - D)
  have e2 : D' - D0 = (D' - (D + 4886901 / 67108864 * ((E' - E) / (5368709 / 2147483648) - D))) +
      4886901 / 67108864 / (5368709 / 2147483648) * (E' - E0) := by simp only [D0]; ring
  have wD : |D' - D0| ≤ 23 / 10 ^ 5 := by
    rw [e2]
    calc _ ≤ |D' - (D + 4886901 / 67108864 * ((E' - E) / (5368709 / 2147483648) - D))| +
          |4886901 / 67108864 / (5368709 / 2147483648) * (E' - E0)| := abs_add_le _ _
      _ ≤ 12 / 10 ^ 5 + 4886901 / 67108864 / (5368709 / 2147483648) * (36 / 10 ^ 7) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4886901 / 67108864 / (5368709 / 2147483648))]
          gcongr
      _ ≤ 23 / 10 ^ 5 := by norm_num
  set I0 := I + 1 * (5368709 / 2147483648) * E0
  have e3 : I' - I0 = (I' - (I + 1 * (5368709 / 2147483648) * E')) +
      5368709 / 2147483648 * (E' - E0) := by simp only [I0]; ring
  have wI : |I' - I0| ≤ 61 / 10 ^ 8 := by
    rw [e3]
    calc _ ≤ |I' - (I + 1 * (5368709 / 2147483648) * E')| + |5368709 / 2147483648 * (E' - E0)| :=
          abs_add_le _ _
      _ ≤ 6 / 10 ^ 7 + 5368709 / 2147483648 * (36 / 10 ^ 7) := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5368709 / 2147483648)]
          gcongr
      _ ≤ 61 / 10 ^ 8 := by norm_num
  refine ⟨wE, wD, wI, ?_⟩
  have e4 : acc - (6 * E0 + I0 + 1 / 2 * D0 + asp) = (acc - (out + asp)) +
      (out - (6 * E' + I' + 1 / 2 * D')) + 6 * (E' - E0) + (I' - I0) + 1 / 2 * (D' - D0) := by ring
  rw [e4]
  have a1 := abs_add_le (acc - (out + asp) + (out - (6 * E' + I' + 1 / 2 * D')) + 6 * (E' - E0) +
    (I' - I0)) (1 / 2 * (D' - D0))
  have a2 := abs_add_le (acc - (out + asp) + (out - (6 * E' + I' + 1 / 2 * D')) + 6 * (E' - E0))
    (I' - I0)
  have a3 := abs_add_le (acc - (out + asp) + (out - (6 * E' + I' + 1 / 2 * D'))) (6 * (E' - E0))
  have a4 := abs_add_le (acc - (out + asp)) (out - (6 * E' + I' + 1 / 2 * D'))
  have m1 : |6 * (E' - E0)| ≤ 6 * (36 / 10 ^ 7) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]; gcongr
  have m2 : |1 / 2 * (D' - D0)| ≤ 1 / 2 * (23 / 10 ^ 5) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; gcongr
  have k : (6 / 10 ^ 6 + 3 / 2 / 10 ^ 5 + 6 * (36 / 10 ^ 7) + 61 / 10 ^ 8 +
    1 / 2 * (23 / 10 ^ 5) : ℝ) ≤ 16 / 10 ^ 5 := by norm_num
  linarith

/-- A finite value-`1` factor twice (`ahrsControlScaleXY`, `_ne_control_scale_factor`). -/
theorem scale2 {v : Vector2f.State} {a b : Float32} (ha : a.IsFinite) (ha1 : a.toReal = 1)
    (hb : b.IsFinite) (hb1 : b.toReal = 1) (hx : v.x.IsFinite) (hy : v.y.IsFinite) :
    let w := (Vector2f.op_mul_assign (Vector2f.op_mul_assign v a).1 b).1
    w.x.IsFinite ∧ w.x.toReal = v.x.toReal ∧ w.y.IsFinite ∧ w.y.toReal = v.y.toReal := by
  intro w
  have h1 := mul_one_val hx ha ha1
  have h2 := mul_one_val hy ha ha1
  have h3 := mul_one_val h1.1 hb hb1
  have h4 := mul_one_val h2.1 hb hb1
  exact ⟨h3.1, h3.2.trans h1.2, h4.1, h4.2.trans h2.2⟩

/-! ## The region and the specification -/

/-- The state of the velocity PID and the limit vector, as the region needs them. -/
structure PIDState (q : AC_PID_2D.State) (lim : Vector3f.State) : Prop where
  reset : q._reset_filter = false
  Ex : FB 4 q._error.x
  Ey : FB 4 q._error.y
  Dx : FB 64 q._derivative.x
  Dy : FB 64 q._derivative.y
  Ix : q._integrator.x.IsFinite
  Iy : q._integrator.y.IsFinite
  I9 : N2 q._integrator.x.toReal q._integrator.y.toReal ≤ 9
  limx : lim.x.IsFinite ∧ lim.x.toReal = 0
  limy : lim.y.IsFinite ∧ lim.y.toReal = 0

/-- The values one axis of the controller reads, as reals. -/
structure AxisIn where
  sp : ℝ
  p : ℝ
  vsp : ℝ
  v : ℝ
  E : ℝ
  D : ℝ
  I : ℝ
  asp : ℝ

/-- The north (`x`) and east (`y`) inputs of `NE_update_controller` from the state. -/
def axisX (s : State) : AxisIn :=
  ⟨s._pos_desired_ned_m.x.toReal, s._pos_estimate_ned_m.x.toReal, s._vel_desired_ned_ms.x.toReal,
    s._vel_estimate_ned_ms.x.toReal, s._pid_vel_ne_m._error.x.toReal,
    s._pid_vel_ne_m._derivative.x.toReal, s._pid_vel_ne_m._integrator.x.toReal,
    s._accel_desired_ned_mss.x.toReal⟩
def axisY (s : State) : AxisIn :=
  ⟨s._pos_desired_ned_m.y.toReal, s._pos_estimate_ned_m.y.toReal, s._vel_desired_ned_ms.y.toReal,
    s._vel_estimate_ned_ms.y.toReal, s._pid_vel_ne_m._error.y.toReal,
    s._pid_vel_ne_m._derivative.y.toReal, s._pid_vel_ne_m._integrator.y.toReal,
    s._accel_desired_ned_mss.y.toReal⟩

/-- The ideal command of one axis. -/
def AxisIn.c (a : AxisIn) : ℝ := lawC a.sp a.p a.vsp a.v a.E a.D a.I a.asp

/-- **The region of one call of `NE_update_controller`** (`HORIZONTAL.md` §7, D6, D7, D13). -/
structure NERegion (p : Params) (s : State) (inp : Inputs) : Prop where
  ekf : inp.get_position_NE_reset_count = s._ahrs_position_NE_reset_count
  active : NE_is_active s inp = true
  posg : PosGains p._p_pos_ne_m s._p_pos_ne_m
  velg : VelGains p._pid_vel_ne_m s._dt_s
  scXY : inp.get_control_gain_scaler_XY.IsFinite ∧ inp.get_control_gain_scaler_XY.toReal = 1
  sc : s._ne_control_scale_factor.IsFinite ∧ s._ne_control_scale_factor.toReal = 1
  dpx : s._disturb_pos_ne_m.x.IsFinite ∧ s._disturb_pos_ne_m.x.toReal = 0
  dpy : s._disturb_pos_ne_m.y.IsFinite ∧ s._disturb_pos_ne_m.y.toReal = 0
  dvx : s._disturb_vel_ne_ms.x.IsFinite ∧ s._disturb_vel_ne_ms.x.toReal = 0
  dvy : s._disturb_vel_ne_ms.y.IsFinite ∧ s._disturb_vel_ne_ms.y.toReal = 0
  off : OffZero (nS3 s inp)
  spx : s._pos_desired_ned_m.x.IsFinite
  spy : s._pos_desired_ned_m.y.IsFinite
  px : s._pos_estimate_ned_m.x.IsFinite
  py : s._pos_estimate_ned_m.y.IsFinite
  e : N2 (s._pos_desired_ned_m.x.toReal - s._pos_estimate_ned_m.x.toReal)
    (s._pos_desired_ned_m.y.toReal - s._pos_estimate_ned_m.y.toReal) ≤ 2 / 5
  vspx : FB 3 s._vel_desired_ned_ms.x
  vspy : FB 3 s._vel_desired_ned_ms.y
  vx : FB 4 s._vel_estimate_ned_ms.x
  vy : FB 4 s._vel_estimate_ned_ms.y
  aspx : FB 4 s._accel_desired_ned_mss.x
  aspy : FB 4 s._accel_desired_ned_mss.y
  pid : PIDState s._pid_vel_ne_m s._limit_vector_ned
  amax : (nAmax p s inp).IsFinite ∧ 1 / 2 ^ 20 ≤ (nAmax p s inp).toReal ∧
    (nAmax p s inp).toReal ≤ 2 ^ 40
  lim : N2 (axisX s).c (axisY s).c + 1 / 10 ^ 3 ≤ (nAmax p s inp).toReal * (1 - 1 / 2 ^ 20)

/-- One axis of `NE_update_controller` (`HORIZONTAL.md` §7): the velocity target, the PID rows and
the acceleration target, each against its real row. -/
def NEAxis (a : AxisIn) (vt E' D' I' out acc : Float32) : Prop :=
  A32 vt (lawVt a.sp a.p a.vsp) (5 / 10 ^ 7) ∧
  PIDAxis vt.toReal a.v a.E a.D a.I E' D' I' out ∧
  A32 acc (out.toReal + a.asp) (6 / 10 ^ 6)

theorem nS3_eq (s : State) (inp : Inputs) :
    (nS3 s inp)._p_pos_ne_m = s._p_pos_ne_m ∧ (nS3 s inp)._pid_vel_ne_m = s._pid_vel_ne_m ∧
    (nS3 s inp)._pos_desired_ned_m = s._pos_desired_ned_m ∧
    (nS3 s inp)._pos_estimate_ned_m = s._pos_estimate_ned_m ∧
    (nS3 s inp)._vel_desired_ned_ms = s._vel_desired_ned_ms ∧
    (nS3 s inp)._vel_estimate_ned_ms = s._vel_estimate_ned_ms ∧
    (nS3 s inp)._accel_desired_ned_mss = s._accel_desired_ned_mss ∧
    (nS3 s inp)._disturb_pos_ne_m = s._disturb_pos_ne_m ∧
    (nS3 s inp)._disturb_vel_ne_ms = s._disturb_vel_ne_ms ∧
    (nS3 s inp)._ne_control_scale_factor = s._ne_control_scale_factor ∧
    (nS3 s inp)._dt_s = s._dt_s ∧ (nS3 s inp)._limit_vector_ned = s._limit_vector_ned ∧
    (nS3 s inp)._angle_max_override_rad = s._angle_max_override_rad := by
  unfold nS3
  rw [off_p, off_pid, off_posd, off_pose, off_veld, off_vele, off_accd, off_dp, off_dv, off_sc,
    off_dt, off_lim, off_amo]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nAmax_eq (p : Params) (s : State) (inp : Inputs) : nAmax p (nS3 s inp) inp = nAmax p s inp := by
  unfold nAmax get_lean_angle_max_rad
  rw [(nS3_eq s inp).2.2.2.2.2.2.2.2.2.2.2.2]

end

end Contracts.Track.HCtl
