import Contracts.CopterZeroAtt
import AC_AttitudeControl.AC_PosControl

/-!
# Zero lemmas for `AC_PosControl` (horizontal channel)

- `pid2_update_all_Z`: `AC_PID_2D::update_all` at a zero target, a zero measurement and zero
  memory gives a zero output and keeps the memory at zero;
- `p2_update_all_Z`: `AC_P_2D::update_all` at a zero position error (formed in `double`, narrowed
  to `float`) keeps the target and outputs a zero velocity;
- `NE_update_offsets_Z`: the horizontal offsets stay at zero;
- `NE_update_controller_Z`: with zero horizontal position error, zero desired, estimated and offset
  velocities and accelerations, and the velocity PID at zero, the horizontal acceleration target is
  a zero, and the offsets, the velocity PID and the position-loop error stay at zero;
- `get_thrust_vector_Z`: the thrust vector is then `(±0, ±0, -GRAVITY_MSS)`;
- `calculate_yaw_and_rate_yaw_Z`: at zero desired velocity the yaw target is the attitude
  target's yaw and the yaw rate target is `0`.
-/

open Float.Model UnpackedFloat AP_Math AC_PosControl

namespace Contracts.CopterZero

/-! ## Vector helpers -/

theorem ZV2_default : ZV2 ({} : Vector2f) := ⟨Z_zero, Z_zero⟩

theorem ZV2_dot {a b : Vector2f} (ha : ZV2 a) (hb : b.x.IsFinite ∧ b.y.IsFinite) : Z (a * b) :=
  Z_add (Z_mul_left ha.1 hb.1) (Z_mul_left ha.2 hb.2)

theorem ZV2_mul_v {a : Vector2f} {k : Float32} (ha : ZV2 a) (hk : k.IsFinite) : ZV2 (a * k) :=
  ZV2_mul ha hk

theorem ZV2_is_nan {v : Vector2f} (hv : ZV2 v) : v.is_nan = false := by
  simp [Vector2f.is_nan, isNaN_false hv.1.1, isNaN_false hv.2.1]

theorem ZV2_is_inf {v : Vector2f} (hv : ZV2 v) : v.is_inf = false := by
  simp [Vector2f.is_inf, isInf_false hv.1.1, isInf_false hv.2.1]

/-- A finite `Vector2f`. -/
def FinV2 (v : Vector2f) : Prop := v.x.IsFinite ∧ v.y.IsFinite

/-! ## `AC_PID_2D` -/

/-- `AC_PID_2D` memory at zero. -/
def ZPID2 (s : AC_PID_2D.State) : Prop :=
  ZV2 s._target ∧ ZV2 s._error ∧ ZV2 s._derivative ∧ ZV2 s._integrator

/-- Finite gains and filter frequencies of magnitude at most `10³⁰`. -/
structure Pid2OK (p : AC_PID_2D.Params) : Prop where
  P : p.P.IsFinite
  I : p.I.IsFinite
  D : p.D.IsFinite
  FF : p.FF.IsFinite
  FLTE : p.FLTE.IsFinite
  FLTD : p.FLTD.IsFinite
  FLTEb : |p.FLTE.toReal| ≤ 1e30
  FLTDb : |p.FLTD.toReal| ≤ 1e30

theorem update_i2_Z (p : AC_PID_2D.Params) (hp : Pid2OK p) {s : AC_PID_2D.State} (hs : ZPID2 s)
    {dt : Float32} (hdt : dt.IsFinite) {limit : Vector2f} (hl : FinV2 limit) :
    ZPID2 (AC_PID_2D.update_i p s dt limit) := by
  unfold AC_PID_2D.update_i
  simp only [Id.run, pure]
  have hd : ZV2 ((s._error * p.I) * dt) := ZV2_mul (ZV2_mul hs.2.1 hp.I) hdt
  have hi : ZV2 (s._integrator + (s._error * p.I) * dt) := ZV2_add hs.2.2.2 hd
  have hc : is_positive (((s._error * p.I) * dt).dot limit) = false := is_positive_Z (ZV2_dot hd hl)
  simp only [hc, Bool.false_eq_true, if_false]
  rw [ZV2_limit_length hi]
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hi⟩

/-- **`AC_PID_2D::update_all` at zero**: zero output, memory stays at zero. -/
theorem pid2_update_all_Z (p : AC_PID_2D.Params) (hp : Pid2OK p) {s : AC_PID_2D.State}
    (hs : ZPID2 s) {target measurement : Vector2f} (ht : ZV2 target) (hm : ZV2 measurement)
    {dt : Float32} (hdt : dt.IsFinite) (hdtb : |dt.toReal| ≤ 1e30) {limit : Vector2f}
    (hl : FinV2 limit) :
    ZPID2 (AC_PID_2D.update_all p s target measurement dt limit).1 ∧
      ZV2 (AC_PID_2D.update_all p s target measurement dt limit).2 := by
  have hE : (AC_PID_2D.get_filt_E_alpha p dt).IsFinite := alpha_fin hdt hp.FLTE hdtb hp.FLTEb
  have hD : (AC_PID_2D.get_filt_D_alpha p dt).IsFinite := alpha_fin hdt hp.FLTD hdtb hp.FLTDb
  unfold AC_PID_2D.update_all
  simp only [Id.run, pure, ZV2_is_nan ht, ZV2_is_inf ht, ZV2_is_nan hm, ZV2_is_inf hm,
    Bool.or_false, Bool.false_eq_true, if_false]
  have tail : ∀ s1 : AC_PID_2D.State, ZPID2 s1 →
      ZV2 (s1._error * p.P + s1._integrator + s1._derivative * p.D + s1._target * p.FF) :=
    fun s1 h => ZV2_add (ZV2_add (ZV2_add (ZV2_mul h.2.1 hp.P) h.2.2.2) (ZV2_mul h.2.2.1 hp.D))
      (ZV2_mul h.1 hp.FF)
  split
  · have hU := update_i2_Z p hp (s := { s with
        _target := target, _error := target - measurement, _derivative := {},
        _reset_filter := false }) ⟨ht, ZV2_sub ht hm, ZV2_default, hs.2.2.2⟩ hdt hl
    generalize AC_PID_2D.update_i p _ dt limit = s1 at hU ⊢
    exact ⟨hU, tail s1 hU⟩
  · have hEr : ZV2 (s._error + ((target - measurement) - s._error) * AC_PID_2D.get_filt_E_alpha p dt) :=
      ZV2_add hs.2.1 (ZV2_mul (ZV2_sub (ZV2_sub ht hm) hs.2.1) hE)
    split
    · rename_i hpos
      have hdt0 := is_positive_ge hdt hpos
      have hne : dt.toReal ≠ 0 := by linarith [eps_pos]
      have hU := update_i2_Z p hp (s := { s with
          _target := target,
          _error := s._error + ((target - measurement) - s._error) * AC_PID_2D.get_filt_E_alpha p dt,
          _derivative := s._derivative + ((s._error + ((target - measurement) - s._error) *
            AC_PID_2D.get_filt_E_alpha p dt - s._error) / dt - s._derivative) *
            AC_PID_2D.get_filt_D_alpha p dt })
        ⟨ht, hEr, ZV2_add hs.2.2.1 (ZV2_mul (ZV2_sub (ZV2_div (ZV2_sub hEr hs.2.1) hdt hne)
          hs.2.2.1) hD), hs.2.2.2⟩ hdt hl
      generalize AC_PID_2D.update_i p _ dt limit = s1 at hU ⊢
      exact ⟨hU, tail s1 hU⟩
    · have hU := update_i2_Z p hp (s := { s with
          _target := target,
          _error := s._error + ((target - measurement) - s._error) * AC_PID_2D.get_filt_E_alpha p dt })
        ⟨ht, hEr, hs.2.2.1, hs.2.2.2⟩ hdt hl
      generalize AC_PID_2D.update_i p _ dt limit = s1 at hU ⊢
      exact ⟨hU, tail s1 hU⟩

/-! ## `AC_P_2D` -/

theorem sqrt_controller_xy_Z {e : Vector2f} (he : ZV2 e) (p sol dt : Float32) :
    ZV2 (sqrt_controller_xy e p sol dt) := by
  unfold sqrt_controller_xy
  simp only [is_positive_Z (ZV2_length he), Bool.not_false, if_true]
  exact ZV2_default

/-- `(a - b).tofloat` of two `Vector2p` whose components agree in value is the zero `Vector2f`. -/
theorem tofloat_sub_Z (C : ConvZero) {a b : Vector2p} (hx : ZD (a.x - b.x)) (hy : ZD (a.y - b.y)) :
    ZV2 (a - b).tofloat :=
  ⟨C.toFloat32_zero _ hx, C.toFloat32_zero _ hy⟩

/-- **`AC_P_2D::update_all` at zero error** keeps the target, stores a zero error, outputs a zero
velocity. -/
theorem p2_update_all_Z (p : AC_P_2D.Params) (s : AC_P_2D.State) {target measurement : Vector2p}
    (he : ZV2 (target - measurement).tofloat) :
    ZV2 (AC_P_2D.update_all p s target measurement).1._error ∧
      (AC_P_2D.update_all p s target measurement).2.1 = target ∧
      ZV2 (AC_P_2D.update_all p s target measurement).2.2 ∧
      (AC_P_2D.update_all p s target measurement).1._error_max = s._error_max ∧
      (AC_P_2D.update_all p s target measurement).1._D1_max = s._D1_max := by
  unfold AC_P_2D.update_all
  simp only [Id.run, pure]
  split
  · simp only [ZV2_limit_length he, ZV2_limit_length_snd he, Bool.false_eq_true, if_false]
    refine ⟨he, ?_, sqrt_controller_xy_Z he _ _ _, ?_, ?_⟩ <;> trivial
  · exact ⟨he, rfl, sqrt_controller_xy_Z he _ _ _, rfl, rfl⟩

theorem p2_update_all_ex (p : AC_P_2D.Params) (s : AC_P_2D.State) {target measurement : Vector2p}
    (he : ZV2 (target - measurement).tofloat) :
    ∃ s' : AC_P_2D.State, ∃ v : Vector2f,
      AC_P_2D.update_all p s target measurement = (s', target, v) ∧ ZV2 s'._error ∧ ZV2 v := by
  obtain ⟨h1, h2, h3, -, -⟩ := p2_update_all_Z p s he
  exact ⟨_, _, Prod.ext rfl (Prod.ext h2 rfl), h1, h3⟩

theorem pid2_update_all_ex (p : AC_PID_2D.Params) (hp : Pid2OK p) {s : AC_PID_2D.State}
    (hs : ZPID2 s) {target measurement : Vector2f} (ht : ZV2 target) (hm : ZV2 measurement)
    {dt : Float32} (hdt : dt.IsFinite) (hdtb : |dt.toReal| ≤ 1e30) {limit : Vector2f}
    (hl : FinV2 limit) :
    ∃ s' : AC_PID_2D.State, ∃ v : Vector2f,
      AC_PID_2D.update_all p s target measurement dt limit = (s', v) ∧ ZPID2 s' ∧ ZV2 v := by
  obtain ⟨h1, h2⟩ := pid2_update_all_Z p hp hs ht hm hdt hdtb hl
  exact ⟨_, _, rfl, h1, h2⟩

/-! ## Horizontal shaping helpers -/

theorem limit_accel_xy_Z {vn a : Vector2f} (hvn : ZV2 vn) (ha : ZV2 a) (m : Float32) :
    ZV2 (limit_accel_xy vn a m).1 := by
  unfold limit_accel_xy
  simp only []
  split
  · exact ha
  · split
    · exact ha
    · simp only [ZV2_limit_length ha, is_positive_Z (ZV2_length hvn), Bool.not_false, if_true]
      exact ha

theorem limit_accel_xy_ex {vn a : Vector2f} (hvn : ZV2 vn) (ha : ZV2 a) (m : Float32) :
    ∃ v : Vector2f, ∃ b : Bool, limit_accel_xy vn a m = (v, b) ∧ ZV2 v :=
  ⟨_, _, rfl, limit_accel_xy_Z hvn ha m⟩

theorem limit_accel_corner_xy_Z {v a : Vector2f} (hv : ZV2 v) (ha : ZV2 a) (m : Float32) :
    ZV2 (limit_accel_corner_xy v a m).1 := by
  unfold limit_accel_corner_xy
  simp only [ZV2_is_zero hv, if_true]
  split
  · exact ha
  · rw [ZV2_limit_length ha]; exact ha

theorem shape_accel_xy_Z {ad a : Vector2f} (had : ZV2 ad) (ha : ZV2 a) (j dt : Float32) :
    ZV2 (shape_accel_xy ad a j dt) := by
  unfold shape_accel_xy
  simp only [ZV2_limit_length (ZV2_sub had ha)]
  split
  · exact ha
  · split
    · exact ZV2_add ha (ZV2_sub had ha)
    · exact ha

/-- `update_pos_vel_accel_xy` with zero velocity and acceleration keeps a zero position and a zero
velocity (for `|dt| ≤ 10¹⁸`). -/
theorem update_pos_vel_accel_xy_Z (C : ConvZero) {pos : Vector2p} {vel accel : Vector2f}
    (hp : ZV2p pos) (hv : ZV2 vel) (ha : ZV2 accel) {dt : Float32} (hdt : dt.IsFinite)
    (hdtb : |dt.toReal| ≤ 1e18) (limit pos_error vel_error : Vector2f) :
    ZV2p (update_pos_vel_accel_xy pos vel accel dt limit pos_error vel_error).1 ∧
      ZV2 (update_pos_vel_accel_xy pos vel accel dt limit pos_error vel_error).2 := by
  have hsq : (AP_Math.sq dt).IsFinite :=
    fin_mul hdt hdt (by rw [abs_mul]; nlinarith [abs_nonneg dt.toReal])
  have hd : ZV2 (vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt) :=
    ZV2_add (ZV2_mul hv hdt) (ZV2_mul (ZV2_mul ha lit_half.1) hsq)
  have hdv : ZV2 (accel * dt) := ZV2_mul ha hdt
  unfold update_pos_vel_accel_xy update_vel_accel_xy
  simp only [ZV2_is_zero hdv, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false]
  have hdp : ZV2 (if (!is_zero limit.length_squared) = true then
      (if (is_positive ((vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt) * limit) &&
          is_positive (pos_error * limit)) = true then
        (vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt).zero
      else vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt)
      else vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt) := by
    split
    · split
      · exact ZV2_zero_lit
      · exact hd
    · exact hd
  generalize (if (!is_zero limit.length_squared) = true then
      (if (is_positive ((vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt) * limit) &&
          is_positive (pos_error * limit)) = true then
        (vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt).zero
      else vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt)
      else vel * dt + accel * (0.5 : Float32) * AP_Math.sq dt) = dp at hdp ⊢
  exact ⟨⟨ZD_add hp.1 (C.toFloat_zero _ hdp.1), ZD_add hp.2 (C.toFloat_zero _ hdp.2)⟩,
    ZV2_add hv hdv⟩

/-- `shape_pos_vel_accel_xy` at zero position error and zero velocities and accelerations returns
a zero acceleration (`|jerk_max| ≤ 10¹⁸`). -/
theorem shape_pos_vel_accel_xy_Z {pos_desired pos : Vector2p}
    {vel_desired accel_desired vel accel : Vector2f} {vel_max accel_max jerk_max dt : Float32}
    (hpe : ZV2 (pos_desired - pos).tofloat) (hvd : ZV2 vel_desired) (had : ZV2 accel_desired)
    (hv : ZV2 vel) (ha : ZV2 accel) (hamax : accel_max.IsFinite) (hj : jerk_max.IsFinite)
    (hjb : |jerk_max.toReal| ≤ 1e18) (limit_total : Bool) :
    ZV2 (shape_pos_vel_accel_xy pos_desired vel_desired accel_desired pos vel accel vel_max
      accel_max jerk_max dt limit_total) := by
  unfold shape_pos_vel_accel_xy
  simp only [is_positive_Z (ZV2_length hpe), Bool.false_eq_true, if_false]
  split
  · exact ha
  · rename_i hg
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hg
    obtain ⟨⟨-, hamp⟩, -⟩ := hg
    have ham0 := is_positive_ge hamax (by simpa using hamp)
    have he := eps_pos
    rw [eps_eq] at ham0
    have hampos : 0 < accel_max.toReal := by linarith
    have hk : (jerk_max / accel_max).IsFinite := by
      refine fin_div hj hamax hampos.ne' ?_
      rw [abs_div, abs_of_pos hampos, div_le_iff₀ hampos]; nlinarith
    have hvt : ZV2 (vel_desired + ({} : Vector2f)) := ZV2_add hvd ZV2_default
    have hvt' : ZV2 (if (limit_total && is_positive vel_max) = true then
        ((vel_desired + ({} : Vector2f)).limit_length vel_max).1 else vel_desired + ({} : Vector2f)) := by
      split
      · rw [ZV2_limit_length hvt]; exact hvt
      · exact hvt
    generalize (if (limit_total && is_positive vel_max) = true then
        ((vel_desired + ({} : Vector2f)).limit_length vel_max).1 else vel_desired + ({} : Vector2f)) = vt
      at hvt' ⊢
    have h1 := limit_accel_corner_xy_Z hv (ZV2_mul (ZV2_sub hvt' hv) hk) accel_max
    have h2 := ZV2_add h1 had
    have h3 : ZV2 (if limit_total = true then
        (((limit_accel_corner_xy vel ((vt - vel) * (jerk_max / accel_max)) accel_max).1 +
          accel_desired).limit_length accel_max).1
        else (limit_accel_corner_xy vel ((vt - vel) * (jerk_max / accel_max)) accel_max).1 +
          accel_desired) := by
      split
      · rw [ZV2_limit_length h2]; exact h2
      · exact h2
    exact shape_accel_xy_Z h3 ha _ _

/-! ## Offsets -/

/-- The six horizontal offset vectors (position, velocity, acceleration; target and current) are
zeros. -/
def OffZ (s : State) : Prop :=
  ZV2p s._pos_offset_target_ned_m.xy ∧ ZV2p s._pos_offset_ned_m.xy ∧
    ZV2 s._vel_offset_target_ned_ms.xy ∧ ZV2 s._vel_offset_ned_ms.xy ∧
    ZV2 s._accel_offset_target_ned_mss.xy ∧ ZV2 s._accel_offset_ned_mss.xy

/-- `NE_update_offsets` writes only the six offset vectors. -/
theorem NE_update_offsets_eq (s : State) (clock : Clock) :
    ∃ pt po : Vector3p, ∃ vt vo acct acco : Vector3f, NE_update_offsets s clock =
      { s with
        _pos_offset_target_ned_m := pt, _pos_offset_ned_m := po,
        _vel_offset_target_ned_ms := vt, _vel_offset_ned_ms := vo,
        _accel_offset_target_ned_mss := acct, _accel_offset_ned_mss := acco } := by
  unfold NE_update_offsets
  simp only [Id.run, pure]
  split <;> exact ⟨_, _, _, _, _, _, rfl⟩

theorem set_xy_xy_p (v : Vector3p) (w : Vector2p) : (v.set_xy w).xy = w := rfl
theorem set_xy_xy_f (v : Vector3f) (w : Vector2f) : (v.set_xy w).xy = w := rfl
theorem ZV2p_zero (v : Vector2p) : ZV2p v.zero := ⟨ZD_zero, ZD_zero⟩
theorem ZV2_zero (v : Vector2f) : ZV2 v.zero := ⟨Z_zero, Z_zero⟩

/-- **`NE_update_offsets` keeps zero offsets** (`|dt| ≤ 10¹⁸`, finite acceleration limit,
`|jerk| ≤ 10¹⁸`). -/
theorem NE_update_offsets_Z (C : ConvZero) (s : State) (clock : Clock) (h : OffZ s)
    (hdt : s._dt_s.IsFinite) (hdtb : |s._dt_s.toReal| ≤ 1e18)
    (hamax : s._accel_max_ne_mss.IsFinite) (hj : s._jerk_max_ne_msss.IsFinite)
    (hjb : |s._jerk_max_ne_msss.toReal| ≤ 1e18) : OffZ (NE_update_offsets s clock) := by
  obtain ⟨hpt, hpo, hvt, hvo, hat, hao⟩ := h
  unfold NE_update_offsets
  simp only [Id.run, pure, set_xy_xy_p, set_xy_xy_f]
  unfold OffZ
  split
  · simp only [set_xy_xy_p, set_xy_xy_f]
    have A := update_pos_vel_accel_xy_Z C (ZV2p_zero s._pos_offset_target_ned_m.xy)
      (ZV2_zero s._vel_offset_target_ned_ms.xy) (ZV2_zero s._accel_offset_target_ned_mss.xy) hdt hdtb
      {} {} {}
    have B := update_pos_vel_accel_xy_Z C hpo hvo hao hdt hdtb s._limit_vector_ned.xy
      (AC_P_2D.get_error s._p_pos_ne_m) (AC_PID_2D.get_error s._pid_vel_ne_m)
    exact ⟨A.1, B.1, A.2, B.2, ZV2_zero _,
      shape_pos_vel_accel_xy_Z (tofloat_sub_Z C (ZD_sub A.1.1 B.1.1) (ZD_sub A.1.2 B.1.2))
        A.2 (ZV2_zero _) B.2 hao hamax hj hjb false⟩
  · simp only [set_xy_xy_p, set_xy_xy_f]
    have A := update_pos_vel_accel_xy_Z C hpt hvt hat hdt hdtb {} {} {}
    have B := update_pos_vel_accel_xy_Z C hpo hvo hao hdt hdtb s._limit_vector_ned.xy
      (AC_P_2D.get_error s._p_pos_ne_m) (AC_PID_2D.get_error s._pid_vel_ne_m)
    exact ⟨A.1, B.1, A.2, B.2, hat,
      shape_pos_vel_accel_xy_Z (tofloat_sub_Z C (ZD_sub A.1.1 B.1.1) (ZD_sub A.1.2 B.1.2))
        A.2 hat B.2 hao hamax hj hjb false⟩

/-! ## Yaw target -/

/-- `calculate_yaw_and_rate_yaw` writes only the yaw target and the yaw rate target. -/
theorem calculate_yaw_and_rate_yaw_eq (s : State) (att : AttitudeControlInputs) :
    ∃ a b : Float32, calculate_yaw_and_rate_yaw s att =
      { s with _yaw_target_rad := a, _yaw_rate_target_rads := b } := by
  unfold calculate_yaw_and_rate_yaw
  simp only [Id.run, pure]
  split_ifs <;> exact ⟨_, _, rfl⟩

/-- **`calculate_yaw_and_rate_yaw` at zero desired velocity**: the yaw target is the attitude
target's yaw and the yaw rate target is `0`, for a finite `0 ≤ _vel_max_ne_ms ≤ 10³⁰`. -/
theorem calculate_yaw_and_rate_yaw_Z (s : State) (att : AttitudeControlInputs)
    (hv : ZV2 s._vel_desired_ned_ms.xy) (hvm : s._vel_max_ne_ms.IsFinite)
    (hvm0 : 0 ≤ s._vel_max_ne_ms.toReal) (hvmb : s._vel_max_ne_ms.toReal ≤ 1e30) :
    calculate_yaw_and_rate_yaw s att =
      { s with _yaw_target_rad := att.get_att_target_euler_rad.z, _yaw_rate_target_rads := 0 } := by
  have hl := ZV2_length hv
  obtain ⟨h5f, h50⟩ := lit_twentieth
  have hb : |s._vel_max_ne_ms.toReal * (0.05 : Float32).toReal| ≤ 1e38 := by
    have h51 : (0.05 : Float32).toReal ≤ 1 := by
      rw [(litPos (x := (0.05 : Float32)) (m := 13421773) (e := -28) (hm := by decide) (by rfl)).2]
      norm_num
    rw [abs_of_nonneg (by positivity)]; nlinarith
  have hm := fin_mul hvm h5f hb
  have hm0 := nonneg_mul hvm h5f hb (by positivity)
  have hc : ¬ (s._vel_desired_ned_ms.xy.length > s._vel_max_ne_ms * 0.05) := by
    show ¬ (_ < _)
    rw [lt_iff hm hl.1, hl.2]; linarith
  unfold calculate_yaw_and_rate_yaw
  simp only [Id.run, pure, is_positive_Z hl, Bool.false_eq_true, if_false, hc]

/-! ## The horizontal position controller -/

/-- Parameters and limits of the horizontal controller: finite, with `|dt|, |jerk| ≤ 10¹⁸`, the
velocity PID as `Pid2OK`, a finite limit vector and finite control scalers. -/
structure NEOK (p : Params) (s : State) (ahrs : AHRSInputs) : Prop where
  pid : Pid2OK p._pid_vel_ne_m
  dt : s._dt_s.IsFinite
  dtb : |s._dt_s.toReal| ≤ 1e18
  amax : s._accel_max_ne_mss.IsFinite
  jmax : s._jerk_max_ne_msss.IsFinite
  jmaxb : |s._jerk_max_ne_msss.toReal| ≤ 1e18
  vmax : s._vel_max_ne_ms.IsFinite
  lim : FinV2 s._limit_vector_ned.xy
  scale : ahrs.get_control_gain_scaler_XY.IsFinite
  nescale : s._ne_control_scale_factor.IsFinite

/-- What `NE_update_controller` establishes at the hover fixed point. -/
def NEConcl (r : State) : Prop :=
  ZV2 r._accel_target_ned_mss.xy ∧ OffZ r ∧ ZPID2 r._pid_vel_ne_m ∧ ZV2 r._p_pos_ne_m._error ∧
    ZV2 r._vel_target_ned_ms.xy

theorem calc_yaw_concl {r : State} (att : AttitudeControlInputs) (h : NEConcl r) :
    NEConcl (calculate_yaw_and_rate_yaw r att) := by
  obtain ⟨a, b, e⟩ := calculate_yaw_and_rate_yaw_eq r att
  rw [e]; exact h

/-- **`NE_update_controller` at zero horizontal error and zero velocities.** If the controller ran
on the previous tick (`NE_is_active`), the offsets are zeros, the desired horizontal position equals
the estimate (in value, both finite), the desired, estimated velocities and the desired
acceleration are zeros and the velocity PID memory is at zero, then the horizontal acceleration
target is a zero, and the offsets, the velocity PID memory, the position-loop error and the
velocity target stay at zero (`NEConcl`). -/
theorem NE_update_controller_Z (C : ConvZero) (p : Params) (s : State) (ahrs : AHRSInputs)
    (att : AttitudeControlInputs) (clock : Clock) (h : NEOK p s ahrs)
    (hact : NE_is_active s clock = true) (hoff : OffZ s)
    (hpdx : s._pos_desired_ned_m.x.IsFinite) (hpdy : s._pos_desired_ned_m.y.IsFinite)
    (hpex : s._pos_estimate_ned_m.x.IsFinite) (hpey : s._pos_estimate_ned_m.y.IsFinite)
    (hpx : s._pos_desired_ned_m.x.toReal = s._pos_estimate_ned_m.x.toReal)
    (hpy : s._pos_desired_ned_m.y.toReal = s._pos_estimate_ned_m.y.toReal)
    (hvd : ZV2 s._vel_desired_ned_ms.xy) (hve : ZV2 s._vel_estimate_ned_ms.xy)
    (had : ZV2 s._accel_desired_ned_mss.xy) (hpid : ZPID2 s._pid_vel_ne_m) :
    NEConcl (NE_update_controller p s ahrs att clock) := by
  unfold NE_update_controller
  simp (config := {zeta := false}) only [Id.run, pure]
  extract_lets s0 sc dz jpf jpm si
  simp (config := {zeta := false}) only [s0, hact, Bool.not_true, Bool.false_eq_true, if_false, jpm]
  extract_lets s1 s2 s3 cp comb sA sB vt2 vt1 vt0 sC vtne sD cv1 cv0 sE at2 at1 at0 sF sG atne sH
    amax accmax sI jpv vn
  -- the offsets
  obtain ⟨pt, po, vt, vo, acct, acco, hoffeq⟩ := NE_update_offsets_eq s1 clock
  have hoffZ : OffZ s2 := NE_update_offsets_Z C s1 clock hoff h.dt h.dtb h.amax h.jmax h.jmaxb
  have e2 : s2 = _ := hoffeq
  clear_value s2
  subst e2
  have hpt : ZV2p pt.xy := hoffZ.1
  have hpo : ZV2p po.xy := hoffZ.2.1
  have hvo : ZV2 vo.xy := hoffZ.2.2.2.1
  have hao : ZV2 acco.xy := hoffZ.2.2.2.2.2
  -- the position loop: zero error
  have hd0 : ZD (Vector2f.topostype dz).x := C.toFloat_zero _ Z_zero
  have hd1 : ZD (Vector2f.topostype dz).y := C.toFloat_zero _ Z_zero
  have hex : ZD (s3._pos_target_ned_m.xy - comb).x := by
    have a1 : ((s._pos_desired_ned_m.xy + po.xy).x).IsFinite ∧
        ((s._pos_desired_ned_m.xy + po.xy).x).toReal = s._pos_desired_ned_m.x.toReal :=
      add_ZD_right hpdx hpo.1
    have a2 : ((s._pos_estimate_ned_m.xy + Vector2f.topostype dz).x).IsFinite ∧
        ((s._pos_estimate_ned_m.xy + Vector2f.topostype dz).x).toReal = s._pos_estimate_ned_m.x.toReal :=
      add_ZD_right hpex hd0
    exact ZD_sub_eq (a := (s._pos_desired_ned_m.xy + po.xy).x)
      (b := (s._pos_estimate_ned_m.xy + Vector2f.topostype dz).x) a1.1 a2.1 (a1.2.trans (hpx.trans a2.2.symm))
  have hey : ZD (s3._pos_target_ned_m.xy - comb).y := by
    have a1 : ((s._pos_desired_ned_m.xy + po.xy).y).IsFinite ∧
        ((s._pos_desired_ned_m.xy + po.xy).y).toReal = s._pos_desired_ned_m.y.toReal :=
      add_ZD_right hpdy hpo.2
    have a2 : ((s._pos_estimate_ned_m.xy + Vector2f.topostype dz).y).IsFinite ∧
        ((s._pos_estimate_ned_m.xy + Vector2f.topostype dz).y).toReal = s._pos_estimate_ned_m.y.toReal :=
      add_ZD_right hpey hd1
    exact ZD_sub_eq (a := (s._pos_desired_ned_m.xy + po.xy).y)
      (b := (s._pos_estimate_ned_m.xy + Vector2f.topostype dz).y) a1.1 a2.1 (a1.2.trans (hpy.trans a2.2.symm))
  have hE : ZV2 (s3._pos_target_ned_m.xy - comb).tofloat :=
    ⟨C.toFloat32_zero _ hex, C.toFloat32_zero _ hey⟩
  have EP := p2_update_all_Z p._p_pos_ne_m s3._p_pos_ne_m hE
  have hpe : ZV2 sA._p_pos_ne_m._error := EP.1
  have hvt2 : ZV2 vt2 := EP.2.2.1
  -- the velocity loop
  have hvtne : ZV2 vtne := ZV2_add (ZV2_mul (ZV2_mul hvt2 h.scale) h.nescale) (ZV2_add hvd hvo)
  have hVT : ZV2 sD._vel_target_ned_ms.xy := hvtne
  have hVE : ZV2 cv0 := ZV2_add hve ZV2_default
  have FP := pid2_update_all_Z _ h.pid (s := sD._pid_vel_ne_m) hpid hVT hVE (dt := sD._dt_s) h.dt
    (h.dtb.trans (by norm_num)) (limit := sD._limit_vector_ned.xy) h.lim
  have hpid' : ZPID2 sE._pid_vel_ne_m := FP.1
  have hat2 : ZV2 at2 := FP.2
  have hatne : ZV2 atne := ZV2_add (ZV2_mul (ZV2_mul hat2 h.scale) h.nescale)
    (ZV2_add had hao)
  have hAT : ZV2 sI._accel_target_ned_mss.xy := hatne
  have fin : ∀ v : Vector2f, ZV2 v → NEConcl (jpv () v) := by
    intro v hv
    simp only [jpv, jpf]
    split <;> exact calc_yaw_concl att
      ⟨limit_accel_xy_Z hv hAT accmax, hoffZ, hpid', hpe, hvtne⟩
  split
  · rename_i hvp
    have hv0 := is_positive_ge h.vmax hvp
    exact fin vn (ZV2_div hvd h.vmax (by linarith [eps_pos]))
  · exact fin dz ZV2_default

/-- **The thrust vector at hover**: with a zero horizontal acceleration target,
`get_thrust_vector` is `(±0, ±0, -GRAVITY_MSS)`. -/
theorem get_thrust_vector_Z (s : State) (h : ZV2 s._accel_target_ned_mss.xy) :
    Z (get_thrust_vector s).x ∧ Z (get_thrust_vector s).y ∧
      (get_thrust_vector s).z = -GRAVITY_MSS :=
  ⟨h.1, h.2, rfl⟩

/-- The desired attitude computed from the position controller's thrust vector at hover is the
identity (`NE_update_controller_Z`, `get_thrust_vector_Z`, `attitude_from_thrust_vector_Id`). -/
theorem hover_desired_attitude_Id (L : LibmZero32) (s : State) (h : ZV2 s._accel_target_ned_mss.xy)
    {heading : Float32} (hh : Z heading) :
    IdQ (AC_AttitudeControl.attitude_from_thrust_vector (get_thrust_vector s) heading) := by
  obtain ⟨hx, hy, hz⟩ := get_thrust_vector_Z s h
  exact attitude_from_thrust_vector_Id L hx hy hz hh

end Contracts.CopterZero
