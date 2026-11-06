import Contracts.Track.Induction.Pieces
import Contracts.Track.Frame

/-!
# M9: the tick glue (C15, C16)

The glue between the per-tick lemmas of the other milestones and `Vehicle.tick` of the run
(`run w₀ x t`). Sections:

* **the navigator's calls** (`NavGlue`): `update_wpnav` as the speed checks (`uwPre`), the advance
  along the track and the `NE_update_controller` event; the log of the advance
  (`set_pos_terrain_target_D_m 0`, `set_pos_vel_accel_NED_m P V A`); the frames of the track
  scaler; `vel_dt_scalar = 1` (`velDt_one`, kept by `offvel_step`); the S-curve step;
* **the horizontal offsets stay zero** (`OffZero`): `offZ_offsets`, `offZero_of_offZ`,
  `offZ_NE_update`, `offZ_D_update` and the setters;
* **the tick in calls** (`TickSplit`): `tick_split_first`, `tick_eq_wp_run`, `replayPos_push`,
  `navW_steady`;
* **pacing** (`Pace`): the definitions `scRun`, `rRun`, `qRun` and the fields `pace_*`;
* **the horizontal and vertical glue** (`NEGlue`, `VGlue`);
* **the first tick** (`init`).
-/

namespace Contracts.Track.Induction.TG

/-! ## The navigator's calls -/

section NavGlue

open AC_WPNav_lib AC_WPNav Contracts.Mission


/-- The speed checks at the start of `update_wpnav` (`AC_WPNav.cpp:715-731`). -/
def uwPre (p : Params) (s : State) (inp : Inputs) : State × Outputs := Id.run do
  let mut s := s
  let mut o : Outputs := #[]
  if s._check_wp_speed_change then
    if !(AC_WPNav_lib.is_equal_float2 p._wp_speed_ms s._last_wp_speed_ms) then
      let (t'1, t'2) := set_speed_NE_ms p s o inp (get_default_speed_NE_ms p)
      s := t'1
      o := t'2
      s := { s with _last_wp_speed_ms := p._wp_speed_ms }
  if !(AC_WPNav_lib.is_equal_float2 p._wp_speed_up_ms s._last_wp_speed_up_ms) then
    let (t'3, t'4) := set_speed_up_ms p s o inp (get_default_speed_up_ms p)
    s := t'3
    o := t'4
    s := { s with _last_wp_speed_up_ms := p._wp_speed_up_ms }
  if !(AC_WPNav_lib.is_equal_float2 p._wp_speed_down_ms s._last_wp_speed_down_ms) then
    let (t'5, t'6) := set_speed_down_ms p s o inp (get_default_speed_down_ms p)
    s := t'5
    o := t'6
    s := { s with _last_wp_speed_down_ms := p._wp_speed_down_ms }
  return (s, o)

/-- The result of `advance_wp_target_along_track` inside `update_wpnav`. -/
abbrev uwAdv (p : Params) (s : State) (inp : Inputs) : State × Outputs × Bool :=
  advance_wp_target_along_track p (uwPre p s inp).1 (uwPre p s inp).2 inp
    (inp.get_dt_s (uwPre p s inp).2)

set_option maxHeartbeats 1000000 in
/-- **`update_wpnav` split**: the speed checks (`uwPre`), then the advance along the track, then
the `NE_update_controller` event and the update time. -/
theorem update_wpnav_eq (p : Params) (s : State) (inp : Inputs) :
    (update_wpnav p s #[] inp).1 = { (uwAdv p s inp).1 with _wp_last_update_ms := inp.millis } ∧
    (update_wpnav p s #[] inp).2.1 = (uwAdv p s inp).2.1.push Output.NE_update_controller := by
  unfold update_wpnav uwAdv uwPre
  simp only [Id.run]
  split <;> (try split) <;> split <;> split <;> (try split) <;> exact ⟨rfl, rfl⟩

/-- No speed-change branch of `update_wpnav` is taken. -/
def SpeedSteady (p : Params) (s : State) : Prop :=
  (s._check_wp_speed_change = false ∨
      AC_WPNav_lib.is_equal_float2 p._wp_speed_ms s._last_wp_speed_ms = true) ∧
    AC_WPNav_lib.is_equal_float2 p._wp_speed_up_ms s._last_wp_speed_up_ms = true ∧
    AC_WPNav_lib.is_equal_float2 p._wp_speed_down_ms s._last_wp_speed_down_ms = true

theorem uwPre_steady {p : Params} {s : State} (inp : Inputs) (h : SpeedSteady p s) :
    uwPre p s inp = (s, #[]) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold uwPre
  rcases h1 with h1 | h1 <;> simp [Id.run, h1, h2, h3]

section TrackFrames

theorem utl_track (p : Params) (s : State) (o : Outputs) (inp : Inputs) :
    (update_track_with_speed_accel_limits p s o inp)._track_dt_scalar = s._track_dt_scalar ∧
    (update_track_with_speed_accel_limits p s o inp)._is_terrain_alt = s._is_terrain_alt := by
  unfold update_track_with_speed_accel_limits
  simp only [Id.run]
  split <;> split <;> exact ⟨rfl, rfl⟩

theorem set_speed_NE_track (p : Params) (s : State) (o : Outputs) (inp : Inputs) (v : Float32) :
    (set_speed_NE_ms p s o inp v).1._track_dt_scalar = s._track_dt_scalar ∧
    (set_speed_NE_ms p s o inp v).1._is_terrain_alt = s._is_terrain_alt := by
  unfold set_speed_NE_ms
  simp only [Id.run]
  split
  · exact utl_track _ _ _ _
  · exact ⟨rfl, rfl⟩

theorem set_speed_up_track (p : Params) (s : State) (o : Outputs) (inp : Inputs) (v : Float32) :
    (set_speed_up_ms p s o inp v).1._track_dt_scalar = s._track_dt_scalar ∧
    (set_speed_up_ms p s o inp v).1._is_terrain_alt = s._is_terrain_alt := by
  unfold set_speed_up_ms
  exact utl_track _ _ _ _

theorem set_speed_down_track (p : Params) (s : State) (o : Outputs) (inp : Inputs) (v : Float32) :
    (set_speed_down_ms p s o inp v).1._track_dt_scalar = s._track_dt_scalar ∧
    (set_speed_down_ms p s o inp v).1._is_terrain_alt = s._is_terrain_alt := by
  unfold set_speed_down_ms
  exact utl_track _ _ _ _

theorem uwPre_track (p : Params) (s : State) (inp : Inputs) :
    (uwPre p s inp).1._track_dt_scalar = s._track_dt_scalar ∧
    (uwPre p s inp).1._is_terrain_alt = s._is_terrain_alt := by
  unfold uwPre
  simp only [Id.run]
  split <;> (try split) <;> (try split) <;> (try split) <;>
    simp only [pure, set_speed_NE_track, set_speed_up_track, set_speed_down_track, and_self]

end TrackFrames

/-- The log of one advance: the terrain target, then the three targets. -/
def IsLog (o x : Outputs) : Prop :=
  ∃ P V A, x = (o.push (Output.set_pos_terrain_target_D_m 0.0)).push (Output.set_pos_vel_accel_NED_m P V A)

theorem isLog_ite {o a b : Outputs} {c : Prop} [Decidable c] (ha : IsLog o a) (hb : IsLog o b) :
    IsLog o (if c then a else b) := by
  split
  · exact ha
  · exact hb

set_option maxHeartbeats 2000000 in
/-- **The log of `advance_wp_target_along_track`** without terrain following: the terrain target
`0` and the new position, velocity and acceleration targets, and the call succeeds. -/
theorem advance_log (p : Params) (s : State) (o : Outputs) (inp : Inputs) (dt : Float32)
    (hT : s._is_terrain_alt = false) :
    (∃ P V A, (advance_wp_target_along_track p s o inp dt).2.1 =
      (o.push (Output.set_pos_terrain_target_D_m 0.0)).push (Output.set_pos_vel_accel_NED_m P V A)) ∧
    (advance_wp_target_along_track p s o inp dt).2.2 = true := by
  unfold advance_wp_target_along_track
  simp only [hT, Id.run, Bool.false_eq_true, ite_false]
  simp only [Contracts.Mission.id_pure_eq, apply_ite (fun r : State × Outputs × Bool => r.2.1),
    apply_ite (fun r : State × Outputs × Bool => r.2.2), ite_self]
  refine ⟨?_, trivial⟩
  show IsLog o _
  repeat' (first | exact ⟨_, _, _, rfl⟩ | apply isLog_ite)

/-! ## The navigator's initialisation and new destinations -/

/-- `wp_and_spline_init_m` resets the scaler to `1`, terrain following off, the offset speed to the
desired speed, the offset acceleration to `(float) 0.0`, not paused, and the update time. -/
theorem wp_init_fields (p : Params) (s : State) (o : Outputs) (inp : Inputs) (v : Float32)
    (sp : AC_WPNav_lib.Vector3p.State) :
    (wp_and_spline_init_m p s o inp v sp).2.1._track_dt_scalar = 1.0 ∧
    (wp_and_spline_init_m p s o inp v sp).2.1._is_terrain_alt = false ∧
    (wp_and_spline_init_m p s o inp v sp).2.1._offset_vel_ms =
      (wp_and_spline_init_m p s o inp v sp).2.1._wp_desired_speed_ne_ms ∧
    (wp_and_spline_init_m p s o inp v sp).2.1._offset_accel_mss = Float.toFloat32 0.0 ∧
    (wp_and_spline_init_m p s o inp v sp).2.1._paused = false ∧
    (wp_and_spline_init_m p s o inp v sp).2.1._wp_last_update_ms = inp.millis := by
  unfold wp_and_spline_init_m
  simp only [Id.run]
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fields of the navigator a new destination leaves alone when it does not re-initialise. -/
structure DestFrame (s t : State) : Prop where
  track : t._track_dt_scalar = s._track_dt_scalar
  ovel : t._offset_vel_ms = s._offset_vel_ms
  oacc : t._offset_accel_mss = s._offset_accel_mss
  dspd : t._wp_desired_speed_ne_ms = s._wp_desired_speed_ne_ms
  paused : t._paused = s._paused
  upd : t._wp_last_update_ms = s._wp_last_update_ms

set_option maxHeartbeats 2000000 in
/-- **`set_wp_destination_NED_m` without re-initialisation** (the navigator active and the last
destination reached): the scaler and the offset speed are unchanged, terrain following stays off,
and the call succeeds. -/
theorem set_dest_frame (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (d : AC_WPNav_lib.Vector3p.State) (ha : is_active s inp = true)
    (hr : (s._flags.reached_destination != 0) = true) (hT : s._is_terrain_alt = false) :
    DestFrame s (set_wp_destination_NED_m p s o inp d).2.1 ∧
      (set_wp_destination_NED_m p s o inp d).2.1._is_terrain_alt = false ∧
      (set_wp_destination_NED_m p s o inp d).2.2.1 = o ∧
      (set_wp_destination_NED_m p s o inp d).1 = p := by
  unfold set_wp_destination_NED_m
  simp only [Id.run, ha, hr, hT, Bool.not_true, Bool.or_self, Bool.false_eq_true, ite_false,
    beq_self_eq_true, ite_true]
  repeat' split
  all_goals exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩

set_option maxHeartbeats 2000000 in
/-- `set_wp_destination_next_NED_m` leaves the scaler and the offsets alone. -/
theorem set_dest_next_frame (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (d : AC_WPNav_lib.Vector3p.State) :
    DestFrame s (set_wp_destination_next_NED_m p s o inp d).1 ∧
      (set_wp_destination_next_NED_m p s o inp d).1._is_terrain_alt = s._is_terrain_alt := by
  unfold set_wp_destination_next_NED_m
  simp only [Id.run]
  repeat' split
  all_goals exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-! ## `vel_dt_scalar` and the offset speed -/

section Zero

open Contracts.Mission

/-- A finite float of value `0`. -/
def Z (x : Float32) : Prop := x.IsFinite ∧ x.toReal = 0

theorem Z_lit : Z (0.0 : Float32) := ⟨f32_isFinite_0p0, f32_toReal_0p0⟩

theorem Z_toF32 (hL : LibmSpec) : Z (Float.toFloat32 (0.0 : Float)) := by
  obtain ⟨h1, h2⟩ := hL.f64ToF32_exact 0.0 0.0 f64_isFinite_0p0 f32_isFinite_0p0
    (by rw [f64_toReal_0p0, f32_toReal_0p0])
  exact ⟨h1, by rw [h2, f64_toReal_0p0]⟩

theorem f32_div_exact' {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (hb0 : b.toReal ≠ 0) (h : a.toReal / b.toReal = f.toReal) :
    (a / b).IsFinite ∧ (a / b).toReal = f.toReal := by
  have hm : |a.toReal / b.toReal| ≤ Float.Model.UnpackedFloat.maxFinite32 :=
    h ▸ _root_.Float32.abs_toReal_le_maxFinite f
  obtain ⟨b1, b2⟩ := _root_.Float32.div_bracket ha hb hb0 hm hf
  exact ⟨(_root_.Float32.div_err_all ha hb hb0 hm).1, le_antisymm (b2 h.le) (b1 h.symm.le)⟩

theorem Z_mul_left {a b : Float32} (ha : Z a) (hb : b.IsFinite) : Z (a * b) := by
  obtain ⟨h1, h2⟩ := Float32.mul_exact ha.1 hb f32_isFinite_0p0
    (by rw [ha.2, zero_mul, f32_toReal_0p0])
  exact ⟨h1, by rw [h2, f32_toReal_0p0]⟩

theorem Z_mul_right {a b : Float32} (ha : a.IsFinite) (hb : Z b) : Z (a * b) := by
  obtain ⟨h1, h2⟩ := Float32.mul_exact ha hb.1 f32_isFinite_0p0
    (by rw [hb.2, mul_zero, f32_toReal_0p0])
  exact ⟨h1, by rw [h2, f32_toReal_0p0]⟩

theorem Z_add {a b : Float32} (ha : Z a) (hb : Z b) : Z (a + b) := by
  obtain ⟨h1, h2⟩ := Float32.add_exact ha.1 hb.1 f32_isFinite_0p0
    (by rw [ha.2, hb.2, add_zero, f32_toReal_0p0])
  exact ⟨h1, by rw [h2, f32_toReal_0p0]⟩

theorem Z_sub_self {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : a.toReal = b.toReal) :
    Z (a - b) := by
  obtain ⟨h1, h2⟩ := Float32.sub_exact ha hb f32_isFinite_0p0 (by rw [h, sub_self, f32_toReal_0p0])
  exact ⟨h1, by rw [h2, f32_toReal_0p0]⟩

theorem Z_div {a b : Float32} (ha : Z a) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0) : Z (a / b) := by
  obtain ⟨h1, h2⟩ := f32_div_exact' ha.1 hb f32_isFinite_0p0 hb0
    (by rw [ha.2, zero_div, f32_toReal_0p0])
  exact ⟨h1, by rw [h2, f32_toReal_0p0]⟩

theorem Z_neg {a : Float32} (ha : Z a) : Z (-a) :=
  ⟨(Float32.isFinite_neg a).2 ha.1, by rw [Float32.toReal_neg, ha.2, neg_zero]⟩

theorem Z_abs {a : Float32} (ha : Z a) : Z (Float32.abs a) :=
  ⟨(Float32.isFinite_abs a).2 ha.1, by rw [Float32.toReal_abs, ha.2, abs_zero]⟩

/-- The clamp keeps a zero inside bounds around zero. -/
theorem Z_cvl {a lo hi : Float32} (ha : Z a) (hlo : lo.IsFinite) (hhi : hi.IsFinite)
    (h1 : lo.toReal ≤ 0) (h2 : 0 ≤ hi.toReal) : Z (Float32.cvl a lo hi) := by
  unfold Float32.cvl
  rw [ite_eq_right (by rw [Float32.not_isNaN_of_isFinite ha.1]; decide)]
  rw [ite_eq_right (fun h => by have := (Float32.lt_iff_toReal_lt ha.1 hlo).1 h; linarith [ha.2]),
    ite_eq_right (fun h => by have := (Float32.lt_iff_toReal_lt hhi ha.1).1 h; linarith [ha.2])]
  exact ha

theorem isPos_false {x : Float32} (hx : x.IsFinite) (h : x.toReal ≤ 0) :
    AC_WPNav_lib.is_positive_float x = false := by
  have : ¬ ((1.1920929e-7 : Float32) ≤ x) := by
    rw [Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, f32_toReal_1p1920929Em7]
    linarith
  simp [AC_WPNav_lib.is_positive_float, this]

theorem isPos_pos {x : Float32} (hx : x.IsFinite) (h : AC_WPNav_lib.is_positive_float x = true) :
    1 / 8388608 ≤ x.toReal := by
  have h' : (1.1920929e-7 : Float32) ≤ x := by simpa [AC_WPNav_lib.is_positive_float] using h
  rw [Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, f32_toReal_1p1920929Em7] at h'
  exact h'

end Zero

/-- `vel_dt_scalar` of `advance_wp_target_along_track` (`AC_WPNav.cpp:593-600`): the offset speed
after its update, over the desired speed, or `1` without a desired speed. -/
def velDt (s : State) (dt : Float32) : Float32 :=
  if AC_WPNav_lib.is_positive_float s._wp_desired_speed_ne_ms then
    AC_WPNav_lib.update_vel_accel s._offset_vel_ms s._offset_accel_mss dt
      (Float.toFloat32 (0.0 : Float)) (Float.toFloat32 (0.0 : Float)) / s._wp_desired_speed_ne_ms
  else Float.toFloat32 (1.0 : Float)

/-- The offset speed at the desired speed, the offset acceleration zero (the state
`wp_and_spline_init_m` leaves, kept by every advance: `offvel_step`). -/
structure OffVel (s : State) : Prop where
  pos : AC_WPNav_lib.is_positive_float s._wp_desired_speed_ne_ms = true
  dfin : s._wp_desired_speed_ne_ms.IsFinite
  vfin : s._offset_vel_ms.IsFinite
  vval : s._offset_vel_ms.toReal = s._wp_desired_speed_ne_ms.toReal
  acc : Z s._offset_accel_mss

/-- `update_vel_accel` with zero acceleration and zero limit keeps the speed. -/
theorem uva_zero (hL : LibmSpec) {v a dt : Float32} (hv : v.IsFinite) (ha : Z a)
    (hdt : dt.IsFinite) :
    (AC_WPNav_lib.update_vel_accel v a dt (Float.toFloat32 (0.0 : Float))
        (Float.toFloat32 (0.0 : Float))).IsFinite ∧
      (AC_WPNav_lib.update_vel_accel v a dt (Float.toFloat32 (0.0 : Float))
        (Float.toFloat32 (0.0 : Float))).toReal = v.toReal := by
  have z0 := Z_toF32 hL
  have hd : Z (a * dt) := Z_mul_left ha hdt
  have hc : AC_WPNav_lib.is_positive_float (a * dt * Float.toFloat32 (0.0 : Float)) = false :=
    isPos_false (Z_mul_left hd z0.1).1 (Z_mul_left hd z0.1).2.le
  unfold AC_WPNav_lib.update_vel_accel
  simp only [Id.run, hc, Bool.false_and, Bool.false_eq_true, ite_false]
  exact Float32.add_zero_val hv hd.1 hd.2

/-- **`vel_dt_scalar = 1`** on `OffVel`. -/
theorem velDt_one (hL : LibmSpec) {s : State} {dt : Float32} (h : OffVel s) (hdt : dt.IsFinite) :
    (velDt s dt).IsFinite ∧ (velDt s dt).toReal = 1 := by
  obtain ⟨u1, u2⟩ := uva_zero hL h.vfin h.acc hdt
  have hd0 : s._wp_desired_speed_ne_ms.toReal ≠ 0 := by
    have := isPos_pos h.dfin h.pos; intro e; rw [e] at this; norm_num at this
  unfold velDt
  rw [ite_eq_left h.pos]
  obtain ⟨d1, d2⟩ := f32_div_exact' u1 h.dfin Contracts.Mission.f32_isFinite_1p0 hd0
    (by rw [u2, h.vval, div_self hd0, Contracts.Mission.f32_toReal_1p0])
  exact ⟨d1, by rw [d2, Contracts.Mission.f32_toReal_1p0]⟩

section ShapeZero

open Float.Model UnpackedFloat

theorem big_le_max : (10 : ℝ) ^ 12 ≤ maxFinite32 := by
  rw [Float32.maxFinite32_eq]; norm_num

/-- A product of finite floats of moderate size: finite, its sign bounds. -/
theorem mul_sign {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hm : |a.toReal * b.toReal| ≤ 10 ^ 12) :
    (a * b).IsFinite ∧ (0 ≤ a.toReal * b.toReal → 0 ≤ (a * b).toReal) ∧
      (a.toReal * b.toReal ≤ 0 → (a * b).toReal ≤ 0) := by
  have hm' := hm.trans big_le_max
  have br := Float32.mul_bracket ha hb hm' f32_isFinite_0p0
  rw [f32_toReal_0p0] at br
  exact ⟨(Float32.mul_err_all ha hb hm').1, br.1, br.2⟩

theorem div_sign {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hm : |a.toReal / b.toReal| ≤ 10 ^ 12) :
    (a / b).IsFinite ∧ (0 ≤ a.toReal / b.toReal → 0 ≤ (a / b).toReal) := by
  have hm' := hm.trans big_le_max
  have br := Float32.div_bracket ha hb hb0 hm' f32_isFinite_0p0
  rw [f32_toReal_0p0] at br
  exact ⟨(Float32.div_err_all ha hb hb0 hm').1, br.1⟩

theorem isZero_false {x : Float32} (hx : x.IsFinite) (h : 1 / 4096 ≤ |x.toReal|) :
    AC_WPNav_lib.is_zero_float x = false := by
  have : ¬ (Float32.abs x < (1.1920929e-7 : Float32)) := by
    rw [Float32.lt_iff_toReal_lt ((Float32.isFinite_abs x).2 hx) f32_isFinite_1p1920929Em7,
      Float32.toReal_abs, f32_toReal_1p1920929Em7]
    linarith
  simp [AC_WPNav_lib.is_zero_float, this]

/-- `sqrt_controller` of a zero error is zero (gain in `[1/4096, 4096]`, limit in `(0, 1000]`). -/
theorem sqrtc_zero {e p sec dt : Float32} (he : Z e) (hp : p.IsFinite)
    (hp1 : 1 / 4096 ≤ p.toReal) (hp2 : p.toReal ≤ 4096) (hs : sec.IsFinite)
    (hs1 : 0 ≤ sec.toReal) (hs2 : sec.toReal ≤ 1000) (hdt : dt.IsFinite) :
    Z (AC_WPNav_lib.sqrt_controller_float4 e p sec dt) := by
  have hep : Z (e * p) := Z_mul_left he hp
  have hz : AC_WPNav_lib.is_zero_float p = false :=
    isZero_false hp (by rw [abs_of_pos (by linarith)]; exact hp1)
  -- `sq p`
  have hpp : |p.toReal * p.toReal| ≤ 10 ^ 12 := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  obtain ⟨ppf, pp0, -⟩ := mul_sign hp hp hpp
  have pperr := (Float32.mul_err_all hp hp (hpp.trans big_le_max)).2
  have pplo : 1 / 10 ^ 8 ≤ (p * p).toReal := by
    rw [abs_of_nonneg (mul_self_nonneg p.toReal)] at pperr
    have h1 : (1 / 4096) ^ 2 ≤ p.toReal * p.toReal := by nlinarith
    have h2 : (2 : ℝ) ^ (-24 : ℤ) ≤ 1 / 10 ^ 7 := by norm_num
    have h3 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 10 ^ 40 := by norm_num
    have h4 : (2 : ℝ) ^ (-24 : ℤ) * (p.toReal * p.toReal) ≤ 1 / 10 ^ 7 * (p.toReal * p.toReal) :=
      mul_le_mul_of_nonneg_right h2 (mul_self_nonneg _)
    generalize (2 : ℝ) ^ (-24 : ℤ) * (p.toReal * p.toReal) = T at pperr h4
    generalize (2 : ℝ) ^ (-150 : ℤ) = U at pperr h3
    generalize p.toReal * p.toReal = X at pperr h1 h4
    have := (abs_le.1 pperr).1
    linarith
  have hld : |sec.toReal / (p * p).toReal| ≤ 10 ^ 12 := by
    rw [abs_of_nonneg (div_nonneg hs1 (by linarith)), div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨ldf, ld0⟩ := div_sign hs ppf (by linarith) hld
  have ld0' := ld0 (div_nonneg hs1 (by linarith))
  have c1 : ¬ (e > sec / AC_WPNav_lib.sq_float p) := by
    intro h
    have := (Float32.lt_iff_toReal_lt ldf he.1).1 h
    rw [he.2] at this; exact absurd ld0' (not_le.2 this)
  have c2 : ¬ (e < -(sec / AC_WPNav_lib.sq_float p)) := by
    intro h
    have := (Float32.lt_iff_toReal_lt he.1 ((Float32.isFinite_neg _).2 ldf)).1 h
    rw [he.2, Float32.toReal_neg] at this
    change 0 < -(sec / (p * p)).toReal at this
    linarith
  unfold AC_WPNav_lib.sqrt_controller_float4
  simp only [Id.run, hz, Bool.false_eq_true, ite_false, c1, c2]
  have fin : AC_WPNav_lib.is_positive_float dt = true →
      Z (AC_WPNav_lib.constrain_value_line_float (e * p) (-(Float32.abs e) / dt) (Float32.abs e / dt)
        (Int32.toUInt32 606)) := by
    intro hpos
    have h0 : dt.toReal ≠ 0 := by
      have := isPos_pos hdt hpos; intro h; rw [h] at this; norm_num at this
    have l := Z_div (Z_neg (Z_abs he)) hdt h0
    have u := Z_div (Z_abs he) hdt h0
    rw [Contracts.Track.FloatLib.wpnav_cvl]
    exact Z_cvl hep l.1 u.1 l.2.le u.2.ge
  split <;> split <;> rename_i h <;> first | exact fin h | exact hep

/-- `shape_accel` towards zero from zero stays zero. -/
theorem shape_accel_zero {ad a J dt : Float32} (had : Z ad) (ha : Z a) (hJ : J.IsFinite)
    (hJ0 : 0 ≤ J.toReal) (hJ1 : J.toReal ≤ 1000) (hdt : dt.IsFinite) (hdt0 : 0 ≤ dt.toReal)
    (hdt1 : dt.toReal ≤ 1000) : Z (AC_WPNav_lib.shape_accel ad a J dt) := by
  have hm1 : |(-J).toReal * dt.toReal| ≤ 10 ^ 12 := by
    rw [Float32.toReal_neg, abs_mul, abs_neg, abs_of_nonneg hJ0, abs_of_nonneg hdt0]; nlinarith
  have hm2 : |J.toReal * dt.toReal| ≤ 10 ^ 12 := by
    rw [abs_mul, abs_of_nonneg hJ0, abs_of_nonneg hdt0]; nlinarith
  obtain ⟨lf, -, l0⟩ := mul_sign ((Float32.isFinite_neg J).2 hJ) hdt hm1
  obtain ⟨uf, u0, -⟩ := mul_sign hJ hdt hm2
  have l0' := l0 (by rw [Float32.toReal_neg]; nlinarith)
  have u0' := u0 (by nlinarith)
  have hd : Z (ad - a) := Z_sub_self had.1 ha.1 (by rw [had.2, ha.2])
  unfold AC_WPNav_lib.shape_accel
  simp only [Id.run]
  split
  · exact ha
  · split
    · rw [Contracts.Track.FloatLib.wpnav_cvl]
      exact Z_add ha (Z_cvl hd lf uf l0' u0')
    · exact ha

/-- **`shape_vel_accel` at zero velocity error from zero acceleration** gives zero acceleration
(the navigator's offset speed: `AC_WPNav.cpp:596`). -/
theorem shape_vel_accel_zero {vd ad v a amin amax J dt : Float32} (lim : Bool)
    (hvd : vd.IsFinite) (hv : v.IsFinite) (hvv : vd.toReal = v.toReal) (had : Z ad) (ha : Z a)
    (hmin : amin.IsFinite) (hmax : amax.IsFinite) (hmm : amin.toReal = -amax.toReal)
    (hA0 : 1 / 10 ≤ amax.toReal) (hA1 : amax.toReal ≤ 100) (hJ : J.IsFinite)
    (hJ0 : 1 / 10 ≤ J.toReal) (hJ1 : J.toReal ≤ 100) (hdt : dt.IsFinite) (hdt0 : 0 ≤ dt.toReal)
    (hdt1 : dt.toReal ≤ 1) :
    Z (AC_WPNav_lib.shape_vel_accel vd ad v a amin amax J dt lim) := by
  have he : Z (vd - v) := Z_sub_self hvd hv hvv
  have hpe : AC_WPNav_lib.is_positive_float (vd - v) = false := isPos_false he.1 he.2.le
  have hnm : (-amin).IsFinite := (Float32.isFinite_neg _).2 hmin
  have hnmv : (-amin).toReal = amax.toReal := by rw [Float32.toReal_neg, hmm, neg_neg]
  have hq : |J.toReal / (-amin).toReal| ≤ 10 ^ 12 := by
    rw [hnmv, abs_of_nonneg (div_nonneg (by linarith) (by linarith)), div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨kf, kerr⟩ := Float32.div_err_all hJ hnm (by rw [hnmv]; linarith) (hq.trans big_le_max)
  have kr1 : 1 / 1000 ≤ J.toReal / (-amin).toReal := by
    rw [hnmv, le_div_iff₀ (by linarith)]; nlinarith
  have kr2 : J.toReal / (-amin).toReal ≤ 1000 := by
    rw [hnmv, div_le_iff₀ (by linarith)]; nlinarith
  have k1 : 1 / 4096 ≤ (J / -amin).toReal ∧ (J / -amin).toReal ≤ 4096 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ J.toReal / (-amin).toReal)] at kerr
    have h2 : (2 : ℝ) ^ (-24 : ℤ) ≤ 1 / 10 ^ 7 := by norm_num
    have h3 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 10 ^ 40 := by norm_num
    have h4 : (2 : ℝ) ^ (-24 : ℤ) * (J.toReal / (-amin).toReal) ≤
        1 / 10 ^ 7 * (J.toReal / (-amin).toReal) := mul_le_mul_of_nonneg_right h2 (by linarith)
    generalize (2 : ℝ) ^ (-24 : ℤ) * (J.toReal / (-amin).toReal) = T at kerr h4
    generalize (2 : ℝ) ^ (-150 : ℤ) = U at kerr h3
    generalize J.toReal / (-amin).toReal = X at kerr kr1 kr2 h4
    have := abs_le.1 kerr
    constructor <;> linarith
  have hs := sqrtc_zero he kf k1.1 k1.2 hJ (by linarith) (by linarith) hdt (dt := dt)
  have c1 : Z (AC_WPNav_lib.constrain_value_line_float
      (AC_WPNav_lib.sqrt_controller_float4 (vd - v) (J / -amin) J dt) amin amax (Int32.toUInt32 211)) := by
    rw [Contracts.Track.FloatLib.wpnav_cvl]; exact Z_cvl hs hmin hmax (by linarith) (by linarith)
  have c2 := Z_add c1 had
  unfold AC_WPNav_lib.shape_vel_accel
  simp only [Id.run, hpe, Bool.false_eq_true, ite_false]
  split
  · exact ha
  · split
    · rw [Contracts.Track.FloatLib.wpnav_cvl]
      exact shape_accel_zero (Z_cvl c2 hmin hmax (by linarith) (by linarith)) ha hJ (by linarith)
        (by linarith) hdt hdt0 (by linarith)
    · exact shape_accel_zero c2 ha hJ (by linarith) (by linarith) hdt hdt0 (by linarith)

end ShapeZero

set_option maxHeartbeats 4000000 in
/-- **The offset speed inside `advance_wp_target_along_track`** (no terrain following, a positive
desired speed): the offset speed is updated by its acceleration, the offset acceleration is shaped
towards the desired speed times the terrain scaler. -/
theorem advance_offsets (p : Params) (s : State) (o : Outputs) (inp : Inputs) (dt : Float32)
    (hT : s._is_terrain_alt = false)
    (hpos : AC_WPNav_lib.is_positive_float s._wp_desired_speed_ne_ms = true) :
    (advance_wp_target_along_track p s o inp dt).1._wp_desired_speed_ne_ms =
        s._wp_desired_speed_ne_ms ∧
      (advance_wp_target_along_track p s o inp dt).1._paused = s._paused ∧
      (advance_wp_target_along_track p s o inp dt).1._offset_vel_ms =
        AC_WPNav_lib.update_vel_accel s._offset_vel_ms s._offset_accel_mss dt
          (Float.toFloat32 (0.0 : Float)) (Float.toFloat32 (0.0 : Float)) ∧
      (advance_wp_target_along_track p s o inp dt).1._offset_accel_mss =
        AC_WPNav_lib.shape_vel_accel
          (if !s._paused then
            s._wp_desired_speed_ne_ms * inp.terrain_scaler_D_m o (0.0 : Float32) (get_terrain_margin_m p)
           else Float.toFloat32 (0.0 : Float))
          (Float.toFloat32 (0.0 : Float))
          (AC_WPNav_lib.update_vel_accel s._offset_vel_ms s._offset_accel_mss dt
            (Float.toFloat32 (0.0 : Float)) (Float.toFloat32 (0.0 : Float)))
          s._offset_accel_mss (-(get_wp_acceleration_mss p)) (get_wp_acceleration_mss p)
          (inp.get_shaping_jerk_NE_msss (Pacing.scalerLog o)) dt true := by
  unfold advance_wp_target_along_track
  simp only [hT, hpos, Id.run, Bool.false_eq_true, ite_false, ite_true]
  simp only [Contracts.Mission.id_pure_eq,
    apply_ite (fun r : State × Outputs × Bool => r.1._wp_desired_speed_ne_ms),
    apply_ite (fun r : State × Outputs × Bool => r.1._paused),
    apply_ite (fun r : State × Outputs × Bool => r.1._offset_vel_ms),
    apply_ite (fun r : State × Outputs × Bool => r.1._offset_accel_mss), ite_self]
  all_goals refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first | trivial | rfl

/-- **`OffVel` is kept by `advance_wp_target_along_track`** (not paused, the terrain scaler `1`,
the course's acceleration and jerk, a period in `[0, 1]`): so `vel_dt_scalar = 1` on every tick
(`velDt_one`). -/
theorem offvel_step (hL : Contracts.Mission.LibmSpec) {p : Params} {s : State} {o : Outputs}
    {inp : Inputs} {dt : Float32} (h : OffVel s) (hT : s._is_terrain_alt = false)
    (hP : s._paused = false)
    (hsc : (inp.terrain_scaler_D_m o (0.0 : Float32) (get_terrain_margin_m p)).IsFinite ∧
      (inp.terrain_scaler_D_m o (0.0 : Float32) (get_terrain_margin_m p)).toReal = 1)
    (hA : (get_wp_acceleration_mss p).IsFinite ∧ 1 / 10 ≤ (get_wp_acceleration_mss p).toReal ∧
      (get_wp_acceleration_mss p).toReal ≤ 100)
    (hJ : (inp.get_shaping_jerk_NE_msss (Pacing.scalerLog o)).IsFinite ∧
      1 / 10 ≤ (inp.get_shaping_jerk_NE_msss (Pacing.scalerLog o)).toReal ∧
      (inp.get_shaping_jerk_NE_msss (Pacing.scalerLog o)).toReal ≤ 100)
    (hdt : dt.IsFinite) (hdt0 : 0 ≤ dt.toReal) (hdt1 : dt.toReal ≤ 1) :
    OffVel (advance_wp_target_along_track p s o inp dt).1 := by
  obtain ⟨e1, -, e3, e4⟩ := advance_offsets p s o inp dt hT h.pos
  obtain ⟨u1, u2⟩ := uva_zero hL h.vfin h.acc hdt
  obtain ⟨m1, m2⟩ := Float32.mul_exact h.dfin hsc.1 h.dfin (by rw [hsc.2, mul_one])
  have hvin : (if !s._paused then
      s._wp_desired_speed_ne_ms * inp.terrain_scaler_D_m o (0.0 : Float32) (get_terrain_margin_m p)
      else Float.toFloat32 (0.0 : Float)) =
      s._wp_desired_speed_ne_ms * inp.terrain_scaler_D_m o (0.0 : Float32) (get_terrain_margin_m p) := by
    simp [hP]
  rw [hvin] at e4
  refine ⟨by rw [e1]; exact h.pos, by rw [e1]; exact h.dfin, by rw [e3]; exact u1,
    by rw [e3, u2, h.vval, e1], ?_⟩
  rw [e4]
  exact shape_vel_accel_zero true m1 u1 (by rw [m2, u2, h.vval]) (Z_toF32 hL) h.acc
    ((Float32.isFinite_neg _).2 hA.1) hA.1 (by rw [Float32.toReal_neg]) hA.2.1 hA.2.2 hJ.1 hJ.2.1
    hJ.2.2 hdt hdt0 hdt1

/-- `wp_and_spline_init_m` establishes `OffVel` (the desired speed finite and positive). -/
theorem offvel_init (hL : Contracts.Mission.LibmSpec) (p : Params) (s : State) (o : Outputs)
    (inp : Inputs) (v : Float32) (sp : AC_WPNav_lib.Vector3p.State)
    (hd : (wp_and_spline_init_m p s o inp v sp).2.1._wp_desired_speed_ne_ms.IsFinite)
    (hp : AC_WPNav_lib.is_positive_float
      (wp_and_spline_init_m p s o inp v sp).2.1._wp_desired_speed_ne_ms = true) :
    OffVel (wp_and_spline_init_m p s o inp v sp).2.1 := by
  obtain ⟨-, -, h3, h4, -, -⟩ := wp_init_fields p s o inp v sp
  exact ⟨hp, hd, by rw [h3]; exact hd, by rw [h3], by rw [h4]; exact Z_toF32 hL⟩

theorem OffVel.of_frame {s t : State} (h : OffVel s) (hf : DestFrame s t) : OffVel t := by
  obtain ⟨_, h2, h3, h4, _, _⟩ := hf
  exact ⟨h4 ▸ h.pos, h4 ▸ h.dfin, h2 ▸ h.vfin, by rw [h2, h4]; exact h.vval, h3 ▸ h.acc⟩

set_option maxHeartbeats 4000000 in
/-- **The S-curve step** (`AC_WPNav.cpp:631`): on a straight leg the S-curve is advanced by the new
filtered scaler times `vel_dt_scalar` times `dt`. -/
theorem advance_scurve (p : Params) (s : State) (o : Outputs) (inp : Inputs) (dt : Float32)
    (hT : s._is_terrain_alt = false) (hsp : s._this_leg_is_spline = false) :
    (advance_wp_target_along_track p s o inp dt).1._scurve_this_leg =
      (SCurve.advance_target_along_track s._scurve_this_leg s._scurve_prev_leg s._scurve_next_leg
        p._wp_radius_m (get_corner_acceleration_mss p) (s._flags.fast_waypoint != 0)
        ((s._track_dt_scalar + (Pacing.rawScaler (Pacing.curTargetVel inp (Pacing.scalerLog o))
            (inp.get_pos_error_NED_m (Pacing.scalerLog o))
            (inp.get_vel_estimate_NED_ms (Pacing.scalerLog o))
            (inp.NE_get_pos_p_kP (Pacing.scalerLog o)) - s._track_dt_scalar) *
            (dt / Pacing.trackTc p)) * velDt s dt * dt)
        s._origin_ned_m AC_WPNav_lib.Vector3f.init_void AC_WPNav_lib.Vector3f.init_void).1 := by
  unfold advance_wp_target_along_track
  simp only [hT, hsp, Id.run, Bool.false_eq_true, ite_false, ite_true, Bool.not_false]
  simp only [Contracts.Mission.id_pure_eq,
    apply_ite (fun r : State × Outputs × Bool => r.1._scurve_this_leg), ite_self]
  unfold Pacing.rawScaler Pacing.trackTc velDt Pacing.curTargetVel Pacing.scalerLog
  split_ifs <;> rfl

/-- The same with the step written through the new scaler (`advance_track_dt_scalar`). -/
theorem advance_scurve' (p : Params) (s : State) (o : Outputs) (inp : Inputs) (dt : Float32)
    (hT : s._is_terrain_alt = false) (hsp : s._this_leg_is_spline = false) :
    (advance_wp_target_along_track p s o inp dt).1._scurve_this_leg =
      (SCurve.advance_target_along_track s._scurve_this_leg s._scurve_prev_leg s._scurve_next_leg
        p._wp_radius_m (get_corner_acceleration_mss p) (s._flags.fast_waypoint != 0)
        ((advance_wp_target_along_track p s o inp dt).1._track_dt_scalar * velDt s dt * dt)
        s._origin_ned_m AC_WPNav_lib.Vector3f.init_void AC_WPNav_lib.Vector3f.init_void).1 := by
  rw [Pacing.advance_track_dt_scalar p s o inp dt hT]
  exact advance_scurve p s o inp dt hT hsp

/-- **`update_wpnav` on a steady tick** (speeds unchanged, no terrain following): the state is the
advance's with the update time, the log is the terrain target `0`, the three targets, and one
`NE_update_controller`. -/
theorem update_wpnav_steady {p : Params} {s : State} (inp : Inputs) (h : SpeedSteady p s)
    (hT : s._is_terrain_alt = false) :
    (update_wpnav p s #[] inp).1 =
        { (advance_wp_target_along_track p s #[] inp (inp.get_dt_s #[])).1 with
          _wp_last_update_ms := inp.millis } ∧
      ∃ P V A, (update_wpnav p s #[] inp).2.1 =
        ((((#[] : Outputs).push (Output.set_pos_terrain_target_D_m 0.0)).push
          (Output.set_pos_vel_accel_NED_m P V A)).push Output.NE_update_controller) := by
  obtain ⟨e1, e2⟩ := update_wpnav_eq p s inp
  have hu := uwPre_steady inp h
  simp only [uwAdv, hu] at e1 e2
  obtain ⟨⟨P, V, A, hl⟩, -⟩ := advance_log p s #[] inp (inp.get_dt_s #[]) hT
  exact ⟨e1, P, V, A, by rw [e2, hl]⟩


end NavGlue

/-! ## The horizontal offsets stay zero -/

noncomputable section OffZeroSec

open AC_PosControl_lib Contracts.Quick Float.Model UnpackedFloat
open Contracts.Track.HCtl
open Contracts.Mission hiding isPos_iff isZero_iff


/-! ## Zero floats -/

/-- A finite `float` of value `0` (either sign). -/
def Z32 (x : Float32) : Prop := x.IsFinite ∧ x.toReal = 0
/-- A finite `double` of value `0` (either sign). -/
def Z64 (x : Float) : Prop := x.IsFinite ∧ x.toReal = 0

theorem Z32.lit : Z32 (0.0 : Float32) := ⟨Float32.isFinite_lit_zero, by simp⟩
theorem Z32.int : Z32 (Int32.toFloat32 (0 : Int32)) := ⟨Float32.isFinite_int32_zero, by simp⟩

theorem Z64.lit : Z64 (0.0 : Float) := ⟨Float.isFinite_lit_zero, by simp⟩
theorem f64_unpack_int32_zero' : (Int32.toFloat (0 : Int32)).toModel.unpack = .zero .positive := by
  f32_unpack
theorem Z64.int : Z64 (Int32.toFloat (0 : Int32)) :=
  ⟨Float.isFinite_of_unpack_zero f64_unpack_int32_zero',
    Float.toReal_of_unpack_zero f64_unpack_int32_zero'⟩

theorem Z32.add {a b : Float32} (ha : Z32 a) (hb : Z32 b) : Z32 (a + b) := by
  obtain ⟨h1, h2⟩ := Float32.add_zero_val ha.1 hb.1 hb.2
  exact ⟨h1, h2.trans ha.2⟩
theorem Z32.sub {a b : Float32} (ha : Z32 a) (hb : Z32 b) : Z32 (a - b) := by
  obtain ⟨h1, h2⟩ := Float32.sub_zero_val ha.1 hb.1 hb.2
  exact ⟨h1, h2.trans ha.2⟩
theorem Z32.mul_r {a b : Float32} (ha : Z32 a) (hb : b.IsFinite) : Z32 (a * b) := by
  have := Float32.mul_exact ha.1 hb ha.1 (by rw [ha.2, zero_mul])
  exact ⟨this.1, this.2.trans ha.2⟩
theorem Z32.mul_l {a b : Float32} (ha : a.IsFinite) (hb : Z32 b) : Z32 (a * b) :=
  Float32.mul_zero_val ha hb.1 hb.2
theorem Z32.neg {a : Float32} (ha : Z32 a) : Z32 (-a) :=
  ⟨(Float32.isFinite_neg _).2 ha.1, by rw [Float32.toReal_neg, ha.2, neg_zero]⟩
theorem Z32.abs {a : Float32} (ha : Z32 a) : Z32 (Float32.abs a) :=
  ⟨(Float32.isFinite_abs a).2 ha.1, by rw [Float32.toReal_abs, ha.2, abs_zero]⟩
theorem Z32.div {a b : Float32} (ha : Z32 a) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0) : Z32 (a / b) := by
  have hq : |a.toReal / b.toReal| ≤ maxFinite32 := by
    rw [ha.2, zero_div, abs_zero]; exact (abs_nonneg _).trans (Float32.abs_toReal_le_maxFinite 0)
  obtain ⟨b1, b2⟩ := Float32.div_bracket ha.1 hb hb0 hq ha.1
  refine ⟨(Float32.div_err_all ha.1 hb hb0 hq).1, le_antisymm ?_ ?_⟩
  · rw [← ha.2]; exact b2 (by rw [ha.2, zero_div])
  · rw [← ha.2]; exact b1 (by rw [ha.2, zero_div])
theorem Z32.sqrt {a : Float32} (ha : Z32 a) : Z32 (Float32.sqrt a) := by
  have h0 : 0 ≤ a.toReal := ha.2.ge
  have h1 : a.toReal ≤ maxFinite32 := by rw [ha.2]; exact (abs_nonneg _).trans (Float32.abs_toReal_le_maxFinite 0)
  obtain ⟨b1, b2⟩ := Float32.sqrt_bracket ha.1 h0 h1 ha.1
  refine ⟨(Float32.sqrt_err_all ha.1 h0 h1).1, le_antisymm ?_ ?_⟩
  · rw [← ha.2]; exact b2 (by rw [ha.2, Real.sqrt_zero])
  · rw [← ha.2]; exact b1 (by rw [ha.2, Real.sqrt_zero])
theorem Z32.toFloat (hL : LibmSpec) {a : Float32} (ha : Z32 a) : Z64 (Float32.toFloat a) := by
  obtain ⟨h1, h2⟩ := hL.f32ToF64 a ha.1
  exact ⟨h1, h2.trans ha.2⟩
theorem Z64.toFloat32 (hL : LibmSpec) {a : Float} (ha : Z64 a) : Z32 (Float.toFloat32 a) := by
  obtain ⟨h1, h2⟩ := hL.f64ToF32_exact a (0.0 : Float32) ha.1 Float32.isFinite_lit_zero
    (by rw [ha.2]; simp)
  exact ⟨h1, h2.trans ha.2⟩
theorem Z64.add {a b : Float} (ha : Z64 a) (hb : Z64 b) : Z64 (a + b) := by
  obtain ⟨h1, h2⟩ := F64.add_zero_val ha.1 hb.1 hb.2
  exact ⟨h1, h2.trans ha.2⟩
theorem Z64.sub {a b : Float} (ha : Z64 a) (hb : Z64 b) : Z64 (a - b) := by
  have hm : |a.toReal - b.toReal| ≤ maxFinite := by
    rw [ha.2, hb.2, sub_zero, abs_zero]; exact (abs_nonneg _).trans (Float.abs_toReal_le_maxFinite 0)
  obtain ⟨b1, b2⟩ := Float.sub_bracket ha.1 hb.1 hm ha.1
  refine ⟨(Float.sub_err_all ha.1 hb.1 hm).1, le_antisymm ?_ ?_⟩
  · rw [← ha.2]; exact b2 (by rw [ha.2, hb.2, sub_zero])
  · rw [← ha.2]; exact b1 (by rw [ha.2, hb.2, sub_zero])

theorem Z32.not_pos {a : Float32} (ha : Z32 a) : is_positive_float a = false := by
  rcases h : is_positive_float a
  · rfl
  · have := (isPos_iff ha.1).1 h
    rw [ha.2] at this
    exact absurd this (not_le.2 (zpow_pos (by norm_num) _))
theorem Z32.is_zero {a : Float32} (ha : Z32 a) : is_zero_float a = true :=
  (isZero_iff ha.1).2 (by rw [ha.2, abs_zero]; exact zpow_pos (by norm_num) _)

/-! ## Zero vectors -/

abbrev ZV (v : AC_PosControl_lib.Vector2f.State) : Prop := Z32 v.x ∧ Z32 v.y
abbrev ZP (v : AC_PosControl_lib.Vector2p.State) : Prop := Z64 v.x ∧ Z64 v.y

theorem ZV.add {a b : AC_PosControl_lib.Vector2f.State} (ha : ZV a) (hb : ZV b) : ZV (AC_PosControl_lib.Vector2f.op_add a b) :=
  ⟨ha.1.add hb.1, ha.2.add hb.2⟩
theorem ZV.sub {a b : AC_PosControl_lib.Vector2f.State} (ha : ZV a) (hb : ZV b) : ZV (AC_PosControl_lib.Vector2f.op_sub_Vector2f a b) :=
  ⟨ha.1.sub hb.1, ha.2.sub hb.2⟩
theorem ZV.add_assign {a b : AC_PosControl_lib.Vector2f.State} (ha : ZV a) (hb : ZV b) :
    ZV (AC_PosControl_lib.Vector2f.op_add_assign a b).1 := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
theorem ZV.mul {a : AC_PosControl_lib.Vector2f.State} (ha : ZV a) {c : Float32} (hc : c.IsFinite) :
    ZV (AC_PosControl_lib.Vector2f.op_mul_float a c) := ⟨ha.1.mul_r hc, ha.2.mul_r hc⟩
theorem ZV.zero (a : AC_PosControl_lib.Vector2f.State) : ZV (AC_PosControl_lib.Vector2f.zero a) := ⟨Z32.int, Z32.int⟩
theorem ZV.init_void : ZV AC_PosControl_lib.Vector2f.init_void := ⟨Z32.int, Z32.int⟩
theorem ZV.todouble (hL : LibmSpec) {a : AC_PosControl_lib.Vector2f.State} (ha : ZV a) : ZP (AC_PosControl_lib.Vector2f.todouble a) :=
  ⟨ha.1.toFloat hL, ha.2.toFloat hL⟩
theorem ZP.tofloat (hL : LibmSpec) {a : AC_PosControl_lib.Vector2p.State} (ha : ZP a) : ZV (AC_PosControl_lib.Vector2p.tofloat a) :=
  ⟨ha.1.toFloat32 hL, ha.2.toFloat32 hL⟩
theorem ZP.sub {a b : AC_PosControl_lib.Vector2p.State} (ha : ZP a) (hb : ZP b) : ZP (AC_PosControl_lib.Vector2p.op_sub_Vector2p a b) :=
  ⟨ha.1.sub hb.1, ha.2.sub hb.2⟩
theorem ZP.add_assign {a b : AC_PosControl_lib.Vector2p.State} (ha : ZP a) (hb : ZP b) :
    ZP (AC_PosControl_lib.Vector2p.op_add_assign a b).1 := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
theorem ZP.zero (a : AC_PosControl_lib.Vector2p.State) : ZP (AC_PosControl_lib.Vector2p.zero a) := ⟨Z64.int, Z64.int⟩
theorem ZV.length {a : AC_PosControl_lib.Vector2f.State} (ha : ZV a) : Z32 (AC_PosControl_lib.Vector2f.length a) :=
  ((ha.1.mul_r ha.1.1).add (ha.2.mul_r ha.2.1)).sqrt
theorem ZV.is_zero {a : AC_PosControl_lib.Vector2f.State} (ha : ZV a) : AC_PosControl_lib.Vector2f.is_zero a = true := by
  simp [AC_PosControl_lib.Vector2f.is_zero, Id.run, ha.1.is_zero, ha.2.is_zero]
theorem ZV.limit_length {a : AC_PosControl_lib.Vector2f.State} (ha : ZV a) (m : Float32) :
    AC_PosControl_lib.Vector2f.limit_length a m = (a, false) := by
  simp [AC_PosControl_lib.Vector2f.limit_length, Id.run, ha.length.not_pos]

/-! ## The helpers on zeros -/

theorem sq_dt_fin {dt : Float32} (hdt : dt.IsFinite) (hdt1 : |dt.toReal| ≤ 1) : (sq_float dt).IsFinite := by
  refine (Float32.mul_err_all hdt hdt ?_).1
  rw [abs_mul]
  have : |dt.toReal| * |dt.toReal| ≤ 1 := by nlinarith [abs_nonneg dt.toReal]
  exact this.trans Float32.one_le_maxFinite32

theorem update_vel_accel_xy_Z {vel accel : AC_PosControl_lib.Vector2f.State} (hv : ZV vel) (ha : ZV accel) {dt : Float32}
    (hdt : dt.IsFinite) (limit vel_error : AC_PosControl_lib.Vector2f.State) :
    ZV (update_vel_accel_xy vel accel dt limit vel_error) := by
  have hd : ZV (AC_PosControl_lib.Vector2f.op_mul_float accel dt) := ha.mul hdt
  unfold update_vel_accel_xy
  simp only [Id.run, Contracts.Quick.id_pure]
  split_ifs
  · exact hv.add_assign (ZV.zero _)
  · exact hv.add_assign hd
  · exact hv.add_assign hd

theorem update_pos_vel_accel_xy_Z {pos : AC_PosControl_lib.Vector2p.State} {vel accel : AC_PosControl_lib.Vector2f.State} (hp : ZP pos)
    (hv : ZV vel) (ha : ZV accel) (hL : LibmSpec) {dt : Float32} (hdt : dt.IsFinite)
    (hdt1 : |dt.toReal| ≤ 1) (limit pos_error vel_error : AC_PosControl_lib.Vector2f.State) :
    ZP (update_pos_vel_accel_xy pos vel accel dt limit pos_error vel_error).1 ∧
      ZV (update_pos_vel_accel_xy pos vel accel dt limit pos_error vel_error).2 := by
  have hd : ZV (AC_PosControl_lib.Vector2f.op_add (AC_PosControl_lib.Vector2f.op_mul_float vel dt)
      (AC_PosControl_lib.Vector2f.op_mul_float (AC_PosControl_lib.Vector2f.op_mul_float accel (0.5 : Float32)) (sq_float dt))) :=
    (hv.mul hdt).add ((ha.mul Float32.isFinite_lit_half).mul (sq_dt_fin hdt hdt1))
  have hvn := update_vel_accel_xy_Z hv ha hdt limit vel_error
  unfold update_pos_vel_accel_xy
  simp only [Id.run, Contracts.Quick.id_pure]
  split_ifs
  · exact ⟨hp.add_assign ((ZV.zero _).todouble hL), hvn⟩
  · exact ⟨hp.add_assign (hd.todouble hL), hvn⟩
  · exact ⟨hp.add_assign (hd.todouble hL), hvn⟩

theorem limit_accel_corner_xy_Z {vel : AC_PosControl_lib.Vector2f.State} (hv : ZV vel) (a : AC_PosControl_lib.Vector2f.State)
    (m : Float32) (ha : ZV a) : ZV (limit_accel_corner_xy vel a m).1 := by
  unfold limit_accel_corner_xy
  simp only [Id.run, Contracts.Quick.id_pure, hv.is_zero, ha.limit_length]
  split_ifs <;> exact ha

theorem shape_accel_xy_Z {at_ a : AC_PosControl_lib.Vector2f.State} (hat : ZV at_) (ha : ZV a) (jerk dt : Float32) :
    ZV (shape_accel_xy_Vector2f2_float2 at_ a jerk dt) := by
  unfold shape_accel_xy_Vector2f2_float2
  simp only [Id.run, Contracts.Quick.id_pure, (hat.sub ha).limit_length]
  split_ifs
  · exact ha
  · exact ha.add (hat.sub ha)
  · exact ha

theorem shape_pos_vel_accel_xy_Z (hL : LibmSpec) {pd : AC_PosControl_lib.Vector2p.State} {vd ad : AC_PosControl_lib.Vector2f.State}
    {pos : AC_PosControl_lib.Vector2p.State} {vel accel : AC_PosControl_lib.Vector2f.State} (hpd : ZP pd) (hvd : ZV vd) (had : ZV ad)
    (hpos : ZP pos) (hvel : ZV vel) (hacc : ZV accel) (vel_max accel_max jerk_max dt : Float32)
    (hk : (jerk_max / accel_max).IsFinite) :
    ZV (shape_pos_vel_accel_xy pd vd ad pos vel accel vel_max accel_max jerk_max dt false) := by
  have hpe := (hpd.sub hpos).tofloat hL
  have hvt : ZV (AC_PosControl_lib.Vector2f.op_add vd AC_PosControl_lib.Vector2f.init_void) := hvd.add ZV.init_void
  have hat : ZV (AC_PosControl_lib.Vector2f.op_mul_float (AC_PosControl_lib.Vector2f.op_sub_Vector2f (AC_PosControl_lib.Vector2f.op_add vd AC_PosControl_lib.Vector2f.init_void) vel)
      (jerk_max / accel_max)) := (hvt.sub hvel).mul hk
  have hc := limit_accel_corner_xy_Z hvel _ accel_max hat
  unfold shape_pos_vel_accel_xy
  simp only [Id.run, Contracts.Quick.id_pure, hpe.length.not_pos, Bool.false_eq_true, ite_false,
    Bool.false_and]
  split_ifs
  · exact hacc
  · exact shape_accel_xy_Z (hc.add_assign had) hacc _ _

/-! ## The offsets of the position controller -/

open AC_PosControl in
/-- **The horizontal offsets and their targets are zero** (finite, value `0`, either sign). -/
structure OffZ (s : State) : Prop where
  px : Z64 s._pos_offset_ned_m.x
  py : Z64 s._pos_offset_ned_m.y
  vx : Z32 s._vel_offset_ned_ms.x
  vy : Z32 s._vel_offset_ned_ms.y
  ax : Z32 s._accel_offset_ned_mss.x
  ay : Z32 s._accel_offset_ned_mss.y
  tpx : Z64 s._pos_offset_target_ned_m.x
  tpy : Z64 s._pos_offset_target_ned_m.y
  tvx : Z32 s._vel_offset_target_ned_ms.x
  tvy : Z32 s._vel_offset_target_ned_ms.y
  tax : Z32 s._accel_offset_target_ned_mss.x
  tay : Z32 s._accel_offset_target_ned_mss.y

/-- The arguments of the offset updates are zero vectors: the hypotheses, the zeroed targets, or
the results of the updates (recursively). -/
syntax "zarg" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| zarg) => `(tactic| first
    | with_reducible exact ⟨hO.px, hO.py⟩ | with_reducible exact ⟨hO.vx, hO.vy⟩
    | with_reducible exact ⟨hO.ax, hO.ay⟩
    | with_reducible exact ⟨hO.tpx, hO.tpy⟩ | with_reducible exact ⟨hO.tvx, hO.tvy⟩
    | with_reducible exact ⟨hO.tax, hO.tay⟩
    | with_reducible exact ⟨(ZP.zero _).1, (ZP.zero _).2⟩
    | with_reducible exact ⟨(ZV.zero _).1, (ZV.zero _).2⟩
    | with_reducible exact ⟨(update_pos_vel_accel_xy_Z (by zarg) (by zarg) (by zarg) hL hdt hdt1 _ _ _).1.1,
        (update_pos_vel_accel_xy_Z (by zarg) (by zarg) (by zarg) hL hdt hdt1 _ _ _).1.2⟩
    | with_reducible exact ⟨(update_pos_vel_accel_xy_Z (by zarg) (by zarg) (by zarg) hL hdt hdt1 _ _ _).2.1,
        (update_pos_vel_accel_xy_Z (by zarg) (by zarg) (by zarg) hL hdt hdt1 _ _ _).2.2⟩)

open AC_PosControl in
theorem offZ_offsets (hL : LibmSpec) (s : State) (inp : Inputs) (hO : OffZ s)
    (hdt : s._dt_s.IsFinite) (hdt1 : |s._dt_s.toReal| ≤ 1)
    (hk : (s._jerk_max_ne_msss / s._accel_max_ne_mss).IsFinite) :
    OffZ (NE_update_offsets s inp) := by
  unfold NE_update_offsets
  simp only [Id.run, Contracts.Quick.id_pure]
  split_ifs <;> constructor <;> simp only [AC_PosControl_lib.Vector3f.xy, AC_PosControl_lib.Vector3p.xy, Id.run, Contracts.Quick.id_pure]
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.px, hO.py⟩ ⟨hO.vx, hO.vy⟩ ⟨hO.ax, hO.ay⟩ hL hdt hdt1 _ _ _).1.1
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.px, hO.py⟩ ⟨hO.vx, hO.vy⟩ ⟨hO.ax, hO.ay⟩ hL hdt hdt1 _ _ _).1.2
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.px, hO.py⟩ ⟨hO.vx, hO.vy⟩ ⟨hO.ax, hO.ay⟩ hL hdt hdt1 _ _ _).2.1
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.px, hO.py⟩ ⟨hO.vx, hO.vy⟩ ⟨hO.ax, hO.ay⟩ hL hdt hdt1 _ _ _).2.2
  · with_reducible exact (shape_pos_vel_accel_xy_Z hL (by zarg) (by zarg) (by zarg) (by zarg) (by zarg) (by zarg) _ _ _ _ hk).1
  · with_reducible exact (shape_pos_vel_accel_xy_Z hL (by zarg) (by zarg) (by zarg) (by zarg) (by zarg) (by zarg) _ _ _ _ hk).2
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨(ZP.zero _).1, (ZP.zero _).2⟩ ⟨(ZV.zero _).1, (ZV.zero _).2⟩ ⟨(ZV.zero _).1, (ZV.zero _).2⟩ hL hdt hdt1 _ _ _).1.1
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨(ZP.zero _).1, (ZP.zero _).2⟩ ⟨(ZV.zero _).1, (ZV.zero _).2⟩ ⟨(ZV.zero _).1, (ZV.zero _).2⟩ hL hdt hdt1 _ _ _).1.2
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨(ZP.zero _).1, (ZP.zero _).2⟩ ⟨(ZV.zero _).1, (ZV.zero _).2⟩ ⟨(ZV.zero _).1, (ZV.zero _).2⟩ hL hdt hdt1 _ _ _).2.1
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨(ZP.zero _).1, (ZP.zero _).2⟩ ⟨(ZV.zero _).1, (ZV.zero _).2⟩ ⟨(ZV.zero _).1, (ZV.zero _).2⟩ hL hdt hdt1 _ _ _).2.2
  · with_reducible exact (ZV.zero _).1
  · with_reducible exact (ZV.zero _).2
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.px, hO.py⟩ ⟨hO.vx, hO.vy⟩ ⟨hO.ax, hO.ay⟩ hL hdt hdt1 _ _ _).1.1
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.px, hO.py⟩ ⟨hO.vx, hO.vy⟩ ⟨hO.ax, hO.ay⟩ hL hdt hdt1 _ _ _).1.2
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.px, hO.py⟩ ⟨hO.vx, hO.vy⟩ ⟨hO.ax, hO.ay⟩ hL hdt hdt1 _ _ _).2.1
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.px, hO.py⟩ ⟨hO.vx, hO.vy⟩ ⟨hO.ax, hO.ay⟩ hL hdt hdt1 _ _ _).2.2
  · with_reducible exact (shape_pos_vel_accel_xy_Z hL (by zarg) (by zarg) (by zarg) (by zarg) (by zarg) (by zarg) _ _ _ _ hk).1
  · with_reducible exact (shape_pos_vel_accel_xy_Z hL (by zarg) (by zarg) (by zarg) (by zarg) (by zarg) (by zarg) _ _ _ _ hk).2
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.tpx, hO.tpy⟩ ⟨hO.tvx, hO.tvy⟩ ⟨hO.tax, hO.tay⟩ hL hdt hdt1 _ _ _).1.1
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.tpx, hO.tpy⟩ ⟨hO.tvx, hO.tvy⟩ ⟨hO.tax, hO.tay⟩ hL hdt hdt1 _ _ _).1.2
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.tpx, hO.tpy⟩ ⟨hO.tvx, hO.tvy⟩ ⟨hO.tax, hO.tay⟩ hL hdt hdt1 _ _ _).2.1
  · with_reducible exact (update_pos_vel_accel_xy_Z ⟨hO.tpx, hO.tpy⟩ ⟨hO.tvx, hO.tvy⟩ ⟨hO.tax, hO.tay⟩ hL hdt hdt1 _ _ _).2.2
  · with_reducible exact hO.tax
  · with_reducible exact hO.tay

open AC_PosControl in
theorem OffZ.congr {s t : State} (h : OffZ s) (hp : t._pos_offset_ned_m = s._pos_offset_ned_m)
    (hv : t._vel_offset_ned_ms = s._vel_offset_ned_ms)
    (ha : t._accel_offset_ned_mss = s._accel_offset_ned_mss)
    (htp : t._pos_offset_target_ned_m = s._pos_offset_target_ned_m)
    (htv : t._vel_offset_target_ned_ms = s._vel_offset_target_ned_ms)
    (hta : t._accel_offset_target_ned_mss = s._accel_offset_target_ned_mss) : OffZ t := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  constructor <;> simp only [hp, hv, ha, htp, htv, hta] <;> assumption

open AC_PosControl in
/-- **`OffZero` of the state after `NE_update_offsets`**, from `OffZ` before the call
(`HCtl.nS3`). -/
theorem offZero_of_offZ (hL : LibmSpec) (s : State) (inp : Inputs) (hO : OffZ s)
    (hdt : s._dt_s.IsFinite) (hdt1 : |s._dt_s.toReal| ≤ 1)
    (hk : (s._jerk_max_ne_msss / s._accel_max_ne_mss).IsFinite) :
    OffZero (nS3 s inp) := by
  have h := offZ_offsets hL { s with _last_update_ne_ticks := inp.ticks32 } inp
    (hO.congr rfl rfl rfl rfl rfl rfl) hdt hdt1 hk
  exact ⟨h.px, h.py, h.vx, h.vy, h.ax, h.ay⟩

section CY
open AC_PosControl
variable (s : State) (inp : Inputs)
theorem cy_po : (calculate_yaw_and_rate_yaw s inp)._pos_offset_ned_m = s._pos_offset_ned_m := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_vo : (calculate_yaw_and_rate_yaw s inp)._vel_offset_ned_ms = s._vel_offset_ned_ms := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_ao : (calculate_yaw_and_rate_yaw s inp)._accel_offset_ned_mss = s._accel_offset_ned_mss := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_tpo : (calculate_yaw_and_rate_yaw s inp)._pos_offset_target_ned_m = s._pos_offset_target_ned_m := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_tvo : (calculate_yaw_and_rate_yaw s inp)._vel_offset_target_ned_ms = s._vel_offset_target_ned_ms := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_tao : (calculate_yaw_and_rate_yaw s inp)._accel_offset_target_ned_mss =
    s._accel_offset_target_ned_mss := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
end CY

set_option maxHeartbeats 1000000 in
open AC_PosControl in
/-- `NE_update_controller` writes the horizontal offsets only through `NE_update_offsets`. -/
theorem ne_off (p : Params) (s : State) (inp : Inputs)
    (hekf : inp.get_position_NE_reset_count = s._ahrs_position_NE_reset_count)
    (hact : NE_is_active s inp = true) :
    (NE_update_controller p s inp)._pos_offset_ned_m = (nS3 s inp)._pos_offset_ned_m ∧
    (NE_update_controller p s inp)._vel_offset_ned_ms = (nS3 s inp)._vel_offset_ned_ms ∧
    (NE_update_controller p s inp)._accel_offset_ned_mss = (nS3 s inp)._accel_offset_ned_mss ∧
    (NE_update_controller p s inp)._pos_offset_target_ned_m = (nS3 s inp)._pos_offset_target_ned_m ∧
    (NE_update_controller p s inp)._vel_offset_target_ned_ms = (nS3 s inp)._vel_offset_target_ned_ms ∧
    (NE_update_controller p s inp)._accel_offset_target_ned_mss =
      (nS3 s inp)._accel_offset_target_ned_mss := by
  unfold NE_update_controller
  simp only [Id.run, ekf_noop s inp hekf, hact, Bool.not_true, Bool.false_eq_true, ite_false, cy_po,
    cy_vo, cy_ao, cy_tpo, cy_tvo, cy_tao]
  split <;> split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

open AC_PosControl in
/-- **The offsets stay zero through `NE_update_controller`** (no EKF reset, controller active). -/
theorem offZ_NE_update (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) (hO : OffZ s)
    (hekf : inp.get_position_NE_reset_count = s._ahrs_position_NE_reset_count)
    (hact : NE_is_active s inp = true)
    (hdt : s._dt_s.IsFinite) (hdt1 : |s._dt_s.toReal| ≤ 1)
    (hk : (s._jerk_max_ne_msss / s._accel_max_ne_mss).IsFinite) :
    OffZ (NE_update_controller p s inp) := by
  have h := offZ_offsets hL { s with _last_update_ne_ticks := inp.ticks32 } inp
    (hO.congr rfl rfl rfl rfl rfl rfl) hdt hdt1 hk
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := ne_off p s inp hekf hact
  exact h.congr e1 e2 e3 e4 e5 e6

/-! ## Frames: the other calls of the tick leave the horizontal offsets alone -/

open AC_PosControl in
/-- The horizontal components of the offsets and their targets of `t` are those of `s`. -/
def OffEq (s t : State) : Prop :=
  t._pos_offset_ned_m.x = s._pos_offset_ned_m.x ∧ t._pos_offset_ned_m.y = s._pos_offset_ned_m.y ∧
  t._vel_offset_ned_ms.x = s._vel_offset_ned_ms.x ∧ t._vel_offset_ned_ms.y = s._vel_offset_ned_ms.y ∧
  t._accel_offset_ned_mss.x = s._accel_offset_ned_mss.x ∧
  t._accel_offset_ned_mss.y = s._accel_offset_ned_mss.y ∧
  t._pos_offset_target_ned_m.x = s._pos_offset_target_ned_m.x ∧
  t._pos_offset_target_ned_m.y = s._pos_offset_target_ned_m.y ∧
  t._vel_offset_target_ned_ms.x = s._vel_offset_target_ned_ms.x ∧
  t._vel_offset_target_ned_ms.y = s._vel_offset_target_ned_ms.y ∧
  t._accel_offset_target_ned_mss.x = s._accel_offset_target_ned_mss.x ∧
  t._accel_offset_target_ned_mss.y = s._accel_offset_target_ned_mss.y

open AC_PosControl in
theorem OffZ.of_eq {s t : State} (h : OffZ s) (e : OffEq s t) : OffZ t := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := e
  exact ⟨e1 ▸ h.px, e2 ▸ h.py, e3 ▸ h.vx, e4 ▸ h.vy, e5 ▸ h.ax, e6 ▸ h.ay, e7 ▸ h.tpx, e8 ▸ h.tpy,
    e9 ▸ h.tvx, e10 ▸ h.tvy, e11 ▸ h.tax, e12 ▸ h.tay⟩

open AC_PosControl in
theorem offEq_refl (s : State) : OffEq s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
open AC_PosControl in
/-- `D_update_controller` writes only the vertical components of the offsets. -/
theorem offEq_D_update (p : Params) (s : State) (o : Outputs) (inp : Inputs) :
    OffEq s (D_update_controller p s o inp).2.1 := by
  frame_gen State (fun t : State => OffEq s t) (D_update_controller p s o inp)
    using first | exact offEq_refl s | assumption

open AC_PosControl in
theorem offZ_D_update {p : Params} {s : State} (o : Outputs) (inp : Inputs) (h : OffZ s) :
    OffZ (D_update_controller p s o inp).2.1 := h.of_eq (offEq_D_update p s o inp)

set_option maxHeartbeats 1000000 in
open AC_PosControl in
theorem offEq_update_estimates (s : State) (inp : Inputs) (hv : Bool) :
    OffEq s (update_estimates s inp hv) := by
  frame_gen State (fun t : State => OffEq s t) (update_estimates s inp hv)
    using first | exact offEq_refl s | assumption

section Setters
open AC_PosControl
variable {s : State} (h : OffZ s)
include h
theorem offZ_set_dt_s (dt : Float32) : OffZ (set_dt_s s dt) := by
  simp only [set_dt_s, Id.run, Contracts.Quick.id_pure]
  exact h.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem offZ_update_estimates (inp : Inputs) (hv : Bool) : OffZ (update_estimates s inp hv) :=
  h.of_eq (offEq_update_estimates s inp hv)
theorem offZ_set_reset_handling_method (m : EKFResetMethod) : OffZ (set_reset_handling_method s m) := by
  simp only [set_reset_handling_method, Id.run, Contracts.Quick.id_pure]
  exact h.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem offZ_set_pos_terrain_target_D_m (d : Float32) : OffZ (set_pos_terrain_target_D_m s d) := by
  simp only [set_pos_terrain_target_D_m, Id.run, Contracts.Quick.id_pure]
  exact h.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem offZ_set_pos_vel_accel_NED_m (P : AC_PosControl_lib.Vector3p.State) (V A : AC_PosControl_lib.Vector3f.State) :
    OffZ (set_pos_vel_accel_NED_m s P V A) := by
  simp only [set_pos_vel_accel_NED_m, Id.run, Contracts.Quick.id_pure]
  exact h.of_eq ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end Setters

end OffZeroSec

/-! ## The tick in calls -/

section TickSplit

open Vehicle Contracts.Track.CtrlV

/-- The first tick's world before `ModeAuto::init`: the sample, the view, the estimates. -/
def preInit (w : World) (smp : Sample) : World :=
  let w := { w with sample := { smp with gyro := w.sample.gyro } }
  let w := viewUpdate w
  { w with ps := AC_PosControl_lib.AC_PosControl.update_estimates w.ps (posInputs w) false }

/-- `Copter::set_mode(AUTO)` on the first tick: `ModeAuto::init`, the rate time constants. -/
def initW (w : World) : World :=
  let w := auto_init w
  let w := { w with «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.set_roll_pitch_rate_tc w.as w.h.ACRO_RP_RATE_TC }
  { w with «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.set_yaw_rate_tc w.as w.h.PILOT_Y_RATE_TC, in_auto := true }

/-- The landed gain and the reset method (`Copter::update_flight_mode`). -/
def postInit (w : World) : World :=
  let w := { w with «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.landed_gain_reduction w.ap w.as false }
  { w with ps := AC_PosControl_lib.AC_PosControl.set_reset_handling_method w.ps .MoveVehicle }

theorem preAuto_eq (w : World) (smp : Sample) : preAuto w smp = postInit (preInit w smp) := rfl

/-- **The first tick in stages** (`in_auto = false`): the scheduler, the rate controller, the
motors' output, the sample, the view, the estimates, `ModeAuto::init` and the rate time constants,
the landed gain and the reset method, then `ModeAuto::run`. -/
theorem tick_split_first (w : World) (smp : Sample) (hin : w.in_auto = false) :
    Vehicle.tick w smp = (auto_run (postInit (initW (preInit (postMot (preMot w smp)) smp))),
      actOf (postMot (preMot w smp))) := by
  cases w
  simp only at hin
  subst hin
  unfold Vehicle.tick preMot postMot actOf preInit initW postInit
  dsimp only [Id.run, viewUpdate, withMotors_in_auto, Bool.not_false, ↓reduceIte]
  rfl


/-- The world `ModeAuto::run` receives. -/
def autoIn (w : World) (smp : Sample) : World :=
  if w.in_auto then preAuto (postMot (preMot w smp)) smp
  else postInit (initW (preInit (postMot (preMot w smp)) smp))

/-- The world `wp_run` receives: the mission's start (first tick) or update. -/
def wpIn (w : World) (smp : Sample) : World :=
  if (autoIn w smp).au.waiting_to_start then
    { mission_start (autoIn w smp) with au.waiting_to_start := false }
  else mission_update (autoIn w smp)

theorem auto_run_wpIn (w : World) (smp : Sample) : auto_run (autoIn w smp) = wp_run (wpIn w smp) := by
  unfold auto_run wpIn
  cases (autoIn w smp).au.waiting_to_start <;> rfl

/-- **Every tick** is `wp_run` of `wpIn`, with the actuators of the motors' output. -/
theorem tick_eq (w : World) (smp : Sample) :
    Vehicle.tick w smp = (wp_run (wpIn w smp), actOf (postMot (preMot w smp))) := by
  cases hin : w.in_auto
  · rw [tick_split_first w smp hin, ← auto_run_wpIn]
    simp [autoIn, hin]
  · rw [tick_split w smp hin, ← auto_run_wpIn]
    simp [autoIn, hin]

/-- The spool state `wp_run` sets first. -/
def spoolW (w : World) : World :=
  { w with ms := AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state w.ms .THROTTLE_UNLIMITED }

/-- One of the navigator's calls into the position controller (the body of `replayPos`). -/
def replayEv (w : World) (ev : AC_WPNav_lib.Output) : World :=
  let pp := w.pp
  let inp := posInputs w
  match ev with
  | .init_pos_terrain_D_m d => { w with ps := AC_PosControl_lib.AC_PosControl.init_pos_terrain_D_m w.ps d }
  | .D_init_controller_stopping_point => { w with ps := AC_PosControl_lib.AC_PosControl.D_init_controller_stopping_point pp w.ps inp }
  | .NE_init_controller_stopping_point => { w with ps := AC_PosControl_lib.AC_PosControl.NE_init_controller_stopping_point pp w.ps inp }
  | .NE_set_max_speed_accel_m v a => { w with ps := AC_PosControl_lib.AC_PosControl.NE_set_max_speed_accel_m pp w.ps inp v a }
  | .NE_set_correction_speed_accel_m v a => { w with ps := AC_PosControl_lib.AC_PosControl.NE_set_correction_speed_accel_m pp w.ps v a }
  | .D_set_max_speed_accel_m dn up a => { w with ps := AC_PosControl_lib.AC_PosControl.D_set_max_speed_accel_m pp w.ps dn up a }
  | .D_set_correction_speed_accel_m dn up a => { w with ps := AC_PosControl_lib.AC_PosControl.D_set_correction_speed_accel_m pp w.ps dn up a }
  | .set_pos_terrain_target_D_m d => { w with ps := AC_PosControl_lib.AC_PosControl.set_pos_terrain_target_D_m w.ps d }
  | .set_pos_vel_accel_NED_m pos vel acc => { w with ps := AC_PosControl_lib.AC_PosControl.set_pos_vel_accel_NED_m w.ps (p3 pos) (f3 vel) (f3 acc) }
  | .NE_update_controller => { w with ps := AC_PosControl_lib.AC_PosControl.NE_update_controller pp w.ps inp }

theorem replayPos_eq_foldl (w : World) (log : AC_WPNav_lib.Outputs) :
    replayPos w log = log.foldl replayEv w := by
  unfold replayPos
  simp only [Id.run]
  rw [← Array.foldl_toList, ← Array.forIn_toList]
  generalize log.toList = l
  induction l generalizing w with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons, List.foldl_cons, ← ih]
    cases a <;> rfl

theorem replayPos_empty (w : World) : replayPos w #[] = w := by
  rw [replayPos_eq_foldl]; rfl

theorem replayPos_push (w : World) (log : AC_WPNav_lib.Outputs) (ev : AC_WPNav_lib.Output) :
    replayPos w (log.push ev) = replayEv (replayPos w log) ev := by
  rw [replayPos_eq_foldl, replayPos_eq_foldl, Array.foldl_push]

/-- `posInputs` does not read the position controller nor the navigator. -/
theorem posInputs_ps (w : World) ps : posInputs { w with ps := ps } = posInputs w := rfl
theorem posInputs_nav (w : World) wpp wps : posInputs { w with wpp := wpp, wps := wps } = posInputs w := rfl

theorem navW_eq (w : World) : navW w =
    afterWP (spoolW w) w.wpp (AC_WPNav_lib.AC_WPNav.update_wpnav w.wpp w.wps #[] (wpInputs (spoolW w))).1
      (AC_WPNav_lib.AC_WPNav.update_wpnav w.wpp w.wps #[] (wpInputs (spoolW w))).2.1 := by
  unfold navW spoolW
  dsimp only

/-- The advance of a steady tick (the navigator's state handed back). -/
def advW (w : World) : AC_WPNav_lib.AC_WPNav.State :=
  (AC_WPNav_lib.AC_WPNav.advance_wp_target_along_track w.wpp w.wps #[] (wpInputs (spoolW w))
    ((wpInputs (spoolW w)).get_dt_s #[])).1

/-- **The navigator's update on a steady tick** (speeds unchanged, no terrain following): the
navigator's state is the advance's (with the update time), and the position controller receives,
in order, `set_pos_terrain_target_D_m 0`, `set_pos_vel_accel_NED_m P V A` (the targets of the
tick) and one `NE_update_controller`, with the position controller's inputs of the world. -/
theorem navW_steady (w : World) (hS : SpeedSteady w.wpp w.wps) (hT : w.wps._is_terrain_alt = false) :
    ∃ P V A, navW w = { spoolW w with
      wps := { advW w with _wp_last_update_ms := (wpInputs (spoolW w)).millis },
      ps := AC_PosControl_lib.AC_PosControl.NE_update_controller w.pp
        (AC_PosControl_lib.AC_PosControl.set_pos_vel_accel_NED_m
          (AC_PosControl_lib.AC_PosControl.set_pos_terrain_target_D_m w.ps 0.0) (p3 P) (f3 V) (f3 A))
        (posInputs (spoolW w)) } := by
  obtain ⟨e1, P, V, A, e2⟩ := update_wpnav_steady (wpInputs (spoolW w)) hS hT
  refine ⟨P, V, A, ?_⟩
  rw [navW_eq, e1, e2]
  simp only [afterWP, replayPos_push, replayPos_empty]
  rfl

end TickSplit

end Contracts.Track.Induction.TG
