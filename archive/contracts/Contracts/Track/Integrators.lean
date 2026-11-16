import FloatModel.Lit
import Contracts.Mission.Loop
import Contracts.Mission.Spec
import Contracts.Track.Frame

/-!
# M2: the PID integrators stay bounded

The stack's integrators, as the vehicle runs them each tick:

* the three body-rate PIDs of the attitude controller (`AC_Attitude_lib.AC_PID`, the attitude
  library's own translation of `AC_PID`): `_pid_rate_roll`, `_pid_rate_pitch`, `_pid_rate_yaw`;
* the vertical acceleration PID of the position controller (`AC_PosControl_lib.AC_PID`,
  `_pid_accel_d_m`) and its vertical velocity PI (`AC_PID_Basic`, `_pid_vel_d_m`);
* the horizontal velocity PID (`AC_PID_2D`, `_pid_vel_ne_m`, a 2-vector integrator): see
  `Integrators2D.lean`.

(`AC_P_1D`/`AC_P_2D`, the position P controllers, have no integrator.)

**The scalar integrators.** Every write is one of three things:
* `constrain_value_line(·, -IMAX, IMAX)` (`update_i`, `set_integrator`);
* `0` (`update_i` with `ki = 0` or `dt ≤ 0`; `reset_I`, whose `(float) 0.0` takes its value from
  `LibmSpec`);
* nothing.

`constrain_value_line` maps NaN to the midpoint `(-IMAX + IMAX) / 2 = 0` and `±∞` to `±IMAX`
(`Float32.cvl_symm`). So `|I| ≤ IMAX` holds after every update **for every input, NaN and `±∞`
included**. It needs only two things: that the bound held before (on the paths that do not write
the integrator), and that `IMAX` is a finite float in `[0, maxFinite32 / 2]` (`KOK`).

**The moving limit.** `D_update_controller` raises the acceleration PID's `IMAX` to the hover
throttle (`if hover > IMAX: set_imax(hover)`). The invariant uses `K = max(IMAX, hover)`, which
that call leaves unchanged. The hover throttle is `constrain(MOT_THST_HOVER, 0.125, 0.6875)`, in
`[0, 1]` (`hovOK`).

**Results.**
* `intOK_tick`: `IntOK w → IntOK (tick w smp).1` for every sample.
* `intOK_takeover`: the same for the takeover (needs `LibmSpec`).
* `integrators_bounded`: the invariant along every behavior of `Mctrl w₀` from `IntOK w₀`.
-/

namespace Contracts.Track

open Float.Model.UnpackedFloat

/-- An integrator limit as the code needs it: a finite float in `[0, maxFinite32 / 2]` (so that the
clamp's midpoint `(-k + k) / 2` does not overflow). -/
def KOK (k : Float32) : Prop := k.IsFinite ∧ 0 ≤ k.toReal ∧ k.toReal ≤ maxFinite32 / 2

/-- A scalar integrator within its limit: finite and `|I| ≤ k`. -/
def IB (k I : Float32) : Prop := I.IsFinite ∧ |I.toReal| ≤ k.toReal

theorem IB_cvl {k : Float32} (hk : KOK k) (a : Float32) : IB k (Float32.cvl a (-k) k) :=
  Float32.cvl_symm Float32.two32 hk.1 hk.2.1 hk.2.2

theorem IB_lit_zero {k : Float32} (hk : KOK k) : IB k (0.0 : Float32) :=
  ⟨Float32.isFinite_lit_zero, by simp [hk.2.1]⟩

/-- A scalar integrator within a real bound `K` (used when the limit itself moves: the vertical
acceleration PID's `IMAX` is raised to the hover throttle by `D_update_controller`). -/
def IBK (K : ℝ) (I : Float32) : Prop := I.IsFinite ∧ |I.toReal| ≤ K

theorem IBK_of_IB {k I : Float32} {K : ℝ} (h : IB k I) (hK : k.toReal ≤ K) : IBK K I :=
  ⟨h.1, h.2.trans hK⟩

/-! ## The attitude controller's `AC_PID` -/

namespace Att

open AC_Attitude_lib

theorem cvl_eq (a lo hi : Float32) (l : UInt32) :
    constrain_value_line_float a lo hi l = Float32.cvl a lo hi := rfl

theorem IB_clamp {k : Float32} (hk : KOK k) (a : Float32) (l : UInt32) :
    IB k (constrain_value_line_float a (-k) k l) := IB_cvl hk a

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `AC_PID::update_i`: the integrator is clamped to `±IMAX`, or set to `0`, or kept. -/
theorem IB_update_i (p : AC_PID.Params) (s : AC_PID.State) (dt : Float32) (limit : Bool)
    (i_scale : Float32) (hk : KOK p._kimax) (hs : IB p._kimax s._integrator) :
    IB p._kimax (AC_PID.update_i p s dt limit i_scale)._integrator := by
  frame_gen AC_PID.State (fun s' : AC_PID.State => IB p._kimax s'._integrator)
    (AC_PID.update_i p s dt limit i_scale) using first
    | with_reducible assumption
    | with_reducible exact IB_clamp hk _ _
    | with_reducible exact IB_lit_zero hk

/-- `AC_PID::update_all`: for every target, measurement and `dt` (NaN, `±∞` included). -/
theorem IB_update_all (p : AC_PID.Params) (s : AC_PID.State) inp (target meas dt : Float32)
    (limit : Bool) (pd i : Float32) (hk : KOK p._kimax) (hs : IB p._kimax s._integrator) :
    IB p._kimax (AC_PID.update_all p s inp target meas dt limit pd i).1._integrator := by
  frame_gen AC_PID.State (fun s' : AC_PID.State => IB p._kimax s'._integrator)
    (AC_PID.update_all p s inp target meas dt limit pd i) using first
    | with_reducible assumption
    | with_reducible exact IB_update_i _ _ _ _ _ hk (by assumption)

/-- The three rate PIDs' limits are proper (`KOK`). -/
structure AttKOK (p : AC_AttitudeControl_Multi.Params) : Prop where
  roll : KOK p._pid_rate_roll._kimax
  pitch : KOK p._pid_rate_pitch._kimax
  yaw : KOK p._pid_rate_yaw._kimax

/-- The three rate integrators are within their limits. -/
structure AttIB (p : AC_AttitudeControl_Multi.Params) (s : AC_AttitudeControl_Multi.State) :
    Prop where
  roll : IB p._pid_rate_roll._kimax s._pid_rate_roll._integrator
  pitch : IB p._pid_rate_pitch._kimax s._pid_rate_pitch._integrator
  yaw : IB p._pid_rate_yaw._kimax s._pid_rate_yaw._integrator

set_option maxHeartbeats 4000000


open AC_AttitudeControl_Multi in
theorem attIB_rate_controller_run_dt (p : Params) (s : State) o inp g dt (hk : AttKOK p)
    (hs : AttIB p s) : AttIB p (rate_controller_run_dt p s o inp g dt).1 := by
  frame_gen State (fun s' : State => AttIB p s') (rate_controller_run_dt p s o inp g dt) using first
    | field_assumption
    | (constructor <;> first
        | field_assumption
        | (with_reducible apply IB_update_all <;> field_assumption))

open AC_AttitudeControl_Multi in
/-- The body-rate controller: each rate PID runs `update_all`. -/
theorem attIB_rate_controller_run (p : Params) (s : State) o inp (hk : AttKOK p)
    (hs : AttIB p s) : AttIB p (rate_controller_run p s o inp).1 := by
  frame_gen State (fun s' : State => AttIB p s') (rate_controller_run p s o inp) using first
    | field_assumption
    | (constructor <;> first
        | field_assumption
        | (with_reducible apply IB_update_all <;> field_assumption))

/-- `reset_I` writes `(float) 0.0`, a narrowing of the `double` literal (`Float.toFloat32` is opaque
in core v4.36): its value comes from `LibmSpec.f64ToF32_exact`. -/
theorem IB_reset_I (hL : Contracts.Mission.LibmSpec) {k : Float32} (hk : KOK k) (x : AC_PID.State) :
    IB k (AC_PID.reset_I x)._integrator := by
  obtain ⟨h1, h2⟩ := hL.f64ToF32_exact (0.0 : Float) (0.0 : Float32) Float.isFinite_lit_zero
    Float32.isFinite_lit_zero (by simp)
  show IB k (Float.toFloat32 (0.0 : Float))
  exact ⟨h1, by rw [h2, Float.toReal_lit_zero, abs_zero]; exact hk.2.1⟩

theorem reset_filter_I (x : AC_PID.State) : (AC_PID.reset_filter x)._integrator = x._integrator :=
  rfl

/-- The leaf tactic of the attitude frame proofs. -/
macro "att_leaf" : tactic => `(tactic| first
  | field_assumption
  | (constructor <;> first
      | field_assumption
      | (with_reducible apply Contracts.Track.Att.IB_update_all <;> field_assumption)))

open AC_AttitudeControl_Multi in
theorem attIB_set_dt_s (p : Params) (s : State) x (hs : AttIB p s) : AttIB p (set_dt_s s x) := by
  frame_gen State (fun s' : State => AttIB p s') (set_dt_s s x) using att_leaf

open AC_AttitudeControl_Multi in
theorem attIB_rate_controller_target_reset (p : Params) (s : State) (hs : AttIB p s) :
    AttIB p (rate_controller_target_reset s) := by
  frame_gen State (fun s' : State => AttIB p s') (rate_controller_target_reset s) using att_leaf

open AC_AttitudeControl_Multi in
theorem attIB_landed_gain_reduction (p : Params) (s : State) l (hs : AttIB p s) :
    AttIB p (landed_gain_reduction p s l) := by
  frame_gen State (fun s' : State => AttIB p s') (landed_gain_reduction p s l) using att_leaf

open AC_AttitudeControl_Multi in
theorem attIB_set_roll_pitch_rate_tc (p : Params) (s : State) x (hs : AttIB p s) :
    AttIB p (set_roll_pitch_rate_tc s x) := by
  frame_gen State (fun s' : State => AttIB p s') (set_roll_pitch_rate_tc s x) using att_leaf

open AC_AttitudeControl_Multi in
theorem attIB_set_yaw_rate_tc (p : Params) (s : State) x (hs : AttIB p s) :
    AttIB p (set_yaw_rate_tc s x) := by
  frame_gen State (fun s' : State => AttIB p s') (set_yaw_rate_tc s x) using att_leaf

open AC_AttitudeControl_Multi in
theorem attIB_set_throttle_out (p : Params) (s : State) o inp t b c (hs : AttIB p s) :
    AttIB p (set_throttle_out p s o inp t b c).1 := by
  frame_gen State (fun s' : State => AttIB p s') (set_throttle_out p s o inp t b c) using att_leaf

open AC_AttitudeControl_Multi in
theorem attIB_input_thrust_vector_heading (p : Params) (s : State) inp tv h (hs : AttIB p s) :
    AttIB p (input_thrust_vector_heading p s inp tv h) := by
  frame_gen State (fun s' : State => AttIB p s') (input_thrust_vector_heading p s inp tv h)
    using att_leaf

open AC_AttitudeControl_Multi in
/-- `relax_attitude_controllers` (the takeover): the rate integrators are reset to `0`. -/
theorem attIB_relax_attitude_controllers_void (hL : Contracts.Mission.LibmSpec) (p : Params)
    (s : State) inp (hk : AttKOK p) (hs : AttIB p s) :
    AttIB p (relax_attitude_controllers_void s inp) := by
  frame_gen State (fun s' : State => AttIB p s') (relax_attitude_controllers_void s inp) using first
    | field_assumption
    | (constructor <;> first
        | field_assumption
        | (simp only [Contracts.Track.Att.reset_filter_I]; field_assumption)
        | (with_reducible apply IB_reset_I hL <;> field_assumption))

end Att

/-! ## The position controller's `AC_PID` (vertical acceleration) and `AC_PID_Basic` (vertical
velocity) -/

namespace Pos

open AC_PosControl_lib

theorem IB_clamp {k : Float32} (hk : KOK k) (a : Float32) (l : UInt32) :
    IB k (constrain_value_line_float a (-k) k l) := IB_cvl hk a

theorem IBK_clamp {k : Float32} {K : ℝ} (hk : KOK k) (hK : k.toReal ≤ K) (a : Float32)
    (l : UInt32) : IBK K (constrain_value_line_float a (-k) k l) :=
  IBK_of_IB (IB_cvl hk a) hK

theorem IBK_lit_zero {K : ℝ} (hK : 0 ≤ K) : IBK K (0.0 : Float32) :=
  ⟨Float32.isFinite_lit_zero, by simp [hK]⟩

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem IBK_update_i (p : AC_PID.Params) (s : AC_PID.State) (dt : Float32) (limit : Bool)
    (i_scale : Float32) {K : ℝ} (hk : KOK p._kimax) (hK : p._kimax.toReal ≤ K)
    (hs : IBK K s._integrator) : IBK K (AC_PID.update_i p s dt limit i_scale)._integrator := by
  have hK0 : 0 ≤ K := hk.2.1.trans hK
  frame_gen AC_PID.State (fun s' : AC_PID.State => IBK K s'._integrator)
    (AC_PID.update_i p s dt limit i_scale) using first
    | with_reducible assumption
    | with_reducible exact IBK_clamp hk hK _ _
    | with_reducible exact IBK_lit_zero hK0

/-- `AC_PID::update_all` (vertical acceleration): for every input. -/
theorem IBK_update_all (p : AC_PID.Params) (s : AC_PID.State) inp (target meas dt : Float32)
    (limit : Bool) (pd i : Float32) {K : ℝ} (hk : KOK p._kimax) (hK : p._kimax.toReal ≤ K)
    (hs : IBK K s._integrator) :
    IBK K (AC_PID.update_all p s inp target meas dt limit pd i).1._integrator := by
  frame_gen AC_PID.State (fun s' : AC_PID.State => IBK K s'._integrator)
    (AC_PID.update_all p s inp target meas dt limit pd i) using first
    | with_reducible assumption
    | with_reducible exact IBK_update_i _ _ _ _ _ hk hK (by assumption)

/-- `AC_PID::set_integrator`: clamped, for every argument. -/
theorem IBK_set_integrator (p : AC_PID.Params) (s : AC_PID.State) (x : Float32) {K : ℝ}
    (hk : KOK p._kimax) (hK : p._kimax.toReal ≤ K) :
    IBK K (AC_PID.set_integrator p s x)._integrator :=
  IBK_clamp hk hK x (Int32.toUInt32 436)

theorem IB_basic_update_i (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State) (dt : Float32)
    (ln lp : Bool) (hk : KOK p._kimax) (hs : IB p._kimax s._integrator) :
    IB p._kimax (AC_PID_Basic.update_i p s dt ln lp)._integrator := by
  frame_gen AC_PID_Basic.State (fun s' : AC_PID_Basic.State => IB p._kimax s'._integrator)
    (AC_PID_Basic.update_i p s dt ln lp) using first
    | with_reducible assumption
    | with_reducible exact IB_clamp hk _ _
    | with_reducible exact IB_lit_zero hk

/-- `AC_PID_Basic::update_all` (vertical velocity): for every input. -/
theorem IB_basic_update_all (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State)
    (target meas dt : Float32) (ln lp : Bool) (hk : KOK p._kimax) (hs : IB p._kimax s._integrator) :
    IB p._kimax (AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp).1._integrator := by
  frame_gen AC_PID_Basic.State (fun s' : AC_PID_Basic.State => IB p._kimax s'._integrator)
    (AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp) using first
    | with_reducible assumption
    | with_reducible exact IB_basic_update_i _ _ _ _ _ hk (by assumption)

/-- `AC_PID_Basic::set_integrator`: clamped, for every argument. -/
theorem IB_basic_set_integrator (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State) (x : Float32)
    (hk : KOK p._kimax) : IB p._kimax (AC_PID_Basic.set_integrator_float p s x)._integrator :=
  IB_clamp hk x (Int32.toUInt32 182)

/-- The position controller's scalar limits, with the real bound `K` on the vertical acceleration
integrator (at least its `IMAX`). -/
structure PosKOK (K : ℝ) (p : AC_PosControl.Params) : Prop where
  accel : KOK p._pid_accel_d_m._kimax
  accelK : p._pid_accel_d_m._kimax.toReal ≤ K
  veld : KOK p._pid_vel_d_m._kimax

/-- The position controller's scalar integrators within their bounds. -/
structure PosIB (K : ℝ) (p : AC_PosControl.Params) (s : AC_PosControl.State) : Prop where
  accel : IBK K s._pid_accel_d_m._integrator
  veld : IB p._pid_vel_d_m._kimax s._pid_vel_d_m._integrator

theorem pid_reset_filter_I (x : AC_PID.State) : (AC_PID.reset_filter x)._integrator = x._integrator :=
  rfl
theorem basic_reset_filter_I (x : AC_PID_Basic.State) :
    (AC_PID_Basic.reset_filter x)._integrator = x._integrator := rfl

/-- The leaf tactic of the position controller's frame proofs. -/
macro "pos_leaf" : tactic => `(tactic| first
  | field_assumption
  | (constructor <;> first
      | field_assumption
      | (simp only [Contracts.Track.Pos.pid_reset_filter_I, Contracts.Track.Pos.basic_reset_filter_I];
         field_assumption)
      | (with_reducible apply Contracts.Track.Pos.IBK_update_all <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.IBK_set_integrator <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.IB_basic_update_all <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.IB_basic_set_integrator <;> field_assumption)))

set_option maxHeartbeats 4000000

section
open AC_PosControl
variable {K : ℝ} (p : Params) (s : State)

theorem posIB_set_dt_s x (hs : PosIB K p s) : PosIB K p (set_dt_s s x) := by
  frame_gen State (fun s' : State => PosIB K p s') (set_dt_s s x) using pos_leaf

theorem posIB_update_estimates inp v (hs : PosIB K p s) : PosIB K p (update_estimates s inp v) := by
  frame_gen State (fun s' : State => PosIB K p s') (update_estimates s inp v) using pos_leaf

theorem posIB_set_pos_terrain_target_D_m x (hs : PosIB K p s) :
    PosIB K p (set_pos_terrain_target_D_m s x) := by
  frame_gen State (fun s' : State => PosIB K p s') (set_pos_terrain_target_D_m s x) using pos_leaf

theorem posIB_NE_set_max_speed_accel_m inp a b (hs : PosIB K p s) :
    PosIB K p (NE_set_max_speed_accel_m p s inp a b) := by
  frame_gen State (fun s' : State => PosIB K p s') (NE_set_max_speed_accel_m p s inp a b)
    using pos_leaf

theorem posIB_NE_set_correction_speed_accel_m a b (hs : PosIB K p s) :
    PosIB K p (NE_set_correction_speed_accel_m p s a b) := by
  frame_gen State (fun s' : State => PosIB K p s') (NE_set_correction_speed_accel_m p s a b)
    using pos_leaf

theorem posIB_NE_init_controller_stopping_point inp (hk : PosKOK K p) (hs : PosIB K p s) :
    PosIB K p (NE_init_controller_stopping_point p s inp) := by
  frame_gen State (fun s' : State => PosIB K p s') (NE_init_controller_stopping_point p s inp)
    using pos_leaf

theorem posIB_NE_update_controller inp (hk : PosKOK K p) (hs : PosIB K p s) :
    PosIB K p (NE_update_controller p s inp) := by
  frame_gen State (fun s' : State => PosIB K p s') (NE_update_controller p s inp) using pos_leaf

theorem posIB_D_set_max_speed_accel_m a b c (hs : PosIB K p s) :
    PosIB K p (D_set_max_speed_accel_m p s a b c) := by
  frame_gen State (fun s' : State => PosIB K p s') (D_set_max_speed_accel_m p s a b c)
    using pos_leaf

theorem posIB_D_set_correction_speed_accel_m a b c (hs : PosIB K p s) :
    PosIB K p (D_set_correction_speed_accel_m p s a b c) := by
  frame_gen State (fun s' : State => PosIB K p s') (D_set_correction_speed_accel_m p s a b c)
    using pos_leaf

theorem posIB_D_init_controller_stopping_point inp (hk : PosKOK K p) (hs : PosIB K p s) :
    PosIB K p (D_init_controller_stopping_point p s inp) := by
  frame_gen State (fun s' : State => PosIB K p s') (D_init_controller_stopping_point p s inp)
    using pos_leaf

theorem posIB_set_pos_vel_accel_NED_m a b c (hs : PosIB K p s) :
    PosIB K p (set_pos_vel_accel_NED_m s a b c) := by
  frame_gen State (fun s' : State => PosIB K p s') (set_pos_vel_accel_NED_m s a b c) using pos_leaf

theorem posIB_init_pos_terrain_D_m x (hs : PosIB K p s) :
    PosIB K p (init_pos_terrain_D_m s x) := by
  frame_gen State (fun s' : State => PosIB K p s') (init_pos_terrain_D_m s x) using pos_leaf

theorem posIB_set_reset_handling_method m (hs : PosIB K p s) :
    PosIB K p (set_reset_handling_method s m) := by
  frame_gen State (fun s' : State => PosIB K p s') (set_reset_handling_method s m) using pos_leaf

end

/-! ### `D_update_controller`: the acceleration `IMAX` is raised to the hover throttle

`if (throttle_hover > _pid_accel_z.imax()) _pid_accel_z.set_imax(throttle_hover)`: the limit only
grows, to `|hover|`, and only when `hover` exceeds it. With `K = max(IMAX, hover)` (hover in
`[0, 1]`), `K` is the same before and after, and every write of the integrator in the call is a
clamp to the `IMAX` of the moment, which is at most `K`. -/

/-- The parameters as `D_update_controller` may have them: unchanged, or with the acceleration
limit raised to `|hover|` when `hover` exceeded it. -/
structure DParam (K : ℝ) (p : AC_PosControl.Params) (h : Float32) (p' : AC_PosControl.Params) :
    Prop where
  accel : KOK p'._pid_accel_d_m._kimax
  accelK : p'._pid_accel_d_m._kimax.toReal ≤ K
  veld : p'._pid_vel_d_m = p._pid_vel_d_m
  cases : p' = p ∨ (p' = { p with _pid_accel_d_m := AC_PID.set_imax p._pid_accel_d_m h } ∧
    p._pid_accel_d_m._kimax.toReal < h.toReal)

/-- The hover throttle as the position controller reads it: finite, in `[0, 1]`. -/
def HovOK (h : Float32) : Prop := h.IsFinite ∧ 0 ≤ h.toReal ∧ h.toReal ≤ 1

theorem dparam_init {K : ℝ} (p : AC_PosControl.Params) (h : Float32)
    (hk : KOK p._pid_accel_d_m._kimax) (hK : p._pid_accel_d_m._kimax.toReal ≤ K) :
    DParam K p h p := ⟨hk, hK, rfl, Or.inl rfl⟩

theorem dparam_set_imax (p : AC_PosControl.Params) (h : Float32) (hh : HovOK h)
    (hk : KOK p._pid_accel_d_m._kimax)
    (hc : h > AC_PID.imax p._pid_accel_d_m) :
    DParam (max p._pid_accel_d_m._kimax.toReal h.toReal) p h
      { p with _pid_accel_d_m := AC_PID.set_imax p._pid_accel_d_m h } := by
  have hlt : p._pid_accel_d_m._kimax.toReal < h.toReal :=
    (Float32.lt_iff_toReal_lt hk.1 hh.1).1 hc
  have habs : (Float32.abs h).toReal = h.toReal ∧ (Float32.abs h).IsFinite :=
    ⟨by rw [Float32.toReal_abs, abs_of_nonneg hh.2.1], (Float32.isFinite_abs h).2 hh.1⟩
  have hm : (1 : ℝ) ≤ maxFinite32 / 2 := by rw [maxFinite32]; norm_num
  have hkk : ({ p with _pid_accel_d_m := AC_PID.set_imax p._pid_accel_d_m h } :
      AC_PosControl.Params)._pid_accel_d_m._kimax = Float32.abs h := rfl
  refine ⟨?_, ?_, rfl, Or.inr ⟨rfl, hlt⟩⟩
  · rw [hkk]; exact ⟨habs.2, by rw [habs.1]; exact hh.2.1, by rw [habs.1]; linarith [hh.2.2]⟩
  · rw [hkk, habs.1]; exact le_max_right _ _

open AC_PosControl in
theorem D_update_controller_frame (p : Params) (s : State) o inp
    (hh : HovOK inp.get_throttle_hover)
    (hk : PosKOK (max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal) p)
    (hs : PosIB (max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal) p s) :
    DParam (max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal) p
        inp.get_throttle_hover (D_update_controller p s o inp).1 ∧
      PosIB (max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal) p
        (D_update_controller p s o inp).2.1 := by
  frame_genN [Params, State]
    [DParam (max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal) p
        inp.get_throttle_hover,
      PosIB (max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal) p]
    (D_update_controller p s o inp) using first
    | exact dparam_init p _ hk.accel (le_max_left _ _)
    | exact dparam_set_imax p _ hh hk.accel (by assumption)
    | pos_leaf

/-- **`D_update_controller`, M2 form.** With `K = max(IMAX_accel, hover)`: the limits stay proper,
`K` is unchanged by the call (the new `IMAX` is the old one or `|hover| = hover > IMAX`), and the
integrators stay within their bounds. -/
theorem posIB_D_update_controller (p : AC_PosControl.Params) (s : AC_PosControl.State) o inp
    (hh : HovOK inp.get_throttle_hover)
    (hk : PosKOK (max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal) p)
    (hs : PosIB (max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal) p s) :
    let r := AC_PosControl.D_update_controller p s o inp
    let K' := max r.1._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal
    PosKOK K' r.1 ∧ PosIB K' r.1 r.2.1 := by
  intro r K'
  obtain ⟨hd, hb⟩ := D_update_controller_frame p s o inp hh hk hs
  have hKK : K' = max p._pid_accel_d_m._kimax.toReal inp.get_throttle_hover.toReal := by
    rcases hd.cases with h1 | ⟨h1, hlt⟩
    · show max r.1._pid_accel_d_m._kimax.toReal _ = _
      rw [show r.1 = p from h1]
    · show max r.1._pid_accel_d_m._kimax.toReal _ = _
      rw [show r.1 = _ from h1]
      show max (Float32.abs inp.get_throttle_hover).toReal _ = _
      rw [Float32.toReal_abs, abs_of_nonneg hh.2.1, max_self, max_eq_right hlt.le]
  rw [hKK]
  refine ⟨⟨hd.accel, hd.accelK, ?_⟩, ⟨hb.accel, ?_⟩⟩
  · rw [hd.veld]; exact hk.veld
  · rw [hd.veld]; exact hb.veld

end Pos

/-! ## The vehicle -/

section World

open Vehicle Att Pos

/-- The hover throttle the position controller reads (`get_throttle_hover` of the motors):
`constrain_value_line(MOT_THST_HOVER, 0.125, 0.6875)`. -/
abbrev hov (w : World) : Float32 := AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover w.mp

/-- The bound of the vertical acceleration integrator: `max(IMAX, hover)`. -/
noncomputable abbrev KA (w : World) : ℝ := max w.pp._pid_accel_d_m._kimax.toReal (hov w).toReal

/-- **The M2 invariant**: the limits are proper and every scalar integrator is within its bound. -/
structure IntOK (w : World) : Prop where
  attK : AttKOK w.ap
  att : AttIB w.ap w.as
  posK : PosKOK (KA w) w.pp
  pos : PosIB (KA w) w.pp w.ps

theorem hovOK (mp : AP_Motors_lib.AP_MotorsMatrix.Params) :
    HovOK (AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover mp) := by
  have hm : (1 : ℝ) ≤ maxFinite32 / 2 := by rw [maxFinite32]; norm_num
  obtain ⟨h1, h2, h3⟩ := Float32.cvl_mem Float32.two32 (amt := mp._throttle_hover) (A := 0) (B := 1)
    Float32.isFinite_lit_eighth Float32.isFinite_lit_0_6875
    (by rw [Float32.toReal_lit_eighth]; norm_num; linarith)
    (by rw [Float32.toReal_lit_0_6875]; norm_num; linarith)
    (by rw [Float32.toReal_lit_eighth]; norm_num) (by rw [Float32.toReal_lit_0_6875]; norm_num)
    (by rw [Float32.toReal_lit_eighth]; norm_num) (by rw [Float32.toReal_lit_0_6875]; norm_num)
  exact ⟨h1, h2, h3⟩

theorem hover_output (mp : AP_Motors_lib.AP_MotorsMatrix.Params) ms o inp :
    (AP_Motors_lib.AP_MotorsMatrix.output mp ms o inp).1._throttle_hover = mp._throttle_hover := by
  frame_gen AP_Motors_lib.AP_MotorsMatrix.Params
    (fun p' : AP_Motors_lib.AP_MotorsMatrix.Params => p'._throttle_hover = mp._throttle_hover)
    (AP_Motors_lib.AP_MotorsMatrix.output mp ms o inp) using first
    | with_reducible rfl
    | with_reducible assumption

/-- The motors' output does not change the hover throttle, so it keeps the invariant. -/
theorem intOK_output (w : World) o inp (hw : IntOK w) :
    IntOK { w with mp := (AP_Motors_lib.AP_MotorsMatrix.output w.mp w.ms o inp).1,
                   ms := (AP_Motors_lib.AP_MotorsMatrix.output w.mp w.ms o inp).2.1 } := by
  have hh : AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover
      (AP_Motors_lib.AP_MotorsMatrix.output w.mp w.ms o inp).1 =
      AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover w.mp := by
    simp only [AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover, hover_output]
  exact ⟨hw.attK, hw.att, by simp only [KA, hov, hh]; exact hw.posK,
    by simp only [KA, hov, hh]; exact hw.pos⟩

/-- `D_update_controller` on the world: the bound `KA` is the same after the call. -/
theorem intOK_D_update_controller (w : World) (hw : IntOK w) :
    let r := AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w)
    PosKOK (max r.1._pid_accel_d_m._kimax.toReal (hov w).toReal) r.1 ∧
      PosIB (max r.1._pid_accel_d_m._kimax.toReal (hov w).toReal) r.1 r.2.1 :=
  posIB_D_update_controller w.pp w.ps #[] (posInputs w) (hovOK w.mp) hw.posK hw.pos

/-- The leaf tactic of the vehicle-level M2 proof. -/
macro "int_leaf" : tactic => `(tactic| first
  | field_assumption
  | (with_reducible exact Contracts.Track.intOK_output _ _ _ (by field_assumption))
  | (constructor <;> first
      | field_assumption
      | (with_reducible exact (Contracts.Track.intOK_D_update_controller _ (by field_assumption)).1)
      | (with_reducible exact (Contracts.Track.intOK_D_update_controller _ (by field_assumption)).2)
      | (with_reducible apply Contracts.Track.Att.attIB_rate_controller_run <;> field_assumption)
      | (with_reducible apply Contracts.Track.Att.attIB_set_dt_s <;> field_assumption)
      | (with_reducible apply Contracts.Track.Att.attIB_rate_controller_target_reset <;> field_assumption)
      | (with_reducible apply Contracts.Track.Att.attIB_landed_gain_reduction <;> field_assumption)
      | (with_reducible apply Contracts.Track.Att.attIB_set_roll_pitch_rate_tc <;> field_assumption)
      | (with_reducible apply Contracts.Track.Att.attIB_set_yaw_rate_tc <;> field_assumption)
      | (with_reducible apply Contracts.Track.Att.attIB_set_throttle_out <;> field_assumption)
      | (with_reducible apply Contracts.Track.Att.attIB_input_thrust_vector_heading <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_set_dt_s <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_update_estimates <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_set_pos_terrain_target_D_m <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_NE_set_max_speed_accel_m <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_NE_set_correction_speed_accel_m <;>
          field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_NE_init_controller_stopping_point <;>
          field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_NE_update_controller <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_D_set_max_speed_accel_m <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_D_set_correction_speed_accel_m <;>
          field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_D_init_controller_stopping_point <;>
          field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_set_pos_vel_accel_NED_m <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_init_pos_terrain_D_m <;> field_assumption)
      | (with_reducible apply Contracts.Track.Pos.posIB_set_reset_handling_method <;>
          field_assumption)))

set_option maxHeartbeats 20000000 in
set_option frame_gen.inline 16 in
/-- **M2, one tick.** -/
theorem intOK_tick (w : World) (smp : Sample) (hw : IntOK w) : IntOK (tick w smp).1 := by
  frame_gen World (fun w' : World => IntOK w') (tick w smp) using int_leaf

/-- The takeover keeps the invariant (the rate integrators are reset; `LibmSpec` gives the value of
the `(float) 0.0` it writes). -/
theorem intOK_takeover (hL : Contracts.Mission.LibmSpec) (w : World) (smp : Sample)
    (hw : IntOK w) : IntOK (takeover w smp) := by
  frame_gen World (fun w' : World => IntOK w') (takeover w smp) using first
    | int_leaf
    | (constructor <;> first
        | field_assumption
        | (with_reducible apply Contracts.Track.Att.attIB_relax_attitude_controllers_void hL <;>
            field_assumption))

end World

/-! ## M2 on the controller component -/

section Lifted

open Vehicle Contracts.Mission

theorem tickT_intOK (hL : LibmSpec) (w₀ : World) (h₀ : IntOK w₀) (s : Option World)
    (hs : ∀ w, s = some w → IntOK w) (smp : Sample) :
    ∀ w, (tickT w₀ s smp).1 = some w → IntOK w := by
  intro w hw
  cases s with
  | some w' =>
    simp only [tickT, Option.some.injEq] at hw
    rw [← hw]
    exact intOK_tick _ smp (hs w' rfl)
  | none =>
    simp only [tickT, Option.some.injEq] at hw
    rw [← hw]
    exact intOK_tick _ smp (intOK_takeover hL w₀ smp h₀)

/-- **M2 (`integrators_bounded`).** From an initial world satisfying the invariant, along every
behavior of the controller component, every hidden world satisfies it: the limits are proper and the
three rate integrators, the vertical acceleration integrator (against `max(IMAX, hover)`) and the
vertical velocity integrator are finite and within their limits, whatever the samples are (NaN and
`±∞` included). -/
theorem integrators_bounded (hL : LibmSpec) (w₀ : World) (h₀ : IntOK w₀) {x : ℕ → X}
    (s : ℕ → Option World) (hs0 : s 0 = none)
    (hstep : ∀ t, (s (t + 1), (x t).out) = tickT w₀ (s t) (x t).smp) :
    ∀ t w, s t = some w → IntOK w := by
  intro t
  induction t with
  | zero => intro w hw; rw [hs0] at hw; cases hw
  | succ t ih =>
    intro w hw
    have := congrArg Prod.fst (hstep t)
    simp only at this
    rw [this] at hw
    exact tickT_intOK hL w₀ h₀ (s t) ih (x t).smp w hw

end Lifted

end Contracts.Track
