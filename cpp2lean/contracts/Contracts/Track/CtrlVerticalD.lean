import Contracts.Track.CtrlVerticalIO

/-!
# C5 + C6 inside `AC_PosControl::D_update_controller`

`D_update_controller` on its nominal branches (EKF reset count unchanged, controller active,
vibration compensation off, hover throttle not above `IMAX`), field by field (`dupd_vel`,
`dupd_acc`, `dupd_par`, `dupd_out`), in terms of the preamble state `preD` (offsets and terrain
updated; `preD_*`: nothing else changes). On the region `DReg` (with the offset and terrain
channels zero, `OffZ`), the vertical laws of `VERTICAL.md` §7 with explicit `β`:

* `dctrl_vt`: `⟦vt⟧ = (sp - z) + vsp + β`;
* `dctrl_vel`: `⟦eV⁺⟧ = eV + αV ((⟦vt⟧ - vz) - eV) + β`, PI output `5 ⟦eV⁺⟧ + β`;
* `dctrl_at`: `⟦at⟧ = 5 ⟦eV⁺⟧ + asp + β`; `dctrl_am`: `⟦am⟧ = accel_ef.z + 9.80665016f + β`;
* `dctrl_acc`: `⟦eA⁺⟧ = eA + αA ((⟦at⟧ - ⟦am⟧) - eA) + β`, `⟦I⁺⟧ = I + kiDt ⟦eA⁺⟧ + β`;
* `dctrl_thr`: `thrust_d_norm = kpAcc ⟦eA⁺⟧ + ⟦I⁺⟧ - hover + β`.

`dctrl2_*` are the same on the region `DReg2` (magnitudes of the errors rather than of the signals)
with the parameters `DPar2` and the float fact `PiF32`; the tick uses these.
-/

namespace Contracts.Track.CtrlV

open Float.Model UnpackedFloat Contracts.Mission

noncomputable section

set_option linter.unusedSimpArgs false

section DCtrl
open AC_PosControl_lib AC_PosControl

/-- The position controller's state after the preamble of `D_update_controller` (EKF reset
handling with an unchanged reset count, the controller active, the offsets and the terrain
updated). -/
def preD (s : State) (inp : Inputs) : State :=
  update_terrain (D_update_offsets { s with _last_update_d_ticks := inp.ticks32 } inp)

theorem ekf_reset_id (s : State) (inp : Inputs)
    (h : inp.get_position_D_reset_count = s._ahrs_position_D_reset_count) :
    D_handle_ekf_reset s inp = s := by
  simp only [D_handle_ekf_reset, Id.run, h, bne_self_eq_false, Bool.false_eq_true, ite_false]
  rfl

/-- The vertical position target `D_update_controller` builds: desired + offset + terrain. -/
def tgtZ (s : State) : Float :=
  s._pos_desired_ned_m.z + s._pos_offset_ned_m.z + Float32.toFloat s._pos_terrain_d_m

/-- The vertical velocity target after the P stage. -/
def velT (p : Params) (s : State) (inp : Inputs) : Float32 :=
  (AC_P_1D.update_all p._p_pos_d_m s._p_pos_d_m (tgtZ s) s._pos_estimate_ned_m.z).2.2 *
      inp.get_control_gain_scaler_Z +
    (s._vel_desired_ned_ms.z + s._vel_offset_ned_ms.z + s._vel_terrain_d_ms)

/-- The velocity PI. -/
def velB (p : Params) (s : State) (inp : Inputs) : AC_PID_Basic.State × Float32 :=
  AC_PID_Basic.update_all_float3_bool2 p._pid_vel_d_m s._pid_vel_d_m (velT p s inp)
    s._vel_estimate_ned_ms.z s._dt_s inp.limit_throttle_lower inp.limit_throttle_upper

/-- The vertical acceleration target. -/
def accT (p : Params) (s : State) (inp : Inputs) : Float32 :=
  (velB p s inp).2 * inp.get_control_gain_scaler_Z +
    (s._accel_desired_ned_mss.z + s._accel_offset_ned_mss.z + s._accel_terrain_d_mss)

/-- The acceleration PID. -/
def accA (p : Params) (s : State) (inp : Inputs) : AC_PID.State × Float32 :=
  AC_PID.update_all p._pid_accel_d_m s._pid_accel_d_m inp._pid_accel_d_m (accT p s inp)
    (get_estimated_accel_D_mss inp) s._dt_s (inp.limit_throttle_lower || inp.limit_throttle_upper)
    1.0 1.0

/-- The normalised thrust `thrust_d_norm` (before the sign of `set_throttle_out`). -/
def thrN (p : Params) (s : State) (inp : Inputs) : Float32 :=
  (accA p s inp).2 + AC_PID.get_ff (accA p s inp).1 - inp.get_throttle_hover

/-- Unfolds `D_update_controller` along the nominal branches. -/
macro "dupd_unfold" : tactic => `(tactic| (
  unfold D_update_controller
  simp only [Id.run, id_pure_eq, id_bind_eq, Bool.not_true, Bool.false_eq_true, ite_false,
    ite_true, *]))

theorem dupd_vel (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (hr : inp.get_position_D_reset_count = s._ahrs_position_D_reset_count)
    (ha : D_is_active s inp = true) (hv : (preD s inp)._vibe_comp_enabled = false)
    (hh : ¬ (inp.get_throttle_hover > AC_PID.imax p._pid_accel_d_m)) :
    (D_update_controller p s o inp).2.1._pid_vel_d_m = (velB p (preD s inp) inp).1 := by
  have he := ekf_reset_id s inp hr
  simp only [preD] at hv
  dupd_unfold
  split <;> (try split) <;> rfl

theorem dupd_acc (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (hr : inp.get_position_D_reset_count = s._ahrs_position_D_reset_count)
    (ha : D_is_active s inp = true) (hv : (preD s inp)._vibe_comp_enabled = false)
    (hh : ¬ (inp.get_throttle_hover > AC_PID.imax p._pid_accel_d_m)) :
    (D_update_controller p s o inp).2.1._pid_accel_d_m = (accA p (preD s inp) inp).1 := by
  have he := ekf_reset_id s inp hr
  simp only [preD] at hv
  dupd_unfold
  split <;> (try split) <;> rfl

theorem dupd_par (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (hr : inp.get_position_D_reset_count = s._ahrs_position_D_reset_count)
    (ha : D_is_active s inp = true) (hv : (preD s inp)._vibe_comp_enabled = false)
    (hh : ¬ (inp.get_throttle_hover > AC_PID.imax p._pid_accel_d_m)) :
    (D_update_controller p s o inp).1 = p := by
  have he := ekf_reset_id s inp hr
  simp only [preD] at hv
  dupd_unfold
  split <;> (try split) <;> rfl

theorem dupd_out (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (hr : inp.get_position_D_reset_count = s._ahrs_position_D_reset_count)
    (ha : D_is_active s inp = true) (hv : (preD s inp)._vibe_comp_enabled = false)
    (hh : ¬ (inp.get_throttle_hover > AC_PID.imax p._pid_accel_d_m)) :
    (D_update_controller p s o inp).2.2 =
      o.push (Output.set_throttle_out (-thrN p (preD s inp) inp) true 2.0) := by
  have he := ekf_reset_id s inp hr
  simp only [preD] at hv
  dupd_unfold
  split <;> (try split) <;> rfl

/-! The preamble changes only the offsets, the terrain and the tick stamp. -/

theorem preD_pidV (s : State) (inp : Inputs) : (preD s inp)._pid_vel_d_m = s._pid_vel_d_m := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_pidA (s : State) (inp : Inputs) : (preD s inp)._pid_accel_d_m = s._pid_accel_d_m := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_pP (s : State) (inp : Inputs) : (preD s inp)._p_pos_d_m = s._p_pos_d_m := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_posE (s : State) (inp : Inputs) : (preD s inp)._pos_estimate_ned_m = s._pos_estimate_ned_m := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_velE (s : State) (inp : Inputs) : (preD s inp)._vel_estimate_ned_ms = s._vel_estimate_ned_ms := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_posD (s : State) (inp : Inputs) : (preD s inp)._pos_desired_ned_m = s._pos_desired_ned_m := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_velD (s : State) (inp : Inputs) : (preD s inp)._vel_desired_ned_ms = s._vel_desired_ned_ms := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_accD (s : State) (inp : Inputs) : (preD s inp)._accel_desired_ned_mss = s._accel_desired_ned_mss := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_dt (s : State) (inp : Inputs) : (preD s inp)._dt_s = s._dt_s := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl

theorem preD_vibe (s : State) (inp : Inputs) : (preD s inp)._vibe_comp_enabled = s._vibe_comp_enabled := by
  simp only [preD, update_terrain, D_update_offsets, Id.run, id_pure_eq, id_bind_eq]
  split <;> rfl


/-! ## The vertical controller of `D_update_controller` (C5 + C6) -/

theorem gf_unpack : (9.80665016 : Float32).toModel.unpack = .finite .positive 10283018 (-20)
    (by decide) := by f32_unpack
theorem gf_fin : (9.80665016 : Float32).IsFinite := Float32.isFinite_of_unpack gf_unpack
/-- `9.80665016f` as a real. -/
def gfR : ℝ := 5141509 / 524288
theorem gf_val : (9.80665016 : Float32).toReal = gfR := by
  rw [Float32.toReal_of_unpack gf_unpack, gfR]; simp [Sign.apply]; norm_num

/-- A float that is `0`: finite, real value `0`. -/
def Z32 (x : Float32) : Prop := x.IsFinite ∧ x.toReal = 0
def Z64 (x : Float) : Prop := x.IsFinite ∧ x.toReal = 0

/-- The vertical offsets and terrain channels are zero. -/
structure OffZ (s : State) : Prop where
  pos : Z64 s._pos_offset_ned_m.z
  vel : Z32 s._vel_offset_ned_ms.z
  acc : Z32 s._accel_offset_ned_mss.z
  tpos : Z32 s._pos_terrain_d_m
  tvel : Z32 s._vel_terrain_d_ms
  tacc : Z32 s._accel_terrain_d_mss

/-- The parameters of the vertical position, velocity and acceleration controllers
(`PSC_D_POS_P 1`, `PSC_D_VEL_P 5`, `PSC_D_ACC_P 0.05`, `PSC_D_ACC_I 0.1`, the rest as in
`accel_pid`, `vel_pi`). -/
structure DPar (p : Params) : Prop where
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
  vfE : p._pid_vel_d_m._filt_E_hz.IsFinite
  vfEv : p._pid_vel_d_m._filt_E_hz.toReal = 5
  vfD : p._pid_vel_d_m._filt_D_hz.IsFinite
  vfDv : p._pid_vel_d_m._filt_D_hz.toReal = 5
  akp : p._pid_accel_d_m._kp.IsFinite
  akpv : p._pid_accel_d_m._kp.toReal = kpA
  aki : p._pid_accel_d_m._ki.IsFinite
  akiv : p._pid_accel_d_m._ki.toReal = kiA
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
  afE : p._pid_accel_d_m._filt_E_hz.IsFinite
  afEv : p._pid_accel_d_m._filt_E_hz.toReal = 20
  afD : p._pid_accel_d_m._filt_D_hz.IsFinite
  afDv : p._pid_accel_d_m._filt_D_hz.toReal = 0
  aimx : p._pid_accel_d_m._kimax.IsFinite
  aimx' : p._pid_accel_d_m._kimax.toReal ≤ 2 ^ 10

/-- The region of the vertical controller (TRACK_PLAN.md 3.2, D6, D13, D15) on the position
controller's state as `D_update_controller` reads it: finite values, the position error `≤ E`
inside the linear zone and the error limits, velocities `≤ MV`, accelerations `≤ MA`, the
integrator `MA/2¹⁰` inside `IMAX`, the filters not in reset, the vibration compensation off. -/
structure DReg (p : Params) (s : State) (E MV MA : ℝ) : Prop where
  E0 : 1 / 2 ^ 20 ≤ E
  E1 : E ≤ 1
  MV1 : 1 ≤ MV
  MV2 : MV ≤ 2 ^ 6
  MA2 : MA ≤ 2 ^ 10
  dt : s._dt_s.IsFinite
  dtv : s._dt_s.toReal = dtR
  emin : s._p_pos_d_m._error_min.IsFinite
  eminv : s._p_pos_d_m._error_min.toReal ≤ -(2 * E)
  emax : s._p_pos_d_m._error_max.IsFinite
  emaxv : 2 * E ≤ s._p_pos_d_m._error_max.toReal
  d1 : s._p_pos_d_m._D1_max.IsFinite
  d1v : 2 * E ≤ s._p_pos_d_m._D1_max.toReal
  sp : s._pos_desired_ned_m.z.IsFinite
  z : s._pos_estimate_ned_m.z.IsFinite
  ez : |s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal| ≤ E
  off : OffZ s
  vsp : s._vel_desired_ned_ms.z.IsFinite
  vz : s._vel_estimate_ned_ms.z.IsFinite
  vspb : |s._vel_desired_ned_ms.z.toReal| + E + 1 ≤ MV
  vzb : |s._vel_estimate_ned_ms.z.toReal| ≤ MV
  vr : s._pid_vel_d_m._reset_filter = false
  ve : s._pid_vel_d_m._error.IsFinite
  veb : |s._pid_vel_d_m._error.toReal| ≤ 2 * MV
  vd : s._pid_vel_d_m._derivative.IsFinite
  vdb : |s._pid_vel_d_m._derivative.toReal| ≤ 2 ^ 30
  asp : s._accel_desired_ned_mss.z.IsFinite
  aspb : |s._accel_desired_ned_mss.z.toReal| + 16 * MV + 1 ≤ MA
  ar : s._pid_accel_d_m._flags._reset_filter = false
  aT : s._pid_accel_d_m._target.IsFinite
  aTb : |s._pid_accel_d_m._target.toReal| ≤ MA
  ae : s._pid_accel_d_m._error.IsFinite
  aeb : |s._pid_accel_d_m._error.toReal| ≤ 2 * MA
  aI : s._pid_accel_d_m._integrator.IsFinite
  aIb : |s._pid_accel_d_m._integrator.toReal| + MA / 2 ^ 10 ≤ p._pid_accel_d_m._kimax.toReal
  ad : s._pid_accel_d_m._derivative.IsFinite
  adb : |s._pid_accel_d_m._derivative.toReal| ≤ 2 ^ 30

/-- What `D_update_controller` reads from the other objects, inside the region: the gain scaler
`1`, the motors' throttle limits clear, the measured specific force within `MA - 1` of `-g`, the
hover throttle in `[0, 1]`. -/
structure DInp (inp : Inputs) (MA : ℝ) : Prop where
  gz : inp.get_control_gain_scaler_Z.IsFinite
  gzv : inp.get_control_gain_scaler_Z.toReal = 1
  lo : inp.limit_throttle_lower = false
  up : inp.limit_throttle_upper = false
  acc : inp.get_accel_ef.z.IsFinite
  accb : |inp.get_accel_ef.z.toReal + gfR| + 1 ≤ MA
  hov : inp.get_throttle_hover.IsFinite
  hov0 : 0 ≤ inp.get_throttle_hover.toReal
  hov1 : inp.get_throttle_hover.toReal ≤ 1

theorem dctrl_vt (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) {E MV MA : ℝ}
    (hp : DPar p) (hs : DReg p s E MV MA) (hi : DInp inp MA) :
    A32 (velT p s inp) (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal +
      s._vel_desired_ned_ms.z.toReal) (u32 * (2 * E + MV) + 4 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  -- the position target is the desired position (zero offset and terrain)
  obtain ⟨ft1, vt1⟩ := f64_add_exact hs.sp hs.off.pos.1 hs.sp (by rw [hs.off.pos.2, add_zero])
  obtain ⟨tf, tv⟩ := hL.f32ToF64 _ hs.off.tpos.1
  obtain ⟨ft2, vt2⟩ := f64_add_exact ft1 tf hs.sp (by rw [vt1, tv, hs.off.tpos.2, add_zero])
  have htz : (tgtZ s).IsFinite ∧ (tgtZ s).toReal = s._pos_desired_ned_m.z.toReal := ⟨ft2, vt2⟩
  -- the P stage
  obtain ⟨-, hP, -⟩ := pos_p hL p._p_pos_d_m s._p_pos_d_m (tgtZ s) s._pos_estimate_ned_m.z
    hp.kpP hp.kpPv htz.1 hs.z hs.E0 (by linarith [hs.E1]) (by rw [htz.2]; exact hs.ez)
    hs.emin hs.eminv hs.emax hs.emaxv hs.d1 hs.d1v
  rw [htz.2] at hP
  obtain ⟨g1f, g1v⟩ := f32_mul_one hP.1 hi.gz hi.gzv
  -- the velocity feedforward (zero offset and terrain)
  obtain ⟨v1f, v1v⟩ := f32_add_zero hs.vsp hs.off.vel.1 hs.off.vel.2
  obtain ⟨v2f, v2v⟩ := f32_add_zero v1f hs.off.tvel.1 hs.off.tvel.2
  have hP' : A32 ((AC_P_1D.update_all p._p_pos_d_m s._p_pos_d_m (tgtZ s)
      s._pos_estimate_ned_m.z).2.2 * inp.get_control_gain_scaler_Z)
      (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal) (2 * u32 * E + 2 * η32) :=
    ⟨g1f, by rw [g1v]; exact hP.2⟩
  have hV : A32 (s._vel_desired_ned_ms.z + s._vel_offset_ned_ms.z + s._vel_terrain_d_ms)
      s._vel_desired_ned_ms.z.toReal 0 := ⟨v2f, by rw [v2v, v1v]; simp⟩
  have hsum := hP'.add hV (by
    have := abs_add_le (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal)
      s._vel_desired_ned_ms.z.toReal
    have := hs.ez; have := hs.vspb; have := hs.MV2; have := hs.E1
    rw [hu]; norm_num [capF]; nlinarith)
  refine hsum.mono ?_
  have := abs_add_le (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal)
    s._vel_desired_ned_ms.z.toReal
  have := hs.ez; have := hs.vspb; have := hs.E1; have := hs.MV2
  rw [hu]; nlinarith


theorem velT_bound (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) {E MV MA : ℝ}
    (hp : DPar p) (hs : DReg p s E MV MA) (hi : DInp inp MA) :
    (velT p s inp).IsFinite ∧ |(velT p s inp).toReal| ≤ MV := by
  have h := dctrl_vt hL p s inp hp hs hi
  refine ⟨h.1, ?_⟩
  have h1 := h.abs_le
  have := abs_add_le (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal)
    s._vel_desired_ned_ms.z.toReal
  have := hs.ez; have := hs.vspb; have := hs.E1; have := hs.MV2
  have hη1 := η32_small
  rw [u32_eq] at h1; nlinarith

/-- **C5 in `D_update_controller`, the velocity PI.** -/
theorem dctrl_vel (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) {E MV MA : ℝ}
    (hp : DPar p) (hs : DReg p s E MV MA) (hi : DInp inp MA) :
    let B := velB p s inp
    A32 B.1._error (s._pid_vel_d_m._error.toReal + αVr * (((velT p s inp).toReal -
        s._vel_estimate_ned_ms.z.toReal) - s._pid_vel_d_m._error.toReal)) (40 * u32 * MV + 4 * η32) ∧
    A32 B.2 (5 * B.1._error.toReal) (16 * u32 * MV + η32) ∧
    B.1._reset_filter = false ∧ B.1._derivative.IsFinite ∧ |B.1._derivative.toReal| ≤ 2 ^ 30 ∧
    |B.1._error.toReal| ≤ 3 * MV ∧ B.1._integrator = 0.0 := by
  obtain ⟨hvf, hvb⟩ := velT_bound hL p s inp hp hs hi
  exact vel_pi hL p._pid_vel_d_m s._pid_vel_d_m (velT p s inp) s._vel_estimate_ned_ms.z s._dt_s
    inp.limit_throttle_lower inp.limit_throttle_upper hp.vkp hp.vkpv hp.vki hp.vkiv hp.vkd hp.vkdv
    hp.vkff hp.vkffv hp.vfE hp.vfEv hp.vfD hp.vfDv hs.dt hs.dtv hs.vr hs.ve hs.vd hvf hs.vz
    hs.MV1 (by linarith [hs.MV2]) hvb hs.vzb hs.veb hs.vdb

/-- The acceleration target: `5 ⟦eV⁺⟧ + asp` (zero offset and terrain). -/
theorem dctrl_at (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) {E MV MA : ℝ}
    (hp : DPar p) (hs : DReg p s E MV MA) (hi : DInp inp MA) :
    A32 (accT p s inp) (5 * (velB p s inp).1._error.toReal + s._accel_desired_ned_mss.z.toReal)
      (u32 * (32 * MV + MA) + 3 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  obtain ⟨-, hB2, -, -, -, hEb, -⟩ := dctrl_vel hL p s inp hp hs hi
  obtain ⟨g1f, g1v⟩ := f32_mul_one hB2.1 hi.gz hi.gzv
  obtain ⟨a1f, a1v⟩ := f32_add_zero hs.asp hs.off.acc.1 hs.off.acc.2
  obtain ⟨a2f, a2v⟩ := f32_add_zero a1f hs.off.tacc.1 hs.off.tacc.2
  have hB2' : A32 ((velB p s inp).2 * inp.get_control_gain_scaler_Z)
      (5 * (velB p s inp).1._error.toReal) (16 * u32 * MV + η32) := ⟨g1f, by rw [g1v]; exact hB2.2⟩
  have hA : A32 (s._accel_desired_ned_mss.z + s._accel_offset_ned_mss.z + s._accel_terrain_d_mss)
      s._accel_desired_ned_mss.z.toReal 0 := ⟨a2f, by rw [a2v, a1v]; simp⟩
  have hsb : |5 * (velB p s inp).1._error.toReal + s._accel_desired_ned_mss.z.toReal| ≤ MA := by
    have := abs_add_le (5 * (velB p s inp).1._error.toReal) s._accel_desired_ned_mss.z.toReal
    rw [abs_mul, show |(5 : ℝ)| = 5 by norm_num] at this
    have := hs.aspb; have := hs.MV1; linarith
  have hsum := hB2'.add hA (by
    have := hs.MA2; have := hs.MV2
    rw [hu]; norm_num [capF]; nlinarith)
  refine hsum.mono ?_
  have := hs.MA2; have := hs.MV2; have := hs.MV1
  rw [hu]; nlinarith

/-- The measured acceleration `accel_ef.z + 9.80665016f`. -/
theorem dctrl_am (inp : Inputs) {MA : ℝ} (hi : DInp inp MA) (hMA : MA ≤ 2 ^ 10) :
    A32 (get_estimated_accel_D_mss inp) (inp.get_accel_ef.z.toReal + gfR) (u32 * MA + η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have h := (A32.of_exact hi.acc).add ((A32.of_exact gf_fin).congr gf_val) (by
    have := hi.accb; norm_num [capF]; linarith)
  refine h.mono ?_
  have := hi.accb
  simp only [add_zero, zero_add]
  have := u32_pos
  nlinarith

/-- `|⟦am⟧| ≤ MA`. -/
theorem am_bound (inp : Inputs) {MA : ℝ} (hi : DInp inp MA) (hMA : MA ≤ 2 ^ 10) :
    |(get_estimated_accel_D_mss inp).toReal| ≤ MA := by
  have h := (dctrl_am inp hi hMA).abs_le
  have := hi.accb; have hη1 := η32_small
  rw [u32_eq] at h; nlinarith

/-- **C6 in `D_update_controller`, the acceleration PID.** -/
theorem dctrl_acc (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) {E MV MA : ℝ}
    (hp : DPar p) (hs : DReg p s E MV MA) (hi : DInp inp MA) :
    let A := accA p s inp
    A32 A.1._error (s._pid_accel_d_m._error.toReal + (16042859 / 67108864 : ℝ) *
        (((accT p s inp).toReal - (get_estimated_accel_D_mss inp).toReal) -
          s._pid_accel_d_m._error.toReal)) (44 * u32 * MA + 4 * η32) ∧
    A32 A.1._integrator (s._pid_accel_d_m._integrator.toReal + kiA * dtR * A.1._error.toReal)
        (u32 * |s._pid_accel_d_m._integrator.toReal| + u32 * MA / 2 ^ 7 + 4 * η32) ∧
    A32 A.2 (kpA * A.1._error.toReal + A.1._integrator.toReal)
        (u32 * (MA / 2 + p._pid_accel_d_m._kimax.toReal) + 4 * η32) ∧
    (AC_PID.get_ff A.1).IsFinite ∧ (AC_PID.get_ff A.1).toReal = 0 ∧
    A.1._flags._reset_filter = false ∧ A.1._derivative.IsFinite ∧
    |A.1._derivative.toReal| ≤ 2 ^ 30 ∧ |A.1._error.toReal| ≤ 3 * MA ∧
    A32 A.1._target (accT p s inp).toReal (13 * u32 * MA + 2 * η32) := by
  intro A
  have hat := dctrl_at hL p s inp hp hs hi
  have hatb : |(accT p s inp).toReal| ≤ MA := by
    have h1 := hat.abs_le
    obtain ⟨-, -, -, -, -, hEb, -⟩ := dctrl_vel hL p s inp hp hs hi
    have := abs_add_le (5 * (velB p s inp).1._error.toReal) s._accel_desired_ned_mss.z.toReal
    rw [abs_mul, show |(5 : ℝ)| = 5 by norm_num] at this
    have := hs.aspb; have := hs.MA2; have := hs.MV2; have := hs.MV1; have hη1 := η32_small
    rw [u32_eq] at h1; nlinarith
  have hMA1 : 1 ≤ MA := by have := hs.aspb; have := hs.MV1; linarith [abs_nonneg s._accel_desired_ned_mss.z.toReal]
  have hlim : (inp.limit_throttle_lower || inp.limit_throttle_upper) = false := by
    rw [hi.lo, hi.up]; rfl
  have h := accel_pid hL p._pid_accel_d_m s._pid_accel_d_m inp._pid_accel_d_m (accT p s inp)
    (get_estimated_accel_D_mss inp) s._dt_s hp.akp hp.akpv hp.aki hp.akiv hp.akd hp.akdv hp.akff
    hp.akffv hp.akdff hp.akdffv hp.apd hp.apdv hp.asr hp.asrv hp.afT hp.afTv hp.afE hp.afEv hp.afD
    hp.afDv hp.aimx hp.aimx' hs.dt hs.dtv hs.ar hs.aT hs.ae hs.aI hs.ad hat.1 (dctrl_am inp hi hs.MA2).1
    hMA1 hs.MA2 hs.aTb hatb (am_bound inp hi hs.MA2) hs.aeb hs.adb hs.aIb
  simp only [A, accA, hlim]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h1⟩

/-- **The thrust command** `thrust_d_norm = (output + get_ff) - hover`. -/
theorem dctrl_thr (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) {E MV MA : ℝ}
    (hp : DPar p) (hs : DReg p s E MV MA) (hi : DInp inp MA) :
    A32 (thrN p s inp) (kpA * (accA p s inp).1._error.toReal + (accA p s inp).1._integrator.toReal -
      inp.get_throttle_hover.toReal) (u32 * (MA + 2 * p._pid_accel_d_m._kimax.toReal + 4) + 6 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  obtain ⟨-, hI, hO, hff, hffv, -, -, -, hEb, -⟩ := dctrl_acc hL p s inp hp hs hi
  obtain ⟨s1f, s1v⟩ := f32_add_zero hO.1 hff hffv
  have hO' : A32 ((accA p s inp).2 + AC_PID.get_ff (accA p s inp).1)
      (kpA * (accA p s inp).1._error.toReal + (accA p s inp).1._integrator.toReal)
      (u32 * (MA / 2 + p._pid_accel_d_m._kimax.toReal) + 4 * η32) := ⟨s1f, by rw [s1v]; exact hO.2⟩
  have hk := hp.aimx'
  have hk0 : 0 ≤ p._pid_accel_d_m._kimax.toReal := by
    have := hs.aIb; have := hs.MA2; linarith [abs_nonneg s._pid_accel_d_m._integrator.toReal,
      show 0 ≤ MA by have := hs.aspb; linarith [abs_nonneg s._pid_accel_d_m._integrator.toReal, abs_nonneg s._accel_desired_ned_mss.z.toReal, hs.MV1]]
  have hMA0 : 0 ≤ MA := by
    have := hs.aspb; have := hs.MV1; linarith [abs_nonneg s._accel_desired_ned_mss.z.toReal]
  have hIb : |(accA p s inp).1._integrator.toReal| ≤ p._pid_accel_d_m._kimax.toReal + 1 := by
    have h1 := hI.abs_le
    have := abs_add_le s._pid_accel_d_m._integrator.toReal (kiA * dtR * (accA p s inp).1._error.toReal)
    have : |kiA * dtR * (accA p s inp).1._error.toReal| ≤ MA / 1300 := by
      rw [abs_mul, abs_mul, kiA, dtR]; norm_num; nlinarith [abs_nonneg (accA p s inp).1._error.toReal]
    have := hs.aIb; have := hs.MA2
    rw [hu] at h1; nlinarith [abs_nonneg s._pid_accel_d_m._integrator.toReal]
  have hrb : |kpA * (accA p s inp).1._error.toReal + (accA p s inp).1._integrator.toReal| ≤
      MA / 2 + p._pid_accel_d_m._kimax.toReal + 1 := by
    have := abs_add_le (kpA * (accA p s inp).1._error.toReal) (accA p s inp).1._integrator.toReal
    have : |kpA * (accA p s inp).1._error.toReal| ≤ MA / 2 := by
      rw [abs_mul, kpA]; norm_num; nlinarith [abs_nonneg (accA p s inp).1._error.toReal]
    linarith
  have hd := abs_sub (kpA * (accA p s inp).1._error.toReal + (accA p s inp).1._integrator.toReal)
      inp.get_throttle_hover.toReal
  rw [abs_of_nonneg hi.hov0] at hd
  have := hi.hov1; have := hs.MA2
  have hsub := hO'.sub ((A32.of_exact hi.hov)) (by
    rw [hu]; norm_num [capF]; linarith)
  refine hsub.mono ?_
  rw [hu]; simp only [add_zero]
  have : 1 / 16777216 * (1 / 16777216 * (MA / 2 + p._pid_accel_d_m._kimax.toReal)) ≤
      1 / 16777216 * 2 := by nlinarith
  nlinarith

end DCtrl

/-! ## Sharp forms (`DPar2`, `DReg2`): exact coefficients, error-scale magnitudes -/

section DCtrl2
open AC_PosControl_lib AC_PosControl

/-- The parameters of the vertical controllers as `D_update_controller` reads them, with the
filter cutoffs as the float literals of `AC_PosControl::init` (`PSC_D_VEL_FLTE = FLTD = 5`,
`PSC_D_ACC_FLTE = 20`) and `IMAX ≤ 2`. -/
structure DPar2 (p : Params) : Prop where
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
  akpv : p._pid_accel_d_m._kp.toReal = kpA
  aki : p._pid_accel_d_m._ki.IsFinite
  akiv : p._pid_accel_d_m._ki.toReal = kiA
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

/-- The velocity-error scale of the region: `E + Ev + 1/8`. -/
def MeV (E Ev : ℝ) : ℝ := E + Ev + 1 / 8

/-- **The region of the vertical controller** (TRACK_PLAN.md 3.2: D6, D13, D15), on the state and
the inputs `D_update_controller` reads, by magnitudes: the position error `E` (inside the linear
zone and the error limits), the velocity error `Ev`, the target velocity `Vv`, the target
acceleration `Aa`, the acceleration error `Aam = |asp - (accel_ef.z + 9.80665016f)|`, the
acceleration signals `Ma`, the acceleration-error scale `MeA`. -/
structure DReg2 (p : Params) (s : State) (inp : Inputs) (E Ev Vv Aa Aam Ma MeA : ℝ) : Prop where
  E0 : 1 / 2 ^ 20 ≤ E
  E1 : E ≤ 1
  Ev0 : 0 ≤ Ev
  Ev1 : Ev ≤ 2 ^ 6
  Vv1 : Vv ≤ 2 ^ 6
  dt : s._dt_s = d0
  emin : s._p_pos_d_m._error_min.IsFinite
  eminv : s._p_pos_d_m._error_min.toReal ≤ -(2 * E)
  emax : s._p_pos_d_m._error_max.IsFinite
  emaxv : 2 * E ≤ s._p_pos_d_m._error_max.toReal
  d1 : s._p_pos_d_m._D1_max.IsFinite
  d1v : 2 * E ≤ s._p_pos_d_m._D1_max.toReal
  sp : s._pos_desired_ned_m.z.IsFinite
  z : s._pos_estimate_ned_m.z.IsFinite
  ez : |s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal| ≤ E
  off : OffZ s
  vsp : s._vel_desired_ned_ms.z.IsFinite
  vz : s._vel_estimate_ned_ms.z.IsFinite
  vspb : |s._vel_desired_ned_ms.z.toReal| ≤ Vv
  ev : |s._vel_desired_ned_ms.z.toReal - s._vel_estimate_ned_ms.z.toReal| ≤ Ev
  vr : s._pid_vel_d_m._reset_filter = false
  ve : s._pid_vel_d_m._error.IsFinite
  veb : |s._pid_vel_d_m._error.toReal| ≤ MeV E Ev
  vd : s._pid_vel_d_m._derivative.IsFinite
  vdb : |s._pid_vel_d_m._derivative.toReal| ≤ 2 ^ 30
  asp : s._accel_desired_ned_mss.z.IsFinite
  aspb : |s._accel_desired_ned_mss.z.toReal| ≤ Aa
  acc : inp.get_accel_ef.z.IsFinite
  accb : |s._accel_desired_ned_mss.z.toReal - (inp.get_accel_ef.z.toReal + gfR)| ≤ Aam
  Ma1 : 10 * MeV E Ev + Aa + 1 ≤ Ma
  Ma2 : Ma ≤ 2 ^ 10
  MeA1 : 10 * MeV E Ev + Aam + 1 / 8 ≤ MeA
  MeA2 : MeA ≤ 2 ^ 10
  MaMeA : Ma ≤ 2 ^ 10 * MeA
  ar : s._pid_accel_d_m._flags._reset_filter = false
  aT : s._pid_accel_d_m._target.IsFinite
  aTb : |s._pid_accel_d_m._target.toReal| ≤ Ma
  ae : s._pid_accel_d_m._error.IsFinite
  aeb : |s._pid_accel_d_m._error.toReal| ≤ MeA
  aI : s._pid_accel_d_m._integrator.IsFinite
  aIb : |s._pid_accel_d_m._integrator.toReal| + MeA / 2 ^ 10 ≤ p._pid_accel_d_m._kimax.toReal
  ad : s._pid_accel_d_m._derivative.IsFinite
  adb : |s._pid_accel_d_m._derivative.toReal| ≤ 2 ^ 30
  gz : inp.get_control_gain_scaler_Z.IsFinite
  gzv : inp.get_control_gain_scaler_Z.toReal = 1
  lo : inp.limit_throttle_lower = false
  up : inp.limit_throttle_upper = false
  hov : inp.get_throttle_hover.IsFinite
  hov0 : 0 ≤ inp.get_throttle_hover.toReal
  hov1 : inp.get_throttle_hover.toReal ≤ 1

theorem dctrl2_vt (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) {E Ev Vv Aa Aam Ma MeA : ℝ}
    (hp : DPar2 p) (hs : DReg2 p s inp E Ev Vv Aa Aam Ma MeA) :
    A32 (velT p s inp) (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal +
      s._vel_desired_ned_ms.z.toReal) (u32 * (4 * E + Vv) + 4 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  obtain ⟨ft1, vt1⟩ := f64_add_exact hs.sp hs.off.pos.1 hs.sp (by rw [hs.off.pos.2, add_zero])
  obtain ⟨tf, tv⟩ := hL.f32ToF64 _ hs.off.tpos.1
  obtain ⟨ft2, vt2⟩ := f64_add_exact ft1 tf hs.sp (by rw [vt1, tv, hs.off.tpos.2, add_zero])
  have htz : (tgtZ s).IsFinite ∧ (tgtZ s).toReal = s._pos_desired_ned_m.z.toReal := ⟨ft2, vt2⟩
  obtain ⟨-, hP, -⟩ := pos_p hL p._p_pos_d_m s._p_pos_d_m (tgtZ s) s._pos_estimate_ned_m.z
    hp.kpP hp.kpPv htz.1 hs.z hs.E0 (by linarith [hs.E1]) (by rw [htz.2]; exact hs.ez)
    hs.emin hs.eminv hs.emax hs.emaxv hs.d1 hs.d1v
  rw [htz.2] at hP
  obtain ⟨g1f, g1v⟩ := f32_mul_one hP.1 hs.gz hs.gzv
  obtain ⟨v1f, v1v⟩ := f32_add_zero hs.vsp hs.off.vel.1 hs.off.vel.2
  obtain ⟨v2f, v2v⟩ := f32_add_zero v1f hs.off.tvel.1 hs.off.tvel.2
  have hP' : A32 ((AC_P_1D.update_all p._p_pos_d_m s._p_pos_d_m (tgtZ s)
      s._pos_estimate_ned_m.z).2.2 * inp.get_control_gain_scaler_Z)
      (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal) (2 * u32 * E + 2 * η32) :=
    ⟨g1f, by rw [g1v]; exact hP.2⟩
  have hV : A32 (s._vel_desired_ned_ms.z + s._vel_offset_ned_ms.z + s._vel_terrain_d_ms)
      s._vel_desired_ned_ms.z.toReal 0 := ⟨v2f, by rw [v2v, v1v]; simp⟩
  have hab := abs_add_le (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal)
      s._vel_desired_ned_ms.z.toReal
  have := hs.ez; have := hs.vspb; have := hs.Vv1; have := hs.E1; have := hs.E0
  have hsum := hP'.add hV (by rw [hu]; norm_num [capF]; nlinarith)
  refine hsum.mono ?_
  rw [hu]; nlinarith

theorem velT_bound2 (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) {E Ev Vv Aa Aam Ma MeA : ℝ}
    (hp : DPar2 p) (hs : DReg2 p s inp E Ev Vv Aa Aam Ma MeA) :
    (velT p s inp).IsFinite ∧
      |(velT p s inp).toReal - s._vel_estimate_ned_ms.z.toReal| ≤ MeV E Ev := by
  have h := dctrl2_vt hL p s inp hp hs
  refine ⟨h.1, ?_⟩
  have h1 := h.2
  have t1 := abs_sub_le (velT p s inp).toReal
    (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal + s._vel_desired_ned_ms.z.toReal)
    s._vel_estimate_ned_ms.z.toReal
  have t2 := abs_add_le (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal)
    (s._vel_desired_ned_ms.z.toReal - s._vel_estimate_ned_ms.z.toReal)
  rw [show s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal + s._vel_desired_ned_ms.z.toReal -
    s._vel_estimate_ned_ms.z.toReal = (s._pos_desired_ned_m.z.toReal - s._pos_estimate_ned_m.z.toReal) +
    (s._vel_desired_ned_ms.z.toReal - s._vel_estimate_ned_ms.z.toReal) by ring] at t1
  have := hs.ez; have := hs.ev; have := hs.Vv1; have := hs.E1
  have hη1 := η32_small
  rw [u32_eq] at h1; rw [MeV]; nlinarith

/-- **C5 in `D_update_controller`, sharp form.** -/
theorem dctrl2_vel (hL : LibmSpec) (hpi : PiF32) (p : Params) (s : State) (inp : Inputs)
    {E Ev Vv Aa Aam Ma MeA : ℝ} (hp : DPar2 p) (hs : DReg2 p s inp E Ev Vv Aa Aam Ma MeA) :
    let B := velB p s inp
    A32 B.1._error (s._pid_vel_d_m._error.toReal + αVr * (((velT p s inp).toReal -
        s._vel_estimate_ned_ms.z.toReal) - s._pid_vel_d_m._error.toReal))
      (αVr * (u32 * MeV E Ev + η32) + (102 / 100 + 411 / 100 * αVr) * u32 * MeV E Ev + 2 * η32) ∧
    A32 B.2 (5 * B.1._error.toReal) (10 * u32 * MeV E Ev + η32) ∧
    B.1._reset_filter = false ∧ B.1._derivative.IsFinite ∧ |B.1._derivative.toReal| ≤ 2 ^ 30 ∧
    |B.1._error.toReal| ≤ 2 * MeV E Ev ∧ B.1._integrator = 0.0 := by
  obtain ⟨hvf, hvb⟩ := velT_bound2 hL p s inp hp hs
  have hM1 : 1 / 8 ≤ MeV E Ev := by rw [MeV]; have := hs.E0; have := hs.Ev0; linarith
  have hM2 : MeV E Ev ≤ 2 ^ 10 := by rw [MeV]; have := hs.E1; have := hs.Ev1; norm_num; linarith
  exact vel_pi2 hL hpi p._pid_vel_d_m s._pid_vel_d_m (velT p s inp) s._vel_estimate_ned_ms.z s._dt_s
    inp.limit_throttle_lower inp.limit_throttle_upper hp.vkp hp.vkpv hp.vki hp.vkiv hp.vkd hp.vkdv
    hp.vkff hp.vkffv hp.vfE hp.vfD hs.dt hs.vr hs.ve hs.vd hvf hs.vz hM1 hM2 hvb hs.veb hs.vdb

/-- The acceleration target `5 ⟦eV⁺⟧ + asp`, sharp form. -/
theorem dctrl2_at (hL : LibmSpec) (hpi : PiF32) (p : Params) (s : State) (inp : Inputs)
    {E Ev Vv Aa Aam Ma MeA : ℝ} (hp : DPar2 p) (hs : DReg2 p s inp E Ev Vv Aa Aam Ma MeA) :
    A32 (accT p s inp) (5 * (velB p s inp).1._error.toReal + s._accel_desired_ned_mss.z.toReal)
      (u32 * (21 * MeV E Ev + Aa) + 3 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  obtain ⟨-, hB2, -, -, -, hEb, -⟩ := dctrl2_vel hL hpi p s inp hp hs
  obtain ⟨g1f, g1v⟩ := f32_mul_one hB2.1 hs.gz hs.gzv
  obtain ⟨a1f, a1v⟩ := f32_add_zero hs.asp hs.off.acc.1 hs.off.acc.2
  obtain ⟨a2f, a2v⟩ := f32_add_zero a1f hs.off.tacc.1 hs.off.tacc.2
  have hB2' : A32 ((velB p s inp).2 * inp.get_control_gain_scaler_Z)
      (5 * (velB p s inp).1._error.toReal) (10 * u32 * MeV E Ev + η32) := ⟨g1f, by rw [g1v]; exact hB2.2⟩
  have hA : A32 (s._accel_desired_ned_mss.z + s._accel_offset_ned_mss.z + s._accel_terrain_d_mss)
      s._accel_desired_ned_mss.z.toReal 0 := ⟨a2f, by rw [a2v, a1v]; simp⟩
  have hsb : |5 * (velB p s inp).1._error.toReal + s._accel_desired_ned_mss.z.toReal| ≤
      10 * MeV E Ev + Aa := by
    have := abs_add_le (5 * (velB p s inp).1._error.toReal) s._accel_desired_ned_mss.z.toReal
    rw [abs_mul, show |(5 : ℝ)| = 5 by norm_num] at this
    have := hs.aspb; linarith
  have hM : MeV E Ev ≤ 2 ^ 10 := by rw [MeV]; have := hs.E1; have := hs.Ev1; norm_num; linarith
  have hM0 : 0 ≤ MeV E Ev := by rw [MeV]; have := hs.E0; have := hs.Ev0; linarith
  have hAa : Aa ≤ 2 ^ 10 := by have := hs.Ma1; have := hs.Ma2; linarith
  have hsum := hB2'.add hA (by rw [hu]; norm_num [capF]; nlinarith)
  refine hsum.mono ?_
  rw [hu]; nlinarith

/-- The measured acceleration, sharp form. -/
theorem dctrl2_am (p : Params) (s : State) (inp : Inputs) {E Ev Vv Aa Aam Ma MeA : ℝ}
    (hs : DReg2 p s inp E Ev Vv Aa Aam Ma MeA) :
    A32 (get_estimated_accel_D_mss inp) (inp.get_accel_ef.z.toReal + gfR) (u32 * (Aa + Aam) + η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hb : |inp.get_accel_ef.z.toReal + gfR| ≤ Aa + Aam := by
    have := abs_sub_abs_le_abs_sub s._accel_desired_ned_mss.z.toReal (inp.get_accel_ef.z.toReal + gfR)
    have := abs_sub_comm s._accel_desired_ned_mss.z.toReal (inp.get_accel_ef.z.toReal + gfR)
    have := abs_sub_abs_le_abs_sub (inp.get_accel_ef.z.toReal + gfR) s._accel_desired_ned_mss.z.toReal
    have := hs.accb; have := hs.aspb; linarith
  have hAA : Aa + Aam ≤ 2 ^ 11 := by
    have := hs.Ma1; have := hs.Ma2; have := hs.MeA1; have := hs.MeA2
    have : 0 ≤ MeV E Ev := by rw [MeV]; have := hs.E0; have := hs.Ev0; linarith
    linarith
  have h := (A32.of_exact hs.acc).add ((A32.of_exact gf_fin).congr gf_val) (by
    norm_num [capF]; linarith)
  refine h.mono ?_
  simp only [add_zero, zero_add]
  have := mul_le_mul_of_nonneg_left hb u32_pos.le
  linarith

/-- **C6 in `D_update_controller`, sharp form.** -/
theorem dctrl2_acc (hL : LibmSpec) (hpi : PiF32) (p : Params) (s : State) (inp : Inputs)
    {E Ev Vv Aa Aam Ma MeA : ℝ} (hp : DPar2 p) (hs : DReg2 p s inp E Ev Vv Aa Aam Ma MeA) :
    let A := accA p s inp
    A32 A.1._error (s._pid_accel_d_m._error.toReal + αAr *
        (((accT p s inp).toReal - (get_estimated_accel_D_mss inp).toReal) - s._pid_accel_d_m._error.toReal))
      (αAr * (514 / 100 * u32 * Ma + u32 * MeA + 4 * η32) + (102 / 100 + 411 / 100 * αAr) * u32 * MeA +
        2 * η32) ∧
    A32 A.1._integrator (s._pid_accel_d_m._integrator.toReal + kiA * dtR * A.1._error.toReal)
        (u32 * |s._pid_accel_d_m._integrator.toReal| + u32 * MeA / 2 ^ 7 + 4 * η32) ∧
    A32 A.2 (kpA * A.1._error.toReal + A.1._integrator.toReal)
        (u32 * (MeA / 2 + p._pid_accel_d_m._kimax.toReal) + 4 * η32) ∧
    (AC_PID.get_ff A.1).IsFinite ∧ (AC_PID.get_ff A.1).toReal = 0 ∧
    A.1._flags._reset_filter = false ∧ A.1._derivative.IsFinite ∧
    |A.1._derivative.toReal| ≤ 2 ^ 30 ∧ |A.1._error.toReal| ≤ 2 * MeA ∧
    A32 A.1._target (accT p s inp).toReal (513 / 100 * u32 * Ma + 2 * η32) := by
  intro A
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hat := dctrl2_at hL hpi p s inp hp hs
  have ham := dctrl2_am p s inp hs
  obtain ⟨-, -, -, -, -, hEb, -⟩ := dctrl2_vel hL hpi p s inp hp hs
  have hM : MeV E Ev ≤ 2 ^ 10 := by rw [MeV]; have := hs.E1; have := hs.Ev1; norm_num; linarith
  have hM0 : 0 ≤ MeV E Ev := by rw [MeV]; have := hs.E0; have := hs.Ev0; linarith
  have hAa0 : 0 ≤ Aa := (abs_nonneg _).trans hs.aspb
  have hAam0 : 0 ≤ Aam := (abs_nonneg _).trans hs.accb
  have hAa : Aa ≤ 2 ^ 10 := by have := hs.Ma1; have := hs.Ma2; linarith
  have h5 : |5 * (velB p s inp).1._error.toReal| ≤ 10 * MeV E Ev := by
    rw [abs_mul, show |(5 : ℝ)| = 5 by norm_num]; linarith
  have hatb : |(accT p s inp).toReal| ≤ Ma := by
    have h1 := hat.abs_le
    have := abs_add_le (5 * (velB p s inp).1._error.toReal) s._accel_desired_ned_mss.z.toReal
    have := hs.aspb; have := hs.Ma1
    rw [hu] at h1; nlinarith
  have hdif : |(accT p s inp).toReal - (get_estimated_accel_D_mss inp).toReal| ≤ MeA := by
    have h1 := hat.2; have h2 := ham.2
    have e : (accT p s inp).toReal - (get_estimated_accel_D_mss inp).toReal =
        ((accT p s inp).toReal - (5 * (velB p s inp).1._error.toReal + s._accel_desired_ned_mss.z.toReal)) -
        ((get_estimated_accel_D_mss inp).toReal - (inp.get_accel_ef.z.toReal + gfR)) +
        5 * (velB p s inp).1._error.toReal +
        (s._accel_desired_ned_mss.z.toReal - (inp.get_accel_ef.z.toReal + gfR)) := by ring
    rw [e]
    have t1 := abs_add_le (((accT p s inp).toReal - (5 * (velB p s inp).1._error.toReal + s._accel_desired_ned_mss.z.toReal)) -
        ((get_estimated_accel_D_mss inp).toReal - (inp.get_accel_ef.z.toReal + gfR)) +
        5 * (velB p s inp).1._error.toReal) (s._accel_desired_ned_mss.z.toReal - (inp.get_accel_ef.z.toReal + gfR))
    have t2 := abs_add_le (((accT p s inp).toReal - (5 * (velB p s inp).1._error.toReal + s._accel_desired_ned_mss.z.toReal)) -
        ((get_estimated_accel_D_mss inp).toReal - (inp.get_accel_ef.z.toReal + gfR))) (5 * (velB p s inp).1._error.toReal)
    have t3 := abs_sub ((accT p s inp).toReal - (5 * (velB p s inp).1._error.toReal + s._accel_desired_ned_mss.z.toReal))
        ((get_estimated_accel_D_mss inp).toReal - (inp.get_accel_ef.z.toReal + gfR))
    have := hs.accb; have := hs.MeA1; have := hs.MeA2
    have hAam : Aam ≤ 2 ^ 10 := by linarith
    rw [hu] at h1 h2
    linarith
  have hMA1 : 1 ≤ Ma := by have := hs.Ma1; linarith
  have hMeA1 : 1 / 8 ≤ MeA := by have := hs.MeA1; linarith
  have hlim : (inp.limit_throttle_lower || inp.limit_throttle_upper) = false := by
    rw [hs.lo, hs.up]; rfl
  have h := accel_pid2 hL hpi p._pid_accel_d_m s._pid_accel_d_m inp._pid_accel_d_m (accT p s inp)
    (get_estimated_accel_D_mss inp) s._dt_s hp.akp hp.akpv hp.aki hp.akiv hp.akd hp.akdv hp.akff
    hp.akffv hp.akdff hp.akdffv hp.apd hp.apdv hp.asr hp.asrv hp.afT hp.afTv hp.afE hp.afD
    hp.afDv hp.aimx hp.aimx' hs.dt hs.ar hs.aT hs.ae hs.aI hs.ad hat.1 ham.1
    hMA1 hs.Ma2 hMeA1 hs.MeA2 hs.MaMeA hs.aTb hatb hdif hs.aeb hs.adb hs.aIb
  simp only [A, accA, hlim]
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h1⟩

/-- **The thrust command**, sharp form. -/
theorem dctrl2_thr (hL : LibmSpec) (hpi : PiF32) (p : Params) (s : State) (inp : Inputs)
    {E Ev Vv Aa Aam Ma MeA : ℝ} (hp : DPar2 p) (hs : DReg2 p s inp E Ev Vv Aa Aam Ma MeA) :
    A32 (thrN p s inp) (kpA * (accA p s inp).1._error.toReal + (accA p s inp).1._integrator.toReal -
      inp.get_throttle_hover.toReal) (u32 * (MeA + 2 * p._pid_accel_d_m._kimax.toReal + 2) + 6 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  obtain ⟨-, hI, hO, hff, hffv, -, -, -, hEb, -⟩ := dctrl2_acc hL hpi p s inp hp hs
  obtain ⟨s1f, s1v⟩ := f32_add_zero hO.1 hff hffv
  have hO' : A32 ((accA p s inp).2 + AC_PID.get_ff (accA p s inp).1)
      (kpA * (accA p s inp).1._error.toReal + (accA p s inp).1._integrator.toReal)
      (u32 * (MeA / 2 + p._pid_accel_d_m._kimax.toReal) + 4 * η32) := ⟨s1f, by rw [s1v]; exact hO.2⟩
  have hk := hp.aimx'
  have hMeA := hs.MeA2
  have hMeA0 : 0 ≤ MeA := by have := hs.MeA1; have : 0 ≤ MeV E Ev := by rw [MeV]; have := hs.E0; have := hs.Ev0; linarith
                             linarith [(abs_nonneg _).trans hs.accb]
  have hk0 : 0 ≤ p._pid_accel_d_m._kimax.toReal := by
    have := hs.aIb; linarith [abs_nonneg s._pid_accel_d_m._integrator.toReal]
  have hIb : |(accA p s inp).1._integrator.toReal| ≤ p._pid_accel_d_m._kimax.toReal + 1 := by
    have h1 := hI.abs_le
    have := abs_add_le s._pid_accel_d_m._integrator.toReal (kiA * dtR * (accA p s inp).1._error.toReal)
    have : |kiA * dtR * (accA p s inp).1._error.toReal| ≤ MeA / 1300 := by
      rw [abs_mul, abs_mul, kiA, dtR]; norm_num; nlinarith [abs_nonneg (accA p s inp).1._error.toReal]
    have := hs.aIb
    rw [hu] at h1; nlinarith [abs_nonneg s._pid_accel_d_m._integrator.toReal]
  have hrb : |kpA * (accA p s inp).1._error.toReal + (accA p s inp).1._integrator.toReal| ≤
      MeA / 9 + p._pid_accel_d_m._kimax.toReal + 1 := by
    have := abs_add_le (kpA * (accA p s inp).1._error.toReal) (accA p s inp).1._integrator.toReal
    have : |kpA * (accA p s inp).1._error.toReal| ≤ MeA / 9 := by
      rw [abs_mul, kpA]; norm_num; nlinarith [abs_nonneg (accA p s inp).1._error.toReal]
    linarith
  have hd := abs_sub (kpA * (accA p s inp).1._error.toReal + (accA p s inp).1._integrator.toReal)
      inp.get_throttle_hover.toReal
  rw [abs_of_nonneg hs.hov0] at hd
  have := hs.hov1
  have hsub := hO'.sub ((A32.of_exact hs.hov)) (by
    rw [hu]; norm_num [capF]; linarith)
  refine hsub.mono ?_
  rw [hu]; simp only [add_zero]
  have : 1 / 16777216 * (1 / 16777216 * (MeA / 2 + p._pid_accel_d_m._kimax.toReal)) ≤
      1 / 16777216 * 1 := by nlinarith
  have hMeA8 : 1 / 8 ≤ MeA := by
    have := hs.MeA1; have : 0 ≤ MeV E Ev := by rw [MeV]; have := hs.E0; have := hs.Ev0; linarith
    linarith [(abs_nonneg _).trans hs.accb]
  linarith

end DCtrl2

end

end Contracts.Track.CtrlV
