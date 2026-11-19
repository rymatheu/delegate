import Contracts.Track.FloatLib
import Contracts.Mission.WPHelp
import Contracts.Mission.NavLeg

/-!
# Milestone M8, lemma P-1: the track scaler of the translated navigator

`AC_WPNav::advance_wp_target_along_track` (`AC_WPNav.cpp:557-656`, translated as
`AC_WPNav.advance_wp_target_along_track`) advances the S-curve time at the filtered rate
`_track_dt_scalar`. Each tick it computes the raw rate

  `track_dt_scalar = constrain(0.05 + (v·d − kP e·d) / |v_T|, 0, 1)`,  `d = v_T / |v_T|`,

where `v_T` is the velocity target (`get_vel_desired_NED_ms`, minus the vertical offset), `v` the
velocity estimate, `e` the position controller's stored error (`get_pos_error_NED_m`) and `kP` the
horizontal position gain; it is `1` when `|v_T|²` is not positive. Then
`_track_dt_scalar ← _track_dt_scalar + (track_dt_scalar − _track_dt_scalar) · (dt / tc)` with
`tc = WP_ACC / WP_JERK`.

* `rawScaler`: the emitted expression of the raw rate, verbatim;
* `advance_track_dt_scalar`: the field `_track_dt_scalar` after `advance_wp_target_along_track`
  is the filter step of `rawScaler` (no terrain following);
* `rawScaler_unit`: the raw rate is always a finite float in `[0, 1]` (whatever the inputs: NaN and
  infinities go through the NaN-safe clamp);
* **`rawScaler_ge` (P-1)**: with `kP = 1.5`, a velocity target of speed `L ≥ v_min ≥ 1/10`, an
  along-track velocity lag `(v_T − v)·v_T ≤ ε_v L` and an along-track position error
  `e·v_T ≤ ε_e L`, the raw rate is at least `min 1 (1.05 − (ε_v + 1.5 ε_e)/v_min − 10⁻³)`. The
  `10⁻³` covers the `float` rounding of the whole expression (`len_approx` for the length, then
  one `A32`/`B32` step per operation);
* `rawScaler_ge_iso`: the isotropic form, with `|v − v_T| ≤ ε_v` and `|e| ≤ ε_e`
  (Cauchy–Schwarz).
-/

namespace Contracts.Track.Pacing

open Contracts.Mission Contracts.Track.FloatLib Float.Model UnpackedFloat AC_WPNav_lib AC_WPNav

noncomputable section

/-! ## The emitted expressions -/

/-- The raw track scaler, the expression of `advance_wp_target_along_track` (`AC_WPNav.cpp:582-590`)
with `vT` the velocity target, `pe` the position error, `ve` the velocity estimate, `kP` the gain. -/
def rawScaler (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32) : Float32 :=
  if is_positive_float (Vector3f.length_squared vT) then
    constrain_value_line_float ((0.0500000007 : Float32) +
      (Vector3f.dot ve (Vector3f.normalized vT) - kP * Vector3f.dot pe (Vector3f.normalized vT)) /
        Vector3f.length vT) (0.0 : Float32) (1.0 : Float32) (Int32.toUInt32 (589 : Int32))
  else (1.0 : Float32)

/-- The filter's time constant `tc = WP_ACC / WP_JERK` (`1` if the jerk is zero). -/
def trackTc (p : Params) : Float32 :=
  if !(is_zero_AP_Float p._wp_jerk_msss) then get_wp_acceleration_mss p / p._wp_jerk_msss else 1.0

/-- The velocity target the scaler reads: `get_vel_desired_NED_ms` minus the vertical offset. -/
def curTargetVel (inp : Inputs) (o : Outputs) : AC_WPNav_lib.Vector3f.State :=
  let v := inp.get_vel_desired_NED_ms o
  { v with z := v.z - inp.get_vel_offset_D_ms o }

/-- The output log as the scaler reads it (after `set_pos_terrain_target_D_m 0`). -/
def scalerLog (o : Outputs) : Outputs := o.push (Output.set_pos_terrain_target_D_m 0.0)

/-- **The filter step of the translated navigator.** Without terrain following, the field
`_track_dt_scalar` after `advance_wp_target_along_track` is
`s + (rawScaler … − s) · (dt / tc)`, with the inputs read from the log of the call. -/
theorem advance_track_dt_scalar (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (dt : Float32) (hT : s._is_terrain_alt = false) :
    (advance_wp_target_along_track p s o inp dt).1._track_dt_scalar =
      s._track_dt_scalar + (rawScaler (curTargetVel inp (scalerLog o))
        (inp.get_pos_error_NED_m (scalerLog o)) (inp.get_vel_estimate_NED_ms (scalerLog o))
        (inp.NE_get_pos_p_kP (scalerLog o)) - s._track_dt_scalar) * (dt / trackTc p) := by
  unfold advance_wp_target_along_track
  simp only [hT, Id.run, Bool.false_eq_true, ite_false]
  simp only [id_pure_eq, apply_ite (fun r : State × Outputs × Bool => r.1._track_dt_scalar),
    ite_self]
  simp only [rawScaler, trackTc, curTargetVel, scalerLog]
  cases is_zero_AP_Float p._wp_jerk_msss <;> simp <;> split <;> rename_i h <;>
    simp only [h, ite_true] <;> rfl

/-! ## The raw scaler is in `[0, 1]` -/

theorem f32_half_max : |(0.0 : Float32).toReal| ≤ maxFinite32 / 2 ∧
    |(1.0 : Float32).toReal| ≤ maxFinite32 / 2 := by
  rw [f32_toReal_0p0, f32_toReal_1p0, Float32.maxFinite32_eq]
  constructor <;> norm_num

/-- The raw scaler is a finite float in `[0, 1]`, for all inputs. -/
theorem rawScaler_unit (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32) :
    (rawScaler vT pe ve kP).IsFinite ∧ 0 ≤ (rawScaler vT pe ve kP).toReal ∧
      (rawScaler vT pe ve kP).toReal ≤ 1 := by
  unfold rawScaler
  split
  · rw [wpnav_cvl]
    have h0 := f32_toReal_0p0
    have h1 := f32_toReal_1p0
    exact Float32.cvl_mem Float32.two32 f32_isFinite_0p0 f32_isFinite_1p0 f32_half_max.1
      f32_half_max.2 (by rw [h0]) (by rw [h1]; norm_num) (by rw [h0]; norm_num) (by rw [h1])
  · exact ⟨f32_isFinite_1p0, by rw [f32_toReal_1p0]; norm_num, by rw [f32_toReal_1p0]⟩

/-! ## P-1: the raw scaler while the vehicle tracks -/

/-- The real dot product of two `float` vectors. -/
def dot3 (a b : AC_WPNav_lib.Vector3f.State) : ℝ :=
  a.x.toReal * b.x.toReal + a.y.toReal * b.y.toReal + a.z.toReal * b.z.toReal

/-- The real length of a `float` vector. -/
def len3 (a : AC_WPNav_lib.Vector3f.State) : ℝ :=
  Real.sqrt (a.x.toReal ^ 2 + a.y.toReal ^ 2 + a.z.toReal ^ 2)

/-- The components are finite and at most `B` in absolute value. -/
def Fin3 (a : AC_WPNav_lib.Vector3f.State) (B : ℝ) : Prop :=
  a.x.IsFinite ∧ a.y.IsFinite ∧ a.z.IsFinite ∧ |a.x.toReal| ≤ B ∧ |a.y.toReal| ≤ B ∧ |a.z.toReal| ≤ B

theorem len3_sq (a : AC_WPNav_lib.Vector3f.State) : len3 a ^ 2 = dot3 a a := by
  rw [len3, Real.sq_sqrt (by positivity), dot3]; ring

theorem abs_le_len3_x (a : AC_WPNav_lib.Vector3f.State) : |a.x.toReal| ≤ len3 a := by
  rw [len3, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a.y.toReal, sq_nonneg a.z.toReal])

theorem abs_le_len3_y (a : AC_WPNav_lib.Vector3f.State) : |a.y.toReal| ≤ len3 a := by
  rw [len3, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a.x.toReal, sq_nonneg a.z.toReal])

theorem abs_le_len3_z (a : AC_WPNav_lib.Vector3f.State) : |a.z.toReal| ≤ len3 a := by
  rw [len3, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a.x.toReal, sq_nonneg a.y.toReal])

theorem len3_le (a : AC_WPNav_lib.Vector3f.State) {B : ℝ} (hB : 0 ≤ B) (ha : Fin3 a B) :
    len3 a ≤ 2 * B := by
  obtain ⟨-, -, -, hx, hy, hz⟩ := ha
  rw [len3, Real.sqrt_le_left (by positivity)]
  have := sq_abs a.x.toReal; have := sq_abs a.y.toReal; have := sq_abs a.z.toReal
  nlinarith [abs_nonneg a.x.toReal, abs_nonneg a.y.toReal, abs_nonneg a.z.toReal]

/-- A component divided by the `float` length: within `10⁻⁶` of the unit direction's component. -/
theorem div_len {a len : Float32} {L : ℝ} (ha : a.IsFinite) (hlen : A32 len L (1 / 2 ^ 21 * L))
    (hL : 1 / 10 ≤ L) (haL : |a.toReal| ≤ L) :
    B32 (a / len) (a.toReal / L) (1 / 10 ^ 6) 1 := by
  have hL0 : 0 < L := by linarith
  have hm : 0 < L * (1 - 1 / 2 ^ 21) := mul_pos hL0 (by norm_num)
  have hq : |a.toReal / L| ≤ 1 := by
    rw [abs_div, abs_of_pos hL0, div_le_one hL0]; exact haL
  have hfr : (|L| * 0 + |a.toReal| * (1 / 2 ^ 21 * L)) / (L * (1 - 1 / 2 ^ 21) * |L|) ≤
      1 / (2 ^ 21 - 1) := by
    rw [abs_of_pos hL0, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : |a.toReal| * L ≤ L * L := mul_le_mul_of_nonneg_right haL hL0.le
    nlinarith
  have hd := A32.div (A32.of_exact ha) hlen hm (by rw [abs_of_pos hL0]; ring_nf; linarith) (by
    have : (1 : ℝ) / (2 ^ 21 - 1) ≤ 1 := by norm_num
    exact (add_le_add hq (hfr.trans this)).trans (by norm_num [capF]))
  refine ⟨⟨hd.1, hd.2.trans ?_⟩, hq⟩
  have e32 := η32_small
  have hu : u32 = 1 / 16777216 := by norm_num [u32]
  rw [hu]
  have h1 : 1 / 16777216 * (|a.toReal / L| + (|L| * 0 + |a.toReal| * (1 / 2 ^ 21 * L)) /
      (L * (1 - 1 / 2 ^ 21) * |L|)) ≤ 1 / 16777216 * (1 + 1 / (2 ^ 21 - 1)) := by gcongr
  have h2 : (1 : ℝ) / (2 ^ 21 - 1) + 1 / 16777216 * (1 + 1 / (2 ^ 21 - 1)) + 1 / 10 ^ 40 ≤
      1 / 10 ^ 6 := by norm_num
  linarith

set_option maxHeartbeats 4000000 in
/-- **Lemma P-1 (the track scaler while tracking).** With the gain `kP = 1.5`, a velocity target
`vT` of speed `len3 vT ≥ v_min ≥ 1/10`, an along-track velocity lag `(vT − ve)·vT ≤ ε_v |vT|` and
an along-track position error `pe·vT ≤ ε_e |vT|` (components of `vT`, `ve` at most `3`, of `pe` at
most `4`), the raw scaler is at least `min 1 (1.05 − (ε_v + 1.5 ε_e)/v_min − 10⁻³)`. -/
theorem rawScaler_ge (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32) (hkPf : kP.IsFinite)
    (hkP : kP.toReal = 3 / 2) (hvT : Fin3 vT 3) (hpe : Fin3 pe 4) (hve : Fin3 ve 3)
    {vmin εv εe : ℝ} (hvmin : 1 / 10 ≤ vmin) (hL : vmin ≤ len3 vT) (hε : 0 ≤ εv + 3 / 2 * εe)
    (hv : dot3 vT vT - dot3 ve vT ≤ εv * len3 vT) (he : dot3 pe vT ≤ εe * len3 vT) :
    min 1 (21 / 20 - (εv + 3 / 2 * εe) / vmin - 1 / 1000) ≤ (rawScaler vT pe ve kP).toReal := by
  obtain ⟨fx, fy, fz, bx, by', bz⟩ := hvT
  obtain ⟨fex, fey, fez, bex, bey, bez⟩ := hpe
  obtain ⟨fvx, fvy, fvz, bvx, bvy, bvz⟩ := hve
  set L := len3 vT with hLdef
  have hL0 : 0 < L := by linarith
  have hL6 : L ≤ 6 := by
    have := len3_le vT (by norm_num) ⟨fx, fy, fz, bx, by', bz⟩; linarith
  have hLx := abs_le_len3_x vT
  have hLy := abs_le_len3_y vT
  have hLz := abs_le_len3_z vT
  have e32 := η32_small
  have p32 := η32_pos
  have hu : u32 = 1 / 16777216 := by norm_num [u32]
  -- the squared length is positive
  have hsq : is_positive_float (Vector3f.length_squared vT) = true := by
    have ax := A32.sq_exact fx (by linarith)
    have ay := A32.sq_exact fy (by linarith)
    have az := A32.sq_exact fz (by linarith)
    have hx2 : vT.x.toReal ^ 2 ≤ 9 := by nlinarith [sq_abs vT.x.toReal, abs_nonneg vT.x.toReal]
    have hy2 : vT.y.toReal ^ 2 ≤ 9 := by nlinarith [sq_abs vT.y.toReal, abs_nonneg vT.y.toReal]
    have hz2 : vT.z.toReal ^ 2 ≤ 9 := by nlinarith [sq_abs vT.z.toReal, abs_nonneg vT.z.toReal]
    have axy := A32.add_nonneg ax ay (sq_nonneg _) (sq_nonneg _) (by
      rw [hu]; norm_num [capF]; nlinarith)
    have axyz := A32.add_nonneg axy az (by positivity) (sq_nonneg _) (by
      rw [hu]; norm_num [capF]; nlinarith)
    show is_positive_float (vT.x * vT.x + vT.y * vT.y + vT.z * vT.z) = true
    rw [wp_isPos_iff axyz.1]
    have hS : vT.x.toReal ^ 2 + vT.y.toReal ^ 2 + vT.z.toReal ^ 2 = L ^ 2 := by
      rw [hLdef, len3, Real.sq_sqrt (by positivity)]
    have hL2 : (1 / 100 : ℝ) ≤ L ^ 2 := by nlinarith
    have h1 := (abs_le.1 axyz.2).1
    rw [hu] at h1
    rw [show (2 : ℝ) ^ (-23 : ℤ) = 1 / 8388608 by norm_num]
    linarith
  -- the length
  obtain ⟨flen, elen⟩ := len_approx fx fy fz (by linarith) (by linarith) (by linarith)
    (by rw [← len3]; linarith)
  have hlen : A32 (Vector3f.length vT) L (1 / 2 ^ 21 * L) := ⟨flen, elen⟩
  -- the direction
  have dx := div_len fx hlen (by linarith) hLx
  have dy := div_len fy hlen (by linarith) hLy
  have dz := div_len fz hlen (by linarith) hLz
  -- the two projections
  have tv1 := B32.mul (e := 32 / 10 ^ 7) (R := 3) (B32.of_exact fvx bvx) dx (by norm_num [capF])
    (by norm_num) (by norm_num)
  have tv2 := B32.mul (e := 32 / 10 ^ 7) (R := 3) (B32.of_exact fvy bvy) dy (by norm_num [capF])
    (by norm_num) (by norm_num)
  have tv3 := B32.mul (e := 32 / 10 ^ 7) (R := 3) (B32.of_exact fvz bvz) dz (by norm_num [capF])
    (by norm_num) (by norm_num)
  have tv12 := B32.add (e := 68 / 10 ^ 7) (R := 6) tv1 tv2 (by norm_num) (by norm_num [capF])
    (by norm_num)
  have tv := B32.add (e := 106 / 10 ^ 7) (R := 9) tv12 tv3 (by norm_num) (by norm_num [capF])
    (by norm_num)
  have te1 := B32.mul (e := 43 / 10 ^ 7) (R := 4) (B32.of_exact fex bex) dx (by norm_num [capF])
    (by norm_num) (by norm_num)
  have te2 := B32.mul (e := 43 / 10 ^ 7) (R := 4) (B32.of_exact fey bey) dy (by norm_num [capF])
    (by norm_num) (by norm_num)
  have te3 := B32.mul (e := 43 / 10 ^ 7) (R := 4) (B32.of_exact fez bez) dz (by norm_num [capF])
    (by norm_num) (by norm_num)
  have te12 := B32.add (e := 91 / 10 ^ 7) (R := 8) te1 te2 (by norm_num) (by norm_num [capF])
    (by norm_num)
  have te := B32.add (e := 142 / 10 ^ 7) (R := 12) te12 te3 (by norm_num) (by norm_num [capF])
    (by norm_num)
  have kte := B32.mul (e := 225 / 10 ^ 7) (R := 18) (B32.of_exact hkPf (R := 3 / 2)
    (by rw [hkP]; norm_num)) te (by norm_num [capF]) (by norm_num) (by norm_num)
  have nn := B32.sub (e := 35 / 10 ^ 6) (R := 27) tv kte (by norm_num) (by norm_num [capF])
    (by norm_num)
  -- the quotient by the length
  set Nr := ve.x.toReal * (vT.x.toReal / L) + ve.y.toReal * (vT.y.toReal / L) +
    ve.z.toReal * (vT.z.toReal / L) - kP.toReal * (pe.x.toReal * (vT.x.toReal / L) +
      pe.y.toReal * (vT.y.toReal / L) + pe.z.toReal * (vT.z.toReal / L)) with hNr
  have hNb : |Nr| ≤ 27 := nn.2
  have hm : 0 < L * (1 - 1 / 2 ^ 21) := mul_pos hL0 (by norm_num)
  have qd := A32.div nn.1 hlen hm (by rw [abs_of_pos hL0]; ring_nf; linarith) (by
    rw [abs_div, abs_of_pos hL0]
    have h1 : |Nr| / L ≤ 270 := by rw [div_le_iff₀ hL0]; nlinarith
    have h2 : (L * (35 / 10 ^ 6) + |Nr| * (1 / 2 ^ 21 * L)) / (L * (1 - 1 / 2 ^ 21) * L) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    norm_num [capF]; linarith)
  have hqe : (|L| * (35 / 10 ^ 6) + |Nr| * (1 / 2 ^ 21 * L)) / (L * (1 - 1 / 2 ^ 21) * |L|) +
      u32 * (|Nr / L| + (|L| * (35 / 10 ^ 6) + |Nr| * (1 / 2 ^ 21 * L)) /
        (L * (1 - 1 / 2 ^ 21) * |L|)) + η32 ≤ 5 / 10 ^ 4 := by
    rw [abs_div, abs_of_pos hL0, hu]
    have h1 : |Nr| / L ≤ 270 := by rw [div_le_iff₀ hL0]; nlinarith
    have h2 : (L * (35 / 10 ^ 6) + |Nr| * (1 / 2 ^ 21 * L)) / (L * (1 - 1 / 2 ^ 21) * L) ≤
        48 / 10 ^ 5 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have q := qd.mono hqe
  -- the offset `0.05f`
  have c05f : (0.0500000007 : Float32).IsFinite := by
    rw [Float32.isFinite_iff, show (0.0500000007 : Float32).toModel.unpack =
      .finite .positive 13421773 (-28) (by decide) from rfl]; rfl
  have c05 : (0.0500000007 : Float32).toReal = 13421773 / 268435456 := by
    rw [Float32.toReal, show (0.0500000007 : Float32).toModel.unpack =
      .finite .positive 13421773 (-28) (by decide) from rfl]
    simp [UnpackedFloat.toReal, Sign.apply]; norm_num
  have harg := A32.add (A32.of_exact c05f) q (by
    rw [c05]; have : |Nr / L| ≤ 270 := by rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]; nlinarith
    have := abs_add_le (13421773 / 268435456 : ℝ) (Nr / L)
    norm_num [capF] at this ⊢; linarith)
  -- the argument of the clamp, in the code's form
  obtain ⟨hf0, hab0⟩ := harg
  have hf : ((0.0500000007 : Float32) + (Vector3f.dot ve (Vector3f.normalized vT) -
      kP * Vector3f.dot pe (Vector3f.normalized vT)) / Vector3f.length vT).IsFinite := hf0
  have hab : |((0.0500000007 : Float32) + (Vector3f.dot ve (Vector3f.normalized vT) -
      kP * Vector3f.dot pe (Vector3f.normalized vT)) / Vector3f.length vT).toReal -
      ((0.0500000007 : Float32).toReal + Nr / L)| ≤ _ := hab0
  set arg := ((0.0500000007 : Float32) + (Vector3f.dot ve (Vector3f.normalized vT) -
      kP * Vector3f.dot pe (Vector3f.normalized vT)) / Vector3f.length vT) with hargd
  have hcl : (rawScaler vT pe ve kP).toReal = max 0 (min arg.toReal 1) := by
    rw [rawScaler, ite_eq_left hsq, wpnav_cvl, cvl_toReal hf f32_isFinite_0p0 f32_isFinite_1p0
      (by rw [f32_toReal_0p0, f32_toReal_1p0]; norm_num), f32_toReal_0p0, f32_toReal_1p0]
  -- the real value
  set K := εv + 3 / 2 * εe with hK
  have hNr' : Nr = (dot3 ve vT - 3 / 2 * dot3 pe vT) / L := by
    rw [hNr, hkP, dot3, dot3]; field_simp
  have hL2 : dot3 vT vT = L ^ 2 := (len3_sq vT).symm
  have hA : L ^ 2 - K * L ≤ dot3 ve vT - 3 / 2 * dot3 pe vT := by nlinarith
  have hq1 : 1 - K / vmin ≤ Nr / L := by
    have h1 : 1 - K / L ≤ Nr / L := by
      rw [← sub_nonneg]
      have : Nr / L - (1 - K / L) = (dot3 ve vT - 3 / 2 * dot3 pe vT - (L ^ 2 - K * L)) / L ^ 2 := by
        rw [hNr']; field_simp
      rw [this]; exact div_nonneg (by linarith) (by positivity)
    have h2 : K / L ≤ K / vmin := div_le_div_of_nonneg_left hε (by linarith) hL
    linarith
  have hNL : |Nr / L| ≤ 270 := by rw [abs_div, abs_of_pos hL0, div_le_iff₀ hL0]; nlinarith
  have hX : 21 / 20 - K / vmin - 1 / 1000 ≤ arg.toReal := by
    have h1 := (abs_le.1 hab).1
    rw [c05, hu] at h1
    have h2 : |(13421773 / 268435456 : ℝ) + Nr / L| ≤ 271 := by
      have := abs_add_le (13421773 / 268435456 : ℝ) (Nr / L); norm_num at this ⊢; linarith
    have h3 : 1 / 16777216 * (|(13421773 / 268435456 : ℝ) + Nr / L| + 0 + 5 / 10 ^ 4) ≤
        1 / 16777216 * (271 + 5 / 10 ^ 4) := by gcongr; linarith
    norm_num at h1 h3 ⊢
    linarith
  rw [hcl]
  refine le_trans ?_ (le_max_right 0 _)
  rw [min_comm arg.toReal 1]
  exact min_le_min le_rfl hX

/-- Cauchy–Schwarz in `ℝ³`. -/
theorem cs3 (a1 a2 a3 b1 b2 b3 : ℝ) :
    a1 * b1 + a2 * b2 + a3 * b3 ≤
      Real.sqrt (a1 ^ 2 + a2 ^ 2 + a3 ^ 2) * Real.sqrt (b1 ^ 2 + b2 ^ 2 + b3 ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  by_cases h : a1 * b1 + a2 * b2 + a3 * b3 ≤ 0
  · exact h.trans (Real.sqrt_nonneg _)
  · apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (a1 * b2 - a2 * b1), sq_nonneg (a1 * b3 - a3 * b1),
      sq_nonneg (a2 * b3 - a3 * b2)]

/-- The real distance of two `float` vectors. -/
def dist3 (a b : AC_WPNav_lib.Vector3f.State) : ℝ :=
  Real.sqrt ((a.x.toReal - b.x.toReal) ^ 2 + (a.y.toReal - b.y.toReal) ^ 2 +
    (a.z.toReal - b.z.toReal) ^ 2)

/-- **P-1, isotropic form.** With the velocity estimate within `ε_v` of the velocity target and the
position error at most `ε_e` (Euclidean), the raw scaler is at least
`min 1 (1.05 − (ε_v + 1.5 ε_e)/v_min − 10⁻³)`. -/
theorem rawScaler_ge_iso (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32)
    (hkPf : kP.IsFinite) (hkP : kP.toReal = 3 / 2) (hvT : Fin3 vT 3) (hpe : Fin3 pe 4)
    (hve : Fin3 ve 3) {vmin εv εe : ℝ} (hvmin : 1 / 10 ≤ vmin) (hL : vmin ≤ len3 vT)
    (hεv : 0 ≤ εv) (hεe : 0 ≤ εe) (hv : dist3 ve vT ≤ εv) (he : len3 pe ≤ εe) :
    min 1 (21 / 20 - (εv + 3 / 2 * εe) / vmin - 1 / 1000) ≤ (rawScaler vT pe ve kP).toReal := by
  have hL0 : 0 ≤ len3 vT := Real.sqrt_nonneg _
  refine rawScaler_ge vT pe ve kP hkPf hkP hvT hpe hve hvmin hL (by positivity) ?_ ?_
  · have h := cs3 (vT.x.toReal - ve.x.toReal) (vT.y.toReal - ve.y.toReal)
      (vT.z.toReal - ve.z.toReal) vT.x.toReal vT.y.toReal vT.z.toReal
    have hd : dist3 ve vT = Real.sqrt ((vT.x.toReal - ve.x.toReal) ^ 2 +
        (vT.y.toReal - ve.y.toReal) ^ 2 + (vT.z.toReal - ve.z.toReal) ^ 2) := by
      rw [dist3]; ring_nf
    rw [← hd, ← len3] at h
    have : dot3 vT vT - dot3 ve vT = (vT.x.toReal - ve.x.toReal) * vT.x.toReal +
        (vT.y.toReal - ve.y.toReal) * vT.y.toReal + (vT.z.toReal - ve.z.toReal) * vT.z.toReal := by
      rw [dot3, dot3]; ring
    rw [this]
    exact h.trans (mul_le_mul_of_nonneg_right hv hL0)
  · have h := cs3 pe.x.toReal pe.y.toReal pe.z.toReal vT.x.toReal vT.y.toReal vT.z.toReal
    rw [← len3, ← len3] at h
    exact h.trans (mul_le_mul_of_nonneg_right he hL0)

end

end Contracts.Track.Pacing
