import Contracts.Track.CtrlAttitudeQuat

/-!
# `attitude_from_thrust_vector` near hover (milestone M4, lemma C8)

`AC_AttitudeControl::attitude_from_thrust_vector(tv, ψ)` normalizes the thrust vector `tv`, takes
the rotation from `up = (0, 0, -1)` to `t̂ = tv/|tv|` about `up × t̂` by
`θ = acosf(up · t̂)` (axis `up` when `|up × t̂|` or `θ` is zero), and multiplies by the yaw
rotation by `ψ` about `z`. The real law (`tiltQ`, `yawQ`) is written in the form that is
continuous at `θ = 0`: `q_tilt = (√((1+c)/2), (up × t̂)/√(2(1+c)))`, `c = up · t̂`; it is
`(cos(θ/2), sin(θ/2) · axis)` for `θ = arccos c`.

The `float` `acosf` of a dot product near `1` loses half the digits: one rounding error `δ` of
`c` moves `sin(θ/2) = √((1-c)/2)` by up to `√(δ/2)`. With `|δ| ≤ 2.1·10⁻⁷` (the normalization,
`3.503 u`) the vector part is within `3.25·10⁻⁴`, and the product with the yaw quaternion within
`4.7·10⁻⁴` per component (`attitude_from_thrust_vector_near`), for `|a_N|, |a_E| ≤ 6`,
`a_D ∈ [-10, -9]`, `|ψ| ≤ 4`.
-/

namespace Contracts.Track.AttQ

open Contracts.Mission AC_Attitude_lib Float.Model UnpackedFloat

noncomputable section

namespace TiltReal

theorem sqrt_lip {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 < m) (hmb : m ≤ Real.sqrt b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / m := by
  rw [le_div_iff₀ hm]
  have key : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt a + Real.sqrt b), ← abs_mul]
    congr 1
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb; nlinarith
  have : m ≤ Real.sqrt a + Real.sqrt b := by linarith [Real.sqrt_nonneg a]
  calc |Real.sqrt a - Real.sqrt b| * m ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = _ := key

/-- The half-angle values of an `acosf` result. -/
theorem half_angle {cf θ : ℝ} (h1 : -1 ≤ cf) (h2 : cf ≤ 1)
    (hθ : |θ - Real.arccos cf| ≤ 1 / 2 ^ 22) :
    |Real.sin (θ / 2) - Real.sqrt ((1 - cf) / 2)| ≤ 1 / 2 ^ 23 ∧
      |Real.cos (θ / 2) - Real.sqrt ((1 + cf) / 2)| ≤ 1 / 2 ^ 23 := by
  have ha0 := Real.arccos_nonneg cf
  have hapi := Real.arccos_le_pi cf
  have hs : Real.sin (Real.arccos cf / 2) = Real.sqrt ((1 - cf) / 2) := by
    rw [Real.sin_half_eq_sqrt ha0 (by linarith [Real.pi_pos]), Real.cos_arccos h1 h2]
  have hc : Real.cos (Real.arccos cf / 2) = Real.sqrt ((1 + cf) / 2) := by
    rw [Real.cos_half (by linarith [Real.pi_pos]) hapi, Real.cos_arccos h1 h2]
  have hd : |θ / 2 - Real.arccos cf / 2| ≤ 1 / 2 ^ 23 := by
    rw [show θ / 2 - Real.arccos cf / 2 = (θ - Real.arccos cf) / 2 by ring, abs_div, abs_two]
    have : (1 / 2 ^ 23 : ℝ) = 1 / 2 ^ 22 / 2 := by norm_num
    rw [this]; gcongr
  rw [← hs, ← hc]
  exact ⟨(Real.abs_sin_sub_sin_le _ _).trans hd, (Real.abs_cos_sub_cos_le _ _).trans hd⟩

/-- `√((1-c)/2)` is `1/2`-Hölder in `c`. -/
theorem sin_half_holder {c cf ε : ℝ} (h : |cf - c| ≤ ε) :
    |Real.sqrt ((1 - cf) / 2) - Real.sqrt ((1 - c) / 2)| ≤ Real.sqrt (ε / 2) := by
  refine (sqrt_sub_le _ _).trans (Real.sqrt_le_sqrt ?_)
  rw [show (1 - cf) / 2 - (1 - c) / 2 = -((cf - c) / 2) by ring, abs_neg, abs_div, abs_two]
  linarith

/-- The Euclidean norm in the plane is `√2`-Lipschitz for the max norm. -/
theorem norm2_lip {p q P Q ε : ℝ} (hp : |p - P| ≤ ε) (hq : |q - Q| ≤ ε) :
    |Real.sqrt (P ^ 2 + Q ^ 2) - Real.sqrt (p ^ 2 + q ^ 2)| ≤ 14143 / 10000 * ε := by
  set s := Real.sqrt (P ^ 2 + Q ^ 2)
  set r := Real.sqrt (p ^ 2 + q ^ 2)
  have hs2 : s ^ 2 = P ^ 2 + Q ^ 2 := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hε : 0 ≤ ε := (abs_nonneg _).trans hp
  -- Cauchy–Schwarz: `P p + Q q ≤ s r`
  have hcs : P * p + Q * q ≤ s * r := by
    have h1 : (P * p + Q * q) ^ 2 ≤ (s * r) ^ 2 := by
      rw [mul_pow, hs2, hr2]; nlinarith [sq_nonneg (P * q - Q * p)]
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  have hsq : (s - r) ^ 2 ≤ 2 * ε ^ 2 := by
    have a1 : (p - P) ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; gcongr
    have a2 : (q - Q) ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; gcongr
    nlinarith
  have : (s - r) ^ 2 ≤ (14143 / 10000 * ε) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' this (by positivity) |> abs_le.2


/-- One component of the generic branch: the normalized cross component `A ≈ p/r` times the
computed `sin(θ/2) ≈ S = s/D`, against the true `P/D`. -/
theorem gen_comp {p q P Q A Sθ S D ε k E : ℝ} (hr : 0 < Real.sqrt (p ^ 2 + q ^ 2))
    (hp : |p - P| ≤ ε) (hq : |q - Q| ≤ ε) (hA : |A - p / Real.sqrt (p ^ 2 + q ^ 2)| ≤ k)
    (hSθ : |Sθ - S| ≤ E) (hSθ1 : |Sθ| ≤ 1) (hS : S = Real.sqrt (P ^ 2 + Q ^ 2) / D)
    (hD : 183 / 100 ≤ D) :
    |A * Sθ - P / D| ≤ k + E + 1321 / 1000 * ε := by
  set r := Real.sqrt (p ^ 2 + q ^ 2)
  set s := Real.sqrt (P ^ 2 + Q ^ 2)
  have hε : 0 ≤ ε := (abs_nonneg _).trans hp
  have hDp : 0 < D := by linarith
  have hk : 0 ≤ k := (abs_nonneg _).trans hA
  have hpr : |p / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact Real.abs_le_sqrt (by nlinarith [sq_nonneg q])
  have hsr := norm2_lip hp hq
  have e1 : |(A - p / r) * Sθ| ≤ k := by
    rw [abs_mul]; calc |A - p / r| * |Sθ| ≤ k * 1 := by gcongr
      _ = k := by ring
  have e2 : |p / r * (Sθ - S)| ≤ E := by
    rw [abs_mul]; calc |p / r| * |Sθ - S| ≤ 1 * E := by gcongr
      _ = E := by ring
  have e3 : |p / r * S - P / D| ≤ 1321 / 1000 * ε := by
    rw [hS, show p / r * (s / D) - P / D = (p / r * (s - r) + (p - P)) / D by
      field_simp; ring, abs_div, abs_of_pos hDp, div_le_iff₀ hDp]
    have : |p / r * (s - r) + (p - P)| ≤ 1 * (14143 / 10000 * ε) + ε := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]; gcongr
    nlinarith
  calc |A * Sθ - P / D| = |(A - p / r) * Sθ + p / r * (Sθ - S) + (p / r * S - P / D)| := by
        congr 1; ring
    _ ≤ |(A - p / r) * Sθ| + |p / r * (Sθ - S)| + |p / r * S - P / D| := abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- `√((1-c)/2) = √(X² + Y²) / √(2(1+c))` on the unit sphere, `c = -Z`. -/
theorem S_eq {X Y Z : ℝ} (h : X ^ 2 + Y ^ 2 + Z ^ 2 = 1) (hc : 0 < 1 + -Z) :
    Real.sqrt ((1 - -Z) / 2) = Real.sqrt (Y ^ 2 + (-X) ^ 2) / Real.sqrt (2 * (1 + -Z)) := by
  have hD : 0 < Real.sqrt (2 * (1 + -Z)) := Real.sqrt_pos.2 (by linarith)
  rw [eq_div_iff hD.ne', ← Real.sqrt_mul (by nlinarith [sq_nonneg X, sq_nonneg Y])]
  congr 1; nlinarith


/-- The hypotheses of the tilt analysis: `(X, Y, Z)` the true unit thrust direction with
`c = -Z ≥ 0.68`; `tx, ty` its computed horizontal components and `cf` the computed (clamped)
`up · t̂`, within `2.1·10⁻⁷`; `θ` the `acosf` of `cf`. -/
structure TiltHyp (X Y Z tx ty cf θ : ℝ) : Prop where
  unit : X ^ 2 + Y ^ 2 + Z ^ 2 = 1
  cZ : 68 / 100 ≤ -Z
  htx : |tx - X| ≤ 21 / 10 ^ 8
  hty : |ty - Y| ≤ 21 / 10 ^ 8
  hcf : |cf - -Z| ≤ 21 / 10 ^ 8
  cf1 : cf ≤ 1
  cf0 : -1 ≤ cf
  hθ : |θ - Real.arccos cf| ≤ 1 / 2 ^ 22

namespace TiltHyp

variable {X Y Z tx ty cf θ : ℝ} (h : TiltHyp X Y Z tx ty cf θ)
include h

theorem D_ge : 183 / 100 ≤ Real.sqrt (2 * (1 + -Z)) := by
  rw [show (183 / 100 : ℝ) = Real.sqrt ((183 / 100) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith [h.cZ])

omit h in
theorem sqrt_eps : 1 / 2 ^ 23 + Real.sqrt (21 / 10 ^ 8 / 2) ≤ 32416 / 10 ^ 8 := by
  have : Real.sqrt (21 / 10 ^ 8 / 2) ≤ 32404 / 10 ^ 8 := by
    rw [show (32404 / 10 ^ 8 : ℝ) = Real.sqrt ((32404 / 10 ^ 8) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  norm_num at this ⊢; linarith

/-- `sin(θ/2)` is within `3.2416·10⁻⁴` of `S = √((1-c)/2)`. -/
theorem sin_near : |Real.sin (θ / 2) - Real.sqrt ((1 - -Z) / 2)| ≤ 32416 / 10 ^ 8 := by
  have h1 := (half_angle h.cf0 h.cf1 h.hθ).1
  have h2 := sin_half_holder (c := -Z) h.hcf
  have := abs_sub_le (Real.sin (θ / 2)) (Real.sqrt ((1 - cf) / 2)) (Real.sqrt ((1 - -Z) / 2))
  linarith [sqrt_eps]

/-- **Scalar part**: `cos(θ/2)` is within `2.4·10⁻⁷` of `√((1+c)/2)`. -/
theorem cos_near : |Real.cos (θ / 2) - Real.sqrt ((1 + -Z) / 2)| ≤ 24 / 10 ^ 8 := by
  have h1 := (half_angle h.cf0 h.cf1 h.hθ).2
  have hb : (9 / 10 : ℝ) ≤ Real.sqrt ((1 + -Z) / 2) := by
    rw [show (9 / 10 : ℝ) = Real.sqrt ((9 / 10) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [h.cZ])
  have h2 := sqrt_lip (a := (1 + cf) / 2) (by linarith [h.cf0]) (by linarith [h.cZ])
    (by norm_num) hb
  have h3 : |(1 + cf) / 2 - (1 + -Z) / 2| ≤ 21 / 10 ^ 8 / 2 := by
    rw [show (1 + cf) / 2 - (1 + -Z) / 2 = (cf - -Z) / 2 by ring, abs_div, abs_two]
    linarith [h.hcf]
  have h4 : |(1 + cf) / 2 - (1 + -Z) / 2| / (9 / 10) ≤ 21 / 10 ^ 8 / 2 / (9 / 10) := by gcongr
  have := abs_sub_le (Real.cos (θ / 2)) (Real.sqrt ((1 + cf) / 2)) (Real.sqrt ((1 + -Z) / 2))
  have e : (1 : ℝ) / 2 ^ 23 + 21 / 10 ^ 8 / 2 / (9 / 10) ≤ 24 / 10 ^ 8 := by norm_num
  linarith

theorem S_eq' : Real.sqrt ((1 - -Z) / 2) =
    Real.sqrt (Y ^ 2 + (-X) ^ 2) / Real.sqrt (2 * (1 + -Z)) := S_eq h.unit (by linarith [h.cZ])

/-- **Generic branch** (axis = normalized cross product): both horizontal components within
`3.25·10⁻⁴`. -/
theorem generic {A1 A2 : ℝ} (hr : 0 < Real.sqrt (ty ^ 2 + (-tx) ^ 2))
    (h1 : |A1 - ty / Real.sqrt (ty ^ 2 + (-tx) ^ 2)| ≤ 21 / 10 ^ 8)
    (h2 : |A2 - -tx / Real.sqrt (ty ^ 2 + (-tx) ^ 2)| ≤ 21 / 10 ^ 8) :
    |A1 * Real.sin (θ / 2) - Y / Real.sqrt (2 * (1 + -Z))| ≤ 325 / 10 ^ 6 ∧
      |A2 * Real.sin (θ / 2) - -X / Real.sqrt (2 * (1 + -Z))| ≤ 325 / 10 ^ 6 := by
  have hs1 : |Real.sin (θ / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hx' : |-tx - -X| ≤ 21 / 10 ^ 8 := by
    rw [show -tx - -X = -(tx - X) by ring, abs_neg]; exact h.htx
  constructor
  · have := gen_comp hr h.hty hx' h1 h.sin_near hs1 h.S_eq' h.D_ge
    linarith
  · have hr' : 0 < Real.sqrt ((-tx) ^ 2 + ty ^ 2) := by rwa [add_comm]
    have h2' : |A2 - -tx / Real.sqrt ((-tx) ^ 2 + ty ^ 2)| ≤ 21 / 10 ^ 8 := by rwa [add_comm]
    have hS : Real.sqrt ((1 - -Z) / 2) =
        Real.sqrt ((-X) ^ 2 + Y ^ 2) / Real.sqrt (2 * (1 + -Z)) := by rw [h.S_eq', add_comm]
    have := gen_comp hr' hx' h.hty h2' h.sin_near hs1 hS h.D_ge
    linarith

/-- **Up branch** (`is_zero(length)` or `is_zero(angle)`): `sin(θ/2)` and both components of the
true vector part are below `3.25·10⁻⁴`. -/
theorem up {r : ℝ} (hrr : r = Real.sqrt (ty ^ 2 + (-tx) ^ 2))
    (hcase : r ≤ 12 / 10 ^ 8 ∨ |θ| < 1 / 2 ^ 23) :
    |Real.sin (θ / 2)| ≤ 325 / 10 ^ 6 ∧ |Y / Real.sqrt (2 * (1 + -Z))| ≤ 325 / 10 ^ 6 ∧
      |-X / Real.sqrt (2 * (1 + -Z))| ≤ 325 / 10 ^ 6 := by
  have hD := h.D_ge
  have hDp : 0 < Real.sqrt (2 * (1 + -Z)) := by linarith
  set D := Real.sqrt (2 * (1 + -Z))
  set s := Real.sqrt (Y ^ 2 + (-X) ^ 2)
  have hS := h.S_eq'
  have hsn := h.sin_near
  have hS0 : 0 ≤ s / D := by positivity
  have hY : |Y / D| ≤ s / D := by
    rw [abs_div, abs_of_pos hDp]; gcongr; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg X])
  have hX : |-X / D| ≤ s / D := by
    rw [abs_div, abs_of_pos hDp]; gcongr; exact Real.abs_le_sqrt (by nlinarith [sq_nonneg Y])
  rw [hS] at hsn
  have hsn' := abs_le.1 hsn
  rcases hcase with hr | hθ0
  · have hx' : |-tx - -X| ≤ 21 / 10 ^ 8 := by
      rw [show -tx - -X = -(tx - X) by ring, abs_neg]; exact h.htx
    have hl := norm2_lip h.hty hx'
    rw [← hrr] at hl
    have hs : s ≤ 42 / 10 ^ 8 := by have := (abs_le.1 hl).2; linarith
    have hsD : s / D ≤ 42 / 10 ^ 8 := by
      rw [div_le_iff₀ hDp]; nlinarith [Real.sqrt_nonneg (Y ^ 2 + (-X) ^ 2)]
    refine ⟨?_, by linarith, by linarith⟩
    rw [abs_le]; constructor <;> linarith
  · have hsθ : |Real.sin (θ / 2)| ≤ 1 / 2 ^ 24 := by
      refine Real.abs_sin_le_abs.trans ?_
      rw [abs_div, abs_two]; norm_num at hθ0 ⊢; linarith
    have := abs_le.1 hsθ
    have hsD : s / D ≤ 1 / 2 ^ 24 + 32416 / 10 ^ 8 := by linarith
    refine ⟨by norm_num at hsθ ⊢; linarith, by norm_num at hsD ⊢; linarith,
      by norm_num at hsD ⊢; linarith⟩

end TiltHyp

end TiltReal

open TiltReal

/-! ## The emitted function, unfolded -/

/-- `thrust_vector_up`. -/
def upV : Vector3f.State := Vector3f.init_float3 (0.0 : Float32) (0.0 : Float32) (-(1.0 : Float32))

/-- The rotation axis the code picks. -/
def tiltAxis (t : Vector3f.State) : Vector3f.State :=
  if is_zero_float (Vector3f.length (Vector3f.op_mod upV t)) ||
      is_zero_float (Float32.acos (constrain_value_line_float (Vector3f.op_mul_Vector3f upV t) (-(1.0 : Float32)) (1.0 : Float32) (Int32.toUInt32 (961 : Int32)))) then upV
  else (Vector3f.op_div_assign (Vector3f.op_mod upV t) (Vector3f.length (Vector3f.op_mod upV t))).1

theorem aftv_eq (tv : Vector3f.State) (ψ : Float32)
    (h : is_zero_float (Vector3f.length_squared tv) = false) :
    AC_AttitudeControl_Multi.attitude_from_thrust_vector tv ψ =
      Quaternion.op_mul_Quaternion
        (Quaternion.from_axis_angle_Vector3f_float Quaternion.init_void (tiltAxis (Vector3f.normalize tv))
          (Float32.acos (constrain_value_line_float (Vector3f.op_mul_Vector3f upV (Vector3f.normalize tv)) (-(1.0 : Float32)) (1.0 : Float32) (Int32.toUInt32 (961 : Int32)))))
        (Quaternion.from_axis_angle_Vector3f_float Quaternion.init_void
          (Vector3f.init_float3 (0.0 : Float32) (0.0 : Float32) (1.0 : Float32)) ψ) := by
  simp only [AC_AttitudeControl_Multi.attitude_from_thrust_vector, h, Id.run, Bool.false_eq_true, ite_false]
  unfold tiltAxis upV
  split_ifs <;> rfl

theorem norm_x (tv : Vector3f.State) : (Vector3f.normalize tv).x = tv.x / Vector3f.length tv := rfl
theorem lsq (tv : Vector3f.State) : Vector3f.length_squared tv = tv.x * tv.x + tv.y * tv.y + tv.z * tv.z := rfl

theorem lsq_eq (tv : Vector3f.State) :
    Vector3f.length_squared tv = tv.x * tv.x + tv.y * tv.y + tv.z * tv.z := rfl
theorem nz_eq (tv : Vector3f.State) : (Vector3f.normalize tv).z = tv.z / Vector3f.length tv := rfl
theorem ny_eq (tv : Vector3f.State) : (Vector3f.normalize tv).y = tv.y / Vector3f.length tv := rfl

theorem upx : upV.x = 0.0 := rfl
theorem upy : upV.y = 0.0 := rfl
theorem upz : upV.z = -(1.0 : Float32) := rfl

theorem m1_fin : (-(1.0 : Float32)).IsFinite := (Float32.isFinite_neg _).2 f32_isFinite_1p0
theorem m1_val : (-(1.0 : Float32)).toReal = -1 := by rw [Float32.toReal_neg, f32_toReal_1p0]

theorem zero_mul_exact {a : Float32} (ha : a.IsFinite) :
    ((0.0 : Float32) * a).IsFinite ∧ ((0.0 : Float32) * a).toReal = 0 := by
  have := Float32.mul_exact f32_isFinite_0p0 ha f32_isFinite_0p0 (by rw [f32_toReal_0p0, zero_mul])
  rwa [f32_toReal_0p0] at this

theorem m1_mul_exact {a : Float32} (ha : a.IsFinite) :
    (-(1.0 : Float32) * a).IsFinite ∧ (-(1.0 : Float32) * a).toReal = -a.toReal := by
  have := Float32.mul_exact m1_fin ha ((Float32.isFinite_neg a).2 ha)
    (by rw [m1_val, Float32.toReal_neg]; ring)
  rwa [Float32.toReal_neg] at this

/-- `up × t = (t_y, -t_x, 0)`, exactly. -/
theorem up_cross {t : Vector3f.State} (hx : t.x.IsFinite) (hy : t.y.IsFinite) (hz : t.z.IsFinite) :
    ((Vector3f.op_mod upV t).x.IsFinite ∧ (Vector3f.op_mod upV t).x.toReal = t.y.toReal) ∧
    ((Vector3f.op_mod upV t).y.IsFinite ∧ (Vector3f.op_mod upV t).y.toReal = -t.x.toReal) ∧
    ((Vector3f.op_mod upV t).z.IsFinite ∧ (Vector3f.op_mod upV t).z.toReal = 0) := by
  rw [cross_x, cross_y, cross_z, upx, upy, upz]
  obtain ⟨a1, a2⟩ := zero_mul_exact hz
  obtain ⟨b1, b2⟩ := m1_mul_exact hy
  obtain ⟨c1, c2⟩ := m1_mul_exact hx
  obtain ⟨d1, d2⟩ := zero_mul_exact hy
  obtain ⟨e1, e2⟩ := zero_mul_exact hx
  refine ⟨Float32.sub_exact a1 b1 hy (by rw [a2, b2]; ring), ?_, ?_⟩
  · have := Float32.sub_exact c1 a1 ((Float32.isFinite_neg _).2 hx) (by rw [a2, c2, Float32.toReal_neg]; ring)
    rwa [Float32.toReal_neg] at this
  · have := Float32.sub_exact d1 e1 f32_isFinite_0p0 (by rw [d2, e2, f32_toReal_0p0]; ring)
    rwa [f32_toReal_0p0] at this

/-- `up · t = -t_z`, exactly. -/
theorem up_dot {t : Vector3f.State} (hx : t.x.IsFinite) (hy : t.y.IsFinite) (hz : t.z.IsFinite) :
    (Vector3f.op_mul_Vector3f upV t).IsFinite ∧ (Vector3f.op_mul_Vector3f upV t).toReal = -t.z.toReal := by
  rw [dot_eq, upx, upy, upz]
  obtain ⟨a1, a2⟩ := zero_mul_exact hx
  obtain ⟨b1, b2⟩ := zero_mul_exact hy
  obtain ⟨c1, c2⟩ := m1_mul_exact hz
  obtain ⟨d1, d2⟩ := Float32.add_exact a1 b1 f32_isFinite_0p0 (by rw [a2, b2, f32_toReal_0p0]; ring)
  rw [f32_toReal_0p0] at d2
  have := Float32.add_exact d1 c1 ((Float32.isFinite_neg _).2 hz) (by rw [d2, c2, Float32.toReal_neg]; ring)
  rwa [Float32.toReal_neg] at this

/-! ## Normalizing the thrust vector -/

/-- Hover box of the thrust vector: `|a_N|, |a_E| ≤ 6`, `a_D ∈ [-10, -9]`, finite. -/
structure HoverBox (tv : Vector3f.State) : Prop where
  fx : tv.x.IsFinite
  fy : tv.y.IsFinite
  fz : tv.z.IsFinite
  bx : |tv.x.toReal| ≤ 6
  by' : |tv.y.toReal| ≤ 6
  bz1 : -10 ≤ tv.z.toReal
  bz2 : tv.z.toReal ≤ -9

theorem norm_sq (v : RV) : v.norm ^ 2 = v.x ^ 2 + v.y ^ 2 + v.z ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem HoverBox.norm_lo {tv : Vector3f.State} (h : HoverBox tv) : 9 ≤ (vv tv).norm := by
  rw [show (9 : ℝ) = Real.sqrt (9 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  simp only [vv]; nlinarith [h.bz2, sq_nonneg tv.x.toReal, sq_nonneg tv.y.toReal]

theorem HoverBox.norm_hi {tv : Vector3f.State} (h : HoverBox tv) : (vv tv).norm ≤ 1312 / 100 := by
  rw [show (1312 / 100 : ℝ) = Real.sqrt ((1312 / 100) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  refine Real.sqrt_le_sqrt ?_
  simp only [vv]
  have := abs_le.1 h.bx; have := abs_le.1 h.by'
  nlinarith [h.bz1, h.bz2]

theorem abs_le_norm_x (v : RV) : |v.x| ≤ v.norm := Real.abs_le_sqrt (by nlinarith [sq_nonneg v.y, sq_nonneg v.z])
theorem abs_le_norm_y (v : RV) : |v.y| ≤ v.norm := Real.abs_le_sqrt (by nlinarith [sq_nonneg v.x, sq_nonneg v.z])
theorem abs_le_norm_z (v : RV) : |v.z| ≤ v.norm := Real.abs_le_sqrt (by nlinarith [sq_nonneg v.x, sq_nonneg v.y])

/-- `length_squared` of a thrust vector in the hover box is not zero. -/
theorem HoverBox.lsq_nz {tv : Vector3f.State} (h : HoverBox tv) :
    is_zero_float (Vector3f.length_squared tv) = false := by
  have b1 : |tv.x.toReal| ≤ 1000 := by linarith [h.bx]
  have b2 : |tv.y.toReal| ≤ 1000 := by linarith [h.by']
  have b3 : |tv.z.toReal| ≤ 1000 := by rw [abs_le]; constructor <;> linarith [h.bz1, h.bz2]
  obtain ⟨f, -, hm, e⟩ := sumsq_near h.fx h.fy h.fz b1 b2 b3
  rw [lsq_eq]
  refine Att.isZero_false f ?_
  have h81 : 81 ≤ tv.x.toReal * tv.x.toReal + tv.y.toReal * tv.y.toReal + tv.z.toReal * tv.z.toReal := by
    nlinarith [h.bz2, mul_self_nonneg tv.x.toReal, mul_self_nonneg tv.y.toReal]
  have h172 : tv.x.toReal * tv.x.toReal + tv.y.toReal * tv.y.toReal + tv.z.toReal * tv.z.toReal ≤ 172 := by
    have := abs_le.1 h.bx; have := abs_le.1 h.by'; nlinarith [h.bz1, h.bz2]
  have := (abs_le.1 e).1
  rw [two_pow_m23]
  have : 80 ≤ (tv.x * tv.x + tv.y * tv.y + tv.z * tv.z).toReal := by norm_num at this ⊢; nlinarith
  rw [abs_of_nonneg (by linarith)]; linarith

/-- The normalized thrust vector: each component within `2.1·10⁻⁷` of `tv/|tv|`. -/
theorem HoverBox.normalize {tv : Vector3f.State} (h : HoverBox tv) :
    A32 (Vector3f.normalize tv).x (tv.x.toReal / (vv tv).norm) (21 / 10 ^ 8) ∧
    A32 (Vector3f.normalize tv).y (tv.y.toReal / (vv tv).norm) (21 / 10 ^ 8) ∧
    A32 (Vector3f.normalize tv).z (tv.z.toReal / (vv tv).norm) (21 / 10 ^ 8) := by
  have b1 : |tv.x.toReal| ≤ 1000 := by linarith [h.bx]
  have b2 : |tv.y.toReal| ≤ 1000 := by linarith [h.by']
  have b3 : |tv.z.toReal| ≤ 1000 := by rw [abs_le]; constructor <;> linarith [h.bz1, h.bz2]
  obtain ⟨fL, eL⟩ := len_near h.fx h.fy h.fz b1 b2 b3
  have hn := h.norm_lo
  have hn24 : (1 : ℝ) / 2 ^ 24 ≤ (vv tv).norm := le_trans (by norm_num) hn
  have hnp : 0 < (vv tv).norm := by linarith
  have key : ∀ x : Float32, x.IsFinite → |x.toReal| ≤ (vv tv).norm →
      A32 (x / Vector3f.length tv) (x.toReal / (vv tv).norm) (21 / 10 ^ 8) := by
    intro x hx hxn
    obtain ⟨f, e⟩ := ndiv hx fL hn24 eL hxn
    refine ⟨f, e.trans ?_⟩
    have : |x.toReal| / (vv tv).norm ≤ 1 := by rw [div_le_one hnp]; exact hxn
    have : 3503 / 1000 * (1 / 16777216) * (|x.toReal| / (vv tv).norm) ≤ 3503 / 1000 * (1 / 16777216) * 1 := by
      gcongr
    norm_num at this ⊢; linarith
  exact ⟨key _ h.fx (abs_le_norm_x (vv tv)), key _ h.fy (abs_le_norm_y (vv tv)),
    key _ h.fz (abs_le_norm_z (vv tv))⟩

/-! ## The real law -/

/-- The tilt quaternion taking `up = (0, 0, -1)` to `t̂ = t/|t|`, about `up × t̂ = (t̂_y, -t̂_x, 0)`,
in the form continuous at `θ = 0`: `(√((1+c)/2), (up × t̂)/√(2(1+c)))`, `c = up · t̂ = -t̂_z`. -/
def tiltQ (t : RV) : RQ :=
  ⟨Real.sqrt ((1 + -(t.z / t.norm)) / 2),
   (t.y / t.norm) / Real.sqrt (2 * (1 + -(t.z / t.norm))),
   -(t.x / t.norm) / Real.sqrt (2 * (1 + -(t.z / t.norm))), 0⟩

/-- The yaw quaternion: rotation by `ψ` about `z`. -/
def yawQ (ψ : ℝ) : RQ := ⟨Real.cos (ψ / 2), 0, 0, Real.sin (ψ / 2)⟩

theorem ashift {x : Float32} {r r' e d : ℝ} (h : A32 x r e) (hd : |r - r'| ≤ d) :
    A32 x r' (e + d) :=
  ⟨h.1, (abs_sub_le x.toReal r r').trans (add_le_add h.2 hd)⟩

theorem libm32Err_eq : libm32Err = 1 / 2 ^ 22 := by norm_num [libm32Err]

/-- `max (-1) (min 1 a)` against `c ∈ (-1, 1]`. -/
theorem clamp_near {a c ε : ℝ} (hc : c ≤ 1) (ha : |a - c| ≤ ε) (ha0 : -1 ≤ a) :
    |max (-1) (min 1 a) - c| ≤ ε := by
  rw [max_eq_right (le_min (by norm_num) ha0)]
  rcases le_total a 1 with h1 | h1
  · rw [min_eq_right h1]; exact ha
  · rw [min_eq_left h1, abs_of_nonneg (by linarith)]
    have := (abs_le.1 ha).2; linarith

theorem tiltAxis_up {t : Vector3f.State} {θ : Float32}
    (hθ : θ = Float32.acos (constrain_value_line_float (Vector3f.op_mul_Vector3f upV t)
      (-(1.0 : Float32)) (1.0 : Float32) (Int32.toUInt32 (961 : Int32))))
    (h : is_zero_float (Vector3f.length (Vector3f.op_mod upV t)) = true ∨ is_zero_float θ = true) :
    tiltAxis t = upV := by
  subst hθ; unfold tiltAxis
  rcases h with h | h <;> simp [h]

theorem tiltAxis_gen {t : Vector3f.State} {θ : Float32}
    (hθ : θ = Float32.acos (constrain_value_line_float (Vector3f.op_mul_Vector3f upV t)
      (-(1.0 : Float32)) (1.0 : Float32) (Int32.toUInt32 (961 : Int32))))
    (h1 : is_zero_float (Vector3f.length (Vector3f.op_mod upV t)) = false)
    (h2 : is_zero_float θ = false) :
    tiltAxis t = (Vector3f.op_div_assign (Vector3f.op_mod upV t)
      (Vector3f.length (Vector3f.op_mod upV t))).1 := by
  subst hθ; unfold tiltAxis; simp [h1, h2]

theorem div_assign_x (v : Vector3f.State) (n : Float32) : (Vector3f.op_div_assign v n).1.x = v.x / n := rfl
theorem div_assign_y (v : Vector3f.State) (n : Float32) : (Vector3f.op_div_assign v n).1.y = v.y / n := rfl
theorem div_assign_z (v : Vector3f.State) (n : Float32) : (Vector3f.op_div_assign v n).1.z = v.z / n := rfl

/-- The clamped `up · t̂` the code passes to `acosf`. -/
abbrev cosArg (t : Vector3f.State) : Float32 :=
  constrain_value_line_float (Vector3f.op_mul_Vector3f upV t) (-(1.0 : Float32)) (1.0 : Float32)
    (Int32.toUInt32 (961 : Int32))

theorem HoverBox.unit {tv : Vector3f.State} (h : HoverBox tv) :
    (tv.x.toReal / (vv tv).norm) ^ 2 + (tv.y.toReal / (vv tv).norm) ^ 2 +
      (tv.z.toReal / (vv tv).norm) ^ 2 = 1 := by
  have hn : 0 < (vv tv).norm := by linarith [h.norm_lo]
  have hs := norm_sq (vv tv)
  rw [div_pow, div_pow, div_pow, ← add_div, ← add_div]
  rw [div_eq_one_iff_eq (by positivity)]
  exact hs.symm

theorem HoverBox.cZ {tv : Vector3f.State} (h : HoverBox tv) :
    68 / 100 ≤ -(tv.z.toReal / (vv tv).norm) := by
  have hn := h.norm_hi; have hn9 := h.norm_lo
  have hp : 0 < (vv tv).norm := by linarith
  rw [← neg_div, le_div_iff₀ hp]; nlinarith [h.bz2]

/-- The setup of the tilt analysis: the computed `t̂`, `cf` and `θ` satisfy `TiltHyp`. -/
theorem HoverBox.tiltHyp (hL : LibmSpec) {tv : Vector3f.State} (h : HoverBox tv) :
    TiltHyp (tv.x.toReal / (vv tv).norm) (tv.y.toReal / (vv tv).norm) (tv.z.toReal / (vv tv).norm)
      (Vector3f.normalize tv).x.toReal (Vector3f.normalize tv).y.toReal
      (cosArg (Vector3f.normalize tv)).toReal (Float32.acos (cosArg (Vector3f.normalize tv))).toReal ∧
    (cosArg (Vector3f.normalize tv)).IsFinite ∧
    (Float32.acos (cosArg (Vector3f.normalize tv))).IsFinite ∧
    |(Float32.acos (cosArg (Vector3f.normalize tv))).toReal| ≤ 4 := by
  obtain ⟨tx, ty, tz⟩ := h.normalize
  have hu := h.unit
  have hc := h.cZ
  set Z := tv.z.toReal / (vv tv).norm
  obtain ⟨fd, vd⟩ := up_dot tx.1 ty.1 tz.1
  have hlh : (-(1.0 : Float32)).toReal ≤ (1.0 : Float32).toReal := by
    rw [m1_val, f32_toReal_1p0]; norm_num
  obtain ⟨fc, vc⟩ := Att.constrain_spec (Int32.toUInt32 (961 : Int32)) fd m1_fin f32_isFinite_1p0 hlh
  rw [vd, m1_val, f32_toReal_1p0] at vc
  have hZ1 : -Z ≤ 1 := by
    nlinarith [sq_nonneg (tv.x.toReal / (vv tv).norm), sq_nonneg (tv.y.toReal / (vv tv).norm)]
  have hza := tz.2
  have hcf : |(cosArg (Vector3f.normalize tv)).toReal - -Z| ≤ 21 / 10 ^ 8 := by
    show |(constrain_value_line_float _ _ _ _).toReal - -Z| ≤ _
    rw [vc]
    refine clamp_near hZ1 ?_ ?_
    · rw [show -(Vector3f.normalize tv).z.toReal - -Z = -((Vector3f.normalize tv).z.toReal - Z) by ring,
        abs_neg]; exact hza
    · have := (abs_le.1 hza).2; linarith
  have hcf1 : (cosArg (Vector3f.normalize tv)).toReal ≤ 1 := by
    show (constrain_value_line_float _ _ _ _).toReal ≤ 1
    rw [vc]; exact max_le (by norm_num) (min_le_left _ _)
  have hcf0 : -1 ≤ (cosArg (Vector3f.normalize tv)).toReal := by
    show -1 ≤ (constrain_value_line_float _ _ _ _).toReal
    rw [vc]; exact le_max_left _ _
  obtain ⟨fa, ea⟩ := hL.acosf _ fc (abs_le.2 ⟨hcf0, hcf1⟩)
  rw [libm32Err_eq] at ea
  refine ⟨⟨hu, hc, tx.2, ty.2, hcf, hcf1, hcf0, ea⟩, fc, fa, ?_⟩
  have h0 := Real.arccos_nonneg (cosArg (Vector3f.normalize tv)).toReal
  have hpi := Real.arccos_le_pi (cosArg (Vector3f.normalize tv)).toReal
  have := Real.pi_lt_d2
  have := abs_le.1 ea
  rw [abs_le]; constructor <;> norm_num at * <;> linarith

theorem RV.abs_x_le {X Y Z : ℝ} (h : X ^ 2 + Y ^ 2 + Z ^ 2 = 1) : |X| ≤ 1 :=
  abs_le.2 ⟨by nlinarith [sq_nonneg Y, sq_nonneg Z, sq_nonneg (X + 1)],
    by nlinarith [sq_nonneg Y, sq_nonneg Z, sq_nonneg (X - 1)]⟩

theorem up_VB : VB upV 1.01 := by
  refine ⟨B32.of_exact f32_isFinite_0p0 (by rw [f32_toReal_0p0]; norm_num),
    B32.of_exact f32_isFinite_0p0 (by rw [f32_toReal_0p0]; norm_num),
    B32.of_exact m1_fin (by rw [m1_val]; norm_num)⟩

theorem vv_up : vv upV = ⟨0, 0, -1⟩ := by
  simp only [vv, upx, upy, upz, f32_toReal_0p0, m1_val]

set_option maxHeartbeats 1000000 in
/-- **The tilt quaternion** (`from_axis_angle(axis, θ)` with the code's axis and angle) for a
thrust vector in the hover box: within `3.252·10⁻⁴` per component of `tiltQ (tv)` (the scalar part
within `3.7·10⁻⁷`). -/
theorem HoverBox.tilt_near (hL : LibmSpec) {tv : Vector3f.State} (h : HoverBox tv) :
    QA (Quaternion.from_axis_angle_Vector3f_float Quaternion.init_void
        (tiltAxis (Vector3f.normalize tv)) (Float32.acos (cosArg (Vector3f.normalize tv))))
      (tiltQ (vv tv)) (3252 / 10 ^ 7) := by
  obtain ⟨H, fc, fa, ba⟩ := h.tiltHyp hL
  obtain ⟨tx, ty, tz⟩ := h.normalize
  set t := Vector3f.normalize tv with ht
  set θ := Float32.acos (cosArg t) with hθ
  obtain ⟨⟨c1f, c1v⟩, ⟨c2f, c2v⟩, ⟨c3f, c3v⟩⟩ := up_cross tx.1 ty.1 tz.1
  set cr := Vector3f.op_mod upV t with hcr
  have hX1 := RV.abs_x_le H.unit
  have hY1 : |tv.y.toReal / (vv tv).norm| ≤ 1 :=
    RV.abs_x_le (Y := tv.x.toReal / (vv tv).norm) (Z := tv.z.toReal / (vv tv).norm)
      (by linarith [H.unit])
  have btx : |t.x.toReal| ≤ 1000 := by have := tx.abs_le; linarith
  have bty : |t.y.toReal| ≤ 1000 := by have := ty.abs_le; linarith
  obtain ⟨fL, eL⟩ := len_near c1f c2f c3f (by rw [c1v]; exact bty)
    (by rw [c2v, abs_neg]; exact btx) (by rw [c3v]; norm_num)
  set L := Vector3f.length cr with hLdef
  set r := (vv cr).norm with hr
  have hr_eq : r = Real.sqrt (t.y.toReal ^ 2 + (-t.x.toReal) ^ 2) := by
    rw [hr]; simp only [RV.norm, vv]; rw [c1v, c2v, c3v]; ring_nf
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hcos := H.cos_near
  have hD := H.D_ge
  have eL' := abs_le.1 eL
  unfold QA
  by_cases hgen : is_zero_float L = false ∧ is_zero_float θ = false
  · obtain ⟨hz1, hz2⟩ := hgen
    rw [tiltAxis_gen hθ hz1 hz2]
    have hL0 : 2 ^ (-23 : ℤ) ≤ |L.toReal| := by
      by_contra hc; push Not at hc
      rw [(Att.isZero_iff fL).2 hc] at hz1; exact absurd hz1 (by decide)
    rw [two_pow_m23] at hL0
    have hLpos : 1 / 8388608 ≤ L.toReal := by
      rcases abs_cases L.toReal with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · exfalso; norm_num at eL'; nlinarith
    have hr24 : 1 / 2 ^ 24 ≤ r := by norm_num at eL' ⊢; nlinarith
    have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr24
    have key : ∀ x : Float32, x.IsFinite → |x.toReal| ≤ r →
        A32 (x / L) (x.toReal / r) (21 / 10 ^ 8) := by
      intro x hx hxn
      obtain ⟨f, e⟩ := ndiv hx fL hr24 eL hxn
      refine ⟨f, e.trans ?_⟩
      have : |x.toReal| / r ≤ 1 := by rw [div_le_one hrpos]; exact hxn
      have : 3503 / 1000 * (1 / 16777216) * (|x.toReal| / r) ≤ 3503 / 1000 * (1 / 16777216) * 1 := by
        gcongr
      norm_num at this ⊢; linarith
    have a1 := key _ c1f (abs_le_norm_x (vv cr))
    have a2 := key _ c2f (abs_le_norm_y (vv cr))
    have a3 := key _ c3f (abs_le_norm_z (vv cr))
    rw [c1v] at a1; rw [c2v] at a2; rw [c3v, zero_div] at a3
    have hty_r : |t.y.toReal / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hrpos, div_le_one hrpos, ← c1v]; exact abs_le_norm_x (vv cr)
    have htx_r : |-t.x.toReal / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hrpos, div_le_one hrpos, ← c2v]; exact abs_le_norm_y (vv cr)
    have hVB : VB (Vector3f.op_div_assign cr L).1 1.01 := by
      refine ⟨⟨A32.of_exact a1.1, ?_⟩, ⟨A32.of_exact a2.1, ?_⟩, ⟨A32.of_exact a3.1, ?_⟩⟩
      · have := a1.abs_le; rw [div_assign_x]; linarith
      · have := a2.abs_le; rw [div_assign_y]; linarith
      · have := a3.abs_le; rw [div_assign_z]; norm_num at this ⊢; linarith
    obtain ⟨q1, q2, q3, q4⟩ := axisAngle_near hL Quaternion.init_void hVB fa (by linarith)
    have hgen := H.generic (A1 := (cr.x / L).toReal) (A2 := (cr.y / L).toReal)
      (by rw [← hr_eq]; exact hrpos) (by rw [← hr_eq]; exact a1.2) (by rw [← hr_eq]; exact a2.2)
    have hs1 := Real.abs_sin_le_one (θ.toReal / 2)
    refine ⟨(ashift q1 hcos).mono (by norm_num), (ashift q2 hgen.1).mono (by norm_num),
      (ashift q3 hgen.2).mono (by norm_num), (ashift (d := 21 / 10 ^ 8) q4 ?_).mono (by norm_num)⟩
    show |(cr.z / L).toReal * Real.sin (θ.toReal / 2) - 0| ≤ _
    rw [sub_zero, abs_mul]
    have := a3.2; rw [sub_zero] at this
    calc |(cr.z / L).toReal| * |Real.sin (θ.toReal / 2)| ≤ 21 / 10 ^ 8 * 1 := by gcongr
      _ ≤ _ := by norm_num
  · have hup : is_zero_float L = true ∨ is_zero_float θ = true := by
      rcases hl : is_zero_float L <;> rcases hθz : is_zero_float θ <;> simp_all
    rw [tiltAxis_up hθ hup]
    have hcase : r ≤ 12 / 10 ^ 8 ∨ |θ.toReal| < 1 / 2 ^ 23 := by
      rcases hup with hu | hu
      · left
        have := (Att.isZero_iff fL).1 hu
        rw [two_pow_m23] at this
        have := (abs_lt.1 this).2
        norm_num at eL' ⊢; nlinarith
      · right
        have := (Att.isZero_iff fa).1 hu
        rw [two_pow_m23] at this; norm_num at this ⊢; exact this
    have hup' := H.up hr_eq hcase
    obtain ⟨q1, q2, q3, q4⟩ := axisAngle_near hL Quaternion.init_void up_VB fa (by linarith)
    rw [vv_up] at q1 q2 q3 q4
    simp only [RQ.ofAxisAngle, zero_mul, neg_mul, one_mul] at q1 q2 q3 q4
    refine ⟨(ashift q1 hcos).mono (by norm_num), (ashift (d := 325 / 10 ^ 6) q2 ?_).mono (by norm_num),
      (ashift (d := 325 / 10 ^ 6) q3 ?_).mono (by norm_num),
      (ashift (d := 325 / 10 ^ 6) q4 ?_).mono (by norm_num)⟩
    · rw [zero_sub, abs_neg]; exact hup'.2.1
    · rw [zero_sub, abs_neg]; exact hup'.2.2
    · show |-Real.sin (θ.toReal / 2) - 0| ≤ _
      rw [sub_zero, abs_neg]; exact hup'.1

/-! ## The yaw quaternion and the product -/

theorem yaw_axis_VB : VB (Vector3f.init_float3 (0.0 : Float32) (0.0 : Float32) (1.0 : Float32)) 1.01 :=
  ⟨B32.of_exact f32_isFinite_0p0 (by rw [f32_toReal_0p0]; norm_num),
    B32.of_exact f32_isFinite_0p0 (by rw [f32_toReal_0p0]; norm_num),
    B32.of_exact f32_isFinite_1p0 (by rw [f32_toReal_1p0]; norm_num)⟩

/-- The yaw quaternion `from_axis_angle((0,0,1), ψ)`: within `1.3·10⁻⁷` of `yawQ ψ`. -/
theorem yaw_near (hL : LibmSpec) {ψ : Float32} (hψ : ψ.IsFinite) (bψ : |ψ.toReal| ≤ 1000) :
    QA (Quaternion.from_axis_angle_Vector3f_float Quaternion.init_void
      (Vector3f.init_float3 (0.0 : Float32) (0.0 : Float32) (1.0 : Float32)) ψ) (yawQ ψ.toReal)
      (13 / 10 ^ 8) := by
  have h := axisAngle_near hL Quaternion.init_void yaw_axis_VB hψ bψ
  have e : RQ.ofAxisAngle (vv (Vector3f.init_float3 (0.0 : Float32) (0.0 : Float32) (1.0 : Float32)))
      ψ.toReal = yawQ ψ.toReal := by
    simp only [RQ.ofAxisAngle, yawQ, vv]
    show RQ.mk _ ((0.0 : Float32).toReal * _) ((0.0 : Float32).toReal * _) ((1.0 : Float32).toReal * _) = _
    rw [f32_toReal_0p0, f32_toReal_1p0]; simp
  rwa [e] at h

theorem cos_add_sin_le (x : ℝ) : |Real.cos x| + |Real.sin x| ≤ 14143 / 10000 := by
  have h1 := Real.sin_sq_add_cos_sq x
  have h2 : (|Real.cos x| + |Real.sin x|) ^ 2 ≤ 2 := by
    nlinarith [sq_abs (Real.cos x), sq_abs (Real.sin x), sq_nonneg (|Real.cos x| - |Real.sin x|)]
  nlinarith [abs_nonneg (Real.cos x), abs_nonneg (Real.sin x)]

theorem lip_aux {d1 d2 c s m1 m2 m3 m4 e1 e2 e3 e4 ea eb : ℝ} (h1 : |d1| ≤ ea) (h2 : |d2| ≤ ea)
    (hcs : |c| + |s| ≤ 14143 / 10000) (k1 : |m1| ≤ 1.01) (k2 : |m2| ≤ 1.01)
    (k3 : |m3| ≤ 1.01) (k4 : |m4| ≤ 1.01) (f1 : |e1| ≤ eb) (f2 : |e2| ≤ eb)
    (f3 : |e3| ≤ eb) (f4 : |e4| ≤ eb) :
    |d1 * c + d2 * s + (m1 * e1 + m2 * e2 + m3 * e3 + m4 * e4)| ≤
      14143 / 10000 * ea + 4 * (1.01) * eb := by
  have hea : 0 ≤ ea := (abs_nonneg _).trans h1
  have hp : ∀ m e : ℝ, |m| ≤ 1.01 → |e| ≤ eb → |m * e| ≤ 1.01 * eb := by
    intro m e hm he; rw [abs_mul]; exact mul_le_mul hm he (abs_nonneg _) (by norm_num)
  have g1 : |d1 * c| ≤ ea * |c| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have g2 : |d2 * s| ≤ ea * |s| := by rw [abs_mul]; exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  have g3 : ea * |c| + ea * |s| ≤ ea * (14143 / 10000) := by rw [← mul_add]; gcongr
  have := hp m1 e1 k1 f1; have := hp m2 e2 k2 f2; have := hp m3 e3 k3 f3; have := hp m4 e4 k4 f4
  have t1 := abs_add_le (d1 * c + d2 * s) (m1 * e1 + m2 * e2 + m3 * e3 + m4 * e4)
  have t2 := abs_add_le (d1 * c) (d2 * s)
  have t3 := abs_add_le (m1 * e1 + m2 * e2 + m3 * e3) (m4 * e4)
  have t4 := abs_add_le (m1 * e1 + m2 * e2) (m3 * e3)
  have t5 := abs_add_le (m1 * e1) (m2 * e2)
  linarith

/-- Product with a yaw quaternion: errors `ea` on the first factor (components at most `1.01`) and
`eb` on the second give `1.4143 ea + 4.04 eb` per component. -/
theorem mul_yaw_lip {a b A : RQ} {ψ ea eb : ℝ}
    (ha : |a.w - A.w| ≤ ea ∧ |a.x - A.x| ≤ ea ∧ |a.y - A.y| ≤ ea ∧ |a.z - A.z| ≤ ea)
    (hb : |b.w - (yawQ ψ).w| ≤ eb ∧ |b.x - (yawQ ψ).x| ≤ eb ∧ |b.y - (yawQ ψ).y| ≤ eb ∧
      |b.z - (yawQ ψ).z| ≤ eb)
    (hm : |a.w| ≤ 1.01 ∧ |a.x| ≤ 1.01 ∧ |a.y| ≤ 1.01 ∧ |a.z| ≤ 1.01) :
    let β := 14143 / 10000 * ea + 4 * (1.01) * eb
    |(RQ.mul a b).w - (RQ.mul A (yawQ ψ)).w| ≤ β ∧ |(RQ.mul a b).x - (RQ.mul A (yawQ ψ)).x| ≤ β ∧
      |(RQ.mul a b).y - (RQ.mul A (yawQ ψ)).y| ≤ β ∧ |(RQ.mul a b).z - (RQ.mul A (yawQ ψ)).z| ≤ β := by
  intro β
  obtain ⟨dw, dx, dy, dz⟩ := ha
  obtain ⟨ew, ex, ey, ez⟩ := hb
  obtain ⟨mw, mx, my, mz⟩ := hm
  have hcs := cos_add_sin_le (ψ / 2)
  have ndx : |-(a.x - A.x)| ≤ ea := by rwa [abs_neg]
  have ndz : |-(a.z - A.z)| ≤ ea := by rwa [abs_neg]
  have nmx : |-a.x| ≤ 1.01 := by rwa [abs_neg]
  have nmy : |-a.y| ≤ 1.01 := by rwa [abs_neg]
  have nmz : |-a.z| ≤ 1.01 := by rwa [abs_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (RQ.mul a b).w - (RQ.mul A (yawQ ψ)).w =
        (a.w - A.w) * Real.cos (ψ / 2) + (-(a.z - A.z)) * Real.sin (ψ / 2) +
        (a.w * (b.w - (yawQ ψ).w) + (-a.x) * (b.x - (yawQ ψ).x) + (-a.y) * (b.y - (yawQ ψ).y) +
          (-a.z) * (b.z - (yawQ ψ).z)) := by simp only [RQ.mul, yawQ]; ring
    rw [e]; exact lip_aux dw ndz hcs mw nmx nmy nmz ew ex ey ez
  · have e : (RQ.mul a b).x - (RQ.mul A (yawQ ψ)).x =
        (a.x - A.x) * Real.cos (ψ / 2) + (a.y - A.y) * Real.sin (ψ / 2) +
        (a.w * (b.x - (yawQ ψ).x) + a.x * (b.w - (yawQ ψ).w) + a.y * (b.z - (yawQ ψ).z) +
          (-a.z) * (b.y - (yawQ ψ).y)) := by simp only [RQ.mul, yawQ]; ring
    rw [e]; exact lip_aux dx dy hcs mw mx my nmz ex ew ez ey
  · have e : (RQ.mul a b).y - (RQ.mul A (yawQ ψ)).y =
        (a.y - A.y) * Real.cos (ψ / 2) + (-(a.x - A.x)) * Real.sin (ψ / 2) +
        (a.w * (b.y - (yawQ ψ).y) + (-a.x) * (b.z - (yawQ ψ).z) + a.y * (b.w - (yawQ ψ).w) +
          a.z * (b.x - (yawQ ψ).x)) := by simp only [RQ.mul, yawQ]; ring
    rw [e]; exact lip_aux dy ndx hcs mw nmx my mz ey ez ew ex
  · have e : (RQ.mul a b).z - (RQ.mul A (yawQ ψ)).z =
        (a.z - A.z) * Real.cos (ψ / 2) + (a.w - A.w) * Real.sin (ψ / 2) +
        (a.w * (b.z - (yawQ ψ).z) + a.x * (b.y - (yawQ ψ).y) + (-a.y) * (b.x - (yawQ ψ).x) +
          a.z * (b.w - (yawQ ψ).w)) := by simp only [RQ.mul, yawQ]; ring
    rw [e]; exact lip_aux dz dw hcs mw mx nmy mz ez ey ex ew

/-- A `QA` approximation of a real quaternion with components at most `R` gives the `QB` bound. -/
theorem QA.toQB {q : Quaternion.State} {r : RQ} {e R M : ℝ} (h : QA q r e)
    (hr : |r.w| ≤ R ∧ |r.x| ≤ R ∧ |r.y| ≤ R ∧ |r.z| ≤ R) (hM : R + e ≤ M) : QB q M :=
  ⟨⟨A32.of_exact h.1.1, by have := h.1.abs_le; linarith [hr.1]⟩,
   ⟨A32.of_exact h.2.1.1, by have := h.2.1.abs_le; linarith [hr.2.1]⟩,
   ⟨A32.of_exact h.2.2.1.1, by have := h.2.2.1.abs_le; linarith [hr.2.2.1]⟩,
   ⟨A32.of_exact h.2.2.2.1, by have := h.2.2.2.abs_le; linarith [hr.2.2.2]⟩⟩

theorem yawQ_le (ψ : ℝ) : |(yawQ ψ).w| ≤ 1 ∧ |(yawQ ψ).x| ≤ 1 ∧ |(yawQ ψ).y| ≤ 1 ∧ |(yawQ ψ).z| ≤ 1 :=
  ⟨Real.abs_cos_le_one _, by simp [yawQ], by simp [yawQ], Real.abs_sin_le_one _⟩

theorem HoverBox.tiltQ_le {tv : Vector3f.State} (h : HoverBox tv) :
    |(tiltQ (vv tv)).w| ≤ 1 ∧ |(tiltQ (vv tv)).x| ≤ 1 ∧ |(tiltQ (vv tv)).y| ≤ 1 ∧
      |(tiltQ (vv tv)).z| ≤ 1 := by
  have hu := h.unit
  have hc := h.cZ
  have hX := RV.abs_x_le hu
  have hY : |tv.y.toReal / (vv tv).norm| ≤ 1 :=
    RV.abs_x_le (Y := tv.x.toReal / (vv tv).norm) (Z := tv.z.toReal / (vv tv).norm) (by linarith)
  have hZ : |tv.z.toReal / (vv tv).norm| ≤ 1 :=
    RV.abs_x_le (Y := tv.x.toReal / (vv tv).norm) (Z := tv.y.toReal / (vv tv).norm) (by linarith)
  have hD : 1 ≤ Real.sqrt (2 * (1 + -(tv.z.toReal / (vv tv).norm))) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hDp : 0 < Real.sqrt (2 * (1 + -(tv.z.toReal / (vv tv).norm))) := by linarith
  refine ⟨?_, ?_, ?_, by simp [tiltQ]⟩
  · show |Real.sqrt ((1 + -(tv.z.toReal / (vv tv).norm)) / 2)| ≤ 1
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_le_one]
    have := (abs_le.1 hZ).1; linarith
  · show |tv.y.toReal / (vv tv).norm / Real.sqrt (2 * (1 + -(tv.z.toReal / (vv tv).norm)))| ≤ 1
    rw [abs_div, abs_of_pos hDp, div_le_one hDp]; linarith
  · show |-(tv.x.toReal / (vv tv).norm) / Real.sqrt (2 * (1 + -(tv.z.toReal / (vv tv).norm)))| ≤ 1
    rw [abs_div, abs_of_pos hDp, div_le_one hDp, abs_neg]; linarith

/-- **`attitude_from_thrust_vector` near hover.** For a thrust vector `tv = (a_N, a_E, a_D)` of
finite floats with `|a_N|, |a_E| ≤ 6`, `a_D ∈ [-10, -9]`, and a finite heading `|ψ| ≤ 4`, every
component of the emitted result is finite and within `4.7·10⁻⁴` of the real
`q_tilt(tv) ⊗ q_yaw(ψ)` (`tiltQ`, `yawQ`). The error is dominated by `acosf` of a dot product near
`1` (`sin(θ/2)` within `√(δ/2)` for a rounding error `δ ≤ 3.503 u` of `up · t̂`). -/
theorem attitude_from_thrust_vector_near (hL : LibmSpec) {tv : Vector3f.State} {ψ : Float32}
    (h : HoverBox tv) (hψ : ψ.IsFinite) (bψ : |ψ.toReal| ≤ 4) :
    QA (AC_AttitudeControl_Multi.attitude_from_thrust_vector tv ψ)
      (RQ.mul (tiltQ (vv tv)) (yawQ ψ.toReal)) (47 / 10 ^ 5) := by
  rw [aftv_eq tv ψ h.lsq_nz]
  have ht := h.tilt_near hL
  have hy := yaw_near hL hψ (by linarith)
  have hm := quat_mul_near (ht.toQB (M := 1.01) h.tiltQ_le (by norm_num)) (hy.toQB (M := 1.01) (yawQ_le _) (by norm_num))
  have hbt := (ht.toQB (M := 1.01) h.tiltQ_le (by norm_num))
  have hlip := mul_yaw_lip (a := qv _) (b := qv _) (A := tiltQ (vv tv)) (ψ := ψ.toReal)
    ⟨ht.1.2, ht.2.1.2, ht.2.2.1.2, ht.2.2.2.2⟩ ⟨hy.1.2, hy.2.1.2, hy.2.2.1.2, hy.2.2.2.2⟩
    ⟨hbt.1.2, hbt.2.1.2, hbt.2.2.1.2, hbt.2.2.2.2⟩
  obtain ⟨l1, l2, l3, l4⟩ := hlip
  exact ⟨(ashift hm.1 l1).mono (by norm_num), (ashift hm.2.1 l2).mono (by norm_num),
    (ashift hm.2.2.1 l3).mono (by norm_num), (ashift hm.2.2.2 l4).mono (by norm_num)⟩
