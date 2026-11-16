import Contracts.Track.CtrlAttitudeQuatAxis
import Contracts.Track.CtrlAttitudeQuatUpdate
import Contracts.Track.CtrlAttitudeQuatHeading

/-!
# The thrust-vector attitude error (milestone M4, lemma C8)

`AC_AttitudeControl::thrust_vector_rotation_angles(target, body, …)` rotates `up = (0, 0, -1)` by
both attitudes, takes the thrust error angle `θ = acosf(t_b · t_t)` and the axis
`t_b × t_t / |t_b × t_t|`, rotates the axis into the body frame, forms the correction quaternion
and returns its rotation vector (`to_axis_angle`) as the `x, y` attitude error, together with the
thrust angle `acosf(up · t_b)` and `θ`.

The real law (`ErrR`): the attitudes normalized (`B̂`, `T̂`), `t̂_b = B̂ up B̂*`, `t̂_t = T̂ up T̂*`,
`c = t̂_b · t̂_t`, the rotation vector `arccos c · B̂* (t̂_b × t̂_t) B̂ / |t̂_b × t̂_t|` (written as
`(θ / |t̂_b × t̂_t|) · B̂*(t̂_b × t̂_t)B̂`, which is `0` when the cross product is), and the thrust
angle `arccos(up · t̂_b)`.

The `acosf` of a dot product near `1` is `½`-Hölder: an error `δ` of the dot product moves the
angle by up to `(2/cos A)·√(δ/2)` for angles up to `2A` (`arccos_holder`). With attitudes unit
within `10⁻⁶` the computed thrust directions are within `10⁻⁶` per component of the unit ones
(`tb_near`; the non-unit attitude contributes `5.2·10⁻⁷`), the dot products within `4·10⁻⁶`
(`t_b · t_t`) and `10⁻⁶` (`up · t_b`); hence `β = 3·10⁻³` on the `x, y` error
(`attitude_error_xy_near`), `2.9·10⁻³` on the thrust error angle and `1.5·10⁻³` on the thrust
angle. Region (`Level`): thrust directions within `30°` of vertical (`q₂² + q₃² ≤ 0.067`), and
within `20°` of each other (`t̂_b · t̂_t ≥ 0.94`). `thrust_heading_near` combines this with the
heading clip being inactive. The heading error `z` (second `to_axis_angle`) is not covered.
-/

namespace Contracts.Track.AttQ

open Contracts.Mission AC_Attitude_lib Float.Model UnpackedFloat

noncomputable section

namespace Err

/-! ## Vectors -/

def RV.sub (a b : RV) : RV := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

theorem RV.dot_le_norm (a b : RV) : RV.dot a b ≤ a.norm * b.norm := by
  have hs2 := norm_sq a
  have hr2 := norm_sq b
  have h1 : (RV.dot a b) ^ 2 ≤ (a.norm * b.norm) ^ 2 := by
    rw [mul_pow, hs2, hr2]; simp only [RV.dot]
    nlinarith [sq_nonneg (a.x * b.y - a.y * b.x), sq_nonneg (a.x * b.z - a.z * b.x),
      sq_nonneg (a.y * b.z - a.z * b.y)]
  exact (abs_le_of_sq_le_sq' h1 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2

theorem RV.norm_add_le (a b : RV) : (RV.add a b).norm ≤ a.norm + b.norm := by
  have h := RV.dot_le_norm a b
  have h0 : (RV.add a b).norm ^ 2 = (a.x + b.x) ^ 2 + (a.y + b.y) ^ 2 + (a.z + b.z) ^ 2 :=
    norm_sq (RV.add a b)
  have ha := norm_sq a
  have hb := norm_sq b
  have ha0 : 0 ≤ a.norm := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b.norm := Real.sqrt_nonneg _
  have hn0 : 0 ≤ (RV.add a b).norm := Real.sqrt_nonneg _
  simp only [RV.dot] at h
  have : (RV.add a b).norm ^ 2 ≤ (a.norm + b.norm) ^ 2 := by rw [h0]; nlinarith
  exact abs_le_of_sq_le_sq' this (by positivity) |>.2

theorem RV.norm_sub_tri (a b c : RV) : (RV.sub a c).norm ≤ (RV.sub a b).norm + (RV.sub b c).norm := by
  have := RV.norm_add_le (RV.sub a b) (RV.sub b c)
  have e : RV.add (RV.sub a b) (RV.sub b c) = RV.sub a c := by
    simp only [RV.add, RV.sub]; congr 1 <;> ring
  rwa [e] at this

theorem RV.norm_le_of_comp {a : RV} {e : ℝ} (hx : |a.x| ≤ e) (hy : |a.y| ≤ e) (hz : |a.z| ≤ e) :
    a.norm ≤ 17321 / 10000 * e := by
  have he : 0 ≤ e := (abs_nonneg _).trans hx
  rw [RV.norm, Real.sqrt_le_left (by positivity)]
  have := sq_abs a.x; have := sq_abs a.y; have := sq_abs a.z
  have h1 : |a.x| ^ 2 ≤ e ^ 2 := by gcongr
  have h2 : |a.y| ^ 2 ≤ e ^ 2 := by gcongr
  have h3 : |a.z| ^ 2 ≤ e ^ 2 := by gcongr
  nlinarith

theorem RV.norm_smul (c : ℝ) (a : RV) : (RV.smul c a).norm = |c| * a.norm := by
  simp only [RV.norm, RV.smul]
  rw [show (c * a.x) ^ 2 + (c * a.y) ^ 2 + (c * a.z) ^ 2 = c ^ 2 * (a.x ^ 2 + a.y ^ 2 + a.z ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem RV.norm_nonneg (a : RV) : 0 ≤ a.norm := Real.sqrt_nonneg _

/-- Directions: `|x/|x| - y/|y|| ≤ 2 |x - y| / |y|`. -/
theorem RV.dir_le {x y : RV} (hy : 0 < y.norm) :
    (RV.sub (RV.smul (1 / x.norm) x) (RV.smul (1 / y.norm) y)).norm ≤ 2 * (RV.sub x y).norm / y.norm := by
  rcases eq_or_lt_of_le (RV.norm_nonneg x) with hx | hx
  · -- `x = 0`
    have hx0 : x.x = 0 ∧ x.y = 0 ∧ x.z = 0 := by
      have h := norm_sq x; rw [← hx] at h
      refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg x.x, sq_nonneg x.y, sq_nonneg x.z]
    have e1 : RV.sub (RV.smul (1 / x.norm) x) (RV.smul (1 / y.norm) y) = RV.smul (-1) (RV.smul (1 / y.norm) y) := by
      simp only [RV.sub, RV.smul, hx0.1, hx0.2.1, hx0.2.2]; congr 1 <;> ring
    have e2 : RV.sub x y = RV.smul (-1) y := by
      simp only [RV.sub, RV.smul, hx0.1, hx0.2.1, hx0.2.2]; congr 1 <;> ring
    rw [e1, e2, RV.norm_smul, RV.norm_smul, RV.norm_smul]
    rw [abs_neg, abs_one, one_mul, one_mul, abs_of_pos (one_div_pos.2 hy),
      one_div_mul_cancel hy.ne', mul_div_assoc, div_self hy.ne']; norm_num
  · have e : RV.sub (RV.smul (1 / x.norm) x) (RV.smul (1 / y.norm) y) =
        RV.add (RV.smul (1 / y.norm) (RV.sub x y)) (RV.smul ((y.norm - x.norm) / (x.norm * y.norm)) x) := by
      simp only [RV.sub, RV.smul, RV.add]; congr 1 <;> field_simp <;> ring
    rw [e]
    refine (RV.norm_add_le _ _).trans ?_
    rw [RV.norm_smul, RV.norm_smul]
    have hd : |y.norm - x.norm| ≤ (RV.sub x y).norm := by
      have h1 := RV.norm_sub_tri x y ⟨0, 0, 0⟩
      have h2 := RV.norm_sub_tri y x ⟨0, 0, 0⟩
      have ex : (RV.sub x ⟨0, 0, 0⟩) = x := by simp only [RV.sub, sub_zero]
      have ey : (RV.sub y ⟨0, 0, 0⟩) = y := by simp only [RV.sub, sub_zero]
      have exy : (RV.sub y x).norm = (RV.sub x y).norm := by
        simp only [RV.norm, RV.sub]; congr 1; ring
      rw [ex, ey] at h1 h2; rw [exy] at h2
      rw [abs_le]; constructor <;> linarith
    rw [abs_of_pos (by positivity), abs_div, abs_of_pos (by positivity : 0 < x.norm * y.norm)]
    calc 1 / y.norm * (RV.sub x y).norm + |y.norm - x.norm| / (x.norm * y.norm) * x.norm
        = (RV.sub x y).norm / y.norm + |y.norm - x.norm| / y.norm := by field_simp
      _ ≤ (RV.sub x y).norm / y.norm + (RV.sub x y).norm / y.norm := by gcongr
      _ = _ := by ring

/-! ## Rotations -/

theorem rot_norm_sq (q : RQ) (v : RV) :
    (RQ.rot q v).norm ^ 2 = v.norm ^ 2 + 4 * (RQ.norm2 q - 1) * (RV.cross q.vec v).norm ^ 2 := by
  rw [norm_sq, norm_sq, norm_sq]
  simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec, RQ.norm2]; ring

theorem rot_norm_unit {q : RQ} (hq : RQ.norm2 q = 1) (v : RV) : (RQ.rot q v).norm = v.norm := by
  have h := rot_norm_sq q v
  rw [hq, sub_self, mul_zero, zero_mul, add_zero] at h
  have := RV.norm_nonneg (RQ.rot q v); have := RV.norm_nonneg v
  nlinarith [sq_nonneg ((RQ.rot q v).norm - v.norm), sq_nonneg ((RQ.rot q v).norm + v.norm)]

theorem rot_sub (q : RQ) (a b : RV) : RQ.rot q (RV.sub a b) = RV.sub (RQ.rot q a) (RQ.rot q b) := by
  simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec, RV.sub]; congr 1 <;> ring

/-- Scaling the quaternion by `λ` scales `rot q v - v` by `λ²`. -/
theorem rot_scale (q : RQ) (l : ℝ) (v : RV) :
    RV.sub (RQ.rot ⟨l * q.w, l * q.x, l * q.y, l * q.z⟩ v) v = RV.smul (l ^ 2) (RV.sub (RQ.rot q v) v) := by
  simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec, RV.sub]; congr 1 <;> ring

theorem normalize_unit {P : RQ} (h : 0 < RQ.norm2 P) : RQ.norm2 (RQ.normalize P) = 1 := by
  have hs := Real.sq_sqrt h.le
  have hp : 0 < Real.sqrt (RQ.norm2 P) := Real.sqrt_pos.2 h
  simp only [RQ.normalize]
  have : RQ.norm2 ⟨P.w / Real.sqrt (RQ.norm2 P), P.x / Real.sqrt (RQ.norm2 P),
      P.y / Real.sqrt (RQ.norm2 P), P.z / Real.sqrt (RQ.norm2 P)⟩ = RQ.norm2 P / (Real.sqrt (RQ.norm2 P)) ^ 2 := by
    simp only [RQ.norm2]; field_simp
  rw [this, hs, div_self h.ne']

theorem normalize_scale {P : RQ} (h : 0 < RQ.norm2 P) :
    P = ⟨Real.sqrt (RQ.norm2 P) * (RQ.normalize P).w, Real.sqrt (RQ.norm2 P) * (RQ.normalize P).x,
      Real.sqrt (RQ.norm2 P) * (RQ.normalize P).y, Real.sqrt (RQ.norm2 P) * (RQ.normalize P).z⟩ := by
  have hp : 0 < Real.sqrt (RQ.norm2 P) := Real.sqrt_pos.2 h
  simp only [RQ.normalize]
  rcases P with ⟨w, x, y, z⟩
  congr 1 <;> field_simp

theorem conj_normalize (P : RQ) : RQ.conj (RQ.normalize P) = RQ.normalize (RQ.conj P) := by
  simp only [RQ.conj, RQ.normalize, RQ.norm2, neg_div]; congr 1 <;> ring_nf

theorem norm2_conj (P : RQ) : RQ.norm2 (RQ.conj P) = RQ.norm2 P := by
  simp only [RQ.conj, RQ.norm2]; ring

/-- Rotating by a quaternion unit within `ν` instead of its normalization: `rot P v - rot P̂ v`
is `(|P|² - 1)(rot P̂ v - v)`. -/
theorem rot_vs_normalize {P : RQ} (h : 0 < RQ.norm2 P) (v : RV) :
    RV.sub (RQ.rot P v) (RQ.rot (RQ.normalize P) v) =
      RV.smul (RQ.norm2 P - 1) (RV.sub (RQ.rot (RQ.normalize P) v) v) := by
  have e := rot_scale (RQ.normalize P) (Real.sqrt (RQ.norm2 P)) v
  rw [← normalize_scale h, Real.sq_sqrt h.le] at e
  have : RV.sub (RQ.rot P v) (RQ.rot (RQ.normalize P) v) =
      RV.sub (RV.sub (RQ.rot P v) v) (RV.sub (RQ.rot (RQ.normalize P) v) v) := by
    simp only [RV.sub]; congr 1 <;> ring
  rw [this, e]; simp only [RV.sub, RV.smul]; congr 1 <;> ring

/-- Lagrange's identity. -/
theorem lagrange (a b : RV) : (RV.cross a b).norm ^ 2 = a.norm ^ 2 * b.norm ^ 2 - (RV.dot a b) ^ 2 := by
  rw [norm_sq, norm_sq, norm_sq]; simp only [RV.cross, RV.dot]; ring

/-! ## `arccos` near `1` is `½`-Hölder -/

theorem neg_one_le_of_arccos {x : ℝ} (h : Real.arccos x ≤ 1) : -1 ≤ x := by
  by_contra hc; push Not at hc
  rw [Real.arccos_of_le_neg_one hc.le] at h; linarith [Real.pi_gt_three]

set_option maxHeartbeats 2000000 in
/-- **`arccos` is `½`-Hölder near `1`**: for angles at most `2A ≤ 1` and `k ≤ cos A`, an error `δ`
of the cosine moves the angle by at most `(2/k)(1 + 10⁻⁶) √(δ/2)`. -/
theorem arccos_holder {x y δ A k : ℝ} (hx1 : x ≤ 1) (hy1 : y ≤ 1) (hxA : Real.arccos x ≤ 2 * A)
    (hyA : Real.arccos y ≤ 2 * A) (hA : A ≤ 1 / 2) (hk : 9 / 10 ≤ k) (hkA : k ≤ Real.cos A)
    (hxy : |x - y| ≤ δ) (hδ : δ ≤ 1 / 10 ^ 5) :
    |Real.arccos x - Real.arccos y| ≤ 2 / k * (1 + 1 / 10 ^ 6) * Real.sqrt (δ / 2) := by
  have hx0 := neg_one_le_of_arccos (x := x) (by linarith)
  have hy0 := neg_one_le_of_arccos (x := y) (by linarith)
  have ax := Real.arccos_nonneg x
  have ay := Real.arccos_nonneg y
  set α := Real.arccos x / 2 with hα
  set β := Real.arccos y / 2 with hβ
  have hsa : Real.sin α = Real.sqrt ((1 - x) / 2) := by
    rw [hα, Real.sin_half_eq_sqrt ax (by linarith [Real.pi_gt_three]), Real.cos_arccos hx0 hx1]
  have hsb : Real.sin β = Real.sqrt ((1 - y) / 2) := by
    rw [hβ, Real.sin_half_eq_sqrt ay (by linarith [Real.pi_gt_three]), Real.cos_arccos hy0 hy1]
  have hs : |Real.sin α - Real.sin β| ≤ Real.sqrt (δ / 2) := by
    rw [hsa, hsb]; exact TiltReal.sin_half_holder hxy
  rw [Real.sin_sub_sin] at hs
  have hc : k ≤ Real.cos ((α + β) / 2) := by
    refine hkA.trans (Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by linarith [Real.pi_gt_three]) (by linarith))
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hxy
  have hsq : Real.sqrt (δ / 2) ≤ 2237 / 10 ^ 6 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  set t := (α - β) / 2 with ht
  have htA : |t| ≤ 1 / 4 := by rw [abs_le]; constructor <;> linarith
  -- `2 k |sin t| ≤ √(δ/2)`
  have h1 : 2 * k * |Real.sin t| ≤ Real.sqrt (δ / 2) := by
    rw [abs_mul, abs_mul, abs_two, abs_of_pos (by linarith : 0 < Real.cos ((α + β) / 2))] at hs
    nlinarith [abs_nonneg (Real.sin t)]
  -- `|sin t| ≥ |t| - |t|³/6`
  have h2 : |t| - |t| ^ 3 / 6 ≤ |Real.sin t| := by
    rcases lt_trichotomy t 0 with h | h | h
    · have := Real.sin_gt_sub_cube (x := -t) (by linarith)
      rw [Real.sin_neg] at this
      have hneg : Real.sin t < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt h (by linarith [Real.pi_gt_three, (abs_le.1 htA).1])
      rw [abs_of_neg h, abs_of_neg hneg]
      nlinarith
    · simp [h]
    · have := Real.sin_gt_sub_cube (x := t) h
      have hpos : 0 < Real.sin t :=
        Real.sin_pos_of_pos_of_lt_pi h (by linarith [Real.pi_gt_three, (abs_le.1 htA).2])
      rw [abs_of_pos h, abs_of_pos hpos]
      linarith
  set τ := |t|
  have hτ0 : 0 ≤ τ := abs_nonneg t
  have hτq : τ ≤ 1 / 4 := htA
  have hm : 2 * k * (τ - τ ^ 3 / 6) ≤ Real.sqrt (δ / 2) := by nlinarith
  have hk0 : 0 ≤ k := by linarith
  have hτ3 : τ ^ 3 ≤ τ / 16 := by nlinarith [mul_nonneg hτ0 hτ0]
  have hm2 : 2 * k * (τ * (95 / 96)) ≤ Real.sqrt (δ / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hτ3 hk0]
  have hτ1 : τ ≤ 2 / 10 ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hk hτ0]
  have hτ4 : τ ^ 3 ≤ τ * (4 / 10 ^ 6) := by nlinarith [mul_nonneg hτ0 hτ0]
  have hτ2 : 4 * τ * k * (1 - 67 / 10 ^ 8) ≤ 2 * Real.sqrt (δ / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hτ4 hk0]
  have hfin : 4 * τ ≤ 2 / k * (1 + 1 / 10 ^ 6) * Real.sqrt (δ / 2) := by
    have hkp : 0 < k := by linarith
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hkp]
    have hs0 := Real.sqrt_nonneg (δ / 2)
    have e1 : 4 * τ * k ≤ 2 * Real.sqrt (δ / 2) / (1 - 67 / 10 ^ 8) := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    have e2 : 2 * Real.sqrt (δ / 2) / (1 - 67 / 10 ^ 8) ≤ 2 * (1 + 1 / 10 ^ 6) * Real.sqrt (δ / 2) := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    calc 4 * τ * k ≤ _ := e1
      _ ≤ _ := e2
  have : |Real.arccos x - Real.arccos y| = 4 * τ := by
    rw [show Real.arccos x - Real.arccos y = 4 * t by rw [ht, hα, hβ]; ring, abs_mul]; norm_num; rfl
  rw [this]; exact hfin

/-! ## The emitted function, unfolded -/

/-- The thrust direction `q * up` the code computes. -/
abbrev tbV (B : Quaternion.State) : Vector3f.State := Quaternion.op_mul_Vector3f B upV
abbrev errAngle (B T : Quaternion.State) : Float32 :=
  Float32.acos (constrain_value_line_float (Vector3f.op_mul_Vector3f (tbV B) (tbV T)) (-(1.0 : Float32))
    (1.0 : Float32) (Int32.toUInt32 (1076 : Int32)))
abbrev errCross (B T : Quaternion.State) : Vector3f.State := Vector3f.op_mod (tbV B) (tbV T)
/-- The rotation axis (world frame) the code picks. -/
def errAxisW (B T : Quaternion.State) : Vector3f.State :=
  if is_zero_float (Vector3f.length (errCross B T)) || is_zero_float (errAngle B T) then upV
  else (Vector3f.op_div_assign (errCross B T) (Vector3f.length (errCross B T))).1
abbrev errCorr (B T c : Quaternion.State) : Quaternion.State :=
  Quaternion.from_axis_angle_Vector3f_float c (Quaternion.op_mul_Vector3f (Quaternion.inverse B) (errAxisW B T))
    (errAngle B T)

theorem tvra_x (T B c : Quaternion.State) (e : Vector3f.State) (a b : Float32) :
    (AC_AttitudeControl_Multi.thrust_vector_rotation_angles T B c e a b).2.1.x =
      (Quaternion.to_axis_angle (errCorr B T c) Vector3f.init_void).x := by
  unfold errCorr errAxisW
  cases h : (is_zero_float (Vector3f.length (errCross B T)) || is_zero_float (errAngle B T)) with
  | true =>
    simp only [AC_AttitudeControl_Multi.thrust_vector_rotation_angles, Id.run, ite_true]
    simp only [errCross, errAngle, tbV, upV] at h
    simp only [h, ite_true, id_pure_eq]; rfl
  | false =>
    simp only [AC_AttitudeControl_Multi.thrust_vector_rotation_angles, Id.run, Bool.false_eq_true, ite_false]
    simp only [errCross, errAngle, tbV, upV] at h
    simp only [h, Bool.false_eq_true, ite_false, id_pure_eq]; rfl

theorem tvra_y (T B c : Quaternion.State) (e : Vector3f.State) (a b : Float32) :
    (AC_AttitudeControl_Multi.thrust_vector_rotation_angles T B c e a b).2.1.y =
      (Quaternion.to_axis_angle (errCorr B T c) Vector3f.init_void).y := by
  unfold errCorr errAxisW
  cases h : (is_zero_float (Vector3f.length (errCross B T)) || is_zero_float (errAngle B T)) with
  | true =>
    simp only [AC_AttitudeControl_Multi.thrust_vector_rotation_angles, Id.run, ite_true]
    simp only [errCross, errAngle, tbV, upV] at h
    simp only [h, ite_true, id_pure_eq]; rfl
  | false =>
    simp only [AC_AttitudeControl_Multi.thrust_vector_rotation_angles, Id.run, Bool.false_eq_true, ite_false]
    simp only [errCross, errAngle, tbV, upV] at h
    simp only [h, Bool.false_eq_true, ite_false, id_pure_eq]; rfl

theorem tvra_ta (T B c : Quaternion.State) (e : Vector3f.State) (a b : Float32) :
    (AC_AttitudeControl_Multi.thrust_vector_rotation_angles T B c e a b).2.2.1 =
      Float32.acos (constrain_value_line_float (Vector3f.op_mul_Vector3f upV (tbV B)) (-(1.0 : Float32))
    (1.0 : Float32) (Int32.toUInt32 (1070 : Int32))) := by
  simp only [AC_AttitudeControl_Multi.thrust_vector_rotation_angles, Id.run]
  split_ifs <;> rfl
theorem tvra_tea (T B c : Quaternion.State) (e : Vector3f.State) (a b : Float32) :
    (AC_AttitudeControl_Multi.thrust_vector_rotation_angles T B c e a b).2.2.2 = errAngle B T := by
  simp only [AC_AttitudeControl_Multi.thrust_vector_rotation_angles, Id.run]
  split_ifs <;> rfl

/-! ## The region and the rotation of `up` -/

/-- A nearly-unit attitude whose thrust direction is within `30°` of vertical:
`q₂² + q₃² ≤ 0.067` (`1 - 2(q₂² + q₃²) ≥ cos 30°`), finite components, `|q|²` within `10⁻⁶` of `1`. -/
structure Level (q : Quaternion.State) : Prop where
  f1 : q.q1.IsFinite
  f2 : q.q2.IsFinite
  f3 : q.q3.IsFinite
  f4 : q.q4.IsFinite
  b1 : |q.q1.toReal| ≤ 1.01
  b4 : |q.q4.toReal| ≤ 1.01
  tilt : q.q2.toReal ^ 2 + q.q3.toReal ^ 2 ≤ 67 / 1000
  unit : |RQ.norm2 (qv q) - 1| ≤ 1 / 10 ^ 6

theorem Level.b2 {q : Quaternion.State} (h : Level q) : |q.q2.toReal| ≤ 0.26 := by
  have := h.tilt; rw [← sq_abs] at this
  nlinarith [sq_nonneg q.q3.toReal, abs_nonneg q.q2.toReal]

theorem Level.b3 {q : Quaternion.State} (h : Level q) : |q.q3.toReal| ≤ 0.26 := by
  have := h.tilt; rw [← sq_abs q.q3.toReal] at this
  nlinarith [sq_nonneg q.q2.toReal, abs_nonneg q.q3.toReal]

theorem Level.QB {q : Quaternion.State} (h : Level q) : QB q 1.01 :=
  ⟨⟨A32.of_exact h.f1, h.b1⟩, ⟨A32.of_exact h.f2, by linarith [h.b2]⟩,
   ⟨A32.of_exact h.f3, by linarith [h.b3]⟩, ⟨A32.of_exact h.f4, h.b4⟩⟩

set_option maxHeartbeats 800000 in
/-- **Rotation of `up`** by a level attitude: within `4.5·10⁻⁷` per component of `RQ.rot q up`. -/
theorem rot_up_near {q : Quaternion.State} (h : Level q) :
    VA (Quaternion.op_mul_Vector3f q upV) (RQ.rot (qv q) (vv upV)) (45 / 10 ^ 8) := by
  have q1 : B32 q.q1 q.q1.toReal 0 1.01 := ⟨A32.of_exact h.f1, h.b1⟩
  have q2 : B32 q.q2 q.q2.toReal 0 0.26 := ⟨A32.of_exact h.f2, h.b2⟩
  have q3 : B32 q.q3 q.q3.toReal 0 0.26 := ⟨A32.of_exact h.f3, h.b3⟩
  have q4 : B32 q.q4 q.q4.toReal 0 1.01 := ⟨A32.of_exact h.f4, h.b4⟩
  have v1 : B32 upV.x upV.x.toReal 0 0 :=
    ⟨A32.of_exact f32_isFinite_0p0, by rw [upx, f32_toReal_0p0]; norm_num⟩
  have v2 : B32 upV.y upV.y.toReal 0 0 :=
    ⟨A32.of_exact f32_isFinite_0p0, by rw [upy, f32_toReal_0p0]; norm_num⟩
  have v3 : B32 upV.z upV.z.toReal 0 1 :=
    ⟨A32.of_exact m1_fin, by rw [upz, m1_val]; norm_num⟩
  have c0 := bdbl (bsub (bmul q3 v3 (by norm_num)) (bmul q4 v2 (by norm_num)) (by norm_num))
    (by norm_num)
  have c1 := bdbl (bsub (bmul q4 v1 (by norm_num)) (bmul q2 v3 (by norm_num)) (by norm_num))
    (by norm_num)
  have c2 := bdbl (bsub (bmul q2 v2 (by norm_num)) (bmul q3 v1 (by norm_num)) (by norm_num))
    (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [rot_x, RQ.rot_x]
    exact (badd v1 (bsub (badd (bmul q1 c0 (by norm_num)) (bmul q3 c2 (by norm_num)) (by norm_num))
      (bmul q4 c1 (by norm_num)) (by norm_num)) (by norm_num)).1.mono (by norm_num)
  · rw [rot_y, RQ.rot_y]
    exact (badd v2 (bsub (badd (bmul q1 c1 (by norm_num)) (bmul q4 c0 (by norm_num)) (by norm_num))
      (bmul q2 c2 (by norm_num)) (by norm_num)) (by norm_num)).1.mono (by norm_num)
  · rw [rot_z, RQ.rot_z]
    exact (badd v3 (bsub (badd (bmul q1 c2 (by norm_num)) (bmul q2 c1 (by norm_num)) (by norm_num))
      (bmul q3 c0 (by norm_num)) (by norm_num)) (by norm_num)).1.mono (by norm_num)

/-! ## The real law -/

/-- `up = (0, 0, -1)`. -/
def upR : RV := ⟨0, 0, -1⟩

/-- The thrust direction of the normalized attitude: `q̂ up q̂*`. -/
def tbR (q : Quaternion.State) : RV := RQ.rot (RQ.normalize (qv q)) upR

theorem upR_norm : upR.norm = 1 := by simp [upR, RV.norm]

theorem Level.norm2_pos {q : Quaternion.State} (h : Level q) : 0 < RQ.norm2 (qv q) := by
  have := (abs_le.1 h.unit).1; linarith

theorem tbR_norm {q : Quaternion.State} (h : Level q) : (tbR q).norm = 1 := by
  rw [tbR, rot_norm_unit (normalize_unit h.norm2_pos), upR_norm]

theorem rot_up_eq (Q : RQ) : RQ.rot Q upR =
    ⟨-(2 * (Q.w * Q.y + Q.x * Q.z)), 2 * (Q.w * Q.x - Q.y * Q.z), -1 + 2 * (Q.x ^ 2 + Q.y ^ 2)⟩ := by
  simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec, upR]; congr 1 <;> ring

/-- The normalized attitude of a level one: `x̂² + ŷ² ≤ 0.0671`, `|q̂| = 1`. -/
theorem Level.hat {q : Quaternion.State} (h : Level q) :
    RQ.norm2 (RQ.normalize (qv q)) = 1 ∧
      (RQ.normalize (qv q)).x ^ 2 + (RQ.normalize (qv q)).y ^ 2 ≤ 671 / 10000 := by
  refine ⟨normalize_unit h.norm2_pos, ?_⟩
  have hn := h.norm2_pos
  have hs := Real.sq_sqrt hn.le
  have hp : 0 < Real.sqrt (RQ.norm2 (qv q)) := Real.sqrt_pos.2 hn
  simp only [RQ.normalize, div_pow, hs]
  rw [← add_div, div_le_iff₀ hn]
  have := (abs_le.1 h.unit).1; have := h.tilt
  simp only [qv] at *; nlinarith

/-- The unit thrust direction: components and `up · t̂ = 1 - 2(x̂² + ŷ²) ≥ 0.8658`. -/
theorem tbR_facts {q : Quaternion.State} (h : Level q) :
    |(tbR q).x| ≤ 1 ∧ |(tbR q).y| ≤ 1 ∧ |(tbR q).z| ≤ 1 ∧ 8658 / 10000 ≤ RV.dot upR (tbR q) := by
  have hn := tbR_norm h
  obtain ⟨hu, ht⟩ := h.hat
  refine ⟨hn ▸ abs_le_norm_x _, hn ▸ abs_le_norm_y _, hn ▸ abs_le_norm_z _, ?_⟩
  rw [tbR, rot_up_eq]; simp only [RV.dot, upR]; nlinarith

/-- `rot q up` against the normalized `rot q̂ up`: within `5.2·10⁻⁷` per component. -/
theorem tb_close {q : Quaternion.State} (h : Level q) :
    |(RQ.rot (qv q) upR).x - (tbR q).x| ≤ 52 / 10 ^ 8 ∧ |(RQ.rot (qv q) upR).y - (tbR q).y| ≤ 52 / 10 ^ 8 ∧
      |(RQ.rot (qv q) upR).z - (tbR q).z| ≤ 52 / 10 ^ 8 := by
  have e := rot_vs_normalize h.norm2_pos upR
  obtain ⟨hu, ht⟩ := h.hat
  set Q := RQ.normalize (qv q)
  have hν := h.unit
  have hw : Q.w ^ 2 + Q.z ^ 2 ≤ 1 := by simp only [RQ.norm2] at hu; nlinarith [sq_nonneg Q.x, sq_nonneg Q.y]
  have k1 : |Q.w * Q.y + Q.x * Q.z| ≤ 26 / 100 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Q.w * Q.x - Q.z * Q.y), sq_nonneg (Q.w * Q.y + Q.x * Q.z),
      sq_nonneg Q.w, sq_nonneg Q.z]
  have k2 : |Q.w * Q.x - Q.y * Q.z| ≤ 26 / 100 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Q.w * Q.y + Q.z * Q.x), sq_nonneg (Q.w * Q.x - Q.y * Q.z),
      sq_nonneg Q.w, sq_nonneg Q.z]
  have key : ∀ d r : ℝ, |d| ≤ 52 / 100 → (RQ.rot (qv q) upR).x - (tbR q).x = (RQ.norm2 (qv q) - 1) * d ∨ True →
      |(RQ.norm2 (qv q) - 1) * d| ≤ 52 / 10 ^ 8 := by
    intro d _ hd _
    rw [abs_mul]; calc |RQ.norm2 (qv q) - 1| * |d| ≤ 1 / 10 ^ 6 * (52 / 100) := by gcongr
      _ = 52 / 10 ^ 8 := by norm_num
  have ex : (RQ.rot (qv q) upR).x - (tbR q).x = (RQ.norm2 (qv q) - 1) * (-(2 * (Q.w * Q.y + Q.x * Q.z))) := by
    have h0 := congrArg RV.x e; simp only [RV.sub, RV.smul] at h0
    rw [tbR]; rw [rot_up_eq Q] at h0 ⊢; simp only [upR] at h0 ⊢; linarith
  have ey : (RQ.rot (qv q) upR).y - (tbR q).y = (RQ.norm2 (qv q) - 1) * (2 * (Q.w * Q.x - Q.y * Q.z)) := by
    have h0 := congrArg RV.y e; simp only [RV.sub, RV.smul] at h0
    rw [tbR]; rw [rot_up_eq Q] at h0 ⊢; simp only [upR] at h0 ⊢; linarith
  have ez : (RQ.rot (qv q) upR).z - (tbR q).z = (RQ.norm2 (qv q) - 1) * (2 * (Q.x ^ 2 + Q.y ^ 2)) := by
    have h0 := congrArg RV.z e; simp only [RV.sub, RV.smul] at h0
    rw [tbR]; rw [rot_up_eq Q] at h0 ⊢; simp only [upR] at h0 ⊢; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [ex]; exact key _ 0 (by rw [abs_neg, abs_mul, abs_two]; linarith) (Or.inr trivial)
  · rw [ey]; exact key _ 0 (by rw [abs_mul, abs_two]; linarith) (Or.inr trivial)
  · rw [ez]; exact key _ 0 (by rw [abs_mul, abs_two, abs_of_nonneg (by positivity)]; linarith) (Or.inr trivial)

/-- **The computed thrust direction** `q * up` of a level attitude: within `10⁻⁶` per component
of the unit `t̂ = q̂ up q̂*`. -/
theorem tb_near {q : Quaternion.State} (h : Level q) : VA (tbV q) (tbR q) (1 / 10 ^ 6) := by
  obtain ⟨a1, a2, a3⟩ := rot_up_near h
  obtain ⟨c1, c2, c3⟩ := tb_close h
  rw [vv_up] at a1 a2 a3
  exact ⟨(ashift a1 c1).mono (by norm_num), (ashift a2 c2).mono (by norm_num),
    (ashift a3 c3).mono (by norm_num)⟩

/-! ## The angles -/

theorem arccos_le_of_cos_le {x a : ℝ} (h0 : 0 ≤ a) (hπ : a ≤ Real.pi) (hx : Real.cos a ≤ x) :
    Real.arccos x ≤ a := by
  have := Real.arccos_le_arccos hx; rwa [Real.arccos_cos h0 hπ] at this

theorem cos_le_of_bound {x c : ℝ} (hx : |x| ≤ 1) (h : 1 - x ^ 2 / 2 + |x| ^ 4 * (5 / 96) ≤ c) :
    Real.cos x ≤ c := by
  have := Real.cos_bound hx; have := (abs_le.1 this).2; linarith

theorem cos054 : Real.cos (54 / 100) ≤ 86 / 100 :=
  cos_le_of_bound (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
theorem cos038 : Real.cos (38 / 100) ≤ 93 / 100 :=
  cos_le_of_bound (by norm_num [abs_of_pos]) (by norm_num [abs_of_pos])
theorem cos027 : (96 / 100 : ℝ) ≤ Real.cos (27 / 100) := by
  have := @Real.one_sub_sq_div_two_le_cos (27 / 100); norm_num at this ⊢; linarith
theorem cos019 : (98 / 100 : ℝ) ≤ Real.cos (19 / 100) := by
  have := @Real.one_sub_sq_div_two_le_cos (19 / 100); norm_num at this ⊢; linarith

theorem sqrt_le_num {x b : ℝ} (hb : 0 ≤ b) (h : x ≤ b ^ 2) : Real.sqrt x ≤ b := by
  rw [Real.sqrt_le_left hb]; exact h

set_option maxHeartbeats 800000 in
/-- **The thrust angle** `acosf(up · (body * up))` of a level body attitude: within `1.5·10⁻³` of
the real `arccos(up · t̂_b)`. -/
theorem thrust_angle_near (hL : LibmSpec) {T B c : Quaternion.State} {e : Vector3f.State}
    {a b : Float32} (hB : Level B) :
    A32 (AC_AttitudeControl_Multi.thrust_vector_rotation_angles T B c e a b).2.2.1
      (Real.arccos (RV.dot upR (tbR B))) (15 / 10 ^ 4) := by
  rw [tvra_ta]
  obtain ⟨t1, t2, t3⟩ := tb_near hB
  obtain ⟨fd, vd⟩ := up_dot t1.1 t2.1 t3.1
  obtain ⟨-, -, hz1, hc0⟩ := tbR_facts hB
  have hc : RV.dot upR (tbR B) = -(tbR B).z := by simp [RV.dot, upR]
  have hc1 : RV.dot upR (tbR B) ≤ 1 := by rw [hc]; linarith [neg_abs_le (tbR B).z]
  have hd : |(Vector3f.op_mul_Vector3f upV (tbV B)).toReal - RV.dot upR (tbR B)| ≤ 1 / 10 ^ 6 := by
    rw [vd, hc, show -(tbV B).z.toReal - -(tbR B).z = -((tbV B).z.toReal - (tbR B).z) by ring, abs_neg]
    exact t3.2
  have hlh : (-(1.0 : Float32)).toReal ≤ (1.0 : Float32).toReal := by
    rw [m1_val, f32_toReal_1p0]; norm_num
  obtain ⟨fc, vc⟩ := Att.constrain_spec (Int32.toUInt32 (1070 : Int32)) fd m1_fin f32_isFinite_1p0 hlh
  rw [m1_val, f32_toReal_1p0] at vc
  have hdlo := (abs_le.1 hd).1
  have hcf : |(constrain_value_line_float (Vector3f.op_mul_Vector3f upV (tbV B)) (-(1.0 : Float32))
      (1.0 : Float32) (Int32.toUInt32 (1070 : Int32))).toReal - RV.dot upR (tbR B)| ≤ 1 / 10 ^ 6 := by
    rw [vc]; exact clamp_near hc1 hd (by linarith)
  set cf := (constrain_value_line_float (Vector3f.op_mul_Vector3f upV (tbV B)) (-(1.0 : Float32))
      (1.0 : Float32) (Int32.toUInt32 (1070 : Int32)))
  have hcf1 : cf.toReal ≤ 1 := by rw [vc]; exact max_le (by norm_num) (min_le_left _ _)
  have hcf0 : -1 ≤ cf.toReal := by rw [vc]; exact le_max_left _ _
  obtain ⟨fa, ea⟩ := hL.acosf _ fc (abs_le.2 ⟨hcf0, hcf1⟩)
  rw [libm32Err_eq] at ea
  have hcflo := (abs_le.1 hcf).1
  have h1 : Real.arccos cf.toReal ≤ 2 * (27 / 100) :=
    arccos_le_of_cos_le (by norm_num) (by linarith [Real.pi_gt_three]) (by linarith [cos054])
  have h2 : Real.arccos (RV.dot upR (tbR B)) ≤ 2 * (27 / 100) :=
    arccos_le_of_cos_le (by norm_num) (by linarith [Real.pi_gt_three]) (by linarith [cos054])
  have hH := arccos_holder hcf1 hc1 h1 h2 (by norm_num) (by norm_num) cos027 hcf (by norm_num)
  have hs : Real.sqrt (1 / 10 ^ 6 / 2) ≤ 7072 / 10 ^ 7 := sqrt_le_num (by norm_num) (by norm_num)
  refine ⟨fa, ?_⟩
  have := abs_sub_le (Float32.acos cf).toReal (Real.arccos cf.toReal) (Real.arccos (RV.dot upR (tbR B)))
  have : 2 / (96 / 100) * (1 + 1 / 10 ^ 6) * Real.sqrt (1 / 10 ^ 6 / 2) ≤
      2 / (96 / 100) * (1 + 1 / 10 ^ 6) * (7072 / 10 ^ 7) := by gcongr
  norm_num at ea this ⊢; linarith

theorem dot_abs_le (a b : RV) : |RV.dot a b| ≤ a.norm * b.norm := by
  rw [abs_le]; constructor
  · have := RV.dot_le_norm (RV.smul (-1) a) b
    rw [RV.norm_smul] at this; simp only [RV.dot, RV.smul] at this ⊢; norm_num at this; linarith
  · exact RV.dot_le_norm a b

/-- The dot product of two perturbed unit vectors (errors `ε` per component). -/
theorem dot_lip {a A b B : RV} {ε : ℝ} (hA : A.norm = 1) (hB : B.norm = 1)
    (ha : |a.x - A.x| ≤ ε ∧ |a.y - A.y| ≤ ε ∧ |a.z - A.z| ≤ ε)
    (hb : |b.x - B.x| ≤ ε ∧ |b.y - B.y| ≤ ε ∧ |b.z - B.z| ≤ ε) :
    |RV.dot a b - RV.dot A B| ≤ 2 * (17321 / 10000 * ε) + (17321 / 10000 * ε) ^ 2 := by
  have hda := RV.norm_le_of_comp (a := RV.sub a A) ha.1 ha.2.1 ha.2.2
  have hdb := RV.norm_le_of_comp (a := RV.sub b B) hb.1 hb.2.1 hb.2.2
  have e : RV.dot a b - RV.dot A B = RV.dot (RV.sub a A) b + RV.dot A (RV.sub b B) := by
    simp only [RV.dot, RV.sub]; ring
  have hbn : b.norm ≤ 1 + 17321 / 10000 * ε := by
    have := RV.norm_sub_tri b B ⟨0, 0, 0⟩
    have e1 : RV.sub b ⟨0, 0, 0⟩ = b := by simp only [RV.sub, sub_zero]
    have e2 : RV.sub B ⟨0, 0, 0⟩ = B := by simp only [RV.sub, sub_zero]
    rw [e1, e2, hB] at this; linarith
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have t1 := dot_abs_le (RV.sub a A) b
  have t2 := dot_abs_le A (RV.sub b B)
  rw [hA, one_mul] at t2
  have := RV.norm_nonneg (RV.sub a A)
  have : (RV.sub a A).norm * b.norm ≤ 17321 / 10000 * ε * (1 + 17321 / 10000 * ε) :=
    mul_le_mul hda hbn (RV.norm_nonneg _) (by linarith)
  nlinarith

theorem va_toVB {v : Vector3f.State} {r : RV} {e : ℝ} (h : VA v r e) (hr : |r.x| ≤ 1 ∧ |r.y| ≤ 1 ∧ |r.z| ≤ 1)
    (he : e ≤ 1 / 100) : VB v 1.01 :=
  ⟨⟨A32.of_exact h.1.1, by have := h.1.abs_le; linarith [hr.1]⟩,
   ⟨A32.of_exact h.2.1.1, by have := h.2.1.abs_le; linarith [hr.2.1]⟩,
   ⟨A32.of_exact h.2.2.1, by have := h.2.2.abs_le; linarith [hr.2.2]⟩⟩

theorem tbV_VB {q : Quaternion.State} (h : Level q) : VB (tbV q) 1.01 := by
  obtain ⟨h1, h2, h3, -⟩ := tbR_facts h
  exact va_toVB (tb_near h) ⟨h1, h2, h3⟩ (by norm_num)

/-- The dot product of the two computed thrust directions: within `4·10⁻⁶` of `t̂_b · t̂_t`. -/
theorem dot_tb_near {B T : Quaternion.State} (hB : Level B) (hT : Level T) :
    A32 (Vector3f.op_mul_Vector3f (tbV B) (tbV T)) (RV.dot (tbR B) (tbR T)) (4 / 10 ^ 6) := by
  have h1 := dot_near (tbV_VB hB) (tbV_VB hT)
  obtain ⟨a1, a2, a3⟩ := tb_near hB
  obtain ⟨b1, b2, b3⟩ := tb_near hT
  have h2 := dot_lip (a := vv (tbV B)) (b := vv (tbV T)) (tbR_norm hB) (tbR_norm hT)
    ⟨a1.2, a2.2, a3.2⟩ ⟨b1.2, b2.2, b3.2⟩
  exact (ashift h1 h2).mono (by norm_num)

set_option maxHeartbeats 800000 in
/-- **The thrust error angle** `acosf(t_b · t_t)` for level attitudes with thrust directions within
`20°` (`t̂_b · t̂_t ≥ 0.94`): within `2.9·10⁻³` of `arccos(t̂_b · t̂_t)`. -/
theorem thrust_error_angle_near (hL : LibmSpec) {T B c : Quaternion.State} {e : Vector3f.State}
    {a b : Float32} (hB : Level B) (hT : Level T) (hc : 94 / 100 ≤ RV.dot (tbR B) (tbR T)) :
    (errAngle B T).IsFinite ∧
    A32 (AC_AttitudeControl_Multi.thrust_vector_rotation_angles T B c e a b).2.2.2
      (Real.arccos (RV.dot (tbR B) (tbR T))) (29 / 10 ^ 4) ∧
    |(errAngle B T).toReal - Real.arccos (RV.dot (tbR B) (tbR T))| ≤ 29 / 10 ^ 4 := by
  rw [tvra_tea]
  have hd := dot_tb_near hB hT
  have hc1 : RV.dot (tbR B) (tbR T) ≤ 1 := by
    have := dot_abs_le (tbR B) (tbR T); rw [tbR_norm hB, tbR_norm hT] at this
    linarith [le_abs_self (RV.dot (tbR B) (tbR T))]
  have hlh : (-(1.0 : Float32)).toReal ≤ (1.0 : Float32).toReal := by
    rw [m1_val, f32_toReal_1p0]; norm_num
  obtain ⟨fc, vc⟩ := Att.constrain_spec (Int32.toUInt32 (1076 : Int32)) hd.1 m1_fin f32_isFinite_1p0 hlh
  rw [m1_val, f32_toReal_1p0] at vc
  have hdlo := (abs_le.1 hd.2).1
  have hcf : |(constrain_value_line_float (Vector3f.op_mul_Vector3f (tbV B) (tbV T)) (-(1.0 : Float32))
      (1.0 : Float32) (Int32.toUInt32 (1076 : Int32))).toReal - RV.dot (tbR B) (tbR T)| ≤ 4 / 10 ^ 6 := by
    rw [vc]; exact clamp_near hc1 hd.2 (by linarith)
  set cf := (constrain_value_line_float (Vector3f.op_mul_Vector3f (tbV B) (tbV T)) (-(1.0 : Float32))
      (1.0 : Float32) (Int32.toUInt32 (1076 : Int32)))
  have hcf1 : cf.toReal ≤ 1 := by rw [vc]; exact max_le (by norm_num) (min_le_left _ _)
  have hcf0 : -1 ≤ cf.toReal := by rw [vc]; exact le_max_left _ _
  obtain ⟨fa, ea⟩ := hL.acosf _ fc (abs_le.2 ⟨hcf0, hcf1⟩)
  rw [libm32Err_eq] at ea
  have hcflo := (abs_le.1 hcf).1
  have h1 : Real.arccos cf.toReal ≤ 2 * (19 / 100) :=
    arccos_le_of_cos_le (by norm_num) (by linarith [Real.pi_gt_three]) (by linarith [cos038])
  have h2 : Real.arccos (RV.dot (tbR B) (tbR T)) ≤ 2 * (19 / 100) :=
    arccos_le_of_cos_le (by norm_num) (by linarith [Real.pi_gt_three]) (by linarith [cos038])
  have hH := arccos_holder hcf1 hc1 h1 h2 (by norm_num) (by norm_num) cos019 hcf (by norm_num)
  have hs : Real.sqrt (4 / 10 ^ 6 / 2) ≤ 14143 / 10 ^ 7 := sqrt_le_num (by norm_num) (by norm_num)
  have := abs_sub_le (Float32.acos cf).toReal (Real.arccos cf.toReal) (Real.arccos (RV.dot (tbR B) (tbR T)))
  have : 2 / (98 / 100) * (1 + 1 / 10 ^ 6) * Real.sqrt (4 / 10 ^ 6 / 2) ≤
      2 / (98 / 100) * (1 + 1 / 10 ^ 6) * (14143 / 10 ^ 7) := by gcongr
  have fin : |(Float32.acos cf).toReal - Real.arccos (RV.dot (tbR B) (tbR T))| ≤ 29 / 10 ^ 4 := by
    norm_num at ea this ⊢; linarith
  exact ⟨fa, ⟨fa, fin⟩, fin⟩

/-! ## The rotation vector: real lemmas -/

theorem rot_smul (q : RQ) (k : ℝ) (v : RV) : RQ.rot q (RV.smul k v) = RV.smul k (RQ.rot q v) := by
  simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec]; congr 1 <;> ring

theorem RV.sub_zero' (a : RV) : RV.sub a ⟨0, 0, 0⟩ = a := by simp only [RV.sub, sub_zero]

theorem RV.norm_sub_comm (a b : RV) : (RV.sub a b).norm = (RV.sub b a).norm := by
  simp only [RV.norm, RV.sub]; congr 1; ring

theorem RV.norm_le_add (a b : RV) : a.norm ≤ b.norm + (RV.sub a b).norm := by
  have := RV.norm_sub_tri a b ⟨0, 0, 0⟩
  rw [RV.sub_zero', RV.sub_zero'] at this; linarith

/-- `θ ≤ 1.025 sin θ` and `θ ≤ 0.38` for `θ = arccos c`, `c ≥ 0.93`. -/
theorem theta_le {c : ℝ} (hc : 93 / 100 ≤ c) :
    Real.arccos c ≤ 38 / 100 ∧ Real.arccos c ≤ 1025 / 1000 * Real.sqrt (1 - c ^ 2) := by
  have h1 : Real.arccos c ≤ 38 / 100 :=
    arccos_le_of_cos_le (by norm_num) (by linarith [Real.pi_gt_three]) (by linarith [cos038])
  refine ⟨h1, ?_⟩
  have h0 := Real.arccos_nonneg c
  rw [← Real.sin_arccos]
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; simp
  · have := Real.sin_gt_sub_cube h
    have : Real.arccos c ^ 3 ≤ Real.arccos c * (38 / 100) ^ 2 := by
      have : Real.arccos c ^ 2 ≤ (38 / 100) ^ 2 := by gcongr
      nlinarith
    nlinarith

/-- The final vector estimate: `‖(φ/|a|) a - θ e‖ ≤ |φ - θ| + 2θ‖a - e‖` for a unit `e`. -/
theorem final_vec {a e : RV} {φ θ : ℝ} (he : e.norm = 1) (hθ : 0 ≤ θ) :
    (RV.sub (RV.smul (φ / a.norm) a) (RV.smul θ e)).norm ≤ |φ - θ| + 2 * θ * (RV.sub a e).norm := by
  have hd := RV.dir_le (x := a) (y := e) (by rw [he]; norm_num)
  have ee : RV.smul (1 / e.norm) e = e := by rw [he]; simp [RV.smul]
  rw [ee, he, div_one] at hd
  have hu : (RV.smul (1 / a.norm) a).norm ≤ 1 := by
    rw [RV.norm_smul]
    rcases eq_or_lt_of_le (RV.norm_nonneg a) with h | h
    · rw [← h]; simp
    · rw [abs_of_pos (by positivity), one_div_mul_cancel h.ne']
  have e1 : RV.sub (RV.smul (φ / a.norm) a) (RV.smul θ e) =
      RV.add (RV.smul (φ - θ) (RV.smul (1 / a.norm) a)) (RV.smul θ (RV.sub (RV.smul (1 / a.norm) a) e)) := by
    simp only [RV.sub, RV.smul, RV.add]; congr 1 <;> ring
  rw [e1]
  refine (RV.norm_add_le _ _).trans ?_
  generalize RV.smul (1 / a.norm) a = u at hu hd ⊢
  rw [RV.norm_smul, RV.norm_smul, abs_of_nonneg hθ]
  have : |φ - θ| * u.norm ≤ |φ - θ| * 1 := by gcongr
  have : θ * (RV.sub u e).norm ≤ θ * (2 * (RV.sub a e).norm) := by gcongr
  linarith

/-- The cross product of two perturbed unit vectors (errors `ε ≤ 10⁻⁶` per component). -/
theorem cross_lip {a A b B : RV} {ε : ℝ} (hε : ε ≤ 1 / 10 ^ 6)
    (hA : |A.x| ≤ 1 ∧ |A.y| ≤ 1 ∧ |A.z| ≤ 1) (hB : |B.x| ≤ 1 ∧ |B.y| ≤ 1 ∧ |B.z| ≤ 1)
    (ha : |a.x - A.x| ≤ ε ∧ |a.y - A.y| ≤ ε ∧ |a.z - A.z| ≤ ε)
    (hb : |b.x - B.x| ≤ ε ∧ |b.y - B.y| ≤ ε ∧ |b.z - B.z| ≤ ε) :
    |(RV.cross a b).x - (RV.cross A B).x| ≤ 41 / 10 ^ 7 ∧ |(RV.cross a b).y - (RV.cross A B).y| ≤ 41 / 10 ^ 7 ∧
      |(RV.cross a b).z - (RV.cross A B).z| ≤ 41 / 10 ^ 7 := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans ha.1
  have key : ∀ p P q Q r R t T : ℝ, |P| ≤ 1 → |Q| ≤ 1 → |R| ≤ 1 → |T| ≤ 1 → |p - P| ≤ ε → |q - Q| ≤ ε →
      |r - R| ≤ ε → |t - T| ≤ ε → |(p * q - r * t) - (P * Q - R * T)| ≤ 41 / 10 ^ 7 := by
    intro p P q Q r R t T hP hQ hR hT hp hq hr ht
    have e : (p * q - r * t) - (P * Q - R * T) = (p - P) * q + P * (q - Q) - ((r - R) * t + R * (t - T)) := by ring
    have hq' : |q| ≤ 1 + ε := by have := abs_sub_abs_le_abs_sub q Q; linarith
    have ht' : |t| ≤ 1 + ε := by have := abs_sub_abs_le_abs_sub t T; linarith
    rw [e]
    have t1 : |(p - P) * q| ≤ ε * (1 + ε) := by rw [abs_mul]; exact mul_le_mul hp hq' (abs_nonneg _) hε0
    have t2 : |P * (q - Q)| ≤ 1 * ε := by rw [abs_mul]; exact mul_le_mul hP hq (abs_nonneg _) zero_le_one
    have t3 : |(r - R) * t| ≤ ε * (1 + ε) := by rw [abs_mul]; exact mul_le_mul hr ht' (abs_nonneg _) hε0
    have t4 : |R * (t - T)| ≤ 1 * ε := by rw [abs_mul]; exact mul_le_mul hR ht (abs_nonneg _) zero_le_one
    have := abs_sub ((p - P) * q + P * (q - Q)) ((r - R) * t + R * (t - T))
    have := abs_add_le ((p - P) * q) (P * (q - Q))
    have := abs_add_le ((r - R) * t) (R * (t - T))
    nlinarith
  exact ⟨key _ _ _ _ _ _ _ _ hA.2.1 hB.2.2 hA.2.2 hB.2.1 ha.2.1 hb.2.2 ha.2.2 hb.2.1,
    key _ _ _ _ _ _ _ _ hA.2.2 hB.1 hA.1 hB.2.2 ha.2.2 hb.1 ha.1 hb.2.2,
    key _ _ _ _ _ _ _ _ hA.1 hB.2.1 hA.2.1 hB.1 ha.1 hb.2.1 ha.2.1 hb.1⟩

/-! ## Helpers for the attitude error -/

/-- `to_axis_angle` for an angle of either sign (`(cos(φ/2), a sin(φ/2))` is also the quaternion
of `(-a, -φ)`). -/
theorem toAxisAngle_signed (hL : LibmSpec) (s : Quaternion.State) (v : Vector3f.State) {a : RV}
    {φ δ : ℝ} (hq : QA s (RQ.ofAxisAngle a φ) (13 / 10 ^ 8)) (ha : |a.norm ^ 2 - 1| ≤ δ)
    (hδ : δ ≤ 1 / 10 ^ 4) (hφ : |φ| ≤ 1 / 2) :
    VA (Quaternion.to_axis_angle s v) (RV.smul (φ / a.norm) a) (35 / 10 ^ 7 + 26 / 100 * δ) := by
  rw [norm_sq] at ha
  rcases le_total 0 φ with h | h
  · exact toAxisAngle_near_gen hL s v hq ha hδ h (abs_le.1 hφ).2
  · have e1 : RQ.ofAxisAngle a φ = RQ.ofAxisAngle (RV.smul (-1) a) (-φ) := by
      simp only [RQ.ofAxisAngle, RV.smul, neg_div, Real.cos_neg, Real.sin_neg]; congr 1 <;> ring
    have hn : (RV.smul (-1) a).norm = a.norm := by rw [RV.norm_smul]; simp
    have e2 : RV.smul (φ / a.norm) a = RV.smul (-φ / (RV.smul (-1) a).norm) (RV.smul (-1) a) := by
      rw [hn]; simp only [RV.smul]; congr 1 <;> ring
    rw [e1] at hq; rw [e2]
    refine toAxisAngle_near_gen hL s v hq ?_ hδ (by linarith) (by linarith [(abs_le.1 hφ).1])
    simp only [RV.smul]; convert ha using 2; ring

/-- From per-component closeness to `u` and `‖u - r‖ ≤ e₂`: the `x`, `y` components of `r`. -/
theorem combine_xy {out : Vector3f.State} {u r : RV} {e1 e2 : ℝ} (h1 : VA out u e1)
    (h2 : (RV.sub u r).norm ≤ e2) : A32 out.x r.x (e1 + e2) ∧ A32 out.y r.y (e1 + e2) :=
  ⟨ashift h1.1 ((abs_le_norm_x (RV.sub u r)).trans h2),
   ashift h1.2.1 ((abs_le_norm_y (RV.sub u r)).trans h2)⟩

theorem RV.norm_sub_le_add (a b : RV) : (RV.sub a b).norm ≤ a.norm + b.norm := by
  have := RV.norm_sub_tri a ⟨0, 0, 0⟩ b
  rw [RV.sub_zero', RV.norm_sub_comm ⟨0, 0, 0⟩ b, RV.sub_zero'] at this; exact this

theorem conjB_unit {B : Quaternion.State} (hB : Level B) :
    RQ.norm2 (RQ.conj (RQ.normalize (qv B))) = 1 := by
  rw [norm2_conj]; exact normalize_unit hB.norm2_pos

set_option maxHeartbeats 1000000 in
/-- The body-frame axis: `B⁻¹ * w` (float) against `B̂* w B̂`, within `1.3·10⁻⁵` (Euclidean). -/
theorem axB_close {B : Quaternion.State} (hB : Level B) {w : Vector3f.State} (hw : VB w 1.01)
    (hwn : (vv w).norm ≤ 10001 / 10000) :
    (RV.sub (vv (Quaternion.op_mul_Vector3f (Quaternion.inverse B) w))
      (RQ.rot (RQ.conj (RQ.normalize (qv B))) (vv w))).norm ≤ 13 / 10 ^ 6 ∧
    VB (Quaternion.op_mul_Vector3f (Quaternion.inverse B) w) 1.01 := by
  have hq := (quat_inverse_eq hB.QB).2
  have hr := rot_near hq hw
  rw [qv_inverse] at hr
  set X := Quaternion.op_mul_Vector3f (Quaternion.inverse B) w
  set P := RQ.conj (qv B)
  set r1 := RQ.rot P (vv w)
  set r2 := RQ.rot (RQ.conj (RQ.normalize (qv B))) (vv w)
  have d1 : (RV.sub (vv X) r1).norm ≤ 17321 / 10000 * (6 / 10 ^ 6) :=
    RV.norm_le_of_comp hr.1.2 hr.2.1.2 hr.2.2.2
  have hP : 0 < RQ.norm2 P := by rw [norm2_conj]; exact hB.norm2_pos
  have e := rot_vs_normalize hP (vv w)
  rw [← conj_normalize] at e
  have hr2 : r2.norm = (vv w).norm := rot_norm_unit (conjB_unit hB) _
  have d2 : (RV.sub r1 r2).norm ≤ 1 / 10 ^ 6 * (2 * (10001 / 10000)) := by
    rw [e, RV.norm_smul]
    have h3 := RV.norm_sub_le_add r2 (vv w)
    rw [hr2] at h3
    have hn : |RQ.norm2 P - 1| ≤ 1 / 10 ^ 6 := by rw [norm2_conj]; exact hB.unit
    exact mul_le_mul hn (by linarith) (RV.norm_nonneg _) (by norm_num)
  have d := RV.norm_sub_tri (vv X) r1 r2
  refine ⟨by linarith, ?_⟩
  -- bounds of the components
  have hr1 : r1.norm ≤ 10001 / 10000 + 1 / 10 ^ 6 * (2 * (10001 / 10000)) := by
    have := RV.norm_le_add r1 r2; rw [RV.norm_sub_comm] at this
    have := RV.norm_sub_comm r1 r2; linarith
  have c1 := abs_le_norm_x r1; have c2 := abs_le_norm_y r1; have c3 := abs_le_norm_z r1
  refine ⟨⟨A32.of_exact hr.1.1, ?_⟩, ⟨A32.of_exact hr.2.1.1, ?_⟩, ⟨A32.of_exact hr.2.2.1, ?_⟩⟩
  · have := hr.1.abs_le; norm_num at this hr1 ⊢; linarith
  · have := hr.2.1.abs_le; norm_num at this hr1 ⊢; linarith
  · have := hr.2.2.abs_le; norm_num at this hr1 ⊢; linarith

/-- The computed cross product `t_b × t_t`: within `4.4·10⁻⁶` per component of `t̂_b × t̂_t`. -/
theorem crf_near {B T : Quaternion.State} (hB : Level B) (hT : Level T) :
    VA (errCross B T) (RV.cross (tbR B) (tbR T)) (44 / 10 ^ 7) := by
  have h1 := cross_near (tbV_VB hB) (tbV_VB hT)
  obtain ⟨a1, a2, a3⟩ := tb_near hB
  obtain ⟨b1, b2, b3⟩ := tb_near hT
  obtain ⟨x1, x2, x3, -⟩ := tbR_facts hB
  obtain ⟨y1, y2, y3, -⟩ := tbR_facts hT
  obtain ⟨l1, l2, l3⟩ := cross_lip (a := vv (tbV B)) (b := vv (tbV T)) le_rfl ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩
    ⟨a1.2, a2.2, a3.2⟩ ⟨b1.2, b2.2, b3.2⟩
  exact ⟨(ashift h1.1 l1).mono (by norm_num), (ashift h1.2.1 l2).mono (by norm_num),
    (ashift h1.2.2 l3).mono (by norm_num)⟩

theorem errAxisW_up {B T : Quaternion.State}
    (h : is_zero_float (Vector3f.length (errCross B T)) = true ∨ is_zero_float (errAngle B T) = true) :
    errAxisW B T = upV := by
  unfold errAxisW; rcases h with h | h <;> simp [h]

theorem errAxisW_gen {B T : Quaternion.State}
    (h1 : is_zero_float (Vector3f.length (errCross B T)) = false) (h2 : is_zero_float (errAngle B T) = false) :
    errAxisW B T = (Vector3f.op_div_assign (errCross B T) (Vector3f.length (errCross B T))).1 := by
  unfold errAxisW; simp [h1, h2]

/-- **The real rotation vector of the thrust-vector correction, in the body frame**:
`arccos(t̂_b · t̂_t) · B̂* (t̂_b × t̂_t) B̂ / |t̂_b × t̂_t|` (`0` when the cross product is `0`). -/
def rotvecR (B T : Quaternion.State) : RV :=
  RV.smul (Real.arccos (RV.dot (tbR B) (tbR T)) / (RV.cross (tbR B) (tbR T)).norm)
    (RQ.rot (RQ.conj (RQ.normalize (qv B))) (RV.cross (tbR B) (tbR T)))

/-- The facts on the real law used by both branches. -/
theorem real_facts {B T : Quaternion.State} (hB : Level B) (hT : Level T)
    (hc : 94 / 100 ≤ RV.dot (tbR B) (tbR T)) :
    Real.arccos (RV.dot (tbR B) (tbR T)) ≤ 38 / 100 ∧
    Real.arccos (RV.dot (tbR B) (tbR T)) ≤ 1025 / 1000 * (RV.cross (tbR B) (tbR T)).norm ∧
    (RV.cross (tbR B) (tbR T)).norm ≤ 1 ∧
    (rotvecR B T).norm ≤ Real.arccos (RV.dot (tbR B) (tbR T)) ∧
    ((RV.cross (tbR B) (tbR T)).norm = 0 → Real.arccos (RV.dot (tbR B) (tbR T)) = 0) := by
  have hc1 : RV.dot (tbR B) (tbR T) ≤ 1 := by
    have := dot_abs_le (tbR B) (tbR T); rw [tbR_norm hB, tbR_norm hT] at this
    linarith [le_abs_self (RV.dot (tbR B) (tbR T))]
  obtain ⟨h38, hs⟩ := theta_le (c := RV.dot (tbR B) (tbR T)) (by linarith)
  have hl := lagrange (tbR B) (tbR T)
  rw [tbR_norm hB, tbR_norm hT] at hl
  have hsn : (RV.cross (tbR B) (tbR T)).norm = Real.sqrt (1 - RV.dot (tbR B) (tbR T) ^ 2) := by
    rw [← (Real.sqrt_sq (RV.norm_nonneg _)), hl]; ring_nf
  rw [← hsn] at hs
  have hθ0 := Real.arccos_nonneg (RV.dot (tbR B) (tbR T))
  have hs1 : (RV.cross (tbR B) (tbR T)).norm ≤ 1 := by
    rw [hsn, Real.sqrt_le_one]; nlinarith
  refine ⟨h38, hs, hs1, ?_, ?_⟩
  · rw [rotvecR, RV.norm_smul, rot_norm_unit (conjB_unit hB)]
    rcases eq_or_lt_of_le (RV.norm_nonneg (RV.cross (tbR B) (tbR T))) with h | h
    · rw [← h]; simp; exact hθ0
    · rw [abs_div, abs_of_nonneg hθ0, abs_of_pos h, div_mul_cancel₀ _ h.ne']
  · intro h0
    have : RV.dot (tbR B) (tbR T) ^ 2 = 1 := by rw [h0] at hl; linarith
    have : RV.dot (tbR B) (tbR T) = 1 := by nlinarith
    rw [this, Real.arccos_one]

theorem norm_smul_div_self (φ : ℝ) {A : RV} (h : 0 < A.norm) : (RV.smul (φ / A.norm) A).norm = |φ| := by
  rw [RV.norm_smul, abs_div, abs_of_pos h, div_mul_cancel₀ _ h.ne']

/-- `| |A|² - 1 | ≤ 3·10⁻⁵` from `| |A| - 1 | ≤ 1.4·10⁻⁵`. -/
theorem norm_sq_dev {A : RV} (h : |A.norm - 1| ≤ 14 / 10 ^ 6) : |A.norm ^ 2 - 1| ≤ 3 / 10 ^ 5 := by
  have := abs_le.1 h
  rw [abs_le]; constructor <;> nlinarith

set_option maxHeartbeats 4000000 in
/-- The generic branch (axis = normalized cross product). -/
theorem xy_gen (hL : LibmSpec) {T B c : Quaternion.State} (hB : Level B) (hT : Level T)
    (hc : 94 / 100 ≤ RV.dot (tbR B) (tbR T))
    (hz1 : is_zero_float (Vector3f.length (errCross B T)) = false)
    (hz2 : is_zero_float (errAngle B T) = false) :
    A32 (Quaternion.to_axis_angle (errCorr B T c) Vector3f.init_void).x (rotvecR B T).x (3 / 10 ^ 3) ∧
    A32 (Quaternion.to_axis_angle (errCorr B T c) Vector3f.init_void).y (rotvecR B T).y (3 / 10 ^ 3) := by
  obtain ⟨fθ, -, hθφ⟩ := thrust_error_angle_near hL (T := T) (B := B) (c := c) (e := Vector3f.init_void)
    (a := 0) (b := 0) hB hT hc
  obtain ⟨h38, hθs, hs1, hrv, hs0⟩ := real_facts hB hT hc
  have hcr := crf_near hB hT
  set crf := errCross B T with hcrf
  set cr := RV.cross (tbR B) (tbR T) with hcr_def
  set θ := Real.arccos (RV.dot (tbR B) (tbR T)) with hθdef
  set φ := (errAngle B T).toReal with hφdef
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hφ : |φ| ≤ 1 / 2 := by have := abs_sub_abs_le_abs_sub φ θ; rw [abs_of_nonneg hθ0] at this; linarith
  have hcrn : (RV.sub (vv crf) cr).norm ≤ 17321 / 10000 * (44 / 10 ^ 7) :=
    RV.norm_le_of_comp hcr.1.2 hcr.2.1.2 hcr.2.2.2
  have cx := abs_le_norm_x cr; have cy := abs_le_norm_y cr; have cz := abs_le_norm_z cr
  have bx : |crf.x.toReal| ≤ 1000 := by have := hcr.1.abs_le; linarith
  have by' : |crf.y.toReal| ≤ 1000 := by have := hcr.2.1.abs_le; linarith
  have bz : |crf.z.toReal| ≤ 1000 := by have := hcr.2.2.abs_le; linarith
  obtain ⟨fL, eL⟩ := len_near hcr.1.1 hcr.2.1.1 hcr.2.2.1 bx by' bz
  set L := Vector3f.length crf with hLdef
  set n := (vv crf).norm with hn
  have eL' := abs_le.1 eL
  have hL0 : 2 ^ (-23 : ℤ) ≤ |L.toReal| := by
    by_contra hc'; push Not at hc'
    rw [(Att.isZero_iff fL).2 hc'] at hz1; exact absurd hz1 (by decide)
  rw [two_pow_m23] at hL0
  have hLpos : 1 / 8388608 ≤ L.toReal := by
    rcases abs_cases L.toReal with ⟨h1, _⟩ | ⟨h1, _⟩
    · linarith
    · exfalso; norm_num at eL'; nlinarith [RV.norm_nonneg (vv crf)]
  have hr24 : 1 / 2 ^ 24 ≤ n := by norm_num at eL' ⊢; nlinarith
  have hrpos : 0 < n := lt_of_lt_of_le (by norm_num) hr24
  have key : ∀ x : Float32, x.IsFinite → |x.toReal| ≤ n →
      A32 (x / L) (x.toReal / n) (21 / 10 ^ 8) := by
    intro x hx hxn
    obtain ⟨f, e⟩ := ndiv hx fL hr24 eL hxn
    refine ⟨f, e.trans ?_⟩
    have : |x.toReal| / n ≤ 1 := by rw [div_le_one hrpos]; exact hxn
    have : 3503 / 1000 * (1 / 16777216) * (|x.toReal| / n) ≤ 3503 / 1000 * (1 / 16777216) * 1 := by
      gcongr
    norm_num at this ⊢; linarith
  have a1 := key _ hcr.1.1 (abs_le_norm_x (vv crf))
  have a2 := key _ hcr.2.1.1 (abs_le_norm_y (vv crf))
  have a3 := key _ hcr.2.2.1 (abs_le_norm_z (vv crf))
  set w := (Vector3f.op_div_assign crf L).1 with hw
  set U := RV.smul (1 / n) (vv crf) with hU
  have hUn : U.norm = 1 := by rw [hU, RV.norm_smul, abs_of_pos (by positivity), one_div_mul_cancel hrpos.ne']
  have hwU : (RV.sub (vv w) U).norm ≤ 17321 / 10000 * (21 / 10 ^ 8) := by
    refine RV.norm_le_of_comp ?_ ?_ ?_
    · have := a1.2; simp only [RV.sub, hU, RV.smul, vv] at this ⊢; rw [div_assign_x]
      rwa [show 1 / n * crf.x.toReal = crf.x.toReal / n by ring]
    · have := a2.2; simp only [RV.sub, hU, RV.smul, vv] at this ⊢; rw [div_assign_y]
      rwa [show 1 / n * crf.y.toReal = crf.y.toReal / n by ring]
    · have := a3.2; simp only [RV.sub, hU, RV.smul, vv] at this ⊢; rw [div_assign_z]
      rwa [show 1 / n * crf.z.toReal = crf.z.toReal / n by ring]
  have hwn2 : (vv w).norm ≤ 1 + 17321 / 10000 * (21 / 10 ^ 8) := by
    have := RV.norm_le_add (vv w) U; rw [hUn] at this; linarith
  have hwn : (vv w).norm ≤ 10001 / 10000 := by linarith
  have hwn' : 1 - 17321 / 10000 * (21 / 10 ^ 8) ≤ (vv w).norm := by
    have := RV.norm_le_add U (vv w); rw [hUn, RV.norm_sub_comm] at this; linarith
  have hwVB : VB w 1.01 := by
    have u1 := abs_le_norm_x (vv w); have u2 := abs_le_norm_y (vv w); have u3 := abs_le_norm_z (vv w)
    have h101 : (vv w).norm ≤ 1.01 := by linarith
    exact ⟨⟨A32.of_exact a1.1, u1.trans h101⟩, ⟨A32.of_exact a2.1, u2.trans h101⟩,
      ⟨A32.of_exact a3.1, u3.trans h101⟩⟩
  obtain ⟨hd1, hAVB⟩ := axB_close hB hwVB hwn
  set A := vv (Quaternion.op_mul_Vector3f (Quaternion.inverse B) w) with hA
  set Q := RQ.conj (RQ.normalize (qv B)) with hQ
  have hQw : (RQ.rot Q (vv w)).norm = (vv w).norm := rot_norm_unit (conjB_unit hB) _
  have hAn : |A.norm - 1| ≤ 14 / 10 ^ 6 := by
    have t1 := RV.norm_le_add A (RQ.rot Q (vv w))
    have t2 := RV.norm_le_add (RQ.rot Q (vv w)) A
    rw [RV.norm_sub_comm] at t2
    rw [hQw] at t1 t2
    rw [abs_le]; constructor <;> linarith
  have hApos : 0 < A.norm := by have := abs_le.1 hAn; linarith
  -- the correction quaternion and its rotation vector
  have hcorr := axisAngle_near hL c hAVB fθ (by linarith)
  unfold errCorr; rw [errAxisW_gen hz1 hz2]
  have hout := toAxisAngle_signed hL _ Vector3f.init_void hcorr (norm_sq_dev hAn) (by norm_num) hφ
  refine (combine_xy (e2 := 29 / 10 ^ 4 + 42 / 10 ^ 6) hout ?_).imp (fun h => h.mono (by norm_num)) (fun h => h.mono (by norm_num))
  -- the real estimate
  show (RV.sub (RV.smul (φ / A.norm) A) (rotvecR B T)).norm ≤ 29 / 10 ^ 4 + 42 / 10 ^ 6
  rcases eq_or_lt_of_le (RV.norm_nonneg cr) with hs | hs
  · have hθz : θ = 0 := hs0 hs.symm
    have := RV.norm_sub_le_add (RV.smul (φ / A.norm) A) (rotvecR B T)
    rw [norm_smul_div_self φ hApos] at this
    rw [hθz, sub_zero] at hθφ
    linarith
  · set E := RQ.rot Q (RV.smul (1 / cr.norm) cr) with hE
    have hEn : E.norm = 1 := by
      rw [hE, rot_norm_unit (conjB_unit hB), RV.norm_smul, abs_of_pos (by positivity),
        one_div_mul_cancel hs.ne']
    have hrvE : rotvecR B T = RV.smul θ E := by
      rw [rotvecR, hE, rot_smul]; simp only [RV.smul]; congr 1 <;> ring
    rw [hrvE]
    refine (final_vec hEn hθ0).trans ?_
    -- `|A - E| ≤ |A - Q w| + |w - cr/|cr||`
    have hQE : (RV.sub (RQ.rot Q (vv w)) E).norm = (RV.sub (vv w) (RV.smul (1 / cr.norm) cr)).norm := by
      rw [hE, ← rot_sub, rot_norm_unit (conjB_unit hB)]
    have hdir := RV.dir_le (x := vv crf) (y := cr) hs
    have hwcr : (RV.sub (vv w) (RV.smul (1 / cr.norm) cr)).norm ≤
        17321 / 10000 * (21 / 10 ^ 8) + 2 * (RV.sub (vv crf) cr).norm / cr.norm := by
      have := RV.norm_sub_tri (vv w) U (RV.smul (1 / cr.norm) cr); linarith
    have hAE : (RV.sub A E).norm ≤ 13 / 10 ^ 6 + (17321 / 10000 * (21 / 10 ^ 8) +
        2 * (RV.sub (vv crf) cr).norm / cr.norm) := by
      have := RV.norm_sub_tri A (RQ.rot Q (vv w)) E; rw [hQE] at this; linarith
    have hθd : θ * (2 * (RV.sub (vv crf) cr).norm / cr.norm) ≤ 1025 / 1000 * (2 * (17321 / 10000 * (44 / 10 ^ 7))) := by
      rw [mul_div_assoc', div_le_iff₀ hs]
      have h0 := RV.norm_nonneg (RV.sub (vv crf) cr)
      calc θ * (2 * (RV.sub (vv crf) cr).norm) ≤ (1025 / 1000 * cr.norm) * (2 * (17321 / 10000 * (44 / 10 ^ 7))) := by
            apply mul_le_mul hθs (by linarith) (by positivity) (by positivity)
        _ = _ := by ring
    have : 2 * θ * (RV.sub A E).norm ≤ 2 * θ * (13 / 10 ^ 6 + 17321 / 10000 * (21 / 10 ^ 8)) +
        2 * (θ * (2 * (RV.sub (vv crf) cr).norm / cr.norm)) := by
      have := mul_le_mul_of_nonneg_left hAE (by positivity : 0 ≤ 2 * θ); linarith
    nlinarith

set_option maxHeartbeats 4000000 in
/-- The `up` branch (`is_zero(|t_b × t_t|)` or `is_zero(θ)`). -/
theorem xy_up (hL : LibmSpec) {T B c : Quaternion.State} (hB : Level B) (hT : Level T)
    (hc : 94 / 100 ≤ RV.dot (tbR B) (tbR T))
    (hz : is_zero_float (Vector3f.length (errCross B T)) = true ∨ is_zero_float (errAngle B T) = true) :
    A32 (Quaternion.to_axis_angle (errCorr B T c) Vector3f.init_void).x (rotvecR B T).x (3 / 10 ^ 3) ∧
    A32 (Quaternion.to_axis_angle (errCorr B T c) Vector3f.init_void).y (rotvecR B T).y (3 / 10 ^ 3) := by
  obtain ⟨fθ, -, hθφ⟩ := thrust_error_angle_near hL (T := T) (B := B) (c := c) (e := Vector3f.init_void)
    (a := 0) (b := 0) hB hT hc
  obtain ⟨h38, hθs, hs1, hrv, hs0⟩ := real_facts hB hT hc
  have hcr := crf_near hB hT
  set crf := errCross B T with hcrf
  set cr := RV.cross (tbR B) (tbR T) with hcr_def
  set θ := Real.arccos (RV.dot (tbR B) (tbR T)) with hθdef
  set φ := (errAngle B T).toReal with hφdef
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
  have hφ : |φ| ≤ 1 / 2 := by have := abs_sub_abs_le_abs_sub φ θ; rw [abs_of_nonneg hθ0] at this; linarith
  have hcrn : (RV.sub (vv crf) cr).norm ≤ 17321 / 10000 * (44 / 10 ^ 7) :=
    RV.norm_le_of_comp hcr.1.2 hcr.2.1.2 hcr.2.2.2
  have hun : (vv upV).norm ≤ 10001 / 10000 := by rw [vv_up]; simp [RV.norm]; norm_num
  obtain ⟨hd1, hAVB⟩ := axB_close hB up_VB hun
  set A := vv (Quaternion.op_mul_Vector3f (Quaternion.inverse B) upV) with hA
  set Q := RQ.conj (RQ.normalize (qv B)) with hQ
  have hQw : (RQ.rot Q (vv upV)).norm = 1 := by
    rw [rot_norm_unit (conjB_unit hB), vv_up]; simp [RV.norm]
  have hAn : |A.norm - 1| ≤ 14 / 10 ^ 6 := by
    have t1 := RV.norm_le_add A (RQ.rot Q (vv upV))
    have t2 := RV.norm_le_add (RQ.rot Q (vv upV)) A
    rw [RV.norm_sub_comm] at t2
    rw [hQw] at t1 t2
    rw [abs_le]; constructor <;> linarith
  have hApos : 0 < A.norm := by have := abs_le.1 hAn; linarith
  have hcorr := axisAngle_near hL c hAVB fθ (by linarith)
  unfold errCorr; rw [errAxisW_up hz]
  have hout := toAxisAngle_signed hL _ Vector3f.init_void hcorr (norm_sq_dev hAn) (by norm_num) hφ
  refine (combine_xy (e2 := 29 / 10 ^ 4 + 2 / 10 ^ 5) hout ?_).imp (fun h => h.mono (by norm_num))
    (fun h => h.mono (by norm_num))
  show (RV.sub (RV.smul (φ / A.norm) A) (rotvecR B T)).norm ≤ 29 / 10 ^ 4 + 2 / 10 ^ 5
  have h0 := RV.norm_sub_le_add (RV.smul (φ / A.norm) A) (rotvecR B T)
  rw [norm_smul_div_self φ hApos] at h0
  have hφθ := abs_le.1 hθφ
  rcases hz with hz | hz
  · -- `|t_b × t_t|` is tiny, so is `θ`
    have bx : |crf.x.toReal| ≤ 1000 := by
      have := hcr.1.abs_le; have := abs_le_norm_x cr; linarith
    have by' : |crf.y.toReal| ≤ 1000 := by
      have := hcr.2.1.abs_le; have := abs_le_norm_y cr; linarith
    have bz : |crf.z.toReal| ≤ 1000 := by
      have := hcr.2.2.abs_le; have := abs_le_norm_z cr; linarith
    obtain ⟨fL, eL⟩ := len_near hcr.1.1 hcr.2.1.1 hcr.2.2.1 bx by' bz
    have hL := (Att.isZero_iff fL).1 hz
    rw [two_pow_m23] at hL
    have eL' := (abs_le.1 eL).1
    have hLlt := (abs_lt.1 hL).2
    have hn : (vv crf).norm ≤ 12 / 10 ^ 8 := by norm_num at eL' hLlt ⊢; nlinarith
    have hs := RV.norm_le_add cr (vv crf)
    rw [RV.norm_sub_comm] at hs
    have : θ ≤ 1025 / 1000 * (12 / 10 ^ 8 + 17321 / 10000 * (44 / 10 ^ 7)) := by nlinarith
    rw [abs_le] at hφ
    have : |φ| ≤ θ + 29 / 10 ^ 4 := by rw [abs_le]; constructor <;> linarith
    linarith
  · have hφz := (Att.isZero_iff fθ).1 hz
    rw [two_pow_m23, ← hφdef] at hφz
    have : θ ≤ |φ| + 29 / 10 ^ 4 := by linarith [le_abs_self φ, hφθ.1]
    linarith

/-- **The attitude error `x, y`** (the rotation vector of the thrust-vector correction, body
frame) returned by `thrust_vector_rotation_angles`, for level attitudes (`Level`: unit within
`10⁻⁶`, thrust within `30°` of vertical) whose thrust directions are within `20°` of each other:
within `3·10⁻³` per component of `rotvecR B T`. -/
theorem attitude_error_xy_near (hL : LibmSpec) {T B c : Quaternion.State} {e : Vector3f.State}
    {a b : Float32} (hB : Level B) (hT : Level T) (hc : 94 / 100 ≤ RV.dot (tbR B) (tbR T)) :
    A32 (AC_AttitudeControl_Multi.thrust_vector_rotation_angles T B c e a b).2.1.x (rotvecR B T).x
      (3 / 10 ^ 3) ∧
    A32 (AC_AttitudeControl_Multi.thrust_vector_rotation_angles T B c e a b).2.1.y (rotvecR B T).y
      (3 / 10 ^ 3) := by
  rw [tvra_x, tvra_y]
  by_cases hgen : is_zero_float (Vector3f.length (errCross B T)) = false ∧
      is_zero_float (errAngle B T) = false
  · exact xy_gen hL hB hT hc hgen.1 hgen.2
  · refine xy_up hL hB hT hc ?_
    rcases h1 : is_zero_float (Vector3f.length (errCross B T)) <;>
      rcases h2 : is_zero_float (errAngle B T) <;> simp_all

end Err

/-! ## The real law of `attitude_from_thrust_vector` -/

/-- Sanity check of the real law of `attitude_from_thrust_vector`: `tiltQ t` is a unit quaternion
and rotates `up = (0, 0, -1)` onto `t / |t|`. -/
theorem tiltQ_spec (t : RV) (hn : 0 < t.norm) (hc : -1 < -(t.z / t.norm)) :
    RQ.norm2 (tiltQ t) = 1 ∧
    RQ.rot (tiltQ t) ⟨0, 0, -1⟩ = ⟨t.x / t.norm, t.y / t.norm, t.z / t.norm⟩ := by
  have hu : (t.x / t.norm) ^ 2 + (t.y / t.norm) ^ 2 + (t.z / t.norm) ^ 2 = 1 := by
    rw [div_pow, div_pow, div_pow, ← add_div, ← add_div, div_eq_one_iff_eq (by positivity)]
    exact (norm_sq t).symm
  set X := t.x / t.norm
  set Y := t.y / t.norm
  set Z := t.z / t.norm
  have h1 : 0 < 1 + -Z := by linarith
  set W := Real.sqrt ((1 + -Z) / 2) with hW
  have hW2 : W ^ 2 = (1 + -Z) / 2 := Real.sq_sqrt (by linarith)
  have hWp : 0 < W := Real.sqrt_pos.2 (by linarith)
  have hD : Real.sqrt (2 * (1 + -Z)) = 2 * W := by
    rw [hW, show 2 * (1 + -Z) = 2 ^ 2 * ((1 + -Z) / 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have e : tiltQ t = ⟨W, Y / (2 * W), -X / (2 * W), 0⟩ := by
    simp only [tiltQ]; rw [hD]
  rw [e]
  constructor
  · simp only [RQ.norm2]; field_simp; nlinarith
  · simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec]
    congr 1 <;> field_simp <;> nlinarith

/-! ## `thrust_heading_rotation_angles` with the clip inactive -/

/-- **`thrust_heading_rotation_angles` with the heading clip inactive** (parameters
`ATC_RAT_YAW_P = 0.3`, `ATC_ANG_YAW_P = 4.5`, `ATC_ACCEL_Y_MAX = 270`, so the clip threshold is
`radians(45)`): if the heading error `z` returned by `thrust_vector_rotation_angles` is at most
`π/4 - 10⁻⁶`, the attitude target is returned unchanged and, for level attitudes with thrust
directions within `20°`, the `x, y` error is within `3·10⁻³` of the real rotation vector
`rotvecR`, the thrust angle within `1.5·10⁻³` of `arccos(up · t̂_b)` and the thrust error angle within
`2.9·10⁻³` of `arccos(t̂_b · t̂_t)`. -/
theorem thrust_heading_near (hL : LibmSpec) (p : AC_AttitudeControl_Multi.Params)
    (h1 : p._pid_rate_yaw._kp = (0.300000012 : Float32))
    (h2 : p._p_angle_yaw._kp = (4.5 : Float32))
    (h3 : p._accel_yaw_max_degss = (270.0 : Float32))
    {target body : Quaternion.State} {err : Vector3f.State} {ta tea : Float32}
    (hB : Err.Level body) (hT : Err.Level target)
    (hc : 94 / 100 ≤ RV.dot (Err.tbR body) (Err.tbR target))
    (hz : (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
      err ta tea).2.1.z.IsFinite)
    (hle : |(AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
      err ta tea).2.1.z.toReal| ≤ Real.pi / 4 - 1 / 10 ^ 6) :
    (AC_AttitudeControl_Multi.thrust_heading_rotation_angles p target body err ta tea).1 = target ∧
    A32 (AC_AttitudeControl_Multi.thrust_heading_rotation_angles p target body err ta tea).2.1.x
      (Err.rotvecR body target).x (3 / 10 ^ 3) ∧
    A32 (AC_AttitudeControl_Multi.thrust_heading_rotation_angles p target body err ta tea).2.1.y
      (Err.rotvecR body target).y (3 / 10 ^ 3) ∧
    A32 (AC_AttitudeControl_Multi.thrust_heading_rotation_angles p target body err ta tea).2.2.1
      (Real.arccos (RV.dot Err.upR (Err.tbR body))) (15 / 10 ^ 4) ∧
    A32 (AC_AttitudeControl_Multi.thrust_heading_rotation_angles p target body err ta tea).2.2.2
      (Real.arccos (RV.dot (Err.tbR body) (Err.tbR target))) (29 / 10 ^ 4) := by
  rw [AttHeading.thrust_heading_clip_inactive_pi hL p h1 h2 h3 target body err ta tea hz hle]
  obtain ⟨hx, hy⟩ := Err.attitude_error_xy_near hL (c := Quaternion.init_void) (e := err) (a := ta)
    (b := tea) hB hT hc
  exact ⟨rfl, hx, hy, Err.thrust_angle_near hL hB, (Err.thrust_error_angle_near hL hB hT hc).2.1⟩

end

end Contracts.Track.AttQ
