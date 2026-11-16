import Contracts.Track.CtrlAttitudeBase

/-!
# Quaternion building blocks of the attitude controller (milestone M4, lemma C8)

Real quaternions and vectors (`RQ`, `RV`), the real laws the `AP_Math` quaternion code computes,
and, for each emitted building block, "float output = real law of the float inputs + β" with an
explicit numeric `β` per component:

* `quat_mul_near`: the Hamilton product `Quaternion::operator*` (`RQ.mul`), inputs `|·| ≤ 1.01`;
* `quat_inverse_eq`: `inverse` is exact (`RQ.conj`);
* `cross_near`, `dot_near`: `Vector3f::operator%` and `operator*` (`RV.cross`, `RV.dot`);
* `rot_near`: `Quaternion::operator*(Vector3f)`, the real law `v + q₁ w + u × w` with
  `w = 2 u × v` and `u` the vector part (`RQ.rot`, which is `q v q*` for unit `q`);

`QA q r e` / `VA v r e`: every component of the float quaternion/vector is finite and within `e`
of the corresponding component of the real one.
-/

namespace Contracts.Track.AttQ

open Contracts.Mission AC_Attitude_lib Float.Model UnpackedFloat

noncomputable section

/-! ## Real quaternions and vectors -/

/-- A real quaternion `w + x i + y j + z k`. -/
structure RQ where
  w : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

/-- A real 3-vector. -/
structure RV where
  x : ℝ
  y : ℝ
  z : ℝ

/-- The Hamilton product, in the association of `Quaternion::operator*`. -/
def RQ.mul (a b : RQ) : RQ :=
  ⟨a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z,
   a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y,
   a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x,
   a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w⟩

/-- The conjugate. -/
def RQ.conj (a : RQ) : RQ := ⟨a.w, -a.x, -a.y, -a.z⟩

/-- The squared norm. -/
def RQ.norm2 (a : RQ) : ℝ := a.w ^ 2 + a.x ^ 2 + a.y ^ 2 + a.z ^ 2

def RV.cross (a b : RV) : RV :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

def RV.dot (a b : RV) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z

def RV.norm (a : RV) : ℝ := Real.sqrt (a.x ^ 2 + a.y ^ 2 + a.z ^ 2)

def RV.add (a b : RV) : RV := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def RV.smul (c : ℝ) (a : RV) : RV := ⟨c * a.x, c * a.y, c * a.z⟩

/-- The vector part. -/
def RQ.vec (q : RQ) : RV := ⟨q.x, q.y, q.z⟩

/-- Rotation of `v` by `q` as `Quaternion::operator*(Vector3f)` computes it:
`v + q₁ w + u × w`, `w = 2 (u × v)`, `u` the vector part of `q`. -/
def RQ.rot (q : RQ) (v : RV) : RV :=
  let w := RV.smul 2 (RV.cross q.vec v)
  RV.add v (RV.add (RV.smul q.w w) (RV.cross q.vec w))

/-- The value of a float quaternion. -/
def qv (q : Quaternion.State) : RQ := ⟨q.q1.toReal, q.q2.toReal, q.q3.toReal, q.q4.toReal⟩

/-- The value of a float vector. -/
def vv (v : Vector3f.State) : RV := ⟨v.x.toReal, v.y.toReal, v.z.toReal⟩

/-- Every component finite and within `e` of the real quaternion `r`. -/
def QA (q : Quaternion.State) (r : RQ) (e : ℝ) : Prop :=
  A32 q.q1 r.w e ∧ A32 q.q2 r.x e ∧ A32 q.q3 r.y e ∧ A32 q.q4 r.z e

/-- Every component finite and within `e` of the real vector `r`. -/
def VA (v : Vector3f.State) (r : RV) (e : ℝ) : Prop :=
  A32 v.x r.x e ∧ A32 v.y r.y e ∧ A32 v.z r.z e

/-- Every component finite and at most `M` in magnitude. -/
def QB (q : Quaternion.State) (M : ℝ) : Prop :=
  B32 q.q1 q.q1.toReal 0 M ∧ B32 q.q2 q.q2.toReal 0 M ∧ B32 q.q3 q.q3.toReal 0 M ∧
    B32 q.q4 q.q4.toReal 0 M

def VB (v : Vector3f.State) (M : ℝ) : Prop :=
  B32 v.x v.x.toReal 0 M ∧ B32 v.y v.y.toReal 0 M ∧ B32 v.z v.z.toReal 0 M

theorem QA.mono {q : Quaternion.State} {r : RQ} {e e' : ℝ} (h : QA q r e) (he : e ≤ e') :
    QA q r e' := ⟨h.1.mono he, h.2.1.mono he, h.2.2.1.mono he, h.2.2.2.mono he⟩

theorem VA.mono {v : Vector3f.State} {r : RV} {e e' : ℝ} (h : VA v r e) (he : e ≤ e') :
    VA v r e' := ⟨h.1.mono he, h.2.1.mono he, h.2.2.mono he⟩

/-! ## The `B32` steps with the error as a formula -/

theorem bmul {a b : Float32} {ra rb ea eb Ra Rb : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hcap : Ra * Rb + (Ra * eb + Rb * ea + ea * eb) ≤ capF) :
    B32 (a * b) (ra * rb) (Ra * eb + Rb * ea + ea * eb +
      1 / 16777216 * (Ra * Rb + (Ra * eb + Rb * ea + ea * eb)) + 1 / 10 ^ 40) (Ra * Rb) :=
  B32.mul ha hb hcap le_rfl le_rfl

theorem badd {a b : Float32} {ra rb ea eb Ra Rb : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hcap : Ra + Rb + ea + eb ≤ capF) :
    B32 (a + b) (ra + rb) (ea + eb + 1 / 16777216 * (Ra + Rb + ea + eb) + 1 / 10 ^ 40) (Ra + Rb) :=
  B32.add ha hb le_rfl hcap le_rfl

theorem bsub {a b : Float32} {ra rb ea eb Ra Rb : ℝ} (ha : B32 a ra ea Ra)
    (hb : B32 b rb eb Rb) (hcap : Ra + Rb + ea + eb ≤ capF) :
    B32 (a - b) (ra - rb) (ea + eb + 1 / 16777216 * (Ra + Rb + ea + eb) + 1 / 10 ^ 40) (Ra + Rb) :=
  B32.sub ha hb le_rfl hcap le_rfl

/-- `x + x` is exact. -/
theorem bdbl {a : Float32} {ra ea Ra : ℝ} (ha : B32 a ra ea Ra) (hcap : 2 * Ra + 2 * ea ≤ capF) :
    B32 (a + a) (ra + ra) (2 * ea + 1 / 16777216 * (2 * Ra + 2 * ea) + 1 / 10 ^ 40) (2 * Ra) := by
  have := badd ha ha (by linarith)
  refine ⟨this.1.mono (le_of_eq (by ring)), this.2.trans (le_of_eq (by ring))⟩

theorem bneg {a : Float32} {ra ea Ra : ℝ} (ha : B32 a ra ea Ra) : B32 (-a) (-ra) ea Ra :=
  ⟨⟨(Float32.isFinite_neg a).2 ha.1.1, by
    rw [Float32.toReal_neg, show -a.toReal - -ra = -(a.toReal - ra) by ring, abs_neg]; exact ha.1.2⟩,
    by rw [abs_neg]; exact ha.2⟩

/-! ## Quaternion product -/

theorem rq_mul_w (a b : RQ) : (RQ.mul a b).w = a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z := rfl
theorem rq_mul_x (a b : RQ) : (RQ.mul a b).x = a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y := rfl
theorem rq_mul_y (a b : RQ) : (RQ.mul a b).y = a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x := rfl
theorem rq_mul_z (a b : RQ) : (RQ.mul a b).z = a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w := rfl

/-- **Quaternion product**: for float quaternions with components at most `1.01` in magnitude,
`a * b` is within `8·10⁻⁷` per component of the real Hamilton product of their values. -/
theorem quat_mul_near {a b : Quaternion.State} (ha : QB a 1.01) (hb : QB b 1.01) :
    QA (Quaternion.op_mul_Quaternion a b) (RQ.mul (qv a) (qv b)) (8 / 10 ^ 7) := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (bsub (bsub (bsub (bmul a1 b1 (by norm_num)) (bmul a2 b2 (by norm_num)) (by norm_num))
      (bmul a3 b3 (by norm_num)) (by norm_num)) (bmul a4 b4 (by norm_num)) (by norm_num)).1.mono
      (by norm_num)
  · exact (bsub (badd (badd (bmul a1 b2 (by norm_num)) (bmul a2 b1 (by norm_num)) (by norm_num))
      (bmul a3 b4 (by norm_num)) (by norm_num)) (bmul a4 b3 (by norm_num)) (by norm_num)).1.mono
      (by norm_num)
  · exact (badd (badd (bsub (bmul a1 b3 (by norm_num)) (bmul a2 b4 (by norm_num)) (by norm_num))
      (bmul a3 b1 (by norm_num)) (by norm_num)) (bmul a4 b2 (by norm_num)) (by norm_num)).1.mono
      (by norm_num)
  · exact (badd (bsub (badd (bmul a1 b4 (by norm_num)) (bmul a2 b3 (by norm_num)) (by norm_num))
      (bmul a3 b2 (by norm_num)) (by norm_num)) (bmul a4 b1 (by norm_num)) (by norm_num)).1.mono
      (by norm_num)

theorem bneg_self {a : Float32} {M : ℝ} (ha : B32 a a.toReal 0 M) : B32 (-a) (-a).toReal 0 M := by
  have h := bneg ha
  rw [← Float32.toReal_neg] at h; exact h

theorem quat_inverse_q1 (q : Quaternion.State) : (Quaternion.inverse q).q1 = q.q1 := rfl
theorem quat_inverse_q2 (q : Quaternion.State) : (Quaternion.inverse q).q2 = -q.q2 := rfl
theorem quat_inverse_q3 (q : Quaternion.State) : (Quaternion.inverse q).q3 = -q.q3 := rfl
theorem quat_inverse_q4 (q : Quaternion.State) : (Quaternion.inverse q).q4 = -q.q4 := rfl

/-- **Inverse**: exact, the conjugate. -/
theorem quat_inverse_eq {q : Quaternion.State} (h : QB q 1.01) :
    QA (Quaternion.inverse q) (RQ.conj (qv q)) 0 ∧ QB (Quaternion.inverse q) 1.01 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨⟨h1.1, (bneg h2).1, (bneg h3).1, (bneg h4).1⟩, h1, bneg_self h2, bneg_self h3, bneg_self h4⟩

theorem qv_inverse (q : Quaternion.State) : qv (Quaternion.inverse q) = RQ.conj (qv q) := by
  simp [qv, RQ.conj, quat_inverse_q2, quat_inverse_q3, quat_inverse_q4, quat_inverse_q1,
    Float32.toReal_neg]

/-! ## Cross and dot products -/

theorem cross_x (a b : Vector3f.State) : (Vector3f.op_mod a b).x = a.y * b.z - a.z * b.y := rfl
theorem cross_y (a b : Vector3f.State) : (Vector3f.op_mod a b).y = a.z * b.x - a.x * b.z := rfl
theorem cross_z (a b : Vector3f.State) : (Vector3f.op_mod a b).z = a.x * b.y - a.y * b.x := rfl

/-- **Cross product** (`Vector3f::operator%`) of float vectors with components at most `1.01`:
within `2.5·10⁻⁷` per component of the real cross product of their values. -/
theorem cross_near {a b : Vector3f.State} (ha : VB a 1.01) (hb : VB b 1.01) :
    VA (Vector3f.op_mod a b) (RV.cross (vv a) (vv b)) (25 / 10 ^ 8) := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · exact (bsub (bmul a2 b3 (by norm_num)) (bmul a3 b2 (by norm_num)) (by norm_num)).1.mono
      (by norm_num)
  · exact (bsub (bmul a3 b1 (by norm_num)) (bmul a1 b3 (by norm_num)) (by norm_num)).1.mono
      (by norm_num)
  · exact (bsub (bmul a1 b2 (by norm_num)) (bmul a2 b1 (by norm_num)) (by norm_num)).1.mono
      (by norm_num)

theorem dot_eq (a b : Vector3f.State) :
    Vector3f.op_mul_Vector3f a b = a.x * b.x + a.y * b.y + a.z * b.z := rfl

/-- **Dot product** (`Vector3f::operator*`) of float vectors with components at most `1.01`:
within `5·10⁻⁷` of the real dot product of their values. -/
theorem dot_near {a b : Vector3f.State} (ha : VB a 1.01) (hb : VB b 1.01) :
    A32 (Vector3f.op_mul_Vector3f a b) (RV.dot (vv a) (vv b)) (5 / 10 ^ 7) := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  exact (badd (badd (bmul a1 b1 (by norm_num)) (bmul a2 b2 (by norm_num)) (by norm_num))
    (bmul a3 b3 (by norm_num)) (by norm_num)).1.mono (by norm_num)

/-! ## Rotation of a vector -/

theorem rot_x (q : Quaternion.State) (v : Vector3f.State) : (Quaternion.op_mul_Vector3f q v).x =
    v.x + (q.q1 * ((q.q3 * v.z - q.q4 * v.y) + (q.q3 * v.z - q.q4 * v.y)) +
      q.q3 * ((q.q2 * v.y - q.q3 * v.x) + (q.q2 * v.y - q.q3 * v.x)) -
      q.q4 * ((q.q4 * v.x - q.q2 * v.z) + (q.q4 * v.x - q.q2 * v.z))) := rfl
theorem rot_y (q : Quaternion.State) (v : Vector3f.State) : (Quaternion.op_mul_Vector3f q v).y =
    v.y + (q.q1 * ((q.q4 * v.x - q.q2 * v.z) + (q.q4 * v.x - q.q2 * v.z)) +
      q.q4 * ((q.q3 * v.z - q.q4 * v.y) + (q.q3 * v.z - q.q4 * v.y)) -
      q.q2 * ((q.q2 * v.y - q.q3 * v.x) + (q.q2 * v.y - q.q3 * v.x))) := rfl
theorem rot_z (q : Quaternion.State) (v : Vector3f.State) : (Quaternion.op_mul_Vector3f q v).z =
    v.z + (q.q1 * ((q.q2 * v.y - q.q3 * v.x) + (q.q2 * v.y - q.q3 * v.x)) +
      q.q2 * ((q.q4 * v.x - q.q2 * v.z) + (q.q4 * v.x - q.q2 * v.z)) -
      q.q3 * ((q.q3 * v.z - q.q4 * v.y) + (q.q3 * v.z - q.q4 * v.y))) := rfl

theorem RQ.rot_x (q : RQ) (v : RV) : (RQ.rot q v).x =
    v.x + (q.w * ((q.y * v.z - q.z * v.y) + (q.y * v.z - q.z * v.y)) +
      q.y * ((q.x * v.y - q.y * v.x) + (q.x * v.y - q.y * v.x)) -
      q.z * ((q.z * v.x - q.x * v.z) + (q.z * v.x - q.x * v.z))) := by
  simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec]; ring
theorem RQ.rot_y (q : RQ) (v : RV) : (RQ.rot q v).y =
    v.y + (q.w * ((q.z * v.x - q.x * v.z) + (q.z * v.x - q.x * v.z)) +
      q.z * ((q.y * v.z - q.z * v.y) + (q.y * v.z - q.z * v.y)) -
      q.x * ((q.x * v.y - q.y * v.x) + (q.x * v.y - q.y * v.x))) := by
  simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec]; ring
theorem RQ.rot_z (q : RQ) (v : RV) : (RQ.rot q v).z =
    v.z + (q.w * ((q.x * v.y - q.y * v.x) + (q.x * v.y - q.y * v.x)) +
      q.x * ((q.z * v.x - q.x * v.z) + (q.z * v.x - q.x * v.z)) -
      q.y * ((q.y * v.z - q.z * v.y) + (q.y * v.z - q.z * v.y))) := by
  simp only [RQ.rot, RV.add, RV.smul, RV.cross, RQ.vec]; ring

set_option maxHeartbeats 800000 in
/-- **Rotation** (`Quaternion::operator*(Vector3f)`) of a vector with components at most `1.01` by
a quaternion with components at most `1.01`: within `6·10⁻⁶` per component of `RQ.rot`. -/
theorem rot_near {q : Quaternion.State} {v : Vector3f.State} (hq : QB q 1.01) (hv : VB v 1.01) :
    VA (Quaternion.op_mul_Vector3f q v) (RQ.rot (qv q) (vv v)) (6 / 10 ^ 6) := by
  obtain ⟨q1, q2, q3, q4⟩ := hq
  obtain ⟨v1, v2, v3⟩ := hv
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

/-! ## `from_axis_angle(axis, θ)`: `cos`/`sin` of `θ/2` in `double` -/

/-- `0.5 * (double) θ` is within `10⁻¹²` of `θ/2` for `|θ| ≤ 1000`. -/
theorem half_dbl (hL : LibmSpec) {θ : Float32} (hθ : θ.IsFinite) (hb : |θ.toReal| ≤ 1000) :
    A64 ((0.5 : Float) * Float32.toFloat θ) (θ.toReal / 2) (1 / 10 ^ 12) := by
  have h := A64.mul (A64.of_exact f64_isFinite_0p5) (A32.toFloat hL (A32.of_exact hθ))
    (by rw [f64_toReal_0p5]; simp only [capF, abs_mul]; norm_num; linarith)
  rw [f64_toReal_0p5] at h
  refine (h.congr (by ring)).mono ?_
  have := η64_small
  simp only [u64, abs_mul]; norm_num
  nlinarith [abs_nonneg θ.toReal]

theorem libm64Err_eq : libm64Err = 1 / 2251799813685248 := by norm_num [libm64Err]

/-- `(float) sin(0.5 * (double) θ)` is within `6·10⁻⁸` of `sin(θ/2)`. -/
theorem sin_half (hL : LibmSpec) {θ : Float32} (hθ : θ.IsFinite) (hb : |θ.toReal| ≤ 1000) :
    B32 (Float.toFloat32 (Float.sin ((0.5 : Float) * Float32.toFloat θ))) (Real.sin (θ.toReal / 2))
      (6 / 10 ^ 8) 1 := by
  have hx := half_dbl hL hθ hb
  obtain ⟨f1, -, e1⟩ := hL.sin _ hx.1
  have hs : A64 (Float.sin ((0.5 : Float) * Float32.toFloat θ)) (Real.sin (θ.toReal / 2))
      (libm64Err + 1 / 10 ^ 12) := by
    refine ⟨f1, ?_⟩
    have := Real.abs_sin_sub_sin_le ((0.5 : Float) * Float32.toFloat θ).toReal (θ.toReal / 2)
    have := abs_sub_le (Float.sin ((0.5 : Float) * Float32.toFloat θ)).toReal
      (Real.sin ((0.5 : Float) * Float32.toFloat θ).toReal) (Real.sin (θ.toReal / 2))
    linarith [hx.2]
  have h1 : |Real.sin (θ.toReal / 2)| ≤ 1 := Real.abs_sin_le_one _
  have h := A64.toFloat32 hL hs (by rw [libm64Err_eq]; simp only [capF]; norm_num; linarith)
  refine ⟨h.mono ?_, h1⟩
  rw [libm64Err_eq]; have := η32_small; simp only [u32]
  have : (2:ℝ) ^ (-24:ℤ) * (|Real.sin (θ.toReal / 2)| + (1 / 2251799813685248 + 1 / 10 ^ 12)) ≤
      (2:ℝ) ^ (-24:ℤ) * (1 + (1 / 2251799813685248 + 1 / 10 ^ 12)) := by gcongr
  norm_num at this ⊢; linarith

/-- `(float) cos(0.5 * (double) θ)` is within `6·10⁻⁸` of `cos(θ/2)`. -/
theorem cos_half (hL : LibmSpec) {θ : Float32} (hθ : θ.IsFinite) (hb : |θ.toReal| ≤ 1000) :
    B32 (Float.toFloat32 (Float.cos ((0.5 : Float) * Float32.toFloat θ))) (Real.cos (θ.toReal / 2))
      (6 / 10 ^ 8) 1 := by
  have hx := half_dbl hL hθ hb
  obtain ⟨f1, -, e1⟩ := hL.cos _ hx.1
  have hs : A64 (Float.cos ((0.5 : Float) * Float32.toFloat θ)) (Real.cos (θ.toReal / 2))
      (libm64Err + 1 / 10 ^ 12) := by
    refine ⟨f1, ?_⟩
    have := Real.abs_cos_sub_cos_le ((0.5 : Float) * Float32.toFloat θ).toReal (θ.toReal / 2)
    have := abs_sub_le (Float.cos ((0.5 : Float) * Float32.toFloat θ)).toReal
      (Real.cos ((0.5 : Float) * Float32.toFloat θ).toReal) (Real.cos (θ.toReal / 2))
    linarith [hx.2]
  have h1 : |Real.cos (θ.toReal / 2)| ≤ 1 := Real.abs_cos_le_one _
  have h := A64.toFloat32 hL hs (by rw [libm64Err_eq]; simp only [capF]; norm_num; linarith)
  refine ⟨h.mono ?_, h1⟩
  rw [libm64Err_eq]; have := η32_small; simp only [u32]
  have : (2:ℝ) ^ (-24:ℤ) * (|Real.cos (θ.toReal / 2)| + (1 / 2251799813685248 + 1 / 10 ^ 12)) ≤
      (2:ℝ) ^ (-24:ℤ) * (1 + (1 / 2251799813685248 + 1 / 10 ^ 12)) := by gcongr
  norm_num at this ⊢; linarith

/-- The quaternion of the rotation by `θ` about `axis`: `(cos(θ/2), axis · sin(θ/2))`. -/
def RQ.ofAxisAngle (a : RV) (θ : ℝ) : RQ :=
  ⟨Real.cos (θ / 2), a.x * Real.sin (θ / 2), a.y * Real.sin (θ / 2), a.z * Real.sin (θ / 2)⟩

theorem two_pow_m23 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 8388608 := by norm_num

/-- The `is_zero(θ)` branch: `(1, 0, 0, 0)` is within `1.3·10⁻⁷` of the real law. -/
theorem axisAngle_zero_branch {a : RV} {θ : ℝ} (ha : |a.x| ≤ 1.01 ∧ |a.y| ≤ 1.01 ∧ |a.z| ≤ 1.01)
    (hθ : |θ| < 2 ^ (-23 : ℤ)) :
    |1 - Real.cos (θ / 2)| ≤ 13 / 10 ^ 8 ∧ |0 - a.x * Real.sin (θ / 2)| ≤ 13 / 10 ^ 8 ∧
      |0 - a.y * Real.sin (θ / 2)| ≤ 13 / 10 ^ 8 ∧ |0 - a.z * Real.sin (θ / 2)| ≤ 13 / 10 ^ 8 := by
  rw [two_pow_m23] at hθ
  have hs : |Real.sin (θ / 2)| ≤ 1 / 16777216 := by
    refine Real.abs_sin_le_abs.trans ?_
    rw [abs_div, abs_two]; linarith
  have hc1 := Real.cos_le_one (θ / 2)
  have hc2 := @Real.one_sub_sq_div_two_le_cos (θ / 2)
  have hsq : (θ / 2) ^ 2 ≤ 1 / 10 ^ 12 := by
    have : |θ / 2| ≤ 1 / 10 ^ 6 := by rw [abs_div, abs_two]; linarith
    rw [← sq_abs]; nlinarith [abs_nonneg (θ / 2)]
  have key : ∀ c : ℝ, |c| ≤ 1.01 → |0 - c * Real.sin (θ / 2)| ≤ 13 / 10 ^ 8 := by
    intro c hc
    rw [zero_sub, abs_neg, abs_mul]
    calc |c| * |Real.sin (θ / 2)| ≤ 1.01 * (1 / 16777216) :=
          mul_le_mul hc hs (abs_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  refine ⟨?_, key _ ha.1, key _ ha.2.1, key _ ha.2.2⟩
  rw [abs_le]; constructor <;> nlinarith

theorem aa_q1_zero (s : Quaternion.State) (a : Vector3f.State) (θ : Float32) (h : is_zero_float θ = true) :
    (Quaternion.from_axis_angle_Vector3f_float s a θ).q1 = 1.0 := by
  simp [Quaternion.from_axis_angle_Vector3f_float, h]
theorem aa_q2_zero (s : Quaternion.State) (a : Vector3f.State) (θ : Float32) (h : is_zero_float θ = true) :
    (Quaternion.from_axis_angle_Vector3f_float s a θ).q2 = 0.0 := by
  simp [Quaternion.from_axis_angle_Vector3f_float, h]
theorem aa_q3_zero (s : Quaternion.State) (a : Vector3f.State) (θ : Float32) (h : is_zero_float θ = true) :
    (Quaternion.from_axis_angle_Vector3f_float s a θ).q3 = 0.0 := by
  simp [Quaternion.from_axis_angle_Vector3f_float, h]
theorem aa_q4_zero (s : Quaternion.State) (a : Vector3f.State) (θ : Float32) (h : is_zero_float θ = true) :
    (Quaternion.from_axis_angle_Vector3f_float s a θ).q4 = 0.0 := by
  simp [Quaternion.from_axis_angle_Vector3f_float, h]

/-- `(float) sin(0.5 * (double) θ)`, the `st2` of `from_axis_angle`. -/
abbrev st2 (θ : Float32) : Float32 := Float.toFloat32 (Float.sin ((0.5 : Float) * Float32.toFloat θ))
abbrev ct2 (θ : Float32) : Float32 := Float.toFloat32 (Float.cos ((0.5 : Float) * Float32.toFloat θ))

theorem aa_q1 (s : Quaternion.State) (a : Vector3f.State) (θ : Float32) (h : is_zero_float θ = false) :
    (Quaternion.from_axis_angle_Vector3f_float s a θ).q1 = ct2 θ := by
  simp [Quaternion.from_axis_angle_Vector3f_float, h]
theorem aa_q2 (s : Quaternion.State) (a : Vector3f.State) (θ : Float32) (h : is_zero_float θ = false) :
    (Quaternion.from_axis_angle_Vector3f_float s a θ).q2 = a.x * st2 θ := by
  simp [Quaternion.from_axis_angle_Vector3f_float, h]
theorem aa_q3 (s : Quaternion.State) (a : Vector3f.State) (θ : Float32) (h : is_zero_float θ = false) :
    (Quaternion.from_axis_angle_Vector3f_float s a θ).q3 = a.y * st2 θ := by
  simp [Quaternion.from_axis_angle_Vector3f_float, h]
theorem aa_q4 (s : Quaternion.State) (a : Vector3f.State) (θ : Float32) (h : is_zero_float θ = false) :
    (Quaternion.from_axis_angle_Vector3f_float s a θ).q4 = a.z * st2 θ := by
  simp [Quaternion.from_axis_angle_Vector3f_float, h]

/-- **`from_axis_angle(axis, θ)`** for an axis with components at most `1.01` and `|θ| ≤ 1000`:
both branches (`is_zero(θ)` or not) are within `1.3·10⁻⁷` per component of
`(cos(θ/2), axis · sin(θ/2))` (the `double` `sin`/`cos` within `libm64Err`). -/
theorem axisAngle_near (hL : LibmSpec) (s : Quaternion.State) {a : Vector3f.State} {θ : Float32}
    (ha : VB a 1.01) (hθ : θ.IsFinite) (hb : |θ.toReal| ≤ 1000) :
    QA (Quaternion.from_axis_angle_Vector3f_float s a θ) (RQ.ofAxisAngle (vv a) θ.toReal)
      (13 / 10 ^ 8) := by
  obtain ⟨a1, a2, a3⟩ := ha
  cases hz : is_zero_float θ with
  | true =>
    have hθ0 := (Att.isZero_iff hθ).1 hz
    obtain ⟨e1, e2, e3, e4⟩ := axisAngle_zero_branch (a := vv a) ⟨a1.2, a2.2, a3.2⟩ hθ0
    unfold QA
    rw [aa_q1_zero s a θ hz, aa_q2_zero s a θ hz, aa_q3_zero s a θ hz, aa_q4_zero s a θ hz]
    refine ⟨⟨f32_isFinite_1p0, ?_⟩, ⟨f32_isFinite_0p0, ?_⟩, ⟨f32_isFinite_0p0, ?_⟩,
      ⟨f32_isFinite_0p0, ?_⟩⟩
    · rw [f32_toReal_1p0]; exact e1
    · rw [f32_toReal_0p0]; exact e2
    · rw [f32_toReal_0p0]; exact e3
    · rw [f32_toReal_0p0]; exact e4
  | false =>
    unfold QA
    rw [aa_q1 s a θ hz, aa_q2 s a θ hz, aa_q3 s a θ hz, aa_q4 s a θ hz]
    have hs := sin_half hL hθ hb
    refine ⟨(cos_half hL hθ hb).1.mono (by norm_num), ?_, ?_, ?_⟩
    · exact (bmul a1 hs (by norm_num)).1.mono (by norm_num)
    · exact (bmul a2 hs (by norm_num)).1.mono (by norm_num)
    · exact (bmul a3 hs (by norm_num)).1.mono (by norm_num)

/-! ## Length: relative accuracy -/

/-- The square root step of a length: from `S` within `3.0001 u N + 6·2⁻¹⁵⁰` of `N`, the
rounded `L` of `√S` is within `2.501 u √N + 2⁻⁶⁰` of `√N`. -/
theorem sqrt_rel {S N L : ℝ} (hS : 0 ≤ S) (hN : 0 ≤ N)
    (hSN : |S - N| ≤ 30001 / 10000 * (1 / 16777216) * N + 6 / 2 ^ 150)
    (hL : |L - Real.sqrt S| ≤ 1 / 16777216 * Real.sqrt S + 1 / 2 ^ 150) :
    |L - Real.sqrt N| ≤ 2501 / 1000 * (1 / 16777216) * Real.sqrt N + 1 / 2 ^ 60 := by
  have hs0 := Real.sqrt_nonneg S
  have hn0 := Real.sqrt_nonneg N
  have hs2 := Real.sq_sqrt hS
  have hn2 := Real.sq_sqrt hN
  set s := Real.sqrt S
  set n := Real.sqrt N
  have hd := abs_sub_le L s n
  rcases lt_or_ge N (1 / 2 ^ 100) with hsm | hbig
  · -- tiny: `|s - n| ≤ √|S - N| ≤ 2⁻⁷¹`
    have h1 : |s - n| ≤ Real.sqrt |S - N| := (sqrt_sub_le S N)
    have h2 : |S - N| ≤ (1 / 2 ^ 61) ^ 2 := by
      refine hSN.trans ?_
      have : 30001 / 10000 * (1 / 16777216) * N ≤ 30001 / 10000 * (1 / 16777216) * (1 / 2 ^ 100) := by
        gcongr
      norm_num at this ⊢; linarith
    have h3 : Real.sqrt |S - N| ≤ 1 / 2 ^ 61 := by
      rw [show (1 / 2 ^ 61 : ℝ) = Real.sqrt ((1 / 2 ^ 61) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h2
    have hS' : S ≤ 1 / 2 ^ 98 := by
      have := (abs_le.1 hSN).2
      have : 30001 / 10000 * (1 / 16777216) * N ≤ 30001 / 10000 * (1 / 16777216) * (1 / 2 ^ 100) := by
        gcongr
      norm_num at *; linarith
    have hs1 : s ≤ 1 / 2 ^ 49 := by
      rw [show (1 / 2 ^ 49 : ℝ) = Real.sqrt ((1 / 2 ^ 49) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num at hS' ⊢; linarith)
    have : 0 ≤ 2501 / 1000 * (1 / 16777216) * n := by positivity
    norm_num at *; linarith
  · have hn : 1 / 2 ^ 50 ≤ n := by
      rw [show (1 / 2 ^ 50 : ℝ) = Real.sqrt ((1 / 2 ^ 50) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num at hbig ⊢; linarith)
    have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    -- `|s - n| (s + n) = |S - N|`
    have key : |s - n| * (s + n) = |S - N| := by
      rw [← abs_of_nonneg (by positivity : 0 ≤ s + n), ← abs_mul]; congr 1; nlinarith
    set d := |s - n| with hd_def
    have hd0 : 0 ≤ d := abs_nonneg _
    have hSN' : |S - N| ≤ 30001 / 10000 * (1 / 16777216) * n ^ 2 + 6 / 2 ^ 150 := by
      rw [hn2]; exact hSN
    -- crude: `d ≤ |S - N| / n`
    have hcr : d * n ≤ 30001 / 10000 * (1 / 16777216) * n ^ 2 + 6 / 2 ^ 150 := by
      have : d * n ≤ d * (s + n) := by nlinarith
      linarith
    have hη : 6 / 2 ^ 150 ≤ (1 / 10 ^ 6) * (1 / 16777216) * n ^ 2 := by
      have : (1 / 2 ^ 50 : ℝ) ^ 2 ≤ n ^ 2 := by gcongr
      norm_num at this ⊢; nlinarith
    have hcr' : d ≤ 30002 / 10000 * (1 / 16777216) * n := by
      by_contra hc
      push Not at hc
      have : 30002 / 10000 * (1 / 16777216) * n * n < d * n := by gcongr
      nlinarith
    -- refined: `d (2n - d) ≤ d (s + n)`
    have hsn : 2 * n - d ≤ s + n := by
      have := neg_abs_le (s - n); linarith
    have href : d * (2 * n - d) ≤ 30001 / 10000 * (1 / 16777216) * n ^ 2 + 6 / 2 ^ 150 := by
      have : d * (2 * n - d) ≤ d * (s + n) := mul_le_mul_of_nonneg_left hsn hd0
      linarith
    have hfine : d ≤ 15002 / 10000 * (1 / 16777216) * n := by
      by_contra hc
      push Not at hc
      have h2n : 2 * n - d ≥ 2 * n - 30002 / 10000 * (1 / 16777216) * n := by linarith
      have : 15002 / 10000 * (1 / 16777216) * n * (2 * n - 30002 / 10000 * (1 / 16777216) * n) ≤
          d * (2 * n - d) := by
        apply mul_le_mul hc.le h2n (by nlinarith) hd0
      nlinarith
    have hsle : s ≤ n + d := by have := le_abs_self (s - n); linarith
    have hLs := (abs_le.1 hL)
    rw [abs_le]; constructor
    · nlinarith [abs_le.1 (show |s - n| ≤ d from le_rfl)]
    · nlinarith [abs_le.1 (show |s - n| ≤ d from le_rfl)]

/-- A rounded sum of three rounded squares is within `3.0001 u` relative (plus `6·2⁻¹⁵⁰`). -/
theorem sum3_rel {A B C P1 P2 P3 S1 S2 : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h1 : |P1 - A| ≤ 1 / 16777216 * A + 1 / 2 ^ 150) (h2 : |P2 - B| ≤ 1 / 16777216 * B + 1 / 2 ^ 150)
    (h3 : |P3 - C| ≤ 1 / 16777216 * C + 1 / 2 ^ 150) (_hP1 : 0 ≤ P1) (_hP2 : 0 ≤ P2) (hP3 : 0 ≤ P3)
    (_hS1 : 0 ≤ S1) (e1 : |S1 - (P1 + P2)| ≤ 1 / 16777216 * (P1 + P2))
    (e2 : |S2 - (S1 + P3)| ≤ 1 / 16777216 * (S1 + P3)) :
    |S2 - (A + B + C)| ≤ 30001 / 10000 * (1 / 16777216) * (A + B + C) + 6 / 2 ^ 150 := by
  have a1 := abs_le.1 h1; have a2 := abs_le.1 h2; have a3 := abs_le.1 h3
  have b1 := abs_le.1 e1; have b2 := abs_le.1 e2
  rw [abs_le]; constructor <;> norm_num at * <;> nlinarith

theorem len_eq (v : Vector3f.State) :
    Vector3f.length v = Float32.sqrt (v.x * v.x + v.y * v.y + v.z * v.z) := rfl

theorem two_pow_m24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
theorem two_pow_m150 : (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 := by norm_num

/-- A finite square is nonnegative and within `u x² + 2⁻¹⁵⁰` of `x²`. -/
theorem sq_rnd {x : Float32} (hx : x.IsFinite) (hb : |x.toReal| ≤ 1000) :
    (x * x).IsFinite ∧ 0 ≤ (x * x).toReal ∧
      |(x * x).toReal - x.toReal * x.toReal| ≤ 1 / 16777216 * (x.toReal * x.toReal) + 1 / 2 ^ 150 := by
  have hsq : x.toReal * x.toReal ≤ 10 ^ 6 := by
    have := abs_mul_abs_self x.toReal; nlinarith [abs_nonneg x.toReal]
  have hm : |x.toReal * x.toReal| ≤ maxFinite32 := by
    rw [abs_of_nonneg (mul_self_nonneg x.toReal)]
    have : (10 : ℝ) ^ 6 ≤ capF := by simp only [capF]; norm_num
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.mul_err_all hx hx hm
  have h0 := (Float32.mul_bracket hx hx hm f32_isFinite_0p0).1
    (by rw [f32_toReal_0p0]; exact mul_self_nonneg _)
  rw [f32_toReal_0p0] at h0
  rw [abs_of_nonneg (mul_self_nonneg x.toReal), two_pow_m24, two_pow_m150] at he
  exact ⟨hf, h0, he⟩

/-- A rounded sum of two nonnegative floats is nonnegative and within `u` relative. -/
theorem add_rnd_nonneg {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (ha0 : 0 ≤ a.toReal)
    (hb0 : 0 ≤ b.toReal) (hM : a.toReal + b.toReal ≤ 10 ^ 7) :
    (a + b).IsFinite ∧ 0 ≤ (a + b).toReal ∧
      |(a + b).toReal - (a.toReal + b.toReal)| ≤ 1 / 16777216 * (a.toReal + b.toReal) := by
  have hm : |a.toReal + b.toReal| ≤ maxFinite32 := by
    rw [abs_of_nonneg (show 0 ≤ a.toReal + b.toReal by linarith)]
    have : (10 : ℝ) ^ 7 ≤ capF := by simp only [capF]; norm_num
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.add_err_all ha hb hm
  have h0 := (Float32.add_bracket ha hb hm f32_isFinite_0p0).1 (by rw [f32_toReal_0p0]; linarith)
  rw [f32_toReal_0p0] at h0
  rw [abs_of_nonneg (show 0 ≤ a.toReal + b.toReal by linarith), two_pow_m24] at he
  exact ⟨hf, h0, he⟩

/-- The rounded sum of squares `x*x + y*y + z*z` (`length_squared`, and under the root of
`length`) of components at most `1000`: finite, nonnegative, within `3.0001 u N + 6·2⁻¹⁵⁰` of the
real sum of squares `N`. -/
theorem sumsq_near {a b c : Float32} (hx : a.IsFinite) (hy : b.IsFinite) (hz : c.IsFinite)
    (bx : |a.toReal| ≤ 1000) (by' : |b.toReal| ≤ 1000) (bz : |c.toReal| ≤ 1000) :
    (a * a + b * b + c * c).IsFinite ∧ 0 ≤ (a * a + b * b + c * c).toReal ∧
      (a * a + b * b + c * c).toReal ≤ maxFinite32 ∧
      |(a * a + b * b + c * c).toReal - (a.toReal * a.toReal + b.toReal * b.toReal +
        c.toReal * c.toReal)| ≤ 30001 / 10000 * (1 / 16777216) *
          (a.toReal * a.toReal + b.toReal * b.toReal + c.toReal * c.toReal) + 6 / 2 ^ 150 := by
  obtain ⟨f1, n1, e1⟩ := sq_rnd hx bx
  obtain ⟨f2, n2, e2⟩ := sq_rnd hy by'
  obtain ⟨f3, n3, e3⟩ := sq_rnd hz bz
  have q1 : a.toReal * a.toReal ≤ 10 ^ 6 := by
    have := abs_mul_abs_self a.toReal; nlinarith [abs_nonneg a.toReal]
  have q2 : b.toReal * b.toReal ≤ 10 ^ 6 := by
    have := abs_mul_abs_self b.toReal; nlinarith [abs_nonneg b.toReal]
  have q3 : c.toReal * c.toReal ≤ 10 ^ 6 := by
    have := abs_mul_abs_self c.toReal; nlinarith [abs_nonneg c.toReal]
  have u1 := (abs_le.1 e1).2; have u2 := (abs_le.1 e2).2; have u3 := (abs_le.1 e3).2
  obtain ⟨g1, m1, d1⟩ := add_rnd_nonneg f1 f2 n1 n2 (by norm_num at u1 u2 ⊢; linarith)
  have w1 := (abs_le.1 d1).2
  obtain ⟨g2, m2, d2⟩ := add_rnd_nonneg g1 f3 m1 n3 (by norm_num at u1 u2 u3 w1 ⊢; linarith)
  have w2 := (abs_le.1 d2).2
  have hmx : (a * a + b * b + c * c).toReal ≤ maxFinite32 := by
    have : (10 : ℝ) ^ 8 ≤ capF := by simp only [capF]; norm_num
    norm_num at u1 u2 u3 w1 w2 ⊢; linarith [capF_le_max32]
  exact ⟨g2, m2, hmx, sum3_rel (mul_self_nonneg a.toReal) (mul_self_nonneg b.toReal)
    (mul_self_nonneg c.toReal) e1 e2 e3 n1 n2 n3 m1 d1 d2⟩

/-- **Length** (`Vector3f::length`) of a vector with components at most `1000`: within
`2.501 u |v| + 2⁻⁶⁰` of the real length of its value (relative accuracy). -/
theorem len_near {v : Vector3f.State} (hx : v.x.IsFinite) (hy : v.y.IsFinite) (hz : v.z.IsFinite)
    (bx : |v.x.toReal| ≤ 1000) (by' : |v.y.toReal| ≤ 1000) (bz : |v.z.toReal| ≤ 1000) :
    (Vector3f.length v).IsFinite ∧
      |(Vector3f.length v).toReal - (vv v).norm| ≤
        2501 / 1000 * (1 / 16777216) * (vv v).norm + 1 / 2 ^ 60 := by
  obtain ⟨g2, m2, hmx, hS⟩ := sumsq_near hx hy hz bx by' bz
  obtain ⟨hf, he⟩ := Float32.sqrt_err_all g2 m2 hmx
  rw [two_pow_m24, two_pow_m150] at he
  have hN0 : 0 ≤ v.x.toReal * v.x.toReal + v.y.toReal * v.y.toReal + v.z.toReal * v.z.toReal := by
    nlinarith [mul_self_nonneg v.x.toReal, mul_self_nonneg v.y.toReal, mul_self_nonneg v.z.toReal]
  have := sqrt_rel m2 hN0 hS he
  refine ⟨hf, ?_⟩
  rw [len_eq]
  have hN : (vv v).norm = Real.sqrt (v.x.toReal * v.x.toReal + v.y.toReal * v.y.toReal +
      v.z.toReal * v.z.toReal) := by simp only [RV.norm, vv, sq]
  rw [hN]; exact this

/-- Division by a rounded length: `q = fl(x / L)` with `L` within `2.501 u n + 2⁻⁶⁰` of
`n ≥ 2⁻²⁴` is within `3.503 u |x|/n + 2⁻¹⁵⁰` of `x / n`. -/
theorem div_rel {x n L q : ℝ} (hn : 1 / 2 ^ 24 ≤ n)
    (hL : |L - n| ≤ 2501 / 1000 * (1 / 16777216) * n + 1 / 2 ^ 60)
    (hq : |q - x / L| ≤ 1 / 16777216 * |x / L| + 1 / 2 ^ 150) :
    0 < L ∧ |q - x / n| ≤ 3503 / 1000 * (1 / 16777216) * (|x| / n) + 1 / 2 ^ 150 := by
  have hnp : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have h60 : 1 / 2 ^ 60 ≤ 1 / 4000 * (1 / 16777216) * n := by
    have : 1 / 4000 * (1 / 16777216) * (1 / 2 ^ 24) ≤ 1 / 4000 * (1 / 16777216) * n := by gcongr
    norm_num at this ⊢; linarith
  have hLn : |L - n| ≤ 250125 / 100000 * (1 / 16777216) * n := by linarith
  have hLlo : (1 - 250125 / 100000 * (1 / 16777216)) * n ≤ L := by
    have := (abs_le.1 hLn).1; linarith
  have hLp : 0 < L := lt_of_lt_of_le (by nlinarith) hLlo
  refine ⟨hLp, ?_⟩
  have hρ : 0 ≤ |x| / n := by positivity
  -- `|x/L - x/n| ≤ 2.5013 u |x|/n`
  have h1 : |x / L - x / n| ≤ 25013 / 10000 * (1 / 16777216) * (|x| / n) := by
    rw [show x / L - x / n = (x / n) * ((n - L) / L) by field_simp, abs_mul, abs_div x n,
      abs_of_pos hnp]
    have hr : |(n - L) / L| ≤ 25013 / 10000 * (1 / 16777216) := by
      rw [abs_div, abs_of_pos hLp, div_le_iff₀ hLp, abs_sub_comm]
      nlinarith
    calc |x| / n * |(n - L) / L| ≤ |x| / n * (25013 / 10000 * (1 / 16777216)) := by gcongr
      _ = _ := by ring
  have h2 : |x / L| ≤ (1 + 3 / 16777216) * (|x| / n) := by
    have := abs_sub_abs_le_abs_sub (x / L) (x / n)
    rw [abs_div x n, abs_of_pos hnp] at this
    nlinarith
  have := abs_sub_le q (x / L) (x / n)
  linarith

/-- **Division by a length** (`Vector3f::operator/=` after `length`): a finite `x` with
`|x| ≤ n`, divided by a float `L` within `2.501 u n + 2⁻⁶⁰` of `n ≥ 2⁻²⁴`. -/
theorem ndiv {x L : Float32} {n : ℝ} (hx : x.IsFinite) (hL : L.IsFinite) (hn : 1 / 2 ^ 24 ≤ n)
    (hLn : |L.toReal - n| ≤ 2501 / 1000 * (1 / 16777216) * n + 1 / 2 ^ 60) (hxn : |x.toReal| ≤ n) :
    (x / L).IsFinite ∧
      |(x / L).toReal - x.toReal / n| ≤ 3503 / 1000 * (1 / 16777216) * (|x.toReal| / n) + 1 / 2 ^ 150 := by
  have hnp : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hLlo : n / 2 ≤ L.toReal := by
    have := (abs_le.1 hLn).1
    have : 1 / 2 ^ 60 ≤ n / 4 := by linarith
    nlinarith
  have hLp : 0 < L.toReal := by linarith
  have hq : |x.toReal / L.toReal| ≤ 2 := by
    rw [abs_div, abs_of_pos hLp, div_le_iff₀ hLp]; linarith
  have hm : |x.toReal / L.toReal| ≤ maxFinite32 := by
    have : (2 : ℝ) ≤ capF := by simp only [capF]; norm_num
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.div_err_all hx hL hLp.ne' hm
  rw [two_pow_m24, two_pow_m150] at he
  exact ⟨hf, (div_rel hn hLn he).2⟩
