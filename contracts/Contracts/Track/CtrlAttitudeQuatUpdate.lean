import Contracts.Track.CtrlAttitudeQuatTilt

/-!
# `update_attitude_target`: the attitude target integration step (milestone M4, lemma C8)

`AC_AttitudeControl::update_attitude_target()` integrates the target attitude over one step:
`_attitude_target ← normalize(_attitude_target ⊗ from_axis_angle(ω · dt))` with
`ω = _ang_vel_target_rads` and `dt = _dt_s`. The real law of each building block, and for each a
"float output = real law of the float inputs + β" statement:

* `expV_near`: `Quaternion::from_axis_angle(Vector3f v)` (`θ = |v|`, the identity when
  `is_zero(θ)`, otherwise `from_axis_angle(v/θ, θ)`) against the exponential map `expQ`, both
  branches, `β = 7·10⁻⁷`, for `v` one rounding away from a real `V` with `|V_i| ≤ 1`;
* `normalize_near`: `Quaternion::normalize` against `P / |P|` (`RQ.normalize`) for an input within
  `4·10⁻⁶` of a real `P` with `| |P|² - 1 | ≤ 10⁻⁶` (the `is_zero` branch is not taken),
  `β = 1.3·10⁻⁵`;
* `update_attitude_target_near`: the whole step against `normalize(T ⊗ expQ(ω dt))`,
  `β = 1.3·10⁻⁵`, for `|T_i| ≤ 1.01`, `| |T|² - 1 | ≤ 10⁻⁶`, `|ω_i| ≤ 5`, `0 ≤ dt ≤ 0.1`.

The product error (`8·10⁻⁷`) and the `expQ` error moved through the product (`4.04 · 7·10⁻⁷`)
stay below `4·10⁻⁶`; `|T ⊗ E|² = |T|² |E|²` and `|expQ V|² = 1` keep the unit condition. In
`normalize`, the squared length moves by at most `Σ |p_i² - P_i²| ≤ 4·10⁻⁶ (2 Σ|P_i| + 4·4·10⁻⁶)`,
`Σ|P_i| ≤ 2|P|`, and its square root by half of that.
-/

namespace Contracts.Track.AttQ

open Contracts.Mission AC_Attitude_lib Float.Model UnpackedFloat

noncomputable section

/-! ## The real laws -/

/-- The exponential map of a rotation vector `V`: the unit quaternion of the rotation by `|V|`
about `V/|V|`, `(cos(|V|/2), V/|V| · sin(|V|/2))` (`(1, 0, 0, 0)` at `V = 0`, where Lean's
division by `0` gives `0`). -/
def expQ (V : RV) : RQ :=
  ⟨Real.cos (V.norm / 2), V.x / V.norm * Real.sin (V.norm / 2),
    V.y / V.norm * Real.sin (V.norm / 2), V.z / V.norm * Real.sin (V.norm / 2)⟩

/-- The normalized real quaternion `P / |P|`. -/
def RQ.normalize (P : RQ) : RQ :=
  ⟨P.w / Real.sqrt (RQ.norm2 P), P.x / Real.sqrt (RQ.norm2 P), P.y / Real.sqrt (RQ.norm2 P),
    P.z / Real.sqrt (RQ.norm2 P)⟩

/-! ## Real-analysis and unfolding helpers -/

namespace Upd
/-- The Euclidean norm in space is `1`-Lipschitz. -/
theorem norm3_lip (a b : RV) {D : ℝ} (hD : 0 ≤ D)
    (h : (a.x - b.x) ^ 2 + (a.y - b.y) ^ 2 + (a.z - b.z) ^ 2 ≤ D ^ 2) :
    |a.norm - b.norm| ≤ D := by
  have hs2 := norm_sq a
  have hr2 := norm_sq b
  have hs0 : 0 ≤ a.norm := Real.sqrt_nonneg _
  have hr0 : 0 ≤ b.norm := Real.sqrt_nonneg _
  have hcs : a.x * b.x + a.y * b.y + a.z * b.z ≤ a.norm * b.norm := by
    have h1 : (a.x * b.x + a.y * b.y + a.z * b.z) ^ 2 ≤ (a.norm * b.norm) ^ 2 := by
      rw [mul_pow, hs2, hr2]
      nlinarith [sq_nonneg (a.x * b.y - a.y * b.x), sq_nonneg (a.x * b.z - a.z * b.x),
        sq_nonneg (a.y * b.z - a.z * b.y)]
    exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
  have : (a.norm - b.norm) ^ 2 ≤ D ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' this hD |> abs_le.2

theorem sq_le_of_abs {d c : ℝ} (h : |d| ≤ c) : d ^ 2 ≤ c ^ 2 := by
  have := abs_nonneg d
  rw [← sq_abs]; exact pow_le_pow_left₀ this h 2

/-- Componentwise errors `u |V_i| + τ` give a length error `u |V| + 3τ`. -/
theorem vec_close {v V : RV}
    (hx : |v.x - V.x| ≤ 1 / 16777216 * |V.x| + 1 / 2 ^ 150)
    (hy : |v.y - V.y| ≤ 1 / 16777216 * |V.y| + 1 / 2 ^ 150)
    (hz : |v.z - V.z| ≤ 1 / 16777216 * |V.z| + 1 / 2 ^ 150) :
    |v.norm - V.norm| ≤ 1 / 16777216 * V.norm + 3 / 2 ^ 150 := by
  have hN := norm_sq V
  have h1 := abs_le_norm_x V
  have h2 := abs_le_norm_y V
  have h3 := abs_le_norm_z V
  have hN0 : 0 ≤ V.norm := Real.sqrt_nonneg _
  apply norm3_lip v V (by positivity)
  have e1 := sq_le_of_abs hx
  have e2 := sq_le_of_abs hy
  have e3 := sq_le_of_abs hz
  have s : |V.x| ^ 2 + |V.y| ^ 2 + |V.z| ^ 2 = V.norm ^ 2 := by
    rw [sq_abs, sq_abs, sq_abs, hN]
  have a1 := abs_nonneg V.x
  have a2 := abs_nonneg V.y
  have a3 := abs_nonneg V.z
  nlinarith

/-- The computed angle against the true one: `|θ - N| ≤ 3.502 u N + 2⁻⁵⁹`. -/
theorem theta_close {θ n N : ℝ} (hN0 : 0 ≤ N)
    (hθ : |θ - n| ≤ 2501 / 1000 * (1 / 16777216) * n + 1 / 2 ^ 60)
    (hn : |n - N| ≤ 1 / 16777216 * N + 3 / 2 ^ 150) :
    |θ - N| ≤ 3502 / 1000 * (1 / 16777216) * N + 1 / 2 ^ 59 := by
  have a := abs_le.1 hθ
  have b := abs_le.1 hn
  rw [abs_le]; constructor <;> nlinarith

theorem abs_div_le_one {a N : ℝ} (h : |a| ≤ N) : |a / N| ≤ 1 := by
  rcases (abs_nonneg a |>.trans h).eq_or_lt with h0 | h0
  · rw [← h0, div_zero, abs_zero]; norm_num
  · rw [abs_div, abs_of_pos h0, div_le_one h0]; exact h

/-- The `is_zero(θ)` branch: `(1, 0, 0, 0)` against `expQ`. -/
theorem zero_comp {Vi N : ℝ} (hN : N ≤ 12 / 10 ^ 8) (hVi : |Vi| ≤ N) :
    |1 - Real.cos (N / 2)| ≤ 1 / 10 ^ 7 ∧ |0 - Vi / N * Real.sin (N / 2)| ≤ 1 / 10 ^ 7 := by
  have hN0 : 0 ≤ N := (abs_nonneg _).trans hVi
  have hs : |Real.sin (N / 2)| ≤ 6 / 10 ^ 8 := by
    refine Real.abs_sin_le_abs.trans ?_
    rw [abs_of_nonneg (by linarith)]; linarith
  constructor
  · have hc1 := Real.cos_le_one (N / 2)
    have hc2 := @Real.one_sub_sq_div_two_le_cos (N / 2)
    rw [abs_le]; constructor <;> nlinarith
  · rw [zero_sub, abs_neg, abs_mul]
    calc |Vi / N| * |Real.sin (N / 2)| ≤ 1 * (6 / 10 ^ 8) :=
          mul_le_mul (abs_div_le_one hVi) hs (abs_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num

/-- The scalar part in the generic branch. -/
theorem cos_comp {θ N : ℝ} (hN2 : N ≤ 2)
    (hθ : |θ - N| ≤ 3502 / 1000 * (1 / 16777216) * N + 1 / 2 ^ 59) :
    |Real.cos (θ / 2) - Real.cos (N / 2)| ≤ 21 / 10 ^ 8 := by
  refine (Real.abs_cos_sub_cos_le _ _).trans ?_
  rw [show θ / 2 - N / 2 = (θ - N) / 2 by ring, abs_div, abs_two]
  have : 3502 / 1000 * (1 / 16777216) * N ≤ 3502 / 1000 * (1 / 16777216) * 2 := by gcongr
  norm_num at this ⊢; linarith

/-- The direction error: `|v_i/n - V_i/N| ≤ 2.001 u`. -/
theorem dir_close {vi Vi n N : ℝ} (hN : 1 / 2 ^ 24 ≤ N) (hVi : |Vi| ≤ N)
    (hvi : |vi - Vi| ≤ 1 / 16777216 * |Vi| + 1 / 2 ^ 150)
    (hn : |n - N| ≤ 1 / 16777216 * N + 3 / 2 ^ 150) :
    |vi / n - Vi / N| ≤ 2001 / 1000 * (1 / 16777216) := by
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hnlo := (abs_le.1 hn).1
  have hnp : 0 < n := by norm_num at hnlo hN ⊢; nlinarith
  rw [show vi / n - Vi / N = ((vi - Vi) + Vi / N * (N - n)) / n by field_simp; ring,
    abs_div, abs_of_pos hnp, div_le_iff₀ hnp]
  have h1 := abs_div_le_one hVi
  have h2 : |Vi / N * (N - n)| ≤ 1 / 16777216 * N + 3 / 2 ^ 150 := by
    rw [abs_mul, abs_sub_comm]
    calc |Vi / N| * |n - N| ≤ 1 * (1 / 16777216 * N + 3 / 2 ^ 150) :=
          mul_le_mul h1 hn (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have h3 := abs_add_le (vi - Vi) (Vi / N * (N - n))
  have h4 : 1 / 16777216 * |Vi| ≤ 1 / 16777216 * N := by gcongr
  have key : 2 / 16777216 * N + 4 / 2 ^ 150 ≤ 2001 / 1000 * (1 / 16777216) * n := by
    norm_num at hnlo hN ⊢; linarith
  linarith

/-- A vector component in the generic branch. -/
theorem vec_comp {vi Vi n N θ ai : ℝ} (hN : 1 / 2 ^ 24 ≤ N) (hN2 : N ≤ 2) (hVi : |Vi| ≤ N)
    (hvi : |vi - Vi| ≤ 1 / 16777216 * |Vi| + 1 / 2 ^ 150)
    (hn : |n - N| ≤ 1 / 16777216 * N + 3 / 2 ^ 150)
    (hθ : |θ - N| ≤ 3502 / 1000 * (1 / 16777216) * N + 1 / 2 ^ 59)
    (hvin : |vi| ≤ n)
    (ha : |ai - vi / n| ≤ 3503 / 1000 * (1 / 16777216) * (|vi| / n) + 1 / 2 ^ 150) :
    |ai * Real.sin (θ / 2) - Vi / N * Real.sin (N / 2)| ≤ 54 / 10 ^ 8 := by
  have hNp : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hnp : 0 < n := by
    have := (abs_le.1 hn).1; norm_num at this hN ⊢; nlinarith
  have hvn : |vi| / n ≤ 1 := by rw [div_le_one hnp]; exact hvin
  have hd := dir_close hN hVi hvi hn
  have ha' : |ai - Vi / N| ≤ 3503 / 1000 * (1 / 16777216) + 1 / 2 ^ 150 +
      2001 / 1000 * (1 / 16777216) := by
    have : 3503 / 1000 * (1 / 16777216) * (|vi| / n) ≤ 3503 / 1000 * (1 / 16777216) * 1 := by
      gcongr
    have := abs_sub_le ai (vi / n) (Vi / N)
    linarith
  have hs : |Real.sin (θ / 2) - Real.sin (N / 2)| ≤ 3502 / 1000 * (1 / 16777216) + 1 / 2 ^ 60 := by
    refine (Real.abs_sin_sub_sin_le _ _).trans ?_
    rw [show θ / 2 - N / 2 = (θ - N) / 2 by ring, abs_div, abs_two]
    have : 3502 / 1000 * (1 / 16777216) * N ≤ 3502 / 1000 * (1 / 16777216) * 2 := by gcongr
    norm_num at this hθ ⊢; linarith
  have e1 : |(ai - Vi / N) * Real.sin (θ / 2)| ≤
      3503 / 1000 * (1 / 16777216) + 1 / 2 ^ 150 + 2001 / 1000 * (1 / 16777216) := by
    rw [abs_mul]
    calc _ ≤ (3503 / 1000 * (1 / 16777216) + 1 / 2 ^ 150 + 2001 / 1000 * (1 / 16777216)) * 1 :=
          mul_le_mul ha' (Real.abs_sin_le_one _) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e2 : |Vi / N * (Real.sin (θ / 2) - Real.sin (N / 2))| ≤
      3502 / 1000 * (1 / 16777216) + 1 / 2 ^ 60 := by
    rw [abs_mul]
    calc _ ≤ 1 * (3502 / 1000 * (1 / 16777216) + 1 / 2 ^ 60) :=
          mul_le_mul (abs_div_le_one hVi) hs (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have := abs_add_le ((ai - Vi / N) * Real.sin (θ / 2)) (Vi / N * (Real.sin (θ / 2) - Real.sin (N / 2)))
  rw [show (ai - Vi / N) * Real.sin (θ / 2) + Vi / N * (Real.sin (θ / 2) - Real.sin (N / 2)) =
    ai * Real.sin (θ / 2) - Vi / N * Real.sin (N / 2) by ring] at this
  norm_num at e1 e2 this ⊢; linarith

theorem fav_zero (s : Quaternion.State) (v : Vector3f.State)
    (h : is_zero_float (Vector3f.length v) = true) :
    (Quaternion.from_axis_angle_Vector3f s v).q1 = 1.0 ∧ (Quaternion.from_axis_angle_Vector3f s v).q2 = 0.0 ∧
    (Quaternion.from_axis_angle_Vector3f s v).q3 = 0.0 ∧ (Quaternion.from_axis_angle_Vector3f s v).q4 = 0.0 := by
  simp [Quaternion.from_axis_angle_Vector3f, h]

theorem fav_nz (s : Quaternion.State) (v : Vector3f.State)
    (h : is_zero_float (Vector3f.length v) = false) :
    Quaternion.from_axis_angle_Vector3f s v = Quaternion.from_axis_angle_Vector3f_float s
      (Vector3f.op_div_assign v (Vector3f.length v)).1 (Vector3f.length v) := by
  simp [Quaternion.from_axis_angle_Vector3f, h]

theorem mul_assign_eq (a b : Quaternion.State) :
    (Quaternion.op_mul_assign a b).1 = Quaternion.op_mul_Quaternion a b := rfl

theorem upd_eq (s : AC_AttitudeControl_Multi.State) :
    (AC_AttitudeControl_Multi.update_attitude_target s)._attitude_target =
      Quaternion.normalize (Quaternion.op_mul_Quaternion s._attitude_target
        (Quaternion.from_axis_angle_Vector3f Quaternion.init_void
          (Vector3f.op_mul_float s._ang_vel_target_rads s._dt_s))) := rfl

theorem omf_x (w : Vector3f.State) (d : Float32) : (Vector3f.op_mul_float w d).x = w.x * d := rfl
theorem omf_y (w : Vector3f.State) (d : Float32) : (Vector3f.op_mul_float w d).y = w.y * d := rfl
theorem omf_z (w : Vector3f.State) (d : Float32) : (Vector3f.op_mul_float w d).z = w.z * d := rfl

theorem qlen_eq (q : Quaternion.State) : Quaternion.length q =
    Float32.sqrt (q.q1 * q.q1 + q.q2 * q.q2 + q.q3 * q.q3 + q.q4 * q.q4) := rfl

theorem nrm_eq (q : Quaternion.State) (h : is_zero_float (Quaternion.length q) = false) :
    (Quaternion.normalize q).q1 = q.q1 * ((1.0 : Float32) / Quaternion.length q) ∧
    (Quaternion.normalize q).q2 = q.q2 * ((1.0 : Float32) / Quaternion.length q) ∧
    (Quaternion.normalize q).q3 = q.q3 * ((1.0 : Float32) / Quaternion.length q) ∧
    (Quaternion.normalize q).q4 = q.q4 * ((1.0 : Float32) / Quaternion.length q) := by
  simp [Quaternion.normalize, h]

end Upd

open Upd

/-! ## `from_axis_angle(v)` against the exponential map -/

namespace Upd

theorem norm_le_two {V : RV} (bx : |V.x| ≤ 1) (by' : |V.y| ≤ 1) (bz : |V.z| ≤ 1) : V.norm ≤ 2 := by
  rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  have := sq_le_of_abs bx; have := sq_le_of_abs by'; have := sq_le_of_abs bz
  nlinarith

theorem comp_le {a : Float32} {A : ℝ} (hA : |A| ≤ 1)
    (h : |a.toReal - A| ≤ 1 / 16777216 * |A| + 1 / 2 ^ 150) : |a.toReal| ≤ 1000 := by
  have := abs_sub_abs_le_abs_sub a.toReal A
  have : 1 / 16777216 * |A| ≤ 1 / 16777216 * 1 := by gcongr
  norm_num at *; linarith

end Upd

set_option maxHeartbeats 1000000 in
/-- **`from_axis_angle(v)`** (the rotation vector form: `θ = |v|`, the identity when
`is_zero(θ)`, otherwise `from_axis_angle(v/θ, θ)`) of a float vector `v` each of whose components
is one rounding (`u |V_i| + 2⁻¹⁵⁰`) away from a real `V` with `|V_i| ≤ 1`: every component is
finite and within `7·10⁻⁷` of the exponential map `expQ V`. -/
theorem expV_near (hL : LibmSpec) (s : Quaternion.State) {v : Vector3f.State} {V : RV}
    (fx : v.x.IsFinite) (fy : v.y.IsFinite) (fz : v.z.IsFinite)
    (bx : |V.x| ≤ 1) (by' : |V.y| ≤ 1) (bz : |V.z| ≤ 1)
    (ex : |v.x.toReal - V.x| ≤ 1 / 16777216 * |V.x| + 1 / 2 ^ 150)
    (ey : |v.y.toReal - V.y| ≤ 1 / 16777216 * |V.y| + 1 / 2 ^ 150)
    (ez : |v.z.toReal - V.z| ≤ 1 / 16777216 * |V.z| + 1 / 2 ^ 150) :
    QA (Quaternion.from_axis_angle_Vector3f s v) (expQ V) (7 / 10 ^ 7) := by
  have hN2 := norm_le_two bx by' bz
  have hN0 : 0 ≤ V.norm := Real.sqrt_nonneg _
  obtain ⟨fL, eL⟩ := len_near fx fy fz (comp_le bx ex) (comp_le by' ey) (comp_le bz ez)
  have hnN := vec_close (v := vv v) ex ey ez
  have hθN := theta_close hN0 eL hnN
  have hn0 : 0 ≤ (vv v).norm := Real.sqrt_nonneg _
  set θ := Vector3f.length v with hθdef
  set n := (vv v).norm with hndef
  set N := V.norm with hNdef
  have eL' := abs_le.1 eL
  have hθN' := abs_le.1 hθN
  unfold QA
  cases hz : is_zero_float θ with
  | true =>
    have h0 := (Att.isZero_iff fL).1 hz
    rw [two_pow_m23] at h0
    have hN : N ≤ 12 / 10 ^ 8 := by
      have := (abs_lt.1 h0).2; norm_num at hθN' this ⊢; nlinarith
    obtain ⟨z1, z2, z3, z4⟩ := fav_zero s v hz
    rw [z1, z2, z3, z4]
    obtain ⟨c1, cx⟩ := zero_comp hN (abs_le_norm_x V)
    obtain ⟨-, cy⟩ := zero_comp hN (abs_le_norm_y V)
    obtain ⟨-, cz⟩ := zero_comp hN (abs_le_norm_z V)
    refine ⟨⟨f32_isFinite_1p0, ?_⟩, ⟨f32_isFinite_0p0, ?_⟩, ⟨f32_isFinite_0p0, ?_⟩,
      ⟨f32_isFinite_0p0, ?_⟩⟩
    · rw [f32_toReal_1p0]; exact c1.trans (by norm_num)
    · rw [f32_toReal_0p0]; exact cx.trans (by norm_num)
    · rw [f32_toReal_0p0]; exact cy.trans (by norm_num)
    · rw [f32_toReal_0p0]; exact cz.trans (by norm_num)
  | false =>
    rw [fav_nz s v hz]
    have hθ23 : 2 ^ (-23 : ℤ) ≤ |θ.toReal| := by
      by_contra hc; push Not at hc
      rw [(Att.isZero_iff fL).2 hc] at hz; exact absurd hz (by decide)
    rw [two_pow_m23] at hθ23
    have hθpos : 1 / 8388608 ≤ θ.toReal := by
      rcases abs_cases θ.toReal with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith
      · exfalso; norm_num at eL'; nlinarith
    have hn24 : 1 / 2 ^ 24 ≤ n := by norm_num at eL' ⊢; nlinarith
    have hN24 : 1 / 2 ^ 24 ≤ N := by norm_num at hθN' ⊢; nlinarith
    have hnp : 0 < n := lt_of_lt_of_le (by norm_num) hn24
    obtain ⟨a1f, a1⟩ := ndiv fx fL hn24 eL (abs_le_norm_x (vv v))
    obtain ⟨a2f, a2⟩ := ndiv fy fL hn24 eL (abs_le_norm_y (vv v))
    obtain ⟨a3f, a3⟩ := ndiv fz fL hn24 eL (abs_le_norm_z (vv v))
    have bnd : ∀ x : Float32, |x.toReal| ≤ n → |(x / θ).toReal - x.toReal / n| ≤
        3503 / 1000 * (1 / 16777216) * (|x.toReal| / n) + 1 / 2 ^ 150 → |(x / θ).toReal| ≤ 1.01 := by
      intro x hxn hx
      have h1 : |x.toReal / n| ≤ 1 := abs_div_le_one hxn
      have h2 : |x.toReal| / n ≤ 1 := by rw [div_le_one hnp]; exact hxn
      have h3 : 3503 / 1000 * (1 / 16777216) * (|x.toReal| / n) ≤ 3503 / 1000 * (1 / 16777216) * 1 := by
        gcongr
      have := abs_sub_abs_le_abs_sub (x / θ).toReal (x.toReal / n)
      norm_num at *; linarith
    have hVB : VB (Vector3f.op_div_assign v θ).1 1.01 :=
      ⟨B32.of_exact a1f (bnd _ (abs_le_norm_x (vv v)) a1),
        B32.of_exact a2f (bnd _ (abs_le_norm_y (vv v)) a2),
        B32.of_exact a3f (bnd _ (abs_le_norm_z (vv v)) a3)⟩
    have hθ1000 : |θ.toReal| ≤ 1000 := by
      rw [abs_of_pos (by linarith)]; norm_num at eL' ⊢; nlinarith
    obtain ⟨q1, q2, q3, q4⟩ := axisAngle_near hL s hVB fL hθ1000
    refine ⟨(ashift q1 (cos_comp hN2 hθN)).mono (by norm_num),
      (ashift (d := 54 / 10 ^ 8) q2 ?_).mono (by norm_num),
      (ashift (d := 54 / 10 ^ 8) q3 ?_).mono (by norm_num),
      (ashift (d := 54 / 10 ^ 8) q4 ?_).mono (by norm_num)⟩
    · exact vec_comp hN24 hN2 (abs_le_norm_x V) ex hnN hθN (abs_le_norm_x (vv v)) a1
    · exact vec_comp hN24 hN2 (abs_le_norm_y V) ey hnN hθN (abs_le_norm_y (vv v)) a2
    · exact vec_comp hN24 hN2 (abs_le_norm_z V) ez hnN hθN (abs_le_norm_z (vv v)) a3

/-! ## `normalize` -/

namespace Upd

theorem sqrt_lo : (999999 / 10 ^ 6 : ℝ) ≤ Real.sqrt (1 - 1 / 10 ^ 6) := by
  rw [show (999999 / 10 ^ 6 : ℝ) = Real.sqrt ((999999 / 10 ^ 6) ^ 2) by
    rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- `√` is `1/m`-Lipschitz where `√a + √b ≥ m`. -/
theorem sqrt_lip2 {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : 0 < m)
    (hmb : m ≤ Real.sqrt a + Real.sqrt b) :
    |Real.sqrt a - Real.sqrt b| ≤ |a - b| / m := by
  rw [le_div_iff₀ hm]
  have key : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt a + Real.sqrt b), ← abs_mul]
    congr 1
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb; nlinarith
  calc |Real.sqrt a - Real.sqrt b| * m ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul_of_nonneg_left hmb (abs_nonneg _)
    _ = _ := key

/-- `Σ |P_i| ≤ 2 |P|` for a near-unit quaternion. -/
theorem sum_abs_le {P : RQ} (hu : RQ.norm2 P ≤ 1 + 1 / 10 ^ 6) :
    |P.w| + |P.x| + |P.y| + |P.z| ≤ 2000001 / 10 ^ 6 := by
  simp only [RQ.norm2] at hu
  have h4 : (|P.w| + |P.x| + |P.y| + |P.z|) ^ 2 ≤ (2000001 / 10 ^ 6) ^ 2 := by
    have := sq_abs P.w; have := sq_abs P.x; have := sq_abs P.y; have := sq_abs P.z
    nlinarith [sq_nonneg (|P.w| - |P.x|), sq_nonneg (|P.w| - |P.y|), sq_nonneg (|P.w| - |P.z|),
      sq_nonneg (|P.x| - |P.y|), sq_nonneg (|P.x| - |P.z|), sq_nonneg (|P.y| - |P.z|)]
  exact (abs_le_of_sq_le_sq' h4 (by norm_num)).2

theorem sq_dev {p P e : ℝ} (h : |p - P| ≤ e) : |p * p - P * P| ≤ e * (2 * |P| + e) := by
  rw [show p * p - P * P = (p - P) * (p + P) by ring, abs_mul]
  have : |p + P| ≤ 2 * |P| + e := by
    have := abs_add_le (p - P) (2 * P)
    rw [show p - P + 2 * P = p + P by ring, abs_mul, abs_two] at this; linarith
  exact mul_le_mul h this (abs_nonneg _) ((abs_nonneg _).trans h)

/-- The squared length of `p` against that of `P`: within `1.6001·10⁻⁵`. -/
theorem norm2_dev {p1 p2 p3 p4 : ℝ} {P : RQ} (hu : RQ.norm2 P ≤ 1 + 1 / 10 ^ 6)
    (h1 : |p1 - P.w| ≤ 4 / 10 ^ 6) (h2 : |p2 - P.x| ≤ 4 / 10 ^ 6) (h3 : |p3 - P.y| ≤ 4 / 10 ^ 6)
    (h4 : |p4 - P.z| ≤ 4 / 10 ^ 6) :
    |p1 * p1 + p2 * p2 + p3 * p3 + p4 * p4 - RQ.norm2 P| ≤ 16001 / 10 ^ 9 := by
  have hs := sum_abs_le hu
  have d1 := sq_dev h1; have d2 := sq_dev h2; have d3 := sq_dev h3; have d4 := sq_dev h4
  rw [show p1 * p1 + p2 * p2 + p3 * p3 + p4 * p4 - RQ.norm2 P = (p1 * p1 - P.w * P.w) +
    (p2 * p2 - P.x * P.x) + (p3 * p3 - P.y * P.y) + (p4 * p4 - P.z * P.z) by
      simp only [RQ.norm2]; ring]
  have t1 := abs_add_le ((p1 * p1 - P.w * P.w) + (p2 * p2 - P.x * P.x) + (p3 * p3 - P.y * P.y))
    (p4 * p4 - P.z * P.z)
  have t2 := abs_add_le ((p1 * p1 - P.w * P.w) + (p2 * p2 - P.x * P.x)) (p3 * p3 - P.y * P.y)
  have t3 := abs_add_le (p1 * p1 - P.w * P.w) (p2 * p2 - P.x * P.x)
  nlinarith

theorem abs_le_of_A32 {x : Float32} {r e : ℝ} (h : A32 x r e) (hr : |r| ≤ 1.01)
    (he : e ≤ 4 / 10 ^ 6) : |x.toReal| ≤ 102 / 100 := by
  have := h.abs_le; linarith

end Upd

set_option maxHeartbeats 1000000 in
/-- **`Quaternion::normalize`** of a float quaternion `p` within `4·10⁻⁶` per component of a
real `P` with components at most `1.01` and `| |P|² - 1 | ≤ 10⁻⁶`: the `is_zero(|p|)` branch is
not taken, and every component of the result is finite and within `1.3·10⁻⁵` of `P / |P|`. -/
theorem normalize_near {p : Quaternion.State} {P : RQ} (h : QA p P (4 / 10 ^ 6))
    (hP : |P.w| ≤ 1.01 ∧ |P.x| ≤ 1.01 ∧ |P.y| ≤ 1.01 ∧ |P.z| ≤ 1.01)
    (hu : |RQ.norm2 P - 1| ≤ 1 / 10 ^ 6) :
    QA (Quaternion.normalize p) (RQ.normalize P) (13 / 10 ^ 6) := by
  have b1 : B32 p.q1 P.w (4 / 10 ^ 6) 1.01 := ⟨h.1, hP.1⟩
  have b2 : B32 p.q2 P.x (4 / 10 ^ 6) 1.01 := ⟨h.2.1, hP.2.1⟩
  have b3 : B32 p.q3 P.y (4 / 10 ^ 6) 1.01 := ⟨h.2.2.1, hP.2.2.1⟩
  have b4 : B32 p.q4 P.z (4 / 10 ^ 6) 1.01 := ⟨h.2.2.2, hP.2.2.2⟩
  have x1 := B32.of_exact h.1.1 (abs_le_of_A32 h.1 hP.1 le_rfl)
  have x2 := B32.of_exact h.2.1.1 (abs_le_of_A32 h.2.1 hP.2.1 le_rfl)
  have x3 := B32.of_exact h.2.2.1.1 (abs_le_of_A32 h.2.2.1 hP.2.2.1 le_rfl)
  have x4 := B32.of_exact h.2.2.2.1 (abs_le_of_A32 h.2.2.2 hP.2.2.2 le_rfl)
  -- the rounded sum of squares against the exact one of the float values
  have hS := (badd (badd (badd (bmul x1 x1 (by norm_num)) (bmul x2 x2 (by norm_num)) (by norm_num))
    (bmul x3 x3 (by norm_num)) (by norm_num)) (bmul x4 x4 (by norm_num)) (by norm_num)).1.mono
    (e' := 81 / 10 ^ 8) (by norm_num)
  have hu' := abs_le.1 hu
  have hdev := norm2_dev (by linarith) h.1.2 h.2.1.2 h.2.2.1.2 h.2.2.2.2
  have hS' := ashift hS hdev
  set S := p.q1 * p.q1 + p.q2 * p.q2 + p.q3 * p.q3 + p.q4 * p.q4 with hSdef
  have hSe := abs_le.1 hS'.2
  have h0 : 0 ≤ S.toReal := by norm_num at hSe; linarith
  have hmx : S.toReal ≤ maxFinite32 := by
    have : (2 : ℝ) ≤ capF := by simp only [capF]; norm_num
    norm_num at hSe; linarith [capF_le_max32]
  obtain ⟨fM, eM⟩ := Float32.sqrt_err_all hS'.1 h0 hmx
  rw [two_pow_m24, two_pow_m150] at eM
  rw [← qlen_eq] at fM eM
  -- `√S` and `√|P|²` are both near `1`
  have hN0 : 0 ≤ RQ.norm2 P := by linarith
  have hsN : 999999 / 10 ^ 6 ≤ Real.sqrt (RQ.norm2 P) :=
    sqrt_lo.trans (Real.sqrt_le_sqrt (by linarith))
  have hsS : 99999 / 10 ^ 5 ≤ Real.sqrt S.toReal := by
    rw [show (99999 / 10 ^ 5 : ℝ) = Real.sqrt ((99999 / 10 ^ 5) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num at hSe ⊢; linarith)
  have hsS1 : Real.sqrt S.toReal ≤ 10001 / 10 ^ 4 := by
    rw [show (10001 / 10 ^ 4 : ℝ) = Real.sqrt ((10001 / 10 ^ 4) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num at hSe ⊢; linarith)
  have hsN1 : Real.sqrt (RQ.norm2 P) ≤ 10001 / 10 ^ 4 := by
    rw [show (10001 / 10 ^ 4 : ℝ) = Real.sqrt ((10001 / 10 ^ 4) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num at hu' ⊢; linarith)
  have hlip := sqrt_lip2 h0 hN0 (m := 199998 / 10 ^ 5) (by norm_num) (by linarith)
  have hlip' : |S.toReal - RQ.norm2 P| / (199998 / 10 ^ 5) ≤
      (81 / 10 ^ 8 + 16001 / 10 ^ 9) / (199998 / 10 ^ 5) := by gcongr; exact hS'.2
  have hM : B32 (Quaternion.length p) (Real.sqrt (RQ.norm2 P)) (85 / 10 ^ 7) (10001 / 10 ^ 4) := by
    refine ⟨⟨fM, ?_⟩, by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hsN1⟩
    have := abs_sub_le (Quaternion.length p).toReal (Real.sqrt S.toReal) (Real.sqrt (RQ.norm2 P))
    have : 1 / 16777216 * Real.sqrt S.toReal ≤ 1 / 16777216 * (10001 / 10 ^ 4) := by gcongr
    norm_num at hlip' this eM ⊢; linarith
  have hlo : 999999 / 10 ^ 6 ≤ |Real.sqrt (RQ.norm2 P)| := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hsN
  have hone : B32 (1.0 : Float32) 1 0 1 :=
    ⟨⟨f32_isFinite_1p0, by rw [f32_toReal_1p0]; norm_num⟩, by norm_num⟩
  have hI := B32.div (mlo := 999999 / 10 ^ 6) (R := 1000002 / 10 ^ 6) (e := 86 / 10 ^ 7)
    hone hM hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnz : is_zero_float (Quaternion.length p) = false := by
    refine Att.isZero_false hM.1.1 ?_
    have := (abs_le.1 hM.1.2).1
    rw [two_pow_m23, abs_of_nonneg (by linarith)]; linarith
  obtain ⟨n1, n2, n3, n4⟩ := nrm_eq p hnz
  unfold QA
  rw [n1, n2, n3, n4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((bmul b1 hI (by norm_num)).1.mono (by norm_num)).congr (mul_one_div _ _)
  · exact ((bmul b2 hI (by norm_num)).1.mono (by norm_num)).congr (mul_one_div _ _)
  · exact ((bmul b3 hI (by norm_num)).1.mono (by norm_num)).congr (mul_one_div _ _)
  · exact ((bmul b4 hI (by norm_num)).1.mono (by norm_num)).congr (mul_one_div _ _)

/-! ## The update -/

namespace Upd

theorem norm2_mul (a b : RQ) : RQ.norm2 (RQ.mul a b) = RQ.norm2 a * RQ.norm2 b := by
  simp only [RQ.norm2, RQ.mul]; ring

theorem expQ_unit (V : RV) : RQ.norm2 (expQ V) = 1 := by
  simp only [RQ.norm2, expQ]
  rcases (Real.sqrt_nonneg (V.x ^ 2 + V.y ^ 2 + V.z ^ 2)).eq_or_lt with h0 | h0
  · have : V.norm = 0 := h0.symm
    rw [this]; simp
  · have hN : 0 < V.norm := h0
    have hs := norm_sq V
    have hu : (V.x / V.norm) ^ 2 + (V.y / V.norm) ^ 2 + (V.z / V.norm) ^ 2 = 1 := by
      rw [div_pow, div_pow, div_pow, ← add_div, ← add_div, div_eq_one_iff_eq (by positivity)]
      exact hs.symm
    have := Real.sin_sq_add_cos_sq (V.norm / 2)
    calc Real.cos (V.norm / 2) ^ 2 + (V.x / V.norm * Real.sin (V.norm / 2)) ^ 2 +
          (V.y / V.norm * Real.sin (V.norm / 2)) ^ 2 + (V.z / V.norm * Real.sin (V.norm / 2)) ^ 2 =
        Real.cos (V.norm / 2) ^ 2 + ((V.x / V.norm) ^ 2 + (V.y / V.norm) ^ 2 + (V.z / V.norm) ^ 2) *
          Real.sin (V.norm / 2) ^ 2 := by ring
      _ = 1 := by rw [hu]; linarith

theorem expQ_le (V : RV) : |(expQ V).w| ≤ 1 ∧ |(expQ V).x| ≤ 1 ∧ |(expQ V).y| ≤ 1 ∧
    |(expQ V).z| ≤ 1 := by
  have k : ∀ c : ℝ, |c| ≤ V.norm → |c / V.norm * Real.sin (V.norm / 2)| ≤ 1 := by
    intro c hc
    rw [abs_mul]
    calc |c / V.norm| * |Real.sin (V.norm / 2)| ≤ 1 * 1 :=
          mul_le_mul (abs_div_le_one hc) (Real.abs_sin_le_one _) (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  exact ⟨Real.abs_cos_le_one _, k _ (abs_le_norm_x V), k _ (abs_le_norm_y V), k _ (abs_le_norm_z V)⟩

theorem lip4 {m1 m2 m3 m4 d1 d2 d3 d4 e : ℝ} (k1 : |m1| ≤ 1.01) (k2 : |m2| ≤ 1.01)
    (k3 : |m3| ≤ 1.01) (k4 : |m4| ≤ 1.01) (f1 : |d1| ≤ e) (f2 : |d2| ≤ e) (f3 : |d3| ≤ e)
    (f4 : |d4| ≤ e) : |m1 * d1 + m2 * d2 + m3 * d3 + m4 * d4| ≤ 4 * 1.01 * e := by
  have hp : ∀ m d : ℝ, |m| ≤ 1.01 → |d| ≤ e → |m * d| ≤ 1.01 * e := by
    intro m d hm hd; rw [abs_mul]; exact mul_le_mul hm hd (abs_nonneg _) (by norm_num)
  have := hp m1 d1 k1 f1; have := hp m2 d2 k2 f2; have := hp m3 d3 k3 f3; have := hp m4 d4 k4 f4
  have t3 := abs_add_le (m1 * d1 + m2 * d2 + m3 * d3) (m4 * d4)
  have t4 := abs_add_le (m1 * d1 + m2 * d2) (m3 * d3)
  have t5 := abs_add_le (m1 * d1) (m2 * d2)
  linarith

/-- The Hamilton product is `4.04`-Lipschitz in its second factor (first factor at most `1.01`). -/
theorem mul_lip_right {a b B : RQ} {e : ℝ}
    (ha : |a.w| ≤ 1.01 ∧ |a.x| ≤ 1.01 ∧ |a.y| ≤ 1.01 ∧ |a.z| ≤ 1.01)
    (hb : |b.w - B.w| ≤ e ∧ |b.x - B.x| ≤ e ∧ |b.y - B.y| ≤ e ∧ |b.z - B.z| ≤ e) :
    |(RQ.mul a b).w - (RQ.mul a B).w| ≤ 4 * 1.01 * e ∧
      |(RQ.mul a b).x - (RQ.mul a B).x| ≤ 4 * 1.01 * e ∧
      |(RQ.mul a b).y - (RQ.mul a B).y| ≤ 4 * 1.01 * e ∧
      |(RQ.mul a b).z - (RQ.mul a B).z| ≤ 4 * 1.01 * e := by
  obtain ⟨mw, mx, my, mz⟩ := ha
  obtain ⟨ew, ex, ey, ez⟩ := hb
  have nmx : |-a.x| ≤ 1.01 := by rwa [abs_neg]
  have nmy : |-a.y| ≤ 1.01 := by rwa [abs_neg]
  have nmz : |-a.z| ≤ 1.01 := by rwa [abs_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (RQ.mul a b).w - (RQ.mul a B).w = a.w * (b.w - B.w) + (-a.x) * (b.x - B.x) +
      (-a.y) * (b.y - B.y) + (-a.z) * (b.z - B.z) by simp only [RQ.mul]; ring]
    exact lip4 mw nmx nmy nmz ew ex ey ez
  · rw [show (RQ.mul a b).x - (RQ.mul a B).x = a.w * (b.x - B.x) + a.x * (b.w - B.w) +
      a.y * (b.z - B.z) + (-a.z) * (b.y - B.y) by simp only [RQ.mul]; ring]
    exact lip4 mw mx my nmz ex ew ez ey
  · rw [show (RQ.mul a b).y - (RQ.mul a B).y = a.w * (b.y - B.y) + (-a.x) * (b.z - B.z) +
      a.y * (b.w - B.w) + a.z * (b.x - B.x) by simp only [RQ.mul]; ring]
    exact lip4 mw nmx my mz ey ez ew ex
  · rw [show (RQ.mul a b).z - (RQ.mul a B).z = a.w * (b.z - B.z) + a.x * (b.y - B.y) +
      (-a.y) * (b.x - B.x) + a.z * (b.w - B.w) by simp only [RQ.mul]; ring]
    exact lip4 mw mx nmy mz ez ey ex ew

theorem abs_le_of_norm2 {P : RQ} (h : RQ.norm2 P ≤ 1 + 1 / 10 ^ 6) :
    |P.w| ≤ 1.01 ∧ |P.x| ≤ 1.01 ∧ |P.y| ≤ 1.01 ∧ |P.z| ≤ 1.01 := by
  simp only [RQ.norm2] at h
  have k : ∀ c : ℝ, c ^ 2 ≤ 1.01 ^ 2 → |c| ≤ 1.01 := fun c hc =>
    abs_le_of_sq_le_sq' hc (by norm_num) |> abs_le.2
  refine ⟨k _ ?_, k _ ?_, k _ ?_, k _ ?_⟩ <;>
    nlinarith [sq_nonneg P.w, sq_nonneg P.x, sq_nonneg P.y, sq_nonneg P.z]

/-- One rounded product `ω_i * dt`: finite, within `u |ω_i dt| + 2⁻¹⁵⁰`, `|ω_i dt| ≤ 1/2`. -/
theorem rate_dt {w d : Float32} (hw : w.IsFinite) (hd : d.IsFinite) (bw : |w.toReal| ≤ 5)
    (bd : |d.toReal| ≤ 1 / 10) :
    (w * d).IsFinite ∧ |w.toReal * d.toReal| ≤ 1 ∧
      |(w * d).toReal - w.toReal * d.toReal| ≤ 1 / 16777216 * |w.toReal * d.toReal| + 1 / 2 ^ 150 := by
  have hb : |w.toReal * d.toReal| ≤ 1 := by
    rw [abs_mul]
    calc |w.toReal| * |d.toReal| ≤ 5 * (1 / 10) := mul_le_mul bw bd (abs_nonneg _) (by norm_num)
      _ ≤ 1 := by norm_num
  have hm : |w.toReal * d.toReal| ≤ maxFinite32 := by
    have : (1 : ℝ) ≤ capF := by simp only [capF]; norm_num
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.mul_err_all hw hd hm
  rw [two_pow_m24, two_pow_m150] at he
  exact ⟨hf, hb, he⟩

end Upd

set_option maxHeartbeats 1000000 in
/-- **`update_attitude_target`**: `_attitude_target ← normalize(_attitude_target ⊗
from_axis_angle(ω · dt))` with `ω = _ang_vel_target_rads`, `dt = _dt_s`. For a target `T` with
components at most `1.01` and `| |T|² - 1 | ≤ 10⁻⁶`, finite `|ω_i| ≤ 5` and finite
`0 ≤ dt ≤ 0.1`, every component of the new target is finite and within `1.3·10⁻⁵` of the real
law `normalize(T ⊗ expQ(ω dt))` of the float inputs. -/
theorem update_attitude_target_near (hL : LibmSpec) (s : AC_AttitudeControl_Multi.State)
    (hT : QB s._attitude_target 1.01) (hTu : |RQ.norm2 (qv s._attitude_target) - 1| ≤ 1 / 10 ^ 6)
    (fωx : s._ang_vel_target_rads.x.IsFinite) (fωy : s._ang_vel_target_rads.y.IsFinite)
    (fωz : s._ang_vel_target_rads.z.IsFinite)
    (bωx : |s._ang_vel_target_rads.x.toReal| ≤ 5) (bωy : |s._ang_vel_target_rads.y.toReal| ≤ 5)
    (bωz : |s._ang_vel_target_rads.z.toReal| ≤ 5)
    (fdt : s._dt_s.IsFinite) (hdt0 : 0 ≤ s._dt_s.toReal) (hdt1 : s._dt_s.toReal ≤ 1 / 10) :
    QA (AC_AttitudeControl_Multi.update_attitude_target s)._attitude_target
      (RQ.normalize (RQ.mul (qv s._attitude_target)
        (expQ ⟨s._ang_vel_target_rads.x.toReal * s._dt_s.toReal,
          s._ang_vel_target_rads.y.toReal * s._dt_s.toReal,
          s._ang_vel_target_rads.z.toReal * s._dt_s.toReal⟩))) (13 / 10 ^ 6) := by
  rw [upd_eq]
  set T := s._attitude_target
  set ω := s._ang_vel_target_rads
  set dt := s._dt_s
  set V : RV := ⟨ω.x.toReal * dt.toReal, ω.y.toReal * dt.toReal, ω.z.toReal * dt.toReal⟩ with hV
  have bdt : |dt.toReal| ≤ 1 / 10 := by rw [abs_of_nonneg hdt0]; exact hdt1
  obtain ⟨vxf, vxb, vxe⟩ := rate_dt fωx fdt bωx bdt
  obtain ⟨vyf, vyb, vye⟩ := rate_dt fωy fdt bωy bdt
  obtain ⟨vzf, vzb, vze⟩ := rate_dt fωz fdt bωz bdt
  have hE := expV_near hL Quaternion.init_void (v := Vector3f.op_mul_float ω dt) (V := V)
    vxf vyf vzf vxb vyb vzb vxe vye vze
  set E := Quaternion.from_axis_angle_Vector3f Quaternion.init_void (Vector3f.op_mul_float ω dt)
  have hEB : QB E 1.01 := hE.toQB (expQ_le V) (by norm_num)
  have hm := quat_mul_near hT hEB
  have hTb : |(qv T).w| ≤ 1.01 ∧ |(qv T).x| ≤ 1.01 ∧ |(qv T).y| ≤ 1.01 ∧ |(qv T).z| ≤ 1.01 :=
    ⟨hT.1.2, hT.2.1.2, hT.2.2.1.2, hT.2.2.2.2⟩
  obtain ⟨l1, l2, l3, l4⟩ := mul_lip_right (b := qv E) (B := expQ V) hTb
    ⟨hE.1.2, hE.2.1.2, hE.2.2.1.2, hE.2.2.2.2⟩
  have hP : QA (Quaternion.op_mul_Quaternion T E) (RQ.mul (qv T) (expQ V)) (4 / 10 ^ 6) :=
    ⟨(ashift hm.1 l1).mono (by norm_num), (ashift hm.2.1 l2).mono (by norm_num),
      (ashift hm.2.2.1 l3).mono (by norm_num), (ashift hm.2.2.2 l4).mono (by norm_num)⟩
  have hn : RQ.norm2 (RQ.mul (qv T) (expQ V)) = RQ.norm2 (qv T) := by
    rw [norm2_mul, expQ_unit, mul_one]
  have hu : |RQ.norm2 (RQ.mul (qv T) (expQ V)) - 1| ≤ 1 / 10 ^ 6 := by rw [hn]; exact hTu
  have hPb := abs_le_of_norm2 (P := RQ.mul (qv T) (expQ V)) (by have := (abs_le.1 hu).2; linarith)
  exact normalize_near hP hPb hu

end
end Contracts.Track.AttQ
