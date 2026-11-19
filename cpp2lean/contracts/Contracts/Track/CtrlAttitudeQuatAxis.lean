import Contracts.Track.CtrlAttitudeQuat
import FloatModel.Lit

/-!
# `to_axis_angle` near a small rotation (milestone M4, lemma C8)

`Quaternion::to_axis_angle(v)` computes `l = sqrt(sq(q₂) + sq(q₃) + sq(q₄))`, `v = (q₂, q₃, q₄)`,
and, unless `is_zero(l)`, `v = v / l * wrap_PI(2 · atan2f(l, q₁))`. For a float quaternion within
`1.3·10⁻⁷` per component of the axis–angle quaternion `(cos(φ/2), a sin(φ/2))` of a nearly unit
axis `a` (`| |a|² - 1 | ≤ δ ≤ 10⁻⁴`) and an angle `φ ∈ [0, 1/2]`, the result is within
`3.5·10⁻⁶ + 0.26 δ` per component of the rotation vector `(φ / |a|) a`
(`toAxisAngle_near_gen`; `toAxisAngle_near` at `δ = 10⁻⁴`, `3·10⁻⁵`).

Error budget of the generic branch: `atan2f` within `2⁻²²` of `arg(q₁ + i l) = arctan(l / q₁)`,
the doubling rounded, `wrap_PI` within `1.4·10⁻⁶` (`Ax.wrapPI_near`), the division and product
rounded (`1.98·10⁻⁶` in all, `Ax.angle_W`, `Ax.out_comp`); the real perturbation of
`(c, a σ) ↦ (a σ / |a σ|) · 2 arctan(|a σ| / c)` by `1.3·10⁻⁷` per component and the length
rounding, `1.43·10⁻⁶` (`Ax.gen_real`, written as `p · 2 arctan(l / w) / l` so that no direction is
divided by a small length); and the non-unit axis, `|2 arctan(|a| tan(φ/2)) - φ| ≤ 0.26 δ`
(`Ax.stepA`). The `is_zero(l)` branch returns `(q₂, q₃, q₄)`, and then `φ ≤ 7·10⁻⁷`
(`Ax.zero_real`).
-/

namespace Contracts.Track.AttQ

open Contracts.Mission AC_Attitude_lib Float.Model UnpackedFloat

noncomputable section

namespace Ax

theorem arg_eq {q l : ℝ} (hq : 0 < q) : Complex.arg ⟨q, l⟩ = Real.arctan (l / q) := by
  have h1 : |Complex.arg ⟨q, l⟩| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hq)
  have h2 := Complex.tan_arg (⟨q, l⟩ : ℂ)
  rw [← h2, Real.arctan_tan (by linarith [(abs_lt.1 h1).1]) (abs_lt.1 h1).2]

theorem arctan_lip {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.arctan x - Real.arctan y| ≤ |x - y| := by
  rw [sub_eq_add_neg, ← Real.arctan_neg, Real.arctan_add (by nlinarith)]
  refine Real.abs_arctan_le_abs.trans ?_
  rw [abs_div, abs_of_pos (by nlinarith : (0:ℝ) < 1 - x * -y), div_le_iff₀ (by nlinarith),
    ← sub_eq_add_neg]
  nlinarith [mul_nonneg (abs_nonneg (x - y)) (mul_nonneg hx hy)]

/-- The Euclidean norm in space is `√3`-Lipschitz for the max norm. -/
theorem norm3_lip {p1 p2 p3 P1 P2 P3 ε : ℝ} (h1 : |p1 - P1| ≤ ε) (h2 : |p2 - P2| ≤ ε)
    (h3 : |p3 - P3| ≤ ε) :
    |Real.sqrt (P1 ^ 2 + P2 ^ 2 + P3 ^ 2) - Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2)| ≤
      17321 / 10000 * ε := by
  set s := Real.sqrt (P1 ^ 2 + P2 ^ 2 + P3 ^ 2)
  set r := Real.sqrt (p1 ^ 2 + p2 ^ 2 + p3 ^ 2)
  have hs2 : s ^ 2 = P1 ^ 2 + P2 ^ 2 + P3 ^ 2 := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = p1 ^ 2 + p2 ^ 2 + p3 ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hε : 0 ≤ ε := (abs_nonneg _).trans h1
  have hcs : P1 * p1 + P2 * p2 + P3 * p3 ≤ s * r := by
    have h : (P1 * p1 + P2 * p2 + P3 * p3) ^ 2 ≤ (s * r) ^ 2 := by
      rw [mul_pow, hs2, hr2]
      nlinarith [sq_nonneg (P1 * p2 - P2 * p1), sq_nonneg (P1 * p3 - P3 * p1),
        sq_nonneg (P2 * p3 - P3 * p2)]
    exact abs_le_of_sq_le_sq' h (by positivity) |>.2
  have hsq : (s - r) ^ 2 ≤ 3 * ε ^ 2 := by
    have a1 : (p1 - P1) ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; gcongr
    have a2 : (p2 - P2) ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; gcongr
    have a3 : (p3 - P3) ^ 2 ≤ ε ^ 2 := by rw [← sq_abs]; gcongr
    nlinarith
  have : (s - r) ^ 2 ≤ (17321 / 10000 * ε) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' this (by positivity) |> abs_le.2

/-- Half-angle facts for `φ ∈ [0, 1/2]`. -/
theorem half_facts {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ ≤ 1 / 2) :
    0 ≤ Real.sin (φ / 2) ∧ Real.sin (φ / 2) ≤ 1 / 4 ∧ 31 / 32 ≤ Real.cos (φ / 2) ∧
      Real.cos (φ / 2) ≤ 1 ∧ φ ≤ 2 * (96 / 95) * Real.sin (φ / 2) ∧
      φ = 2 * Real.arctan (Real.sin (φ / 2) / Real.cos (φ / 2)) := by
  have hpi := Real.pi_gt_three
  have hs0 : 0 ≤ Real.sin (φ / 2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : Real.sin (φ / 2) ≤ φ / 2 := Real.sin_le (by linarith)
  have hc0 := @Real.one_sub_sq_div_two_le_cos (φ / 2)
  have hc1 := Real.cos_le_one (φ / 2)
  have hlow : φ / 2 * (95 / 96) ≤ Real.sin (φ / 2) := by
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]; simp
    · have := Real.sin_gt_sub_cube (x := φ / 2) (by linarith)
      have : (φ / 2) ^ 3 / 6 ≤ φ / 2 * (1 / 96) := by
        have : (φ / 2) ^ 2 ≤ 1 / 16 := by nlinarith
        nlinarith
      linarith
  refine ⟨hs0, by linarith, by nlinarith, hc1, by linarith, ?_⟩
  rw [← Real.tan_eq_sin_div_cos, Real.arctan_tan (by linarith) (by linarith)]; ring

/-- Facts on a nearly unit axis. -/
theorem norm_facts {a : RV} {δ : ℝ} (ha : |a.x ^ 2 + a.y ^ 2 + a.z ^ 2 - 1| ≤ δ)
    (hδ : δ ≤ 1 / 10 ^ 4) :
    99 / 100 ≤ a.norm ∧ a.norm ≤ 10001 / 10000 ∧ |a.norm - 1| ≤ δ / (199 / 100) ∧
      |a.x| ≤ a.norm ∧ |a.y| ≤ a.norm ∧ |a.z| ≤ a.norm := by
  have hS := abs_le.1 ha
  have hN0 : 0 ≤ a.norm := Real.sqrt_nonneg _
  have hN2 : a.norm ^ 2 = a.x ^ 2 + a.y ^ 2 + a.z ^ 2 := Real.sq_sqrt (by positivity)
  have hlo : 99 / 100 ≤ a.norm := by nlinarith
  have hhi : a.norm ≤ 10001 / 10000 := by nlinarith
  refine ⟨hlo, hhi, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by norm_num)]
    have e : |a.norm - 1| * (a.norm + 1) = |a.x ^ 2 + a.y ^ 2 + a.z ^ 2 - 1| := by
      rw [← hN2, ← abs_of_pos (show 0 < a.norm + 1 by linarith), ← abs_mul]; congr 1; ring
    nlinarith [abs_nonneg (a.norm - 1)]
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg a.y, sq_nonneg a.z])
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg a.x, sq_nonneg a.z])
  · exact Real.abs_le_sqrt (by nlinarith [sq_nonneg a.y, sq_nonneg a.x])

/-- The angle of the nearly unit quaternion `(c, a σ)`, `2 arctan(N σ / c)`, against `φ`. -/
theorem stepA {ai N σ c φ δ : ℝ} (hai : |ai| ≤ N) (hN : 99 / 100 ≤ N)
    (hN1 : |N - 1| ≤ δ / (199 / 100)) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1 / 4) (hc : 31 / 32 ≤ c)
    (hφ : φ = 2 * Real.arctan (σ / c)) :
    |φ / N * ai - 2 * Real.arctan (N * σ / c) / N * ai| ≤ 26 / 100 * δ := by
  have hNp : 0 < N := by linarith
  have hcp : 0 < c := by linarith
  have hr : |ai / N| ≤ 1 := by rw [abs_div, abs_of_pos hNp, div_le_one hNp]; exact hai
  rw [show φ / N * ai - 2 * Real.arctan (N * σ / c) / N * ai =
    2 * (ai / N) * (Real.arctan (σ / c) - Real.arctan (N * σ / c)) by rw [hφ]; ring, abs_mul,
    abs_mul, abs_two]
  have hδ : 0 ≤ δ := by have := (abs_nonneg _).trans hN1; linarith
  have h1 := arctan_lip (x := σ / c) (y := N * σ / c) (by positivity) (by positivity)
  have h2 : |σ / c - N * σ / c| ≤ δ / (199 / 100) * (1 / 4) / (31 / 32) := by
    rw [show σ / c - N * σ / c = (1 - N) * σ / c by ring, abs_div, abs_mul, abs_of_pos hcp,
      abs_of_nonneg hσ, abs_sub_comm]
    gcongr
  have : 2 * |ai / N| * |Real.arctan (σ / c) - Real.arctan (N * σ / c)| ≤
      2 * 1 * (δ / (199 / 100) * (1 / 4) / (31 / 32)) := by
    gcongr; exact h1.trans h2
  linarith

/-- `|l - N σ|` from the rounded length `l` of `p` and `|p - a σ| ≤ 1.3·10⁻⁷`. -/
theorem len_dev {l n X : ℝ} (hX : X ≤ 2501 / 10000)
    (hl : |l - n| ≤ 2501 / 1000 * (1 / 16777216) * n + 1 / 2 ^ 60)
    (hn : |X - n| ≤ 17321 / 10000 * (13 / 10 ^ 8)) : |l - X| ≤ 263 / 10 ^ 9 := by
  have h1 := abs_le.1 hl; have h2 := abs_le.1 hn
  rw [abs_le]; constructor <;> norm_num at * <;> nlinarith

/-- **Generic branch, real part**: the computed direction `p / l` times the angle
`2 arctan(l / w)` of the perturbed quaternion `(w, p)`, against the exact
`2 arctan(N σ / c) / N · aᵢ` of `(c, a σ)`. -/
theorem gen_real {ai N σ c p w l : ℝ} (hai : |ai| ≤ N) (hN : 99 / 100 ≤ N)
    (hX : N * σ ≤ 2501 / 10000) (hσ : 0 ≤ σ) (hc : 31 / 32 ≤ c)
    (hp : |p - ai * σ| ≤ 13 / 10 ^ 8) (hw : |w - c| ≤ 13 / 10 ^ 8)
    (hl : |l - N * σ| ≤ 263 / 10 ^ 9) (hl0 : 0 < l) :
    |p / l * (2 * Real.arctan (l / w)) - 2 * Real.arctan (N * σ / c) / N * ai| ≤ 143 / 10 ^ 8 := by
  have hw0 : 9687 / 10000 ≤ w := by linarith [(abs_le.1 hw).1]
  have hwp : 0 < w := by linarith
  have hcp : 0 < c := by linarith
  have hNp : 0 < N := by linarith
  have hlw : 0 ≤ l / w := div_nonneg hl0.le hwp.le
  set Θ := 2 * Real.arctan (l / w) with hΘ
  set Φ := 2 * Real.arctan (N * σ / c) with hΦ
  have hT0 : 0 ≤ Θ := by have := Real.arctan_nonneg.2 hlw; linarith
  have hTl : Θ / l ≤ 2 / w := by
    rw [div_le_div_iff₀ hl0 hwp]
    have h := Real.arctan_le_self hlw
    have e : l / w * w = l := by field_simp
    nlinarith
  have hTl0 : 0 ≤ Θ / l := div_nonneg hT0 hl0.le
  have hiw : 2 / w ≤ 2 / (9687 / 10000) := by gcongr
  have hTF : |Θ - Φ| ≤ 2 * |l / w - N * σ / c| := by
    rw [show Θ - Φ = 2 * (Real.arctan (l / w) - Real.arctan (N * σ / c)) by ring, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left (arctan_lip hlw (by positivity)) (by norm_num)
  have hd : |l / w - N * σ / c| ≤ |l - N * σ| / w + N * σ * |c - w| / (w * c) := by
    rw [show l / w - N * σ / c = (l - N * σ) / w + N * σ * (c - w) / (w * c) by field_simp; ring]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hwp, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ N * σ),
      abs_of_pos (by positivity : 0 < w * c)]
  have hd1 : |l - N * σ| / w ≤ 263 / 10 ^ 9 / (9687 / 10000) := by gcongr
  have hd2 : N * σ * |c - w| / (w * c) ≤ 2501 / 10000 * (13 / 10 ^ 8) / (9687 / 10000 * (31 / 32)) := by
    rw [abs_sub_comm]; gcongr
  have hr : |ai / N| ≤ 1 := by rw [abs_div, abs_of_pos hNp, div_le_one hNp]; exact hai
  have key : p / l * Θ - Φ / N * ai =
      (p - ai * σ) * (Θ / l) + (ai / N) * ((N * σ - l) * (Θ / l) + (Θ - Φ)) := by
    field_simp; ring
  rw [key]
  have e1 : |(p - ai * σ) * (Θ / l)| ≤ 13 / 10 ^ 8 * (2 / (9687 / 10000)) := by
    rw [abs_mul, abs_of_nonneg hTl0]; exact mul_le_mul hp (by linarith) hTl0 (by norm_num)
  have e2 : |(N * σ - l) * (Θ / l)| ≤ 263 / 10 ^ 9 * (2 / (9687 / 10000)) := by
    rw [abs_mul, abs_of_nonneg hTl0, abs_sub_comm]; exact mul_le_mul hl (by linarith) hTl0 (by norm_num)
  have e3 : |(ai / N) * ((N * σ - l) * (Θ / l) + (Θ - Φ))| ≤
      1 * (263 / 10 ^ 9 * (2 / (9687 / 10000)) + 2 * (263 / 10 ^ 9 / (9687 / 10000) +
        2501 / 10000 * (13 / 10 ^ 8) / (9687 / 10000 * (31 / 32)))) := by
    rw [abs_mul]
    refine mul_le_mul hr ((abs_add_le _ _).trans ?_) (abs_nonneg _) (by norm_num)
    have := hTF.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
    linarith
  refine (abs_add_le _ _).trans ?_
  norm_num at e1 e3 ⊢; linarith

/-- **`is_zero(l)` branch, real part**: the vector part itself, against `φ/N · aᵢ`. -/
theorem zero_real {ai N σ φ p n : ℝ} (hai : |ai| ≤ N) (hN : 99 / 100 ≤ N) (hφ0 : 0 ≤ φ)
    (hφ : φ ≤ 2 * (96 / 95) * σ) (hpn : |p| ≤ n) (hn : n ≤ 12 / 10 ^ 8)
    (hX : |N * σ - n| ≤ 17321 / 10000 * (13 / 10 ^ 8)) :
    |p - φ / N * ai| ≤ 9 / 10 ^ 7 := by
  have hNp : 0 < N := by linarith
  have hr : |ai / N| ≤ 1 := by rw [abs_div, abs_of_pos hNp, div_le_one hNp]; exact hai
  have hσ : N * σ ≤ 12 / 10 ^ 8 + 17321 / 10000 * (13 / 10 ^ 8) := by
    linarith [(abs_le.1 hX).2]
  have hσ' : σ ≤ (12 / 10 ^ 8 + 17321 / 10000 * (13 / 10 ^ 8)) / (99 / 100) := by
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have e1 : |φ / N * ai| ≤ φ := by
    rw [show φ / N * ai = φ * (ai / N) by ring, abs_mul, abs_of_nonneg hφ0]
    calc φ * |ai / N| ≤ φ * 1 := mul_le_mul_of_nonneg_left hr hφ0
      _ = φ := mul_one φ
  have := abs_sub p (φ / N * ai)
  norm_num at hσ' ⊢; linarith

theorem A32.tri {x : Float32} {r r' e e' : ℝ} (h : A32 x r e) (h' : |r - r'| ≤ e') :
    A32 x r' (e + e') :=
  ⟨h.1, by have := abs_sub_le x.toReal r r'; linarith [h.2]⟩

/-- One output component of the generic branch: `fl(fl(qᵢ / L) · W)`. -/
theorem out_comp {qi L W : Float32} {Θ : ℝ} (hqi : qi.IsFinite) (hLf : L.IsFinite)
    (hl0 : 0 < L.toReal) (hpl : |qi.toReal| ≤ 1000001 / 1000000 * L.toReal)
    (hW : A32 W Θ (191 / 10 ^ 8)) (hΘ : |Θ| ≤ 52 / 100) :
    A32 (qi / L * W) (qi.toReal / L.toReal * Θ) (198 / 10 ^ 8) := by
  have hq1 : |qi.toReal / L.toReal| ≤ 1000001 / 1000000 := by
    rw [abs_div, abs_of_pos hl0, div_le_iff₀ hl0]; exact hpl
  have hm : |qi.toReal / L.toReal| ≤ maxFinite32 := by
    have : (2 : ℝ) ≤ capF := by simp only [capF]; norm_num
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.div_err_all hqi hLf hl0.ne' hm
  rw [two_pow_m24, two_pow_m150] at he
  have hw : A32 (qi / L) (qi.toReal / L.toReal) (6 / 10 ^ 8) := ⟨hf, by
    have : 1 / 16777216 * |qi.toReal / L.toReal| ≤ 1 / 16777216 * (1000001 / 1000000) := by gcongr
    norm_num at this he ⊢; linarith⟩
  have h := A32.mul hw hW (by
    rw [abs_mul]
    have : |qi.toReal / L.toReal| * |Θ| ≤ 1000001 / 1000000 * (52 / 100) :=
      mul_le_mul hq1 hΘ (abs_nonneg _) (by norm_num)
    have : |qi.toReal / L.toReal| * (191 / 10 ^ 8) ≤ 1000001 / 1000000 * (191 / 10 ^ 8) := by gcongr
    have : |Θ| * (6 / 10 ^ 8) ≤ 52 / 100 * (6 / 10 ^ 8) := by gcongr
    simp only [capF]; norm_num at *; linarith)
  refine h.mono ?_
  rw [abs_mul]
  have h1 : |qi.toReal / L.toReal| * |Θ| ≤ 1000001 / 1000000 * (52 / 100) :=
    mul_le_mul hq1 hΘ (abs_nonneg _) (by norm_num)
  have h2 : |qi.toReal / L.toReal| * (191 / 10 ^ 8) ≤ 1000001 / 1000000 * (191 / 10 ^ 8) := by gcongr
  have h3 : |Θ| * (6 / 10 ^ 8) ≤ 52 / 100 * (6 / 10 ^ 8) := by gcongr
  have := η32_small
  simp only [u32]; norm_num at *; nlinarith

theorem A32.of_val {x : Float32} {r : ℝ} (h : x.IsFinite) (hr : x.toReal = r) : A32 x r 0 :=
  ⟨h, by rw [hr, sub_self, abs_zero]⟩

theorem A32.lo {x : Float32} {r e : ℝ} (h : A32 x r e) : r - e ≤ x.toReal := by
  have := (abs_le.1 h.2).1; linarith

theorem A32.hi {x : Float32} {r e : ℝ} (h : A32 x r e) : x.toReal ≤ r + e := by
  have := (abs_le.1 h.2).2; linarith

theorem piD_bounds : (3.1415926 : ℝ) < Att.piD ∧ Att.piD < 3.1415927 := by
  constructor <;> norm_num [Att.piD]

/-! ## `wrap_PI` on `[-3, 3]` (the proof of `Att.wrapPI_near` of the shaping file) -/

/-- `wrap_PI(x)` for `|x| ≤ 3`: within `1.4·10⁻⁶` of `x`, and exactly `x` for `x ≥ 0`. (`fmodf` is
only specified up to the integer multiple, `LibmSpec.fmodf`; for `x < 0` the result goes through
`x + 2π` and back, which rounds.) -/
theorem wrapPI_near (hL : LibmSpec) {x : Float32} (hx : x.IsFinite) (h3 : |x.toReal| ≤ 3) :
    A32 (wrap_PI_float x) x.toReal (14 / 10 ^ 7) ∧
      (0 ≤ x.toReal → (wrap_PI_float x).toReal = x.toReal) := by
  have hp := Att.pi32 hL
  obtain ⟨pb1, pb2⟩ := piD_bounds
  have hη := η32_small
  have hη0 := η32_pos
  have hpe : u32 * Att.piD + η32 ≤ 19 / 10 ^ 8 := by simp only [u32]; norm_num; nlinarith
  have hP := hp.mono hpe
  have hPlo := A32.lo hP
  have hPhi := A32.hi hP
  obtain ⟨d2, hd2f, hd2⟩ := Float32.exists_double hp.1 (by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have := Float32.abs_toReal_le_maxFinite (Float.toFloat32 (3.1415926535897931 : Float))
    have : |(Float.toFloat32 (3.1415926535897931 : Float)).toReal| ≤ 4 := by
      rw [abs_le]; constructor <;> linarith
    have := capF_le_max32; simp only [capF] at this; norm_num at this ⊢; linarith)
  obtain ⟨hBf, hBv⟩ := Float32.mul_exact hp.1 Float32.isFinite_int32_two hd2f
    (by rw [Float32.toReal_int32_two, hd2]; ring)
  have hBv' : (Float.toFloat32 (3.1415926535897931 : Float) * Int32.toFloat32 2).toReal =
      2 * (Float.toFloat32 (3.1415926535897931 : Float)).toReal := hBv.trans hd2
  -- `(float)(M_PI * 2)`
  have h2d : A64 (3.1415926535897931 * Int32.toFloat 2 : Float) (2 * Att.piD) (1 / 10 ^ 15) := by
    have hm := A64.mul (A64.of_exact f64_isFinite_3p1415926535897931) (A64.of_exact Float.two64.1)
      (by rw [Float.two64.2, f64_toReal_3p1415926535897931]; simp only [capF]; norm_num)
    rw [Float.two64.2, f64_toReal_3p1415926535897931] at hm
    refine (hm.congr (by simp only [Att.piD]; ring)).mono ?_
    have := η64_small; simp only [u64]; norm_num; linarith
  have hD := A64.toFloat32 hL h2d (by rw [abs_of_pos (by linarith)]; simp only [capF]; norm_num; linarith)
  have hD' : A32 (Float.toFloat32 (3.1415926535897931 * Int32.toFloat 2 : Float)) (2 * Att.piD)
      (38 / 10 ^ 8) := hD.mono (by
    rw [abs_of_pos (by linarith)]; simp only [u32]; norm_num; nlinarith)
  obtain ⟨hrf, hrlt, n, hn⟩ := hL.fmodf x _ hx hBf (by rw [hBv']; linarith)
  rw [hBv'] at hrlt hn
  rw [abs_of_pos (show (0:ℝ) < 2 * (Float.toFloat32 (3.1415926535897931 : Float)).toReal by linarith)] at hrlt
  have hrlt' := abs_lt.1 hrlt
  have hz0 := Float32.isFinite_int32_zero
  have hz0v := Float32.toReal_int32_zero
  simp only [wrap_PI_float, wrap_2PI_float, Id.run, id_pure_eq]
  generalize CppLibm.fmodf x (Float.toFloat32 3.1415926535897931 * Int32.toFloat32 2) = res at hrf hrlt hrlt' hn ⊢
  generalize hB : Float.toFloat32 3.1415926535897931 * Int32.toFloat32 2 = B at hBf hBv' ⊢
  generalize Float.toFloat32 (3.1415926535897931 * Int32.toFloat 2 : Float) = D at hD' ⊢
  generalize hPg : Float.toFloat32 (3.1415926535897931 : Float) = P at hp hP hPlo hPhi hBv' hn hrlt' ⊢
  have key : ∀ a b : ℤ, (a : ℝ) * (2 * P.toReal) < n * (2 * P.toReal) →
      (n : ℝ) * (2 * P.toReal) < b * (2 * P.toReal) → a < n ∧ n < b := by
    intro a b h1 h2
    have hP0 : 0 < 2 * P.toReal := by linarith
    exact ⟨by exact_mod_cast lt_of_mul_lt_mul_right h1 hP0.le,
      by exact_mod_cast lt_of_mul_lt_mul_right h2 hP0.le⟩
  have hx3 := abs_le.1 h3
  -- the real value of the result of `wrap_2PI`
  rcases le_or_gt 0 x.toReal with hx0 | hx0
  · -- `x ≥ 0`: `wrap_2PI(x) = x` exactly
    have hr1 : (if res < Int32.toFloat32 0 then res + B else res).IsFinite ∧
        (if res < Int32.toFloat32 0 then res + B else res).toReal = x.toReal := by
      by_cases hneg : res < Int32.toFloat32 0
      · rw [ite_eq_left hneg]
        have hr0 := (Float32.lt_iff_toReal_lt hrf hz0).1 hneg
        rw [hz0v] at hr0
        obtain ⟨hn1', hn2'⟩ := key 0 2 (by push_cast; linarith) (by push_cast; linarith)
        have : n = 1 := by omega
        subst this
        exact Float32.add_exact hrf hBf hx (by rw [hn, hBv']; push_cast; ring)
      · rw [ite_eq_right hneg]
        have hr0 : 0 ≤ res.toReal := by
          have := (Float32.lt_iff_toReal_lt hrf hz0).not.1 hneg
          rw [hz0v] at this; linarith
        obtain ⟨hn1', hn2'⟩ := key (-1) 1 (by push_cast; linarith) (by push_cast; linarith)
        have : n = 0 := by omega
        subst this
        exact ⟨hrf, by rw [hn]; simp⟩
    generalize (if res < Int32.toFloat32 0 then res + B else res) = r1 at hr1 ⊢
    have hng : ¬ r1 > P := by
      rw [gt_iff_lt, Float32.lt_iff_toReal_lt hp.1 hr1.1, hr1.2]; linarith
    rw [ite_eq_right hng]
    exact ⟨⟨hr1.1, by rw [hr1.2]; norm_num⟩, fun _ => hr1.2⟩
  · -- `x < 0`: `wrap_2PI(x) ≈ x + 2π`
    have hr1 : A32 (if res < Int32.toFloat32 0 then res + B else res) (x.toReal + 2 * Att.piD)
        (76 / 10 ^ 8) := by
      by_cases hneg : res < Int32.toFloat32 0
      · rw [ite_eq_left hneg]
        have hr0 := (Float32.lt_iff_toReal_lt hrf hz0).1 hneg
        rw [hz0v] at hr0
        obtain ⟨hn1', hn2'⟩ := key (-1) 1 (by push_cast; linarith) (by push_cast; linarith)
        have : n = 0 := by omega
        subst this
        have hres : A32 res x.toReal 0 := A32.of_val hrf (by rw [hn]; simp)
        have hBa : A32 B (2 * Att.piD) (38 / 10 ^ 8) := ⟨hBf, by
          rw [hBv', show 2 * P.toReal - 2 * Att.piD = 2 * (P.toReal - Att.piD) by ring, abs_mul,
            abs_of_pos (by norm_num : (0:ℝ) < 2)]
          linarith [hP.2]⟩
        exact A32.add_c hres hBa (R := 63 / 10) (by rw [abs_le]; constructor <;> linarith)
          (by simp only [capF]; norm_num) (by norm_num)
      · rw [ite_eq_right hneg]
        have hr0 : 0 ≤ res.toReal := by
          have := (Float32.lt_iff_toReal_lt hrf hz0).not.1 hneg
          rw [hz0v] at this; linarith
        obtain ⟨hn1', hn2'⟩ := key (-2) 0 (by push_cast; linarith) (by push_cast; linarith)
        have : n = -1 := by omega
        subst this
        refine ⟨hrf, ?_⟩
        rw [hn, show x.toReal - ((-1 : ℤ) : ℝ) * (2 * P.toReal) - (x.toReal + 2 * Att.piD) =
          2 * (P.toReal - Att.piD) by push_cast; ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith [hP.2]
    generalize (if res < Int32.toFloat32 0 then res + B else res) = r1 at hr1 ⊢
    have hgt : r1 > P := by
      rw [gt_iff_lt, Float32.lt_iff_toReal_lt hp.1 hr1.1]; linarith [A32.lo hr1]
    rw [ite_eq_left hgt]
    have hs := A32.sub_c hr1 hD' (R := 3) (by
      rw [show x.toReal + 2 * Att.piD - 2 * Att.piD = x.toReal by ring]; exact h3)
      (by simp only [capF]; norm_num) (e := 14 / 10 ^ 7) (by norm_num)
    refine ⟨hs.congr (by ring), fun h => absurd h (by linarith)⟩

/-- The angle `wrap_PI(2 · atan2f(l, q₁))` for `l > 0`, `q₁ ≥ 0.9687`: within `1.91·10⁻⁶` of
`2 arctan(l / q₁)` (atan2f within `2⁻²²`, the product rounded, `wrap_PI` within `1.4·10⁻⁶`). -/
theorem angle_W (hL : LibmSpec) {L q1 : Float32} (hLf : L.IsFinite) (hq1f : q1.IsFinite)
    (hl0 : 0 < L.toReal) (hw0 : 9687 / 10000 ≤ q1.toReal) (hlw : L.toReal ≤ 2504 / 10000) :
    A32 (wrap_PI_float (2.0 * Float32.atan2 L q1)) (2 * Real.arctan (L.toReal / q1.toReal))
      (191 / 10 ^ 8) ∧ |2 * Real.arctan (L.toReal / q1.toReal)| ≤ 52 / 100 := by
  have hwp : 0 < q1.toReal := by linarith
  have hlw0 : 0 ≤ L.toReal / q1.toReal := div_nonneg hl0.le hwp.le
  have hz : L.toReal / q1.toReal ≤ 2504 / 10000 / (9687 / 10000) := by gcongr
  have ha0 := Real.arctan_nonneg.2 hlw0
  have ha1 := Real.arctan_le_self hlw0
  have hΘ : |2 * Real.arctan (L.toReal / q1.toReal)| ≤ 52 / 100 := by
    rw [abs_of_nonneg (by linarith)]; norm_num at hz ⊢; linarith
  refine ⟨?_, hΘ⟩
  obtain ⟨hθf, -, hθ⟩ := hL.atan2f L q1 hLf hq1f
  have hθ' := hθ (fun h => by linarith [h.1])
  rw [arg_eq hwp] at hθ'
  have hA : A32 (Float32.atan2 L q1) (Real.arctan (L.toReal / q1.toReal)) (1 / 4194304) :=
    ⟨hθf, by rw [libm32Err] at hθ'; norm_num at hθ' ⊢; exact hθ'⟩
  have h2 := A32.mul (A32.of_exact f32_isFinite_2p0) hA (by
    rw [f32_toReal_2p0, abs_mul, abs_of_nonneg ha0]; simp only [capF]; norm_num at hz ⊢; linarith)
  rw [f32_toReal_2p0] at h2
  have ht : A32 ((2.0 : Float32) * Float32.atan2 L q1) (2 * Real.arctan (L.toReal / q1.toReal))
      (51 / 10 ^ 8) := h2.mono (by
    rw [abs_mul, abs_of_nonneg ha0]; have := η32_small; simp only [u32]; norm_num at hz ⊢
    linarith)
  have h3 : |((2.0 : Float32) * Float32.atan2 L q1).toReal| ≤ 3 := by
    have := ht.abs_le; linarith
  have hw := (wrapPI_near hL ht.1 h3).1
  have := A32.tri hw (r' := 2 * Real.arctan (L.toReal / q1.toReal)) ht.2
  exact this.mono (by norm_num)

/-- The length `l` of `to_axis_angle`: `sqrt(sq(q₂) + sq(q₃) + sq(q₄))`. -/
abbrev lenQ (s : Quaternion.State) : Float32 :=
  Float32.sqrt (sq_float s.q2 + sq_float s.q3 + sq_float s.q4)

theorem lenQ_eq (s : Quaternion.State) :
    lenQ s = Vector3f.length (Vector3f.init_float3 s.q2 s.q3 s.q4) := rfl

theorem taa_zero (s : Quaternion.State) (v : Vector3f.State) (h : is_zero_float (lenQ s) = true) :
    Quaternion.to_axis_angle s v = Vector3f.init_float3 s.q2 s.q3 s.q4 := by
  simp [Quaternion.to_axis_angle, h]

theorem taa_gen (s : Quaternion.State) (v : Vector3f.State) (h : is_zero_float (lenQ s) = false) :
    (Quaternion.to_axis_angle s v).x =
        s.q2 / lenQ s * wrap_PI_float (2.0 * Float32.atan2 (lenQ s) s.q1) ∧
      (Quaternion.to_axis_angle s v).y =
        s.q3 / lenQ s * wrap_PI_float (2.0 * Float32.atan2 (lenQ s) s.q1) ∧
      (Quaternion.to_axis_angle s v).z =
        s.q4 / lenQ s * wrap_PI_float (2.0 * Float32.atan2 (lenQ s) s.q1) := by
  simp [Quaternion.to_axis_angle, h, Vector3f.op_div_assign, Vector3f.op_mul_assign_float,
    Vector3f.init_float3]

theorem sqrt_sigma {N σ x y z : ℝ} (hN : N = Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) (hσ : 0 ≤ σ) :
    N * σ = Real.sqrt ((x * σ) ^ 2 + (y * σ) ^ 2 + (z * σ) ^ 2) := by
  rw [show (x * σ) ^ 2 + (y * σ) ^ 2 + (z * σ) ^ 2 = (x ^ 2 + y ^ 2 + z ^ 2) * σ ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hσ, hN]

end Ax

open Ax in
set_option maxHeartbeats 1000000 in
/-- **`to_axis_angle` near a small rotation** (milestone M4, lemma C8): for a float quaternion
within `1.3·10⁻⁷` per component of the axis–angle quaternion `(cos(φ/2), a sin(φ/2))` of an axis
with `| |a|² - 1 | ≤ δ ≤ 10⁻⁴` and an angle `φ ∈ [0, 1/2]`, both branches of `to_axis_angle`
(`is_zero(l)` or not) are within `3.5·10⁻⁶ + 0.26 δ` per component of the rotation vector
`(φ / |a|) a`. The `0.26 δ` is the real effect of the non-unit axis: the code reads the angle
`2 arctan(|a| tan(φ/2))` of the non-unit quaternion. -/
theorem toAxisAngle_near_gen (hL : LibmSpec) (s : Quaternion.State) (v : Vector3f.State) {a : RV}
    {φ δ : ℝ} (hq : QA s (RQ.ofAxisAngle a φ) (13 / 10 ^ 8))
    (ha : |a.x ^ 2 + a.y ^ 2 + a.z ^ 2 - 1| ≤ δ) (hδ : δ ≤ 1 / 10 ^ 4)
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 2) :
    VA (Quaternion.to_axis_angle s v) (RV.smul (φ / a.norm) a) (35 / 10 ^ 7 + 26 / 100 * δ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  obtain ⟨hs0, hs1, hc0, hc1, hφσ, hφeq⟩ := half_facts hφ0 hφ1
  obtain ⟨hN0, hN1, hNd, hax, hay, haz⟩ := norm_facts ha hδ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans ha
  have e1 : |s.q1.toReal - Real.cos (φ / 2)| ≤ 13 / 10 ^ 8 := h1.2
  have e2 : |s.q2.toReal - a.x * Real.sin (φ / 2)| ≤ 13 / 10 ^ 8 := h2.2
  have e3 : |s.q3.toReal - a.y * Real.sin (φ / 2)| ≤ 13 / 10 ^ 8 := h3.2
  have e4 : |s.q4.toReal - a.z * Real.sin (φ / 2)| ≤ 13 / 10 ^ 8 := h4.2
  set σ := Real.sin (φ / 2) with hσdef
  set c := Real.cos (φ / 2) with hcdef
  set N := a.norm with hNdef
  have hXb : N * σ ≤ 2501 / 10000 := by nlinarith
  have bnd : ∀ (q : Float32) (ai : ℝ), |ai| ≤ N → |q.toReal - ai * σ| ≤ 13 / 10 ^ 8 →
      |q.toReal| ≤ 1000 := by
    intro q ai hai hq
    have : |ai * σ| ≤ N * (1 / 4) := by
      rw [abs_mul, abs_of_nonneg hs0]; exact mul_le_mul hai hs1 hs0 (by linarith)
    have := abs_sub_abs_le_abs_sub q.toReal (ai * σ)
    linarith
  obtain ⟨hlf, hln⟩ := len_near (v := Vector3f.init_float3 s.q2 s.q3 s.q4) h2.1 h3.1 h4.1
    (bnd _ _ hax e2) (bnd _ _ hay e3) (bnd _ _ haz e4)
  rw [← lenQ_eq] at hlf hln
  have hn : (vv (Vector3f.init_float3 s.q2 s.q3 s.q4)).norm =
      Real.sqrt (s.q2.toReal ^ 2 + s.q3.toReal ^ 2 + s.q4.toReal ^ 2) := rfl
  rw [hn] at hln
  set n := Real.sqrt (s.q2.toReal ^ 2 + s.q3.toReal ^ 2 + s.q4.toReal ^ 2) with hndef
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hX : N * σ = Real.sqrt ((a.x * σ) ^ 2 + (a.y * σ) ^ 2 + (a.z * σ) ^ 2) := sqrt_sigma rfl hs0
  have hXn : |N * σ - n| ≤ 17321 / 10000 * (13 / 10 ^ 8) := by rw [hX]; exact norm3_lip e2 e3 e4
  have hp2 : |s.q2.toReal| ≤ n := Real.abs_le_sqrt (by nlinarith [sq_nonneg s.q3.toReal, sq_nonneg s.q4.toReal])
  have hp3 : |s.q3.toReal| ≤ n := Real.abs_le_sqrt (by nlinarith [sq_nonneg s.q2.toReal, sq_nonneg s.q4.toReal])
  have hp4 : |s.q4.toReal| ≤ n := Real.abs_le_sqrt (by nlinarith [sq_nonneg s.q2.toReal, sq_nonneg s.q3.toReal])
  have hlX := len_dev hXb hln hXn
  have hlnb := abs_le.1 hln
  cases hz : is_zero_float (lenQ s) with
  | false =>
    have hl23 : 2 ^ (-23 : ℤ) ≤ |(lenQ s).toReal| := by
      by_contra hc; push Not at hc
      rw [(Att.isZero_iff hlf).2 hc] at hz; exact absurd hz (by decide)
    rw [two_pow_m23] at hl23
    have hlpos : 0 < (lenQ s).toReal := by
      rcases le_or_gt 0 (lenQ s).toReal with h | h
      · rw [abs_of_nonneg h] at hl23; linarith
      · rw [abs_of_neg h] at hl23; norm_num at hlnb; nlinarith
    have hl23' : 1 / 8388608 ≤ (lenQ s).toReal := by rwa [abs_of_pos hlpos] at hl23
    have hnl : n ≤ 1000001 / 1000000 * (lenQ s).toReal := by norm_num at hlnb ⊢; nlinarith
    have hw0 : 9687 / 10000 ≤ s.q1.toReal := by linarith [(abs_le.1 e1).1]
    have hlw : (lenQ s).toReal ≤ 2504 / 10000 := by linarith [(abs_le.1 hlX).2]
    obtain ⟨hW, hΘ⟩ := angle_W hL hlf h1.1 hlpos hw0 hlw
    obtain ⟨tx, ty, tz⟩ := taa_gen s v hz
    have comp : ∀ (q : Float32) (ai : ℝ), q.IsFinite → |ai| ≤ N → |q.toReal - ai * σ| ≤ 13 / 10 ^ 8 →
        |q.toReal| ≤ n → A32 (q / lenQ s * wrap_PI_float (2.0 * Float32.atan2 (lenQ s) s.q1))
          (φ / N * ai) (35 / 10 ^ 7 + 26 / 100 * δ) := by
      intro q ai hqf hai hq hqn
      have ho := out_comp hqf hlf hlpos (hqn.trans hnl) hW hΘ
      have g := gen_real hai hN0 hXb hs0 hc0 hq e1 hlX hlpos
      have st := stepA hai hN0 hNd hs0 hs1 hc0 hφeq
      have := abs_sub_le (q.toReal / (lenQ s).toReal * (2 * Real.arctan ((lenQ s).toReal / s.q1.toReal)))
        (2 * Real.arctan (N * σ / c) / N * ai) (φ / N * ai)
      rw [abs_sub_comm (2 * Real.arctan (N * σ / c) / N * ai)] at this
      exact (A32.tri ho (r' := φ / N * ai) (le_refl _)).mono (by linarith)
    exact ⟨tx ▸ comp _ _ h2.1 hax e2 hp2, ty ▸ comp _ _ h3.1 hay e3 hp3,
      tz ▸ comp _ _ h4.1 haz e4 hp4⟩
  | true =>
    have hl := (Att.isZero_iff hlf).1 hz
    rw [two_pow_m23] at hl
    have hnb : n ≤ 12 / 10 ^ 8 := by
      have := (abs_lt.1 hl).2; norm_num at hlnb this ⊢; nlinarith
    rw [taa_zero s v hz]
    have comp : ∀ (q : Float32) (ai : ℝ), q.IsFinite → |ai| ≤ N → |q.toReal| ≤ n →
        A32 q (φ / N * ai) (35 / 10 ^ 7 + 26 / 100 * δ) := by
      intro q ai hqf hai hqn
      have := zero_real hai hN0 hφ0 hφσ hqn hnb hXn
      exact ⟨hqf, by linarith⟩
    exact ⟨comp _ _ h2.1 hax hp2, comp _ _ h3.1 hay hp3, comp _ _ h4.1 haz hp4⟩

/-- `toAxisAngle_near_gen` at `δ = 10⁻⁴`: within `3·10⁻⁵`. -/
theorem toAxisAngle_near (hL : LibmSpec) (s : Quaternion.State) (v : Vector3f.State) {a : RV}
    {φ : ℝ} (hq : QA s (RQ.ofAxisAngle a φ) (13 / 10 ^ 8))
    (ha : |a.x ^ 2 + a.y ^ 2 + a.z ^ 2 - 1| ≤ 1 / 10 ^ 4) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1 / 2) :
    VA (Quaternion.to_axis_angle s v) (RV.smul (φ / a.norm) a) (3 / 10 ^ 5) :=
  (toAxisAngle_near_gen hL s v hq ha le_rfl hφ0 hφ1).mono (by norm_num)

end
end Contracts.Track.AttQ
