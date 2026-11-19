module

/-
The float-error bundle: read a translated float expression as its real counterpart plus a bound.

`Float32.Near x r ε` (and `Float.Near` for doubles) says that the float `x` is finite and within
`ε` of the real `r`. One lemma per operation propagates it, with the rounding of the operation
added (unit roundoff `2^-24` relative, `2^-150` absolute for `*`, `/`, `√`; `2^-53` and `2^-1075`
for doubles), under a no-overflow hypothesis stated on the real side:

* `Near.exact`, `Near.of_eq`: a finite float is its own value (literals: `FloatModel.Lit`);
* `Near.neg`, `Near.add`, `Near.sub`, `Near.mul`, `Near.div`, `Near.sqrt`;
* `Near.weaken` (to a target `r'`, `ε'`), `Near.abs_le`, `Near.toReal_le`, `Near.le_toReal`.

A proof reads an expression bottom-up: `(ha.mul hb hM).add hc hM'` is a `Near` for
`a * b + c` with the real `ra * rb + rc`, and `Near.weaken` closes against the stated bound (the
side conditions are real inequalities, for `norm_num`/`linarith`/`positivity`).
-/
public import FloatModel.Compare

@[expose] public section

open Float.Model UnpackedFloat

/-- For `x, y ≥ 0`: `|√x - √y| ≤ √|x - y|`. -/
theorem Real.abs_sqrt_sub_sqrt_le_sqrt_abs {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
  wlog hxy : y ≤ x generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]; exact this hy hx (le_of_not_ge hxy)
  have h1 : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hxy
  rw [abs_of_nonneg (sub_nonneg.2 h1), abs_of_nonneg (sub_nonneg.2 hxy)]
  have hs : Real.sqrt x ≤ Real.sqrt y + Real.sqrt (x - y) := by
    rw [Real.sqrt_le_left]
    · have h2 := Real.sq_sqrt hy
      have h3 := Real.sq_sqrt (sub_nonneg.2 hxy)
      nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg (x - y)]
    · positivity
  linarith

namespace Float32

/-- `x` is a finite float within `ε` of the real `r`. -/
structure Near (x : Float32) (r ε : ℝ) : Prop where
  fin : x.IsFinite
  err : |x.toReal - r| ≤ ε

namespace Near

variable {a b x : Float32} {r ra rb ε εa εb : ℝ}

theorem exact (h : x.IsFinite) : Near x x.toReal 0 := ⟨h, by simp⟩

theorem of_eq (h : x.IsFinite) (hr : x.toReal = r) : Near x r 0 := ⟨h, by simp [hr]⟩

theorem eps_nonneg (h : Near x r ε) : 0 ≤ ε := (abs_nonneg _).trans h.err

theorem weaken {r' ε' : ℝ} (h : Near x r ε) (he : |r - r'| + ε ≤ ε') : Near x r' ε' :=
  ⟨h.fin, by
    calc |x.toReal - r'| ≤ |x.toReal - r| + |r - r'| := abs_sub_le _ _ _
      _ ≤ ε' := by linarith [h.err]⟩

theorem abs_le (h : Near x r ε) : |x.toReal| ≤ |r| + ε := by
  have := abs_sub_abs_le_abs_sub x.toReal r
  linarith [h.err]

theorem toReal_le (h : Near x r ε) : x.toReal ≤ r + ε := by
  have := (_root_.abs_le.1 h.err).2; linarith

theorem le_toReal (h : Near x r ε) : r - ε ≤ x.toReal := by
  have := (_root_.abs_le.1 h.err).1; linarith

theorem neg (h : Near x r ε) : Near (-x) (-r) ε := by
  refine ⟨(isFinite_neg x).2 h.fin, ?_⟩
  rw [toReal_neg, show -x.toReal - -r = -(x.toReal - r) by ring, abs_neg]
  exact h.err

/-- `+`: the errors add, plus the rounding of the sum. -/
theorem add (ha : Near a ra εa) (hb : Near b rb εb) (hM : |ra| + |rb| + εa + εb ≤ maxFinite32) :
    Near (a + b) (ra + rb) (εa + εb + 2 ^ (-24 : ℤ) * (|ra + rb| + εa + εb)) := by
  have hs : |a.toReal + b.toReal - (ra + rb)| ≤ εa + εb := by
    calc |a.toReal + b.toReal - (ra + rb)| = |(a.toReal - ra) + (b.toReal - rb)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add ha.err hb.err)
  have hS : |a.toReal + b.toReal| ≤ |ra + rb| + εa + εb := by
    have := abs_sub_abs_le_abs_sub (a.toReal + b.toReal) (ra + rb); linarith
  obtain ⟨hf, he⟩ := add_err_all ha.fin hb.fin (hS.trans (by linarith [abs_add_le ra rb]))
  refine ⟨hf, ?_⟩
  calc |(a + b).toReal - (ra + rb)|
      ≤ |(a + b).toReal - (a.toReal + b.toReal)| + |a.toReal + b.toReal - (ra + rb)| :=
        abs_sub_le _ _ _
    _ ≤ 2 ^ (-24 : ℤ) * (|ra + rb| + εa + εb) + (εa + εb) := by
        gcongr
        exact he.trans (mul_le_mul_of_nonneg_left hS (by positivity))
    _ = _ := by ring

/-- `-`: the errors add, plus the rounding of the difference. -/
theorem sub (ha : Near a ra εa) (hb : Near b rb εb) (hM : |ra| + |rb| + εa + εb ≤ maxFinite32) :
    Near (a - b) (ra - rb) (εa + εb + 2 ^ (-24 : ℤ) * (|ra - rb| + εa + εb)) := by
  have hs : |a.toReal - b.toReal - (ra - rb)| ≤ εa + εb := by
    calc |a.toReal - b.toReal - (ra - rb)| = |(a.toReal - ra) - (b.toReal - rb)| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add ha.err hb.err)
  have hS : |a.toReal - b.toReal| ≤ |ra - rb| + εa + εb := by
    have := abs_sub_abs_le_abs_sub (a.toReal - b.toReal) (ra - rb); linarith
  obtain ⟨hf, he⟩ := sub_err_all ha.fin hb.fin (hS.trans (by linarith [abs_sub ra rb]))
  refine ⟨hf, ?_⟩
  calc |(a - b).toReal - (ra - rb)|
      ≤ |(a - b).toReal - (a.toReal - b.toReal)| + |a.toReal - b.toReal - (ra - rb)| :=
        abs_sub_le _ _ _
    _ ≤ 2 ^ (-24 : ℤ) * (|ra - rb| + εa + εb) + (εa + εb) := by
        gcongr
        exact he.trans (mul_le_mul_of_nonneg_left hS (by positivity))
    _ = _ := by ring

/-- `*`: first-order propagation, plus the rounding of the product (with the underflow term). -/
theorem mul (ha : Near a ra εa) (hb : Near b rb εb)
    (hM : (|ra| + εa) * (|rb| + εb) ≤ maxFinite32) :
    Near (a * b) (ra * rb)
      (|ra| * εb + |rb| * εa + εa * εb + 2 ^ (-24 : ℤ) * ((|ra| + εa) * (|rb| + εb)) +
        2 ^ (-150 : ℤ)) := by
  have hA := ha.abs_le
  have hB := hb.abs_le
  have hεa := ha.eps_nonneg
  have hεb := hb.eps_nonneg
  have hP : |a.toReal * b.toReal| ≤ (|ra| + εa) * (|rb| + εb) := by
    rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
  obtain ⟨hf, he⟩ := mul_err_all ha.fin hb.fin (hP.trans hM)
  have hd : |a.toReal * b.toReal - ra * rb| ≤ |ra| * εb + |rb| * εa + εa * εb := by
    have e1 : a.toReal * b.toReal - ra * rb =
        (a.toReal - ra) * b.toReal + ra * (b.toReal - rb) := by ring
    rw [e1]
    calc |(a.toReal - ra) * b.toReal + ra * (b.toReal - rb)|
        ≤ |a.toReal - ra| * |b.toReal| + |ra| * |b.toReal - rb| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ εa * (|rb| + εb) + |ra| * εb := by
          gcongr
          · exact ha.err
          · exact hb.err
      _ = _ := by ring
  refine ⟨hf, ?_⟩
  calc |(a * b).toReal - ra * rb|
      ≤ |(a * b).toReal - a.toReal * b.toReal| + |a.toReal * b.toReal - ra * rb| :=
        abs_sub_le _ _ _
    _ ≤ (2 ^ (-24 : ℤ) * ((|ra| + εa) * (|rb| + εb)) + 2 ^ (-150 : ℤ)) +
          (|ra| * εb + |rb| * εa + εa * εb) := by
        gcongr
        exact he.trans (by gcongr)
    _ = _ := by ring

/-- `/`: the divisor bounded away from `0` (`εb < |rb|`). -/
theorem div (ha : Near a ra εa) (hb : Near b rb εb) (hb0 : εb < |rb|)
    (hM : (|ra| + εa) / (|rb| - εb) ≤ maxFinite32) :
    Near (a / b) (ra / rb)
      ((|rb| * εa + |ra| * εb) / (|rb| * (|rb| - εb)) +
        2 ^ (-24 : ℤ) * ((|ra| + εa) / (|rb| - εb)) + 2 ^ (-150 : ℤ)) := by
  have hεa := ha.eps_nonneg
  have hεb := hb.eps_nonneg
  have hd0 : 0 < |rb| - εb := by linarith
  have hrb : 0 < |rb| := by linarith
  have hB : |rb| - εb ≤ |b.toReal| := by
    have := abs_sub_abs_le_abs_sub rb b.toReal
    rw [abs_sub_comm] at this; linarith [hb.err]
  have hb0' : b.toReal ≠ 0 := by
    intro h; rw [h, abs_zero] at hB; linarith
  have hbpos : 0 < |b.toReal| := lt_of_lt_of_le hd0 hB
  have hQ : |a.toReal / b.toReal| ≤ (|ra| + εa) / (|rb| - εb) := by
    rw [abs_div]
    exact div_le_div₀ (by positivity) ha.abs_le hd0 hB
  obtain ⟨hf, he⟩ := div_err_all ha.fin hb.fin hb0' (hQ.trans hM)
  have hd : |a.toReal / b.toReal - ra / rb| ≤ (|rb| * εa + |ra| * εb) / (|rb| * (|rb| - εb)) := by
    have hrb0 : rb ≠ 0 := by intro h; rw [h, abs_zero] at hrb; exact lt_irrefl _ hrb
    rw [div_sub_div _ _ hb0' hrb0, abs_div, abs_mul]
    have hnum : |a.toReal * rb - b.toReal * ra| ≤ |rb| * εa + |ra| * εb := by
      have e1 : a.toReal * rb - b.toReal * ra = (a.toReal - ra) * rb - ra * (b.toReal - rb) := by
        ring
      rw [e1]
      calc |(a.toReal - ra) * rb - ra * (b.toReal - rb)|
          ≤ |a.toReal - ra| * |rb| + |ra| * |b.toReal - rb| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ εa * |rb| + |ra| * εb := by gcongr; exacts [ha.err, hb.err]
        _ = _ := by ring
    exact div_le_div₀ (by positivity) hnum (by positivity)
      (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hB hrb.le)
  refine ⟨hf, ?_⟩
  calc |(a / b).toReal - ra / rb|
      ≤ |(a / b).toReal - a.toReal / b.toReal| + |a.toReal / b.toReal - ra / rb| :=
        abs_sub_le _ _ _
    _ ≤ (2 ^ (-24 : ℤ) * ((|ra| + εa) / (|rb| - εb)) + 2 ^ (-150 : ℤ)) +
          (|rb| * εa + |ra| * εb) / (|rb| * (|rb| - εb)) := by
        gcongr
        exact he.trans (by gcongr)
    _ = _ := by ring

/-- `√`: a nonnegative float within `εa` of `ra ≥ 0`. -/
theorem sqrt (ha : Near a ra εa) (h0 : 0 ≤ a.toReal) (hra : 0 ≤ ra)
    (hM : ra + εa ≤ maxFinite32) :
    Near (Float32.sqrt a) (Real.sqrt ra)
      (Real.sqrt εa + 2 ^ (-24 : ℤ) * Real.sqrt (ra + εa) + 2 ^ (-150 : ℤ)) := by
  have hle : a.toReal ≤ ra + εa := ha.toReal_le
  obtain ⟨hf, he⟩ := sqrt_err_all ha.fin h0 (hle.trans hM)
  refine ⟨hf, ?_⟩
  calc |(Float32.sqrt a).toReal - Real.sqrt ra|
      ≤ |(Float32.sqrt a).toReal - Real.sqrt a.toReal| + |Real.sqrt a.toReal - Real.sqrt ra| :=
        abs_sub_le _ _ _
    _ ≤ (2 ^ (-24 : ℤ) * Real.sqrt (ra + εa) + 2 ^ (-150 : ℤ)) + Real.sqrt εa := by
        gcongr
        · exact he.trans (by gcongr)
        · exact (Real.abs_sqrt_sub_sqrt_le_sqrt_abs h0 hra).trans
            (Real.sqrt_le_sqrt ha.err)
    _ = _ := by ring

end Near

end Float32


namespace Float

/-- `x` is a finite float within `ε` of the real `r`. -/
structure Near (x : Float) (r ε : ℝ) : Prop where
  fin : x.IsFinite
  err : |x.toReal - r| ≤ ε

namespace Near

variable {a b x : Float} {r ra rb ε εa εb : ℝ}

theorem exact (h : x.IsFinite) : Near x x.toReal 0 := ⟨h, by simp⟩

theorem of_eq (h : x.IsFinite) (hr : x.toReal = r) : Near x r 0 := ⟨h, by simp [hr]⟩

theorem eps_nonneg (h : Near x r ε) : 0 ≤ ε := (abs_nonneg _).trans h.err

theorem weaken {r' ε' : ℝ} (h : Near x r ε) (he : |r - r'| + ε ≤ ε') : Near x r' ε' :=
  ⟨h.fin, by
    calc |x.toReal - r'| ≤ |x.toReal - r| + |r - r'| := abs_sub_le _ _ _
      _ ≤ ε' := by linarith [h.err]⟩

theorem abs_le (h : Near x r ε) : |x.toReal| ≤ |r| + ε := by
  have := abs_sub_abs_le_abs_sub x.toReal r
  linarith [h.err]

theorem toReal_le (h : Near x r ε) : x.toReal ≤ r + ε := by
  have := (_root_.abs_le.1 h.err).2; linarith

theorem le_toReal (h : Near x r ε) : r - ε ≤ x.toReal := by
  have := (_root_.abs_le.1 h.err).1; linarith

theorem neg (h : Near x r ε) : Near (-x) (-r) ε := by
  refine ⟨(isFinite_neg x).2 h.fin, ?_⟩
  rw [toReal_neg, show -x.toReal - -r = -(x.toReal - r) by ring, abs_neg]
  exact h.err

/-- `+`: the errors add, plus the rounding of the sum. -/
theorem add (ha : Near a ra εa) (hb : Near b rb εb) (hM : |ra| + |rb| + εa + εb ≤ maxFinite) :
    Near (a + b) (ra + rb) (εa + εb + 2 ^ (-53 : ℤ) * (|ra + rb| + εa + εb)) := by
  have hs : |a.toReal + b.toReal - (ra + rb)| ≤ εa + εb := by
    calc |a.toReal + b.toReal - (ra + rb)| = |(a.toReal - ra) + (b.toReal - rb)| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add ha.err hb.err)
  have hS : |a.toReal + b.toReal| ≤ |ra + rb| + εa + εb := by
    have := abs_sub_abs_le_abs_sub (a.toReal + b.toReal) (ra + rb); linarith
  obtain ⟨hf, he⟩ := add_err_all ha.fin hb.fin (hS.trans (by linarith [abs_add_le ra rb]))
  refine ⟨hf, ?_⟩
  calc |(a + b).toReal - (ra + rb)|
      ≤ |(a + b).toReal - (a.toReal + b.toReal)| + |a.toReal + b.toReal - (ra + rb)| :=
        abs_sub_le _ _ _
    _ ≤ 2 ^ (-53 : ℤ) * (|ra + rb| + εa + εb) + (εa + εb) := by
        gcongr
        exact he.trans (mul_le_mul_of_nonneg_left hS (by positivity))
    _ = _ := by ring

/-- `-`: the errors add, plus the rounding of the difference. -/
theorem sub (ha : Near a ra εa) (hb : Near b rb εb) (hM : |ra| + |rb| + εa + εb ≤ maxFinite) :
    Near (a - b) (ra - rb) (εa + εb + 2 ^ (-53 : ℤ) * (|ra - rb| + εa + εb)) := by
  have hs : |a.toReal - b.toReal - (ra - rb)| ≤ εa + εb := by
    calc |a.toReal - b.toReal - (ra - rb)| = |(a.toReal - ra) - (b.toReal - rb)| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (add_le_add ha.err hb.err)
  have hS : |a.toReal - b.toReal| ≤ |ra - rb| + εa + εb := by
    have := abs_sub_abs_le_abs_sub (a.toReal - b.toReal) (ra - rb); linarith
  obtain ⟨hf, he⟩ := sub_err_all ha.fin hb.fin (hS.trans (by linarith [abs_sub ra rb]))
  refine ⟨hf, ?_⟩
  calc |(a - b).toReal - (ra - rb)|
      ≤ |(a - b).toReal - (a.toReal - b.toReal)| + |a.toReal - b.toReal - (ra - rb)| :=
        abs_sub_le _ _ _
    _ ≤ 2 ^ (-53 : ℤ) * (|ra - rb| + εa + εb) + (εa + εb) := by
        gcongr
        exact he.trans (mul_le_mul_of_nonneg_left hS (by positivity))
    _ = _ := by ring

/-- `*`: first-order propagation, plus the rounding of the product (with the underflow term). -/
theorem mul (ha : Near a ra εa) (hb : Near b rb εb)
    (hM : (|ra| + εa) * (|rb| + εb) ≤ maxFinite) :
    Near (a * b) (ra * rb)
      (|ra| * εb + |rb| * εa + εa * εb + 2 ^ (-53 : ℤ) * ((|ra| + εa) * (|rb| + εb)) +
        2 ^ (-1075 : ℤ)) := by
  have hA := ha.abs_le
  have hB := hb.abs_le
  have hεa := ha.eps_nonneg
  have hεb := hb.eps_nonneg
  have hP : |a.toReal * b.toReal| ≤ (|ra| + εa) * (|rb| + εb) := by
    rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
  obtain ⟨hf, he⟩ := mul_err_all ha.fin hb.fin (hP.trans hM)
  have hd : |a.toReal * b.toReal - ra * rb| ≤ |ra| * εb + |rb| * εa + εa * εb := by
    have e1 : a.toReal * b.toReal - ra * rb =
        (a.toReal - ra) * b.toReal + ra * (b.toReal - rb) := by ring
    rw [e1]
    calc |(a.toReal - ra) * b.toReal + ra * (b.toReal - rb)|
        ≤ |a.toReal - ra| * |b.toReal| + |ra| * |b.toReal - rb| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ εa * (|rb| + εb) + |ra| * εb := by
          gcongr
          · exact ha.err
          · exact hb.err
      _ = _ := by ring
  refine ⟨hf, ?_⟩
  calc |(a * b).toReal - ra * rb|
      ≤ |(a * b).toReal - a.toReal * b.toReal| + |a.toReal * b.toReal - ra * rb| :=
        abs_sub_le _ _ _
    _ ≤ (2 ^ (-53 : ℤ) * ((|ra| + εa) * (|rb| + εb)) + 2 ^ (-1075 : ℤ)) +
          (|ra| * εb + |rb| * εa + εa * εb) := by
        gcongr
        exact he.trans (by gcongr)
    _ = _ := by ring

/-- `/`: the divisor bounded away from `0` (`εb < |rb|`). -/
theorem div (ha : Near a ra εa) (hb : Near b rb εb) (hb0 : εb < |rb|)
    (hM : (|ra| + εa) / (|rb| - εb) ≤ maxFinite) :
    Near (a / b) (ra / rb)
      ((|rb| * εa + |ra| * εb) / (|rb| * (|rb| - εb)) +
        2 ^ (-53 : ℤ) * ((|ra| + εa) / (|rb| - εb)) + 2 ^ (-1075 : ℤ)) := by
  have hεa := ha.eps_nonneg
  have hεb := hb.eps_nonneg
  have hd0 : 0 < |rb| - εb := by linarith
  have hrb : 0 < |rb| := by linarith
  have hB : |rb| - εb ≤ |b.toReal| := by
    have := abs_sub_abs_le_abs_sub rb b.toReal
    rw [abs_sub_comm] at this; linarith [hb.err]
  have hb0' : b.toReal ≠ 0 := by
    intro h; rw [h, abs_zero] at hB; linarith
  have hbpos : 0 < |b.toReal| := lt_of_lt_of_le hd0 hB
  have hQ : |a.toReal / b.toReal| ≤ (|ra| + εa) / (|rb| - εb) := by
    rw [abs_div]
    exact div_le_div₀ (by positivity) ha.abs_le hd0 hB
  obtain ⟨hf, he⟩ := div_err_all ha.fin hb.fin hb0' (hQ.trans hM)
  have hd : |a.toReal / b.toReal - ra / rb| ≤ (|rb| * εa + |ra| * εb) / (|rb| * (|rb| - εb)) := by
    have hrb0 : rb ≠ 0 := by intro h; rw [h, abs_zero] at hrb; exact lt_irrefl _ hrb
    rw [div_sub_div _ _ hb0' hrb0, abs_div, abs_mul]
    have hnum : |a.toReal * rb - b.toReal * ra| ≤ |rb| * εa + |ra| * εb := by
      have e1 : a.toReal * rb - b.toReal * ra = (a.toReal - ra) * rb - ra * (b.toReal - rb) := by
        ring
      rw [e1]
      calc |(a.toReal - ra) * rb - ra * (b.toReal - rb)|
          ≤ |a.toReal - ra| * |rb| + |ra| * |b.toReal - rb| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ εa * |rb| + |ra| * εb := by gcongr; exacts [ha.err, hb.err]
        _ = _ := by ring
    exact div_le_div₀ (by positivity) hnum (by positivity)
      (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hB hrb.le)
  refine ⟨hf, ?_⟩
  calc |(a / b).toReal - ra / rb|
      ≤ |(a / b).toReal - a.toReal / b.toReal| + |a.toReal / b.toReal - ra / rb| :=
        abs_sub_le _ _ _
    _ ≤ (2 ^ (-53 : ℤ) * ((|ra| + εa) / (|rb| - εb)) + 2 ^ (-1075 : ℤ)) +
          (|rb| * εa + |ra| * εb) / (|rb| * (|rb| - εb)) := by
        gcongr
        exact he.trans (by gcongr)
    _ = _ := by ring

/-- `√`: a nonnegative float within `εa` of `ra ≥ 0`. -/
theorem sqrt (ha : Near a ra εa) (h0 : 0 ≤ a.toReal) (hra : 0 ≤ ra)
    (hM : ra + εa ≤ maxFinite) :
    Near (Float.sqrt a) (Real.sqrt ra)
      (Real.sqrt εa + 2 ^ (-53 : ℤ) * Real.sqrt (ra + εa) + 2 ^ (-1075 : ℤ)) := by
  have hle : a.toReal ≤ ra + εa := ha.toReal_le
  obtain ⟨hf, he⟩ := sqrt_err_all ha.fin h0 (hle.trans hM)
  refine ⟨hf, ?_⟩
  calc |(Float.sqrt a).toReal - Real.sqrt ra|
      ≤ |(Float.sqrt a).toReal - Real.sqrt a.toReal| + |Real.sqrt a.toReal - Real.sqrt ra| :=
        abs_sub_le _ _ _
    _ ≤ (2 ^ (-53 : ℤ) * Real.sqrt (ra + εa) + 2 ^ (-1075 : ℤ)) + Real.sqrt εa := by
        gcongr
        · exact he.trans (by gcongr)
        · exact (Real.abs_sqrt_sub_sqrt_le_sqrt_abs h0 hra).trans
            (Real.sqrt_le_sqrt ha.err)
    _ = _ := by ring

end Near

end Float
