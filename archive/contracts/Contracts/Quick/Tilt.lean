import FloatModel.Lit
import Contracts.Quick.Order

/-!
# Q3: the lean-angle limiter of the position controller

`AC_PosControl::NE_update_controller` limits the horizontal acceleration target with
`limit_accel_xy(vel_desired / vel_max, accel_target, accel_max)` (`AP_Math/control.cpp:461-509`),
`accel_max = 9.80665 · tanf(min(althold_lean_angle_max, get_lean_angle_max_rad()))`, and
`get_thrust_vector` returns `(accel_target.x, accel_target.y, -9.80665)`; so a bound on the limiter's
output is a bound on the tangent of the thrust vector's tilt.

* `limit_accel_xy_bound`: for finite accelerations below `2^40` and a finite limit of at least
  `2^-23`, **when the reference velocity is zero** (`is_positive(|vel_desired / vel_max|)` false:
  hover, start and end of a leg) the output's length is at most `accel_max (1 + 2^-19) + 2^-70`.
  Two branches: the input already within the limit (`within_bound`, from the `float` comparison
  `length_squared ≤ sq(accel_max)`), and the isotropic `Vector2f::limit_length`
  (`limit_length_bound`).
* `limit_length_bound`: `Vector2f::limit_length` keeps the length within `m (1 + 2^-19) + 2^-70`.
* `flen_ge`: the `float` length `sqrtf(x*x + y*y)` bounds the exact length from above up to
  `(1 + 2^-21)` and `2^-74` (the rounding core shared with Q2).

**Q3 as posed is false** (`QUICK.md`): with a non-zero reference velocity, `limit_accel_xy` limits
the along-track and cross-track components separately and in `float` the result can exceed the limit
when the unlimited acceleration is large: `quick_cex q3` finds `|out| = 1.2435 · accel_max` for the
finite input `accel = (-1507693, 30746904)`, `vel_norm = (-0.03738, 0.7623)`, and at tick level a
finite velocity sample `2·10^7 m/s` off the target gives `|thrust_NE| = 1.0114 · g tan(30°)`
(`quick_cex q3t`); a NaN acceleration passes the limiter (`quick_cex q6b`).

Q7: the limiter has no period argument; the statements hold for every `dt`.
-/

open Float.Model UnpackedFloat

namespace Contracts.Quick

theorem maxF_big : (2 : ℝ) ^ 100 ≤ maxFinite32 := by
  rw [maxFinite32]; norm_num

theorem u24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
theorem e150 : (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 := by norm_num

/-- A finite `float` square of a value below `2^40`: finite, nonnegative, within the rounding
bound. -/
theorem fsq {a : Float32} (ha : a.IsFinite) (hb : |a.toReal| ≤ 2 ^ 40) :
    (a * a).IsFinite ∧ 0 ≤ (a * a).toReal ∧
      |(a * a).toReal - a.toReal ^ 2| ≤ a.toReal ^ 2 / 16777216 + 1 / 2 ^ 150 := by
  have hm : |a.toReal * a.toReal| ≤ maxFinite32 := by
    rw [abs_mul_self]
    have : a.toReal * a.toReal ≤ 2 ^ 80 := by nlinarith [abs_nonneg a.toReal, sq_abs a.toReal]
    linarith [maxF_big, show (2 : ℝ) ^ 80 ≤ 2 ^ 100 by norm_num]
  obtain ⟨hf, he⟩ := Float32.mul_err_all ha ha hm
  refine ⟨hf, ((Float32.mul_bracket ha ha hm Float32.isFinite_zero).1
    (by rw [Float32.toReal_zero]; nlinarith)).trans_eq' Float32.toReal_zero.symm, ?_⟩
  rw [abs_mul_self, u24, e150] at he
  rw [sq]; linarith

set_option maxHeartbeats 1000000 in
/-- **The `float` length bounds the vector**: for finite `a, b` below `2^40`, the length
`sqrt(a*a + b*b)` computed in `float` is finite, and the exact squared length is at most
`(L (1 + 2^-21) + 2^-74)^2`. -/
theorem flen_ge {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (ha' : |a.toReal| ≤ 2 ^ 40)
    (hb' : |b.toReal| ≤ 2 ^ 40) :
    (Float32.sqrt (a * a + b * b)).IsFinite ∧ 0 ≤ (Float32.sqrt (a * a + b * b)).toReal ∧
      (Float32.sqrt (a * a + b * b)).toReal ≤ 2 ^ 42 ∧ a.toReal ^ 2 + b.toReal ^ 2 ≤
        ((Float32.sqrt (a * a + b * b)).toReal * (1 + 1 / 2 ^ 21) + 1 / 2 ^ 74) ^ 2 := by
  obtain ⟨fa, na, ea⟩ := fsq ha ha'
  obtain ⟨fb, nb, eb⟩ := fsq hb hb'
  set x := a.toReal
  set y := b.toReal
  set sa := (a * a).toReal
  set sb := (b * b).toReal
  have hx2 : x ^ 2 ≤ 2 ^ 80 := by nlinarith [abs_nonneg x, sq_abs x]
  have hy2 : y ^ 2 ≤ 2 ^ 80 := by nlinarith [abs_nonneg y, sq_abs y]
  have hsa : sa ≤ 2 ^ 81 := by have := (abs_le.1 ea).2; nlinarith
  have hsb : sb ≤ 2 ^ 81 := by have := (abs_le.1 eb).2; nlinarith
  have hm : |sa + sb| ≤ maxFinite32 := by
    rw [abs_of_nonneg (by linarith)]; linarith [maxF_big, show (2 : ℝ) ^ 82 ≤ 2 ^ 100 by norm_num]
  obtain ⟨fS, eS⟩ := Float32.add_err_all fa fb hm
  set S := (a * a + b * b).toReal
  rw [abs_of_nonneg (by linarith : 0 ≤ sa + sb), u24] at eS
  have hS0 : 0 ≤ S := by have := (abs_le.1 eS).1; nlinarith
  have hS1 : S ≤ maxFinite32 := by
    have := (abs_le.1 eS).2; linarith [maxF_big, show (2 : ℝ) ^ 83 ≤ 2 ^ 100 by norm_num]
  obtain ⟨fL, eL⟩ := Float32.sqrt_err_all fS hS0 hS1
  set L := (Float32.sqrt (a * a + b * b)).toReal
  rw [u24, e150] at eL
  have hsq := Real.sqrt_nonneg S
  have hsqS := Real.sq_sqrt hS0
  have hL0 : 0 ≤ L :=
    ((Float32.sqrt_bracket fS hS0 hS1 Float32.isFinite_zero).1
      (by rw [Float32.toReal_zero]; exact hsq)).trans_eq' Float32.toReal_zero.symm
  have hLup : L ≤ 2 ^ 42 := by
    have hS83 : S ≤ 2 ^ 83 := by have := (abs_le.1 eS).2; linarith
    have hsq83 : Real.sqrt S ≤ 2 ^ 42 := by
      rw [Real.sqrt_le_left (by positivity)]; linarith
    have := (abs_le.1 eL).2; nlinarith
  refine ⟨fL, hL0, hLup, ?_⟩
  -- √S ≤ (L + η) / (1 - u)
  have h1 : Real.sqrt S * (1 - 1 / 16777216) ≤ L + 1 / 2 ^ 150 := by
    have := (abs_le.1 eL).1; linarith
  -- S ≥ (sa + sb)(1 - u),  sa + sb ≥ (x² + y²)(1 - u) - 2η
  have h2 : (sa + sb) * (1 - 1 / 16777216) ≤ S := by have := (abs_le.1 eS).1; linarith
  have h3 : (x ^ 2 + y ^ 2) * (1 - 1 / 16777216) - 2 * (1 / 2 ^ 150) ≤ sa + sb := by
    have := (abs_le.1 ea).1; have := (abs_le.1 eb).1; linarith
  set k : ℝ := 1 - 1 / 16777216 with hk
  set c : ℝ := 1 + 1 / 2 ^ 21 with hc
  set τ : ℝ := 1 / 2 ^ 74 with hτ
  set η : ℝ := 1 / 2 ^ 150 with hη
  have hk0 : 0 < k := by norm_num [hk]
  have hk1 : k ≤ 1 := by norm_num [hk]
  have hck : 1 ≤ c * k ^ 2 := by norm_num [hk, hc]
  have hτη : η ≤ τ * k ^ 4 * c := by norm_num [hk, hc, hτ, hη]
  have hτ2 : η ^ 2 + 2 * η ≤ τ ^ 2 * k ^ 4 := by norm_num [hk, hτ, hη]
  have hη0 : 0 ≤ η := by norm_num [hη]
  have hτ0 : 0 ≤ τ := by norm_num [hτ]
  have e1 : (x ^ 2 + y ^ 2) * k ^ 2 ≤ S + 2 * η * k := by
    have := mul_le_mul_of_nonneg_right h3 hk0.le
    have h2k : (sa + sb) * k ≤ S := h2
    nlinarith only [this, h2k, hk0, hη0]
  have e2 : S * k ^ 2 ≤ (L + η) ^ 2 := by
    have h0 : 0 ≤ Real.sqrt S * k := by positivity
    have := pow_le_pow_left₀ h0 h1 2
    rwa [mul_pow, hsqS] at this
  have e3 : (x ^ 2 + y ^ 2) * k ^ 4 ≤ (L + η) ^ 2 + 2 * η := by
    have h := mul_le_mul_of_nonneg_right e1 (sq_nonneg k)
    have hk3 : k ^ 3 ≤ 1 := pow_le_one₀ hk0.le hk1
    nlinarith only [h, e2, hk3, hη0]
  have e4 : (L + η) ^ 2 + 2 * η ≤ (L * c + τ) ^ 2 * k ^ 4 := by
    have h1' : L ^ 2 ≤ L ^ 2 * (c * k ^ 2) ^ 2 := by
      have : 1 ≤ (c * k ^ 2) ^ 2 := by nlinarith only [hck]
      nlinarith only [this, sq_nonneg L]
    have h2' : 2 * L * η ≤ 2 * L * (τ * k ^ 4 * c) := by nlinarith only [hτη, hL0]
    nlinarith only [h1', h2', hτ2]
  have hk4 : 0 < k ^ 4 := by positivity
  exact le_of_mul_le_mul_right (e3.trans e4) hk4

/-- Minkowski in the plane. -/
theorem norm2_add_le (a b c d : ℝ) :
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤ Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  have hA := Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by positivity)
  have hC := Real.sq_sqrt (show 0 ≤ c ^ 2 + d ^ 2 by positivity)
  have hA0 := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
  have hC0 := Real.sqrt_nonneg (c ^ 2 + d ^ 2)
  rw [Real.sqrt_le_left (by positivity)]
  have cs : a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
    have h1 : (a * c + b * d) ^ 2 ≤ (Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2)) ^ 2 := by
      rw [mul_pow, hA, hC]; nlinarith [sq_nonneg (a * d - b * c)]
    exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  nlinarith

theorem sqrt_sq_le_of {N L : ℝ} (hL : 0 ≤ L) (h : N ^ 2 ≤ L ^ 2) : Real.sqrt (N ^ 2) ≤ L := by
  rw [Real.sqrt_le_left hL]; exact h

theorem unpack_eps : (1.1920929e-7 : Float32).toModel.unpack =
    .finite .positive 8388608 (-46) (by decide) := by f32_unpack
theorem toReal_eps : (1.1920929e-7 : Float32).toReal = 1 / 2 ^ 23 := by
  rw [Float32.toReal_of_unpack unpack_eps]; simp [Sign.apply]; norm_num
theorem isFinite_eps : (1.1920929e-7 : Float32).IsFinite := Float32.isFinite_of_unpack unpack_eps

/-- The plane norm. -/
noncomputable def N2 (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

theorem N2_nonneg (a b : ℝ) : 0 ≤ N2 a b := Real.sqrt_nonneg _

theorem N2_le_of_sq {a b B : ℝ} (hB : 0 ≤ B) (h : a ^ 2 + b ^ 2 ≤ B ^ 2) : N2 a b ≤ B := by
  rw [N2, Real.sqrt_le_left hB]; exact h

theorem abs_le_N2 (a b : ℝ) : |a| ≤ N2 a b ∧ |b| ≤ N2 a b := by
  constructor
  · rw [N2, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])
  · rw [N2, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])

theorem N2_smul (q a b : ℝ) : N2 (q * a) (q * b) = |q| * N2 a b := by
  rw [N2, N2, show (q * a) ^ 2 + (q * b) ^ 2 = q ^ 2 * (a ^ 2 + b ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq_eq_abs]

theorem N2_add_le (a b c d : ℝ) : N2 (a + c) (b + d) ≤ N2 a b + N2 c d := norm2_add_le a b c d

theorem N2_le_abs_add (c d : ℝ) : N2 c d ≤ |c| + |d| := by
  apply N2_le_of_sq (by positivity)
  nlinarith [abs_nonneg c, abs_nonneg d, sq_abs c, sq_abs d]

open AC_PosControl_lib in
set_option maxHeartbeats 2000000 in
/-- **`Vector2f::limit_length` keeps the length within the limit** (up to rounding): for finite
components below `2^40` and a finite limit of at least `2^-23`, the result is finite and its length
is at most `m (1 + 2^-19) + 2^-70`. -/
theorem limit_length_bound (v : Vector2f.State) (m : Float32) (hx : v.x.IsFinite)
    (hy : v.y.IsFinite) (hx' : |v.x.toReal| ≤ 2 ^ 40) (hy' : |v.y.toReal| ≤ 2 ^ 40)
    (hm : m.IsFinite) (hm1 : 1 / 2 ^ 23 ≤ m.toReal) :
    (Vector2f.limit_length v m).1.x.IsFinite ∧ (Vector2f.limit_length v m).1.y.IsFinite ∧
      N2 (Vector2f.limit_length v m).1.x.toReal (Vector2f.limit_length v m).1.y.toReal ≤
        m.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70 := by
  obtain ⟨fL, hL0, hLup, hN⟩ := flen_ge hx hy hx' hy'
  have hdef : Vector2f.limit_length v m =
      if (decide (Float32.sqrt (v.x * v.x + v.y * v.y) > m) &&
        is_positive_float (Float32.sqrt (v.x * v.x + v.y * v.y))) = true then
        ({ x := v.x * (m / Float32.sqrt (v.x * v.x + v.y * v.y)),
           y := v.y * (m / Float32.sqrt (v.x * v.x + v.y * v.y)) }, true)
      else (v, false) := by
    unfold Vector2f.limit_length Vector2f.length norm_float2 sq_float
    rfl
  rw [hdef]
  set L := (Float32.sqrt (v.x * v.x + v.y * v.y)).toReal with hLdef
  set x := v.x.toReal
  set y := v.y.toReal
  set c : ℝ := 1 + 1 / 2 ^ 21
  set τ : ℝ := 1 / 2 ^ 74
  have hNv : N2 x y ≤ L * c + τ := N2_le_of_sq (by positivity) hN
  have hm0 : 0 < m.toReal := lt_of_lt_of_le (by norm_num) hm1
  by_cases hcb : (decide ((v.x * v.x + v.y * v.y).sqrt > m) &&
      is_positive_float (v.x * v.x + v.y * v.y).sqrt) = true
  case neg =>
    rw [ite_eq_right hcb]
    refine ⟨hx, hy, ?_⟩
    simp only [Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not, is_positive_float,
      id_run, id_pure] at hcb
    have hb : L ≤ m.toReal := by
      rcases hcb with h | h
      · have h' : ¬ m < (v.x * v.x + v.y * v.y).sqrt := h
        rw [Float32.lt_iff_toReal_lt hm fL] at h'; exact not_lt.1 h'
      · have h' : ¬ (1.1920929e-7 : Float32) ≤ (v.x * v.x + v.y * v.y).sqrt := by simpa using h
        rw [Float32.le_iff_toReal_le isFinite_eps fL, toReal_eps] at h'
        linarith [not_le.1 h']
    have : L * c ≤ m.toReal * c := by nlinarith [show (0 : ℝ) ≤ c by positivity]
    have hc : c = 1 + 1 / 2 ^ 21 := rfl
    have hτ : τ = 1 / 2 ^ 74 := rfl
    rw [hc] at this; rw [hτ] at hNv
    nlinarith
  case pos =>
    rw [ite_eq_left hcb]
    simp only [Bool.and_eq_true, decide_eq_true_eq, is_positive_float, id_run, id_pure] at hcb
    obtain ⟨hgt, hpos⟩ := hcb
    have hgt' : m < (v.x * v.x + v.y * v.y).sqrt := hgt
    rw [Float32.lt_iff_toReal_lt hm fL] at hgt'
    have hpos' : (1.1920929e-7 : Float32) ≤ (v.x * v.x + v.y * v.y).sqrt := hpos
    rw [Float32.le_iff_toReal_le isFinite_eps fL, toReal_eps] at hpos'
    have hgt := hgt'
    have hpos := hpos'
    have hL1 : 0 < L := lt_of_lt_of_le (by norm_num) hpos
    -- the factor `q = m / L`
    have hqd : |m.toReal / L| ≤ maxFinite32 := by
      rw [abs_of_nonneg (by positivity)]
      have : m.toReal / L ≤ 1 := (div_le_one hL1).2 hgt.le
      linarith [Float32.one_le_maxFinite32]
    obtain ⟨fq, eq⟩ := Float32.div_err_all hm fL hL1.ne' hqd
    set q := (m / Float32.sqrt (v.x * v.x + v.y * v.y)).toReal
    rw [abs_of_nonneg (div_nonneg hm0.le hL1.le), u24, e150] at eq
    have hq1 : m.toReal / L ≤ 1 := (div_le_one hL1).2 hgt.le
    have hqabs : |q| ≤ m.toReal / L * (1 + 1 / 16777216) + 1 / 2 ^ 150 := by
      rw [abs_le]; constructor
      · have := (abs_le.1 eq).1
        have : 0 ≤ m.toReal / L := by positivity
        nlinarith
      · have := (abs_le.1 eq).2; linarith
    have hq2 : |q| ≤ 2 := by
      have : m.toReal / L * (1 + 1 / 16777216) ≤ 1 + 1 / 16777216 := by nlinarith
      linarith [show (1 : ℝ) / 2 ^ 150 ≤ 1 / 2 by norm_num]
    -- the products `x q`, `y q`
    have hxq : |x * q| ≤ maxFinite32 := by
      rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg q, maxF_big]
    have hyq : |y * q| ≤ maxFinite32 := by
      rw [abs_mul]; nlinarith [abs_nonneg y, abs_nonneg q, maxF_big]
    obtain ⟨fx, ex⟩ := Float32.mul_err_all hx fq hxq
    obtain ⟨fy, ey⟩ := Float32.mul_err_all hy fq hyq
    rw [u24, e150] at ex ey
    refine ⟨fx, fy, ?_⟩
    try dsimp only
    set X := (v.x * (m / Float32.sqrt (v.x * v.x + v.y * v.y))).toReal
    set Y := (v.y * (m / Float32.sqrt (v.x * v.x + v.y * v.y))).toReal
    have hsplit : N2 X Y ≤ N2 (q * x) (q * y) + N2 (X - x * q) (Y - y * q) := by
      have := N2_add_le (q * x) (q * y) (X - x * q) (Y - y * q)
      rwa [show q * x + (X - x * q) = X by ring, show q * y + (Y - y * q) = Y by ring] at this
    rw [N2_smul] at hsplit
    have herr := N2_le_abs_add (X - x * q) (Y - y * q)
    obtain ⟨hax, hay⟩ := abs_le_N2 x y
    have hNx0 := N2_nonneg x y
    -- |q| N(x, y) ≤ m (1 + u) c + (1 + u) τ + η (L c + τ)
    have hmain : |q| * N2 x y ≤ m.toReal * (1 + 1 / 16777216) * c + (1 + 1 / 16777216) * τ +
        1 / 2 ^ 150 * (2 ^ 42 * c + τ) := by
      have h1 : |q| * N2 x y ≤ (m.toReal / L * (1 + 1 / 16777216) + 1 / 2 ^ 150) * (L * c + τ) :=
        mul_le_mul hqabs hNv hNx0 (by positivity)
      have h2 : m.toReal / L * L = m.toReal := div_mul_cancel₀ _ hL1.ne'
      have h3 : m.toReal / L * τ ≤ τ := by nlinarith [show (0 : ℝ) ≤ τ by positivity]
      have h4 : 1 / 2 ^ 150 * (L * c + τ) ≤ 1 / 2 ^ 150 * (2 ^ 42 * c + τ) := by
        have : 0 ≤ c := by positivity
        nlinarith
      nlinarith
    have hex : |X - x * q| ≤ |x * q| / 16777216 + 1 / 2 ^ 150 := by
      rw [show |x * q| / 16777216 = 1 / 16777216 * |x * q| by ring]; exact ex
    have hey : |Y - y * q| ≤ |y * q| / 16777216 + 1 / 2 ^ 150 := by
      rw [show |y * q| / 16777216 = 1 / 16777216 * |y * q| by ring]; exact ey
    have hxq' : |x * q| ≤ 2 * N2 x y := by rw [abs_mul]; nlinarith [abs_nonneg q, abs_nonneg x]
    have hyq' : |y * q| ≤ 2 * N2 x y := by rw [abs_mul]; nlinarith [abs_nonneg q, abs_nonneg y]
    have hNup : N2 x y ≤ 2 ^ 42 * c + τ := by
      have : L * c ≤ 2 ^ 42 * c := by nlinarith [show (0 : ℝ) ≤ c by positivity]
      linarith
    -- assemble
    have hfin : |q| * N2 x y + (|x * q| / 16777216 + 1 / 2 ^ 150 + (|y * q| / 16777216 + 1 / 2 ^ 150))
        ≤ m.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70 := by
      -- |x q| + |y q| ≤ 2 |q| N(x,y) ≤ 2 (m (1+u) c + small)
      have hxyq : |x * q| + |y * q| ≤ 2 * (|q| * N2 x y) := by
        rw [abs_mul, abs_mul]; nlinarith [abs_nonneg q]
      have hc : c = 1 + 1 / 2 ^ 21 := rfl
      have hτ : τ = 1 / 2 ^ 74 := rfl
      rw [hc, hτ] at hmain
      nlinarith
    linarith

open AC_PosControl_lib in
theorem limit_accel_xy_within (v a : Vector2f.State) (m : Float32)
    (h1 : is_positive_float m = true) (h2 : Vector2f.length_squared a ≤ sq_float m) :
    limit_accel_xy v a m = (a, false) := by
  unfold limit_accel_xy
  simp [h1, h2]

open AC_PosControl_lib in
theorem limit_accel_xy_iso (v a : Vector2f.State) (m : Float32)
    (h1 : is_positive_float m = true) (h2 : ¬ Vector2f.length_squared a ≤ sq_float m)
    (h3 : is_positive_float (Vector2f.length v) = false) :
    limit_accel_xy v a m = ((Vector2f.limit_length a m).1, true) := by
  unfold limit_accel_xy
  simp [h1, h2, h3]

set_option maxHeartbeats 1000000 in
/-- A `float` squared length below a `float` squared limit: the exact length is within the limit
up to rounding. -/
theorem within_bound {a b m : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hm : m.IsFinite)
    (ha' : |a.toReal| ≤ 2 ^ 40) (hb' : |b.toReal| ≤ 2 ^ 40) (hm0 : 0 ≤ m.toReal)
    (hm' : m.toReal ≤ 2 ^ 40) (h : a * a + b * b ≤ m * m) :
    N2 a.toReal b.toReal ≤ m.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70 := by
  obtain ⟨fa, na, ea⟩ := fsq ha ha'
  obtain ⟨fb, nb, eb⟩ := fsq hb hb'
  obtain ⟨fm, nm, em⟩ := fsq hm (by rw [abs_of_nonneg hm0]; exact hm')
  set x := a.toReal
  set y := b.toReal
  set sa := (a * a).toReal
  set sb := (b * b).toReal
  have hx2 : x ^ 2 ≤ 2 ^ 80 := by nlinarith [abs_nonneg x, sq_abs x]
  have hy2 : y ^ 2 ≤ 2 ^ 80 := by nlinarith [abs_nonneg y, sq_abs y]
  have hsa : sa ≤ 2 ^ 81 := by have := (abs_le.1 ea).2; nlinarith
  have hsb : sb ≤ 2 ^ 81 := by have := (abs_le.1 eb).2; nlinarith
  have hmS : |sa + sb| ≤ maxFinite32 := by
    rw [abs_of_nonneg (by linarith)]; linarith [maxF_big, show (2 : ℝ) ^ 82 ≤ 2 ^ 100 by norm_num]
  obtain ⟨fS, eS⟩ := Float32.add_err_all fa fb hmS
  rw [abs_of_nonneg (by linarith : 0 ≤ sa + sb), u24] at eS
  have hle := (Float32.le_iff_toReal_le fS fm).1 h
  set S := (a * a + b * b).toReal
  set M := (m * m).toReal
  have e1 : (sa + sb) * (1 - 1 / 16777216) ≤ S := by have := (abs_le.1 eS).1; linarith
  have e2 : (x ^ 2 + y ^ 2) * (1 - 1 / 16777216) - 2 * (1 / 2 ^ 150) ≤ sa + sb := by
    have := (abs_le.1 ea).1; have := (abs_le.1 eb).1; linarith
  have e3 : M ≤ m.toReal ^ 2 * (1 + 1 / 16777216) + 1 / 2 ^ 150 := by
    have := (abs_le.1 em).2; linarith
  apply N2_le_of_sq (by positivity)
  set k : ℝ := 1 - 1 / 16777216 with hk
  have hk0 : 0 < k := by norm_num [hk]
  clear_value x y sa sb S M k
  have e4 : (x ^ 2 + y ^ 2) * k ^ 2 ≤ m.toReal ^ 2 * (1 + 1 / 16777216) + 3 * (1 / 2 ^ 150) := by
    have := mul_le_mul_of_nonneg_right e2 hk0.le
    have hk1 : k ≤ 1 := by norm_num [hk]
    have t1 : (x ^ 2 + y ^ 2) * k ^ 2 - 2 * (1 / 2 ^ 150) * k ≤ (sa + sb) * k := by
      have h := this
      have hr : ((x ^ 2 + y ^ 2) * k - 2 * (1 / 2 ^ 150)) * k =
          (x ^ 2 + y ^ 2) * k ^ 2 - 2 * (1 / 2 ^ 150) * k := by ring
      rw [hr] at h; exact h
    linarith
  have e5 : m.toReal ^ 2 * (1 + 1 / 16777216) + 3 * (1 / 2 ^ 150) ≤
      (m.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70) ^ 2 * k ^ 2 := by
    have hc : (1 + 1 / 16777216 : ℝ) ≤ (1 + 1 / 2 ^ 19) ^ 2 * k ^ 2 := by norm_num [hk]
    have ht : 3 * (1 / 2 ^ 150 : ℝ) ≤ (1 / 2 ^ 70) ^ 2 * k ^ 2 := by norm_num [hk]
    have hmid : 0 ≤ 2 * m.toReal * (1 + 1 / 2 ^ 19) * (1 / 2 ^ 70) * k ^ 2 := by positivity
    have hexp : (m.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70) ^ 2 * k ^ 2 =
        m.toReal ^ 2 * ((1 + 1 / 2 ^ 19) ^ 2 * k ^ 2) +
          2 * m.toReal * (1 + 1 / 2 ^ 19) * (1 / 2 ^ 70) * k ^ 2 + (1 / 2 ^ 70) ^ 2 * k ^ 2 := by
      ring
    rw [hexp]
    have := mul_le_mul_of_nonneg_left hc (sq_nonneg m.toReal)
    linarith
  have hk2 : 0 < k ^ 2 := by positivity
  exact le_of_mul_le_mul_right (e4.trans e5) hk2

open AC_PosControl_lib in
/-- **Q3, the limiter of `AC_PosControl::NE_update_controller`** (`limit_accel_xy`,
`AP_Math/control.cpp:461-509`), for finite accelerations below `2^40` and a finite limit of at
least `2^-23`: when the reference velocity is (numerically) zero, the output's length is within the
limit (up to rounding, `(1 + 2^-19)` and `2^-70`). The output is the input when its `float` squared
length is within the squared limit, and `Vector2f::limit_length` of it otherwise (the isotropic
branch). When the reference velocity is not zero the prioritised branch (along-track and
cross-track components limited separately) can exceed the limit in `float`: see `QUICK.md`. -/
theorem limit_accel_xy_bound (v a : Vector2f.State) (m : Float32) (hx : a.x.IsFinite)
    (hy : a.y.IsFinite) (hx' : |a.x.toReal| ≤ 2 ^ 40) (hy' : |a.y.toReal| ≤ 2 ^ 40)
    (hm : m.IsFinite) (hm1 : 1 / 2 ^ 23 ≤ m.toReal) (hm2 : m.toReal ≤ 2 ^ 40)
    (hv : is_positive_float (Vector2f.length v) = false) :
    (limit_accel_xy v a m).1.x.IsFinite ∧ (limit_accel_xy v a m).1.y.IsFinite ∧
      N2 (limit_accel_xy v a m).1.x.toReal (limit_accel_xy v a m).1.y.toReal ≤
        m.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70 := by
  have h1 : is_positive_float m = true := by
    show decide (m ≥ (1.1920929e-7 : Float32)) = true
    rw [decide_eq_true_iff, ge_iff_le, Float32.le_iff_toReal_le isFinite_eps hm, toReal_eps]
    exact hm1
  by_cases h2 : Vector2f.length_squared a ≤ sq_float m
  · rw [limit_accel_xy_within v a m h1 h2]
    exact ⟨hx, hy, within_bound hx hy hm hx' hy' (by linarith) hm2 h2⟩
  · rw [limit_accel_xy_iso v a m h1 h2 hv]
    exact limit_length_bound a m hx hy hx' hy' hm hm1

end Contracts.Quick
