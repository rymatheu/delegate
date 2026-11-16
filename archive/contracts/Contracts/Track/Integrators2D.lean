import Contracts.Track.Integrators
import Contracts.Quick.Tilt

/-!
# M2 for the horizontal velocity PID (`AC_PID_2D`, a 2-vector integrator)

The 2-vector integrator is limited by `Vector2f::limit_length(IMAX)` (`AC_PID_2D::update_i`,
`set_integrator`), which scales the vector by `IMAX / |v|` when its `float` length exceeds `IMAX`.
With rounding the length after the limit is within `IMAX (1 + 2^-19) + 2^-70`
(`Contracts.Quick.limit_length_bound`), for an integrator whose components are finite and below
`2^40` before the limit, and `IMAX ≥ 2^-23`.

Unlike the scalar clamp, `limit_length` does **not** remove a NaN. On a NaN length the comparison
`len > IMAX` is false, so the vector is kept (`limit_length_keeps_nan`). An infinite component
does not help either: it makes the length infinite, the scale is then `IMAX / ∞ = 0`, and
`∞ · 0` is NaN. So the bound needs finite inputs to the step that `update_i` adds, `(e · ki) · dt`.
Here they are taken as `|e| ≤ 2^19` and `|ki|, |dt| ≤ 2^9`, all finite (`StepOK`), which keeps the
step below `2^38`. `AC_PID_2D::update_all` rejects a non-finite target or measurement. It does not
guard against a NaN or an overflow produced inside it: through `dt`, through `ki`, or by the error
filter on huge finite values.
-/

namespace Contracts.Track.TwoD

open AC_PosControl_lib Contracts.Quick Float.Model.UnpackedFloat

/-- The bound `limit_length(IMAX)` leaves: `IMAX (1 + 2^-19) + 2^-70`. -/
noncomputable def B2D (k : Float32) : ℝ := k.toReal * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 70

/-- A 2-vector integrator within its limit: finite components, length at most `B2D IMAX`. -/
def VB (k : Float32) (v : Vector2f.State) : Prop :=
  v.x.IsFinite ∧ v.y.IsFinite ∧ N2 v.x.toReal v.y.toReal ≤ B2D k

/-- A 2D limit as `limit_length` needs it. -/
structure K2OK (k : Float32) : Prop where
  fin : k.IsFinite
  lo : 1 / 2 ^ 23 ≤ k.toReal
  hi : k.toReal ≤ 2 ^ 30

/-- Finite components below `B`. -/
def CB (B : ℝ) (v : Vector2f.State) : Prop :=
  v.x.IsFinite ∧ v.y.IsFinite ∧ |v.x.toReal| ≤ B ∧ |v.y.toReal| ≤ B

theorem VB_limit_length {k : Float32} (hk : K2OK k) {v : Vector2f.State} (hv : CB (2 ^ 40) v) :
    VB k (Vector2f.limit_length v k).1 :=
  limit_length_bound v k hv.1 hv.2.1 hv.2.2.1 hv.2.2.2 hk.fin hk.lo

theorem VB.cb {k : Float32} (hk : K2OK k) {v : Vector2f.State} (h : VB k v) : CB (2 ^ 31) v := by
  have hB : B2D k ≤ 2 ^ 31 := by
    unfold B2D; have := hk.hi; nlinarith
  exact ⟨h.1, h.2.1, ((abs_le_N2 _ _).1.trans h.2.2).trans hB,
    ((abs_le_N2 _ _).2.trans h.2.2).trans hB⟩

/-! ## Float steps -/

theorem maxF_ge : (2 : ℝ) ^ 100 ≤ maxFinite32 := by rw [maxFinite32]; norm_num

/-- A product with a factor in `[0, 1]` does not grow. -/
theorem mul_shrink {x q : Float32} (hx : x.IsFinite) (hxb : |x.toReal| ≤ 2 ^ 40) (hq : q.IsFinite)
    (hq0 : 0 ≤ q.toReal) (hq1 : q.toReal ≤ 1) :
    (x * q).IsFinite ∧ |(x * q).toReal| ≤ |x.toReal| := by
  have hp : |x.toReal * q.toReal| ≤ |x.toReal| := by
    rw [abs_mul, abs_of_nonneg hq0]; nlinarith [abs_nonneg x.toReal]
  have hM : |x.toReal * q.toReal| ≤ maxFinite32 := hp.trans (hxb.trans (by
    linarith [maxF_ge, show (2 : ℝ) ^ 40 ≤ 2 ^ 100 by norm_num]))
  refine ⟨(Float32.mul_err_all hx hq hM).1, ?_⟩
  have hb0 := Float32.mul_bracket hx hq hM Float32.isFinite_zero
  have hbx := Float32.mul_bracket hx hq hM hx
  rw [Float32.toReal_zero] at hb0
  rcases le_total 0 x.toReal with h | h
  · rw [abs_of_nonneg h, abs_le]
    have h1 : 0 ≤ (x * q).toReal := hb0.1 (by positivity)
    have h2 : (x * q).toReal ≤ x.toReal := hbx.2 (by nlinarith)
    constructor <;> linarith
  · rw [abs_of_nonpos h, abs_le]
    have h1 : (x * q).toReal ≤ 0 := hb0.2 (by nlinarith)
    have h2 : x.toReal ≤ (x * q).toReal := hbx.1 (by nlinarith)
    constructor <;> linarith

/-- A quotient `m / L` with `0 ≤ m < L` is a finite float in `[0, 1]`. -/
theorem div_unit {m L : Float32} (hm : m.IsFinite) (hm0 : 0 ≤ m.toReal) (hL : L.IsFinite)
    (hlt : m.toReal < L.toReal) :
    (m / L).IsFinite ∧ 0 ≤ (m / L).toReal ∧ (m / L).toReal ≤ 1 := by
  have hL0 : 0 < L.toReal := lt_of_le_of_lt hm0 hlt
  have hq : m.toReal / L.toReal ≤ 1 := (div_le_one hL0).2 hlt.le
  have hq0 : 0 ≤ m.toReal / L.toReal := by positivity
  have hM : |m.toReal / L.toReal| ≤ maxFinite32 := by
    rw [abs_of_nonneg hq0]; linarith [Float32.one_le_maxFinite32]
  have hb0 := Float32.div_bracket hm hL hL0.ne' hM Float32.isFinite_zero
  have hb1 := Float32.div_bracket hm hL hL0.ne' hM Float32.isFinite_one
  rw [Float32.toReal_zero] at hb0
  rw [Float32.toReal_one] at hb1
  exact ⟨(Float32.div_err_all hm hL hL0.ne' hM).1, hb0.1 hq0, hb1.2 hq⟩

/-- A rounded product, crudely: finite and at most twice the exact magnitude plus `2^-150`. -/
theorem mul_crude {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) {A : ℝ}
    (hab : |a.toReal * b.toReal| ≤ A) (hA : A ≤ 2 ^ 100) :
    (a * b).IsFinite ∧ |(a * b).toReal| ≤ A * (1 + 1 / 2 ^ 24) + 1 / 2 ^ 150 := by
  obtain ⟨hf, he⟩ := Float32.mul_err_all ha hb (hab.trans (hA.trans maxF_ge))
  refine ⟨hf, ?_⟩
  have h1 := abs_sub_abs_le_abs_sub (a * b).toReal (a.toReal * b.toReal)
  rw [show (2 : ℝ) ^ (-24 : ℤ) = 1 / 2 ^ 24 by norm_num,
    show (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 by norm_num] at he
  nlinarith [abs_nonneg (a.toReal * b.toReal)]

/-- A rounded sum, crudely. -/
theorem add_crude {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) {A : ℝ}
    (hab : |a.toReal + b.toReal| ≤ A) (hA : A ≤ 2 ^ 100) :
    (a + b).IsFinite ∧ |(a + b).toReal| ≤ A * (1 + 1 / 2 ^ 24) := by
  obtain ⟨hf, he⟩ := Float32.add_err_all ha hb (hab.trans (hA.trans maxF_ge))
  refine ⟨hf, ?_⟩
  have h1 := abs_sub_abs_le_abs_sub (a + b).toReal (a.toReal + b.toReal)
  rw [show (2 : ℝ) ^ (-24 : ℤ) = 1 / 2 ^ 24 by norm_num] at he
  nlinarith [abs_nonneg (a.toReal + b.toReal)]

/-! ## `limit_length` -/

/-- `limit_length` to a finite `m ≥ 0` keeps finite components and does not make them grow (the
first, conditional, limit of `update_i`, to the integrator's previous length). -/
theorem limit_length_shrink (v : Vector2f.State) (m : Float32) (hv : CB (2 ^ 40) v)
    (hm : m.IsFinite) (hm0 : 0 ≤ m.toReal) :
    (Vector2f.limit_length v m).1.x.IsFinite ∧ (Vector2f.limit_length v m).1.y.IsFinite ∧
      |(Vector2f.limit_length v m).1.x.toReal| ≤ |v.x.toReal| ∧
      |(Vector2f.limit_length v m).1.y.toReal| ≤ |v.y.toReal| := by
  obtain ⟨fL, hL0, -, -⟩ := flen_ge hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
  have hdef : Vector2f.limit_length v m =
      if (decide (Float32.sqrt (v.x * v.x + v.y * v.y) > m) &&
        is_positive_float (Float32.sqrt (v.x * v.x + v.y * v.y))) = true then
        ({ x := v.x * (m / Float32.sqrt (v.x * v.x + v.y * v.y)),
           y := v.y * (m / Float32.sqrt (v.x * v.x + v.y * v.y)) }, true)
      else (v, false) := by
    unfold Vector2f.limit_length Vector2f.length norm_float2 sq_float
    rfl
  rw [hdef]
  by_cases hc : (decide (Float32.sqrt (v.x * v.x + v.y * v.y) > m) &&
      is_positive_float (Float32.sqrt (v.x * v.x + v.y * v.y))) = true
  · rw [ite_eq_left hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hgt : m.toReal < (Float32.sqrt (v.x * v.x + v.y * v.y)).toReal :=
      (Float32.lt_iff_toReal_lt hm fL).1 hc.1
    obtain ⟨fq, hq0, hq1⟩ := div_unit hm hm0 fL hgt
    obtain ⟨f1, b1⟩ := mul_shrink hv.1 hv.2.2.1 fq hq0 hq1
    obtain ⟨f2, b2⟩ := mul_shrink hv.2.1 hv.2.2.2 fq hq0 hq1
    exact ⟨f1, f2, b1, b2⟩
  · rw [ite_eq_right hc]
    exact ⟨hv.1, hv.2.1, le_rfl, le_rfl⟩

/-- `limit_length` keeps a NaN component: NaN inputs break the bound for good. -/
theorem limit_length_keeps_nan :
    ((Vector2f.limit_length { x := (0.0 : Float32) / 0.0, y := 0.0 } 1.0).1.x).isNaN = true := by
  decide

/-! ## The 2D PID's integrator writes -/

theorem update_i_integrator (p : AC_PID_2D.Params) (s : AC_PID_2D.State) dt lim :
    (AC_PID_2D.update_i p s dt lim)._integrator =
      (Vector2f.limit_length
        (if is_positive_float (Vector2f.op_mul_Vector2f
            (Vector2f.op_mul_float (Vector2f.op_mul_float s._error p._ki) dt) lim) = true
         then (Vector2f.limit_length (Vector2f.op_add_assign s._integrator
            (Vector2f.op_mul_float (Vector2f.op_mul_float s._error p._ki) dt)).1
              (Vector2f.length s._integrator)).1
         else (Vector2f.op_add_assign s._integrator
            (Vector2f.op_mul_float (Vector2f.op_mul_float s._error p._ki) dt)).1)
        p._kimax).1 := by
  unfold AC_PID_2D.update_i
  by_cases h : is_positive_float (Vector2f.op_mul_Vector2f
      (Vector2f.op_mul_float (Vector2f.op_mul_float s._error p._ki) dt) lim) = true
  · simp only [h, ite_true]
    split <;> rfl
  · simp only [h]
    rfl

/-- The inputs `update_i` multiplies, as the bound needs them: finite, the error below `2^19`, `ki`
and `dt` below `2^9` (so that the step `e·ki·dt` stays below `2^38`). -/
structure StepOK (e : Vector2f.State) (ki dt : Float32) : Prop where
  ex : e.x.IsFinite
  ey : e.y.IsFinite
  exb : |e.x.toReal| ≤ 2 ^ 19
  eyb : |e.y.toReal| ≤ 2 ^ 19
  kif : ki.IsFinite
  kib : |ki.toReal| ≤ 2 ^ 9
  dtf : dt.IsFinite
  dtb : |dt.toReal| ≤ 2 ^ 9

/-- One component of `update_i`'s step `I + (e·ki)·dt`: finite, below `2^40`. -/
theorem step_comp {i e ki dt : Float32} (hi : i.IsFinite) (hib : |i.toReal| ≤ 2 ^ 31)
    (he : e.IsFinite) (heb : |e.toReal| ≤ 2 ^ 19) (hk : ki.IsFinite) (hkb : |ki.toReal| ≤ 2 ^ 9)
    (hd : dt.IsFinite) (hdb : |dt.toReal| ≤ 2 ^ 9) :
    (i + e * ki * dt).IsFinite ∧ |(i + e * ki * dt).toReal| ≤ 2 ^ 40 := by
  obtain ⟨f1, b1⟩ := mul_crude he hk (A := 2 ^ 28) (by
    rw [abs_mul]; calc |e.toReal| * |ki.toReal| ≤ 2 ^ 19 * 2 ^ 9 := by gcongr
      _ = 2 ^ 28 := by norm_num) (by norm_num)
  have b1' : |(e * ki).toReal| ≤ 2 ^ 29 := b1.trans (by norm_num)
  obtain ⟨f2, b2⟩ := mul_crude f1 hd (A := 2 ^ 38) (by
    rw [abs_mul]; calc |(e * ki).toReal| * |dt.toReal| ≤ 2 ^ 29 * 2 ^ 9 := by gcongr
      _ = 2 ^ 38 := by norm_num) (by norm_num)
  have b2' : |(e * ki * dt).toReal| ≤ 2 ^ 39 := b2.trans (by norm_num)
  obtain ⟨f3, b3⟩ := add_crude hi f2 (A := 2 ^ 31 + 2 ^ 39) ((abs_add_le _ _).trans
    (add_le_add hib b2')) (by norm_num)
  exact ⟨f3, b3.trans (by norm_num)⟩

/-- **`AC_PID_2D::update_i`**: from an integrator within its limit and finite, bounded inputs, the
integrator after the update is within its limit. -/
theorem VB_update_i (p : AC_PID_2D.Params) (s : AC_PID_2D.State) (dt : Float32)
    (lim : Vector2f.State) (hk : K2OK p._kimax) (hs : VB p._kimax s._integrator)
    (hin : StepOK s._error p._ki dt) : VB p._kimax (AC_PID_2D.update_i p s dt lim)._integrator := by
  rw [update_i_integrator]
  have hcb := hs.cb hk
  obtain ⟨fx, bx⟩ := step_comp hcb.1 hcb.2.2.1 hin.ex hin.exb hin.kif hin.kib hin.dtf hin.dtb
  obtain ⟨fy, by_⟩ := step_comp hcb.2.1 hcb.2.2.2 hin.ey hin.eyb hin.kif hin.kib hin.dtf hin.dtb
  have ht1 : CB (2 ^ 40) (Vector2f.op_add_assign s._integrator
      (Vector2f.op_mul_float (Vector2f.op_mul_float s._error p._ki) dt)).1 :=
    ⟨fx, fy, bx, by_⟩
  split
  · apply VB_limit_length hk
    obtain ⟨fL, hL0, -, -⟩ := flen_ge hcb.1 hcb.2.1
      (hcb.2.2.1.trans (by norm_num)) (hcb.2.2.2.trans (by norm_num))
    obtain ⟨g1, g2, g3, g4⟩ := limit_length_shrink _ (Vector2f.length s._integrator) ht1 fL hL0
    exact ⟨g1, g2, g3.trans ht1.2.2.1, g4.trans ht1.2.2.2⟩
  · exact VB_limit_length hk ht1

/-- **`AC_PID_2D::set_integrator`**: the new integrator is limited, for every finite argument with
components below `2^40`. -/
theorem VB_set_integrator (p : AC_PID_2D.Params) (s : AC_PID_2D.State) (i : Vector2f.State)
    (hk : K2OK p._kimax) (hi : CB (2 ^ 40) i) :
    VB p._kimax (AC_PID_2D.set_integrator_Vector2f p s i)._integrator :=
  VB_limit_length hk hi

/-- **`AC_PID_2D::reset_I`**: the zero vector. -/
theorem VB_reset_I (k : Float32) (hk : K2OK k) (s : AC_PID_2D.State) :
    VB k (AC_PID_2D.reset_I s)._integrator := by
  refine ⟨Float32.isFinite_int32_zero, Float32.isFinite_int32_zero, ?_⟩
  show N2 (Int32.toFloat32 0).toReal (Int32.toFloat32 0).toReal ≤ B2D k
  rw [Float32.toReal_int32_zero, N2, B2D]
  have := hk.lo
  norm_num
  positivity

end Contracts.Track.TwoD
