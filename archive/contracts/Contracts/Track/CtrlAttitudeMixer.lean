import Contracts.Mission.FloatCalc
import Contracts.Mission.NavStop
import Contracts.Track.FloatLib
import Contracts.Track.Actuators

/-!
# M4: the motor mixer as a real law plus a float error

The controller lemma for the motors (`AP_Motors_lib.AP_MotorsMatrix`, quad X), in the form "emitted
function output = ideal real law + β on a region". Throughout, `A32 x r e` (`NavFloat.lean`) says
the `float` `x` is finite and `|x - r| ≤ e`; `LibmSpec` is the hypothesis on the opaque
conversions (`Float.toFloat32 1.0` and friends have the values of their literals).

**The frame** (`Quad`, and the factor hypotheses): motors `0 … 3` enabled, `4 … 31` disabled (the
arrays have 32 entries; only the `getElem!` values are used), roll factors within `10⁻⁷` of
`RF = (-½, ½, ½, -½)`, pitch `PF = (½, -½, ½, -½)`, yaw `YF = (½, ½, -½, -½)`, throttle factors
`1`. `init(QUAD, X)` computes the roll factors with `cosf` and `normalise_rpy_factors`: evaluated,
three of them are `±(½ - 2⁻²⁵)`, so they are hypotheses with a tolerance, not equalities.

**Results.**
* `armed_stabilizing_spec` (M4.1): on the region `thr = get_throttle ∈ [0.3, 0.62]`,
  `|roll|, |pitch|, |yaw| ≤ 0.15`, feed-forwards `0`, `_throttle_thrust_max > thr`,
  `_throttle_avg_max ≤ 1`, no boost, compensation gain `1`, `MOT_YAW_HEADROOM = 200`:
  `_thrust_rpyt_out[i] = thr + RF i·roll + PF i·pitch + YF i·yaw` within `β = 3·10⁻⁷` for
  `i < 4`, the five `limit` flags unchanged, `_throttle_out = thr` within `10⁻⁷`. Inside the
  proof: no throttle clamp (`thr > 0`, `thr < max`), `yaw_allowed ≥ 0.2000000029 > |yaw|` (the
  floor `MOT_YAW_HEADROOM · 0.001`, whatever the per-motor headroom loop computes), so no yaw
  clamp; `rpy_high - rpy_low ≤ 0.4502 < 1` and `throttle_avg_max + rpy_low > 0`, so
  `rpy_scale = 1`; `0 < thr_adj` and `thr + rpy_high ≤ 0.8452 < 1`, so no `thr_adj` clamp.
* `sws_spec`, `tta_id` (M4.2): with zero slew times `set_actuator_with_slew` is the clamp to
  `[0, 1]` and the identity on `[0, 1]`; with `MOT_THST_EXPO = 0`, `MOT_SPIN_MIN = 0`,
  `MOT_SPIN_MAX = 1`, battery scale `1`, `lift_max = 1`, `thrust_to_actuator` is the identity on
  `[0, 1]` (`β = 0`).
* `throttle_filter_spec` (M4.3): armed, filter initialised, `f, u ∈ [0.001, 0.999]`,
  `α ∈ [0, 1]`: the new filter output is `f + (u - f) α` within `2·10⁻⁷` of `f + α (u - f)`, no
  reset. `alpha_flight`: at 400 Hz and 2 Hz, `α` is within `4·10⁻⁸` of `dt/(dt + 1/(4π))` and
  within `5·10⁻⁸` of `16352567/536870912`.
* `output_spec` (M4.4): one call of `output` (`update_throttle_filter`, `output_logic` on
  `THROTTLE_UNLIMITED`, `output_armed_stabilizing`, `output_to_motors`, `update_external_limits`):
  the four actuators are `f' + RF i·roll + PF i·pitch + YF i·yaw` within `3·10⁻⁷`, in `(0, 1)`,
  with `f'` the new filter output, and all `limit` flags are false. `tick_output_spec` instantiates
  it at the call of `Vehicle.tick`.
-/

namespace Contracts.Track.Mixer

open Float.Model UnpackedFloat Contracts.Mission AP_Motors_lib AP_MotorsMatrix

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-! ## Loops over `[0:32]`: four enabled motors, twenty-eight disabled ones -/
/-! ## Loops over `[0:32]` -/

theorem forIn_list_eq_foldl {β : Type} (P : β → Prop) (l : List ℕ) (init : β)
    (f : ℕ → β → Id (ForInStep β)) (g : ℕ → β → β) (h0 : P init)
    (hf : ∀ i b, P b → f i b = ForInStep.yield (g i b)) (hg : ∀ i b, P b → P (g i b)) :
    forIn l init f = l.foldl (fun b i => g i b) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn_cons, List.foldl_cons, ← ih (g a init) (hg a init h0)]
    show (match f a init with
      | ForInStep.done b => (pure b : Id β)
      | ForInStep.yield b => forIn as b f) = _
    rw [hf a init h0]

theorem forIn_range_eq_foldl {β : Type} (P : β → Prop) (n : ℕ) (init : β)
    (f : ℕ → β → Id (ForInStep β)) (g : ℕ → β → β) (h0 : P init)
    (hf : ∀ i b, P b → f i b = ForInStep.yield (g i b)) (hg : ∀ i b, P b → P (g i b)) :
    forIn [:n] init f = (List.range' 0 n).foldl (fun b i => g i b) init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact forIn_list_eq_foldl P _ init f g h0 hf hg

/-- The first component of a loop over pairs whose first component evolves on its own. -/
theorem forIn_list_fst {σ α : Type} (l : List ℕ) (s : σ) (a : α)
    (f : ℕ → σ × α → Id (ForInStep (σ × α))) (g : ℕ → σ → σ)
    (hf : ∀ i b, ∃ x, f i b = ForInStep.yield (g i b.1, x)) :
    (forIn l (s, a) f).1 = l.foldl (fun b i => g i b) s := by
  induction l generalizing s a with
  | nil => rfl
  | cons c cs ih =>
    rw [List.forIn_cons, List.foldl_cons]
    obtain ⟨x, hx⟩ := hf c (s, a)
    rw [hx]
    exact ih (g c s) x

theorem forIn_range_fst {σ α : Type} (n : ℕ) (s : σ) (a : α)
    (f : ℕ → σ × α → Id (ForInStep (σ × α))) (g : ℕ → σ → σ)
    (hf : ∀ i b, ∃ x, f i b = ForInStep.yield (g i b.1, x)) :
    (forIn [:n] (s, a) f).1 = (List.range' 0 n).foldl (fun b i => g i b) s := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact forIn_list_fst _ s a f g hf

theorem foldl_skip {β : Type} (g : ℕ → β → β) (P : β → Prop) (l : List ℕ) (b : β) (hb : P b)
    (h : ∀ i ∈ l, ∀ b, P b → g i b = b) : l.foldl (fun b i => g i b) b = b := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, h a (by simp) b hb]
    exact ih (fun i hi b hb => h i (by simp [hi]) b hb)

/-- A loop over `[0:32]` whose iterations `4 … 31` do nothing: four steps. -/
theorem foldl_range32 {β : Type} (g : ℕ → β → β) (P : β → Prop) (b : β)
    (hP : P (g 3 (g 2 (g 1 (g 0 b)))))
    (hskip : ∀ i b, 4 ≤ i → i < 32 → P b → g i b = b) :
    (List.range' 0 32).foldl (fun b i => g i b) b = g 3 (g 2 (g 1 (g 0 b))) := by
  rw [show List.range' 0 32 = [0, 1, 2, 3] ++ List.range' 4 28 by rfl, List.foldl_append]
  refine foldl_skip g P _ _ hP (fun i hi b hb => hskip i b ?_ ?_ hb)
  · simp [List.mem_range'] at hi; omega
  · simp [List.mem_range'] at hi; omega

theorem toUInt8_toNat {i : ℕ} (h : i < 256) : i.toUInt8.toNat = i := by
  simp [Nat.toUInt8]; omega

/-! ## Float facts: literals, exact operations, comparisons -/
noncomputable section

/-! ## Literals -/

theorem f64_unpack_1p25 : (1.25 : Float).toModel.unpack = .finite .positive 5629499534213120 (-52) (by decide) := by rfl
theorem f64_toReal_1p25 : (1.25 : Float).toReal = (5 / 4 : ℝ) := by
  rw [Float.toReal, f64_unpack_1p25]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f64_isFinite_1p25 : (1.25 : Float).IsFinite := by
  rw [Float.isFinite_iff, f64_unpack_1p25]; rfl

theorem f64_unpack_1p5 : (1.5 : Float).toModel.unpack = .finite .positive 6755399441055744 (-52) (by decide) := by rfl
theorem f64_toReal_1p5 : (1.5 : Float).toReal = (3 / 2 : ℝ) := by
  rw [Float.toReal, f64_unpack_1p5]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f64_isFinite_1p5 : (1.5 : Float).IsFinite := by
  rw [Float.isFinite_iff, f64_unpack_1p5]; rfl

theorem f64_unpack_0p3 : (0.3 : Float).toModel.unpack = .finite .positive 5404319552844595 (-54) (by decide) := by rfl
theorem f64_toReal_0p3 : (0.3 : Float).toReal = (5404319552844595 / 18014398509481984 : ℝ) := by
  rw [Float.toReal, f64_unpack_0p3]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f64_isFinite_0p3 : (0.3 : Float).IsFinite := by
  rw [Float.isFinite_iff, f64_unpack_0p3]; rfl

theorem f32_unpack_1p25 : (1.25 : Float32).toModel.unpack = .finite .positive 10485760 (-23) (by decide) := by rfl
theorem f32_toReal_1p25 : (1.25 : Float32).toReal = (5 / 4 : ℝ) := by
  rw [Float32.toReal, f32_unpack_1p25]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_1p25 : (1.25 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_1p25]; rfl

theorem f32_unpack_yamin : (Int16.toFloat32 200 * (1e-3 : Float32)).toModel.unpack =
    .finite .positive 13421773 (-26) (by decide) := by rfl
theorem f32_toReal_yamin : (Int16.toFloat32 200 * (1e-3 : Float32)).toReal = (13421773 / 67108864 : ℝ) := by
  rw [Float32.toReal, f32_unpack_yamin]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_yamin : (Int16.toFloat32 200 * (1e-3 : Float32)).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_yamin]; rfl

/-- `(float) d` of a `double` literal that is a `float` value. -/
theorem toF32_lit (hL : LibmSpec) {a : Float} {b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    {r : ℝ} (har : a.toReal = r) (hbr : b.toReal = r) : A32 (Float.toFloat32 a) r 0 := by
  obtain ⟨h1, h2⟩ := hL.f64ToF32_exact a b ha hb (by rw [har, hbr])
  exact ⟨h1, by rw [h2, har]; simp⟩

theorem toF32_one (hL : LibmSpec) : A32 (Float.toFloat32 1.0) 1 0 :=
  toF32_lit hL f64_isFinite_1p0 f32_isFinite_1p0 f64_toReal_1p0 f32_toReal_1p0
theorem toF32_zero (hL : LibmSpec) : A32 (Float.toFloat32 0.0) 0 0 :=
  toF32_lit hL f64_isFinite_0p0 f32_isFinite_0p0 f64_toReal_0p0 f32_toReal_0p0
theorem toF32_half (hL : LibmSpec) : A32 (Float.toFloat32 0.5) (1 / 2) 0 :=
  toF32_lit hL f64_isFinite_0p5 f32_isFinite_0p5 f64_toReal_0p5 f32_toReal_0p5
theorem toF32_1p25 (hL : LibmSpec) : A32 (Float.toFloat32 1.25) (5 / 4) 0 :=
  toF32_lit hL f64_isFinite_1p25 f32_isFinite_1p25 f64_toReal_1p25 f32_toReal_1p25
theorem toF32_1p5 (hL : LibmSpec) : A32 (Float.toFloat32 1.5) (3 / 2) 0 :=
  toF32_lit hL f64_isFinite_1p5 f32_isFinite_1p5 f64_toReal_1p5 f32_toReal_1p5

theorem toF32_0p3 (hL : LibmSpec) : A32 (Float.toFloat32 0.3) (3 / 10) (1 / 10 ^ 7) := by
  have h := A64.toFloat32 hL (A64.of_exact f64_isFinite_0p3)
    (by rw [f64_toReal_0p3, abs_of_nonneg (by norm_num)]; simp only [capF]; norm_num)
  rw [f64_toReal_0p3] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  have := η32_small
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5404319552844595 / 18014398509481984)] at h2
  have e : |(Float.toFloat32 0.3).toReal - 3 / 10| ≤
      |(Float.toFloat32 0.3).toReal - 5404319552844595 / 18014398509481984| +
        |(5404319552844595 / 18014398509481984 : ℝ) - 3 / 10| := abs_sub_le _ _ _
  simp only [u32] at h2
  norm_num at h2 e ⊢
  linarith

/-! ## Exact operations -/

theorem A32_exact {x : Float32} {r : ℝ} (h : A32 x r 0) : x.IsFinite ∧ x.toReal = r :=
  ⟨h.1, by have := h.2; rw [abs_nonpos_iff, sub_eq_zero] at this; exact this⟩

theorem A32_of_val {x : Float32} {r : ℝ} (hx : x.IsFinite) (h : x.toReal = r) : A32 x r 0 :=
  ⟨hx, by rw [h]; simp⟩

/-- Division by a float of value `1` is exact. -/
theorem Float32.div_exact {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (hb0 : b.toReal ≠ 0) (h : a.toReal / b.toReal = f.toReal) :
    (a / b).IsFinite ∧ (a / b).toReal = f.toReal := by
  have hm : |a.toReal / b.toReal| ≤ maxFinite32 := h ▸ _root_.Float32.abs_toReal_le_maxFinite f
  obtain ⟨b1, b2⟩ := _root_.Float32.div_bracket ha hb hb0 hm hf
  exact ⟨(_root_.Float32.div_err_all ha hb hb0 hm).1, le_antisymm (b2 h.le) (b1 h.symm.le)⟩

/-- `x * g` with `g = 1` is `x`. -/
theorem mul_one_val {x g : Float32} {r : ℝ} (hx : A32 x r 0) (hg : A32 g 1 0) : A32 (x * g) r 0 := by
  obtain ⟨hxf, hxv⟩ := A32_exact hx
  obtain ⟨hgf, hgv⟩ := A32_exact hg
  obtain ⟨h1, h2⟩ := Float32.mul_exact hxf hgf hxf (by rw [hgv, mul_one])
  exact A32_of_val h1 (h2.trans hxv)

theorem one_mul_val {x g : Float32} {r : ℝ} (hx : A32 x r 0) (hg : A32 g 1 0) : A32 (g * x) r 0 := by
  obtain ⟨hxf, hxv⟩ := A32_exact hx
  obtain ⟨hgf, hgv⟩ := A32_exact hg
  obtain ⟨h1, h2⟩ := Float32.mul_exact hgf hxf hxf (by rw [hgv, one_mul])
  exact A32_of_val h1 (h2.trans hxv)

theorem div_one_val {x g : Float32} {r e : ℝ} (hx : A32 x r e) (hg : A32 g 1 0) : A32 (x / g) r e := by
  obtain ⟨hgf, hgv⟩ := A32_exact hg
  obtain ⟨h1, h2⟩ := Float32.div_exact hx.1 hgf hx.1 (by rw [hgv]; norm_num) (by rw [hgv, div_one])
  exact ⟨h1, by rw [h2]; exact hx.2⟩

theorem mul_one_val' {x g : Float32} {r e : ℝ} (hx : A32 x r e) (hg : A32 g 1 0) : A32 (x * g) r e := by
  obtain ⟨hgf, hgv⟩ := A32_exact hg
  obtain ⟨h1, h2⟩ := Float32.mul_exact hx.1 hgf hx.1 (by rw [hgv, mul_one])
  exact ⟨h1, by rw [h2]; exact hx.2⟩

theorem one_mul_val' {x g : Float32} {r e : ℝ} (hx : A32 x r e) (hg : A32 g 1 0) : A32 (g * x) r e := by
  obtain ⟨hgf, hgv⟩ := A32_exact hg
  obtain ⟨h1, h2⟩ := Float32.mul_exact hgf hx.1 hx.1 (by rw [hgv, one_mul])
  exact ⟨h1, by rw [h2]; exact hx.2⟩

theorem add_zero_val' {x z : Float32} {r e : ℝ} (hx : A32 x r e) (hz : A32 z 0 0) : A32 (x + z) r e := by
  obtain ⟨hzf, hzv⟩ := A32_exact hz
  obtain ⟨h1, h2⟩ := Float32.add_zero_val hx.1 hzf hzv
  exact ⟨h1, by rw [h2]; exact hx.2⟩

theorem zero_add_val' {x z : Float32} {r e : ℝ} (hx : A32 x r e) (hz : A32 z 0 0) : A32 (z + x) r e := by
  obtain ⟨hzf, hzv⟩ := A32_exact hz
  obtain ⟨h1, h2⟩ := Float32.add_exact hzf hx.1 hx.1 (by rw [hzv, zero_add])
  exact ⟨h1, by rw [h2]; exact hx.2⟩

theorem lit_one : A32 (1.0 : Float32) 1 0 := A32_of_val f32_isFinite_1p0 f32_toReal_1p0
theorem lit_zero : A32 (0.0 : Float32) 0 0 := A32_of_val f32_isFinite_0p0 f32_toReal_0p0
theorem lit_half : A32 (0.5 : Float32) (1 / 2) 0 := A32_of_val f32_isFinite_0p5 f32_toReal_0p5

/-! ## Comparisons -/

theorem not_lt_of {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : b.toReal ≤ a.toReal) :
    ¬ a < b := by
  rw [Float32.lt_iff_toReal_lt ha hb]; exact not_lt.2 h

theorem not_le_of {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : b.toReal < a.toReal) :
    ¬ a ≤ b := by
  rw [Float32.le_iff_toReal_le ha hb]; exact not_le.2 h

theorem lt_of {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : a.toReal < b.toReal) :
    a < b := by
  rw [Float32.lt_iff_toReal_lt ha hb]; exact h

theorem not_lt_inf_pos {a b : Float32} (ha : a.toModel.unpack = .infinity .positive)
    (hb : b.IsFinite) : ¬ a < b := by
  rw [Float32.isFinite_iff] at hb
  rw [Float32.lt_iff_unpack, ha]
  revert hb; rcases b.toModel.unpack with (s | _ | s | ⟨s, m, e, h⟩) <;>
    simp [UnpackedFloat.lt, UnpackedFloat.compare, UnpackedFloat.isFinite]

theorem not_lt_inf_neg {a b : Float32} (ha : a.toModel.unpack = .infinity .negative)
    (hb : b.IsFinite) : ¬ b < a := by
  rw [Float32.isFinite_iff] at hb
  rw [Float32.lt_iff_unpack, ha]
  revert hb; rcases b.toModel.unpack with (s | _ | s | ⟨s, m, e, h⟩) <;>
    simp [UnpackedFloat.lt, UnpackedFloat.compare, UnpackedFloat.isFinite]

/-- The yaw-headroom comparison: `|yaw| > MAX(yaw_allowed, yaw_allowed_min)` fails whenever
`|yaw| < yaw_allowed_min`, whatever `yaw_allowed` is (NaN and `±∞` included). -/
theorem not_abs_gt_max {y a m : Float32} (hy : y.IsFinite) (hm : m.IsFinite)
    (h : |y.toReal| < m.toReal) : ¬ (Float32.abs y > MAX_float2 a m) := by
  have hya : (Float32.abs y).IsFinite := (_root_.Float32.isFinite_abs y).2 hy
  have hyv : (Float32.abs y).toReal = |y.toReal| := _root_.Float32.toReal_abs y
  show ¬ ((if a > m then a else m) < Float32.abs y)
  by_cases ham : a > m
  · rw [if_pos ham]
    rcases _root_.Float32.trichotomy a with hf | hn | hp | hn'
    · intro hlt
      have h1 := (Float32.lt_iff_toReal_lt hm hf).1 ham
      have h2 := (Float32.lt_iff_toReal_lt hf hya).1 hlt
      linarith
    · exact _root_.Float32.not_lt_of_isNaN_left hn
    · exact not_lt_inf_pos hp hya
    · exact absurd ham (not_lt_inf_neg hn' hm)
  · rw [if_neg ham]
    intro hlt
    have := (Float32.lt_iff_toReal_lt hm hya).1 hlt
    linarith

/-- `is_zero` (motors library) is false away from `0`. -/
theorem isZero_false {x : Float32} (hx : x.IsFinite) (h : 2 ^ (-23 : ℤ) ≤ |x.toReal|) :
    AP_Motors_lib.is_zero_float x = false := by
  rcases hz : AP_Motors_lib.is_zero_float x with _ | _
  · rfl
  · have := (isZero_iff hx).1 hz; linarith

theorem isZero_true {x : Float32} (hx : x.IsFinite) (h : |x.toReal| < 2 ^ (-23 : ℤ)) :
    AP_Motors_lib.is_zero_float x = true := (isZero_iff hx).2 h

theorem isPos_false' {x : Float32} (hx : x.IsFinite) (h : x.toReal < 2 ^ (-23 : ℤ)) :
    AP_Motors_lib.is_positive_float x = false := by
  rcases hz : AP_Motors_lib.is_positive_float x with _ | _
  · rfl
  · have := (isPos_iff hx).1 hz; linarith

/-! ## `MIN`/`MAX` -/

theorem min_val {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    (MIN_float2 a b).IsFinite ∧ (MIN_float2 a b).toReal = min a.toReal b.toReal :=
  Float32.ite_lt_min ha hb

theorem max_val {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) :
    (MAX_float2 a b).IsFinite ∧ (MAX_float2 a b).toReal = max a.toReal b.toReal :=
  Float32.ite_gt_max ha hb

/-! ## The motors' clamp -/

theorem cvl_val {a lo hi : Float32} (l : UInt32) (ha : a.IsFinite) (hlo : lo.IsFinite)
    (hhi : hi.IsFinite) (hle : lo.toReal ≤ hi.toReal) :
    (constrain_value_line_float a lo hi l).IsFinite ∧
      (constrain_value_line_float a lo hi l).toReal = max lo.toReal (min a.toReal hi.toReal) := by
  rw [FloatLib.motors_cvl]
  refine ⟨?_, FloatLib.cvl_toReal ha hlo hhi hle⟩
  unfold Float32.cvl
  rw [ite_eq_right (by rw [_root_.Float32.not_isNaN_of_isFinite ha]; decide)]
  split_ifs <;> assumption

end

/-! ## The mixer loops, iteration by iteration -/
theorem getElem!_set!_self {α : Type} [Inhabited α] {a : Array α} {i : ℕ} {v : α} (h : i < a.size) :
    (a.set! i v)[i]! = v := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ i (by simpa using h)]
  simp
theorem getElem!_set!_ne {α : Type} [Inhabited α] {a : Array α} {i j : ℕ} {v : α} (h : i ≠ j) :
    (a.set! i v)[j]! = a[j]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj]
    exact Array.getElem_setIfInBounds_ne _ h
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]
@[simp] theorem size_set! {α : Type} {a : Array α} {i : ℕ} {v : α} : (a.set! i v).size = a.size := by
  simp [Array.set!_eq_setIfInBounds]

theorem u8_0 : (0 : ℕ).toUInt8.toNat = 0 := rfl
theorem u8_1 : (1 : ℕ).toUInt8.toNat = 1 := rfl
theorem u8_2 : (2 : ℕ).toUInt8.toNat = 2 := rfl
theorem u8_3 : (3 : ℕ).toUInt8.toNat = 3 := rfl

/-- The quad-X frame as `init(QUAD, X)` leaves it: motors `0 … 3` enabled, the others not. -/
structure Quad (s : State) : Prop where
  en0 : s.motor_enabled[0]! = true
  en1 : s.motor_enabled[1]! = true
  en2 : s.motor_enabled[2]! = true
  en3 : s.motor_enabled[3]! = true
  dis : ∀ i, 4 ≤ i → s.motor_enabled[i]! = false
  size : 4 ≤ s._thrust_rpyt_out.size

/-- Iteration `i` of the first mixer loop (`roll_thrust * _roll_factor[i] + pitch_thrust * _pitch_factor[i]`). -/
def step1 (rt pt : Float32) (i : ℕ) (st : State) : State :=
  if st.motor_enabled[i.toUInt8.toNat]! = true then
    { st with _thrust_rpyt_out := (st._thrust_rpyt_out.set! i.toUInt8.toNat
        (rt * st._roll_factor[i.toUInt8.toNat]! + pt * st._pitch_factor[i.toUInt8.toNat]!)) }
  else st

/-- Iteration `i` of the second mixer loop (add yaw; running min and max of the new value, read
back from the array as the code does). -/
def step2 (yt : Float32) (i : ℕ) (b : State × Float32 × Float32) : State × Float32 × Float32 :=
  if b.1.motor_enabled[i.toUInt8.toNat]! = true then
    ({ b.1 with _thrust_rpyt_out := (b.1._thrust_rpyt_out.set! i.toUInt8.toNat
        (b.1._thrust_rpyt_out[i.toUInt8.toNat]! + yt * b.1._yaw_factor[i.toUInt8.toNat]!)) },
     MIN_float2 (b.1._thrust_rpyt_out.set! i.toUInt8.toNat
        (b.1._thrust_rpyt_out[i.toUInt8.toNat]! + yt * b.1._yaw_factor[i.toUInt8.toNat]!))[i.toUInt8.toNat]!
        b.2.1,
     MAX_float2 (b.1._thrust_rpyt_out.set! i.toUInt8.toNat
        (b.1._thrust_rpyt_out[i.toUInt8.toNat]! + yt * b.1._yaw_factor[i.toUInt8.toNat]!))[i.toUInt8.toNat]!
        b.2.2)
  else b

/-- Iteration `i` of the third mixer loop (throttle plus scaled attitude). -/
def step3 (bpa sc : Float32) (i : ℕ) (st : State) : State :=
  if st.motor_enabled[i.toUInt8.toNat]! = true then
    { st with _thrust_rpyt_out := (st._thrust_rpyt_out.set! i.toUInt8.toNat
        (bpa * st._throttle_factor[i.toUInt8.toNat]! + sc * st._thrust_rpyt_out[i.toUInt8.toNat]!)) }
  else st

theorem loop1_eq (rt pt : Float32) (s : State) (hq : Quad s) :
    (List.range' 0 32).foldl (fun b i => step1 rt pt i b) s =
      { s with _thrust_rpyt_out := ((((s._thrust_rpyt_out.set! 0 (rt * s._roll_factor[0]! + pt * s._pitch_factor[0]!)).set! 1
          (rt * s._roll_factor[1]! + pt * s._pitch_factor[1]!)).set! 2
          (rt * s._roll_factor[2]! + pt * s._pitch_factor[2]!)).set! 3
          (rt * s._roll_factor[3]! + pt * s._pitch_factor[3]!)) } := by
  rw [foldl_range32 _ (fun st : State => st.motor_enabled = s.motor_enabled) _
    (by simp only [step1]; split_ifs <;> rfl)
    (by intro i b h4 h32 hb; simp only [step1]; rw [toUInt8_toNat (by omega), hb, hq.dis i h4]; simp)]
  simp only [step1, u8_0, u8_1, u8_2, u8_3, hq.en0, hq.en1, hq.en2, hq.en3, if_true]

theorem loop3_eq (bpa sc : Float32) (s : State) (hq : Quad s) :
    (List.range' 0 32).foldl (fun b i => step3 bpa sc i b) s =
      { s with _thrust_rpyt_out := ((((s._thrust_rpyt_out.set! 0 (bpa * s._throttle_factor[0]! + sc * s._thrust_rpyt_out[0]!)).set! 1
          (bpa * s._throttle_factor[1]! + sc * s._thrust_rpyt_out[1]!)).set! 2
          (bpa * s._throttle_factor[2]! + sc * s._thrust_rpyt_out[2]!)).set! 3
          (bpa * s._throttle_factor[3]! + sc * s._thrust_rpyt_out[3]!)) } := by
  rw [foldl_range32 _ (fun st : State => st.motor_enabled = s.motor_enabled) _
    (by simp only [step3]; split_ifs <;> rfl)
    (by intro i b h4 h32 hb; simp only [step3]; rw [toUInt8_toNat (by omega), hb, hq.dis i h4]; simp)]
  simp only [step3, u8_0, u8_1, u8_2, u8_3, hq.en0, hq.en1, hq.en2, hq.en3, if_true,
    getElem!_set!_ne (show (0:ℕ) ≠ 1 by decide), getElem!_set!_ne (show (0:ℕ) ≠ 2 by decide),
    getElem!_set!_ne (show (0:ℕ) ≠ 3 by decide), getElem!_set!_ne (show (1:ℕ) ≠ 2 by decide),
    getElem!_set!_ne (show (1:ℕ) ≠ 3 by decide), getElem!_set!_ne (show (2:ℕ) ≠ 3 by decide)]

theorem loop2_eq (yt lo hi : Float32) (s : State) (hq : Quad s) :
    (List.range' 0 32).foldl (fun b i => step2 yt i b) (s, lo, hi) =
      ({ s with _thrust_rpyt_out := ((((s._thrust_rpyt_out.set! 0 (s._thrust_rpyt_out[0]! + yt * s._yaw_factor[0]!)).set! 1
          (s._thrust_rpyt_out[1]! + yt * s._yaw_factor[1]!)).set! 2
          (s._thrust_rpyt_out[2]! + yt * s._yaw_factor[2]!)).set! 3
          (s._thrust_rpyt_out[3]! + yt * s._yaw_factor[3]!)) },
       MIN_float2 (s._thrust_rpyt_out[3]! + yt * s._yaw_factor[3]!)
        (MIN_float2 (s._thrust_rpyt_out[2]! + yt * s._yaw_factor[2]!)
          (MIN_float2 (s._thrust_rpyt_out[1]! + yt * s._yaw_factor[1]!)
            (MIN_float2 (s._thrust_rpyt_out[0]! + yt * s._yaw_factor[0]!) lo))),
       MAX_float2 (s._thrust_rpyt_out[3]! + yt * s._yaw_factor[3]!)
        (MAX_float2 (s._thrust_rpyt_out[2]! + yt * s._yaw_factor[2]!)
          (MAX_float2 (s._thrust_rpyt_out[1]! + yt * s._yaw_factor[1]!)
            (MAX_float2 (s._thrust_rpyt_out[0]! + yt * s._yaw_factor[0]!) hi)))) := by
  have h0 : 0 < s._thrust_rpyt_out.size := by have := hq.size; omega
  have h1 : 1 < s._thrust_rpyt_out.size := by have := hq.size; omega
  have h2 : 2 < s._thrust_rpyt_out.size := by have := hq.size; omega
  have h3 : 3 < s._thrust_rpyt_out.size := by have := hq.size; omega
  rw [foldl_range32 _ (fun b : State × Float32 × Float32 => b.1.motor_enabled = s.motor_enabled) _
    (by simp only [step2]; split_ifs <;> rfl)
    (by intro i b h4 h32 hb; simp only [step2]; rw [toUInt8_toNat (by omega), hb, hq.dis i h4]; simp)]
  simp only [step2, u8_0, u8_1, u8_2, u8_3, hq.en0, hq.en1, hq.en2, hq.en3, if_true,
    getElem!_set!_self, size_set!, h0, h1, h2, h3,
    getElem!_set!_ne (show (0:ℕ) ≠ 1 by decide), getElem!_set!_ne (show (0:ℕ) ≠ 2 by decide),
    getElem!_set!_ne (show (0:ℕ) ≠ 3 by decide), getElem!_set!_ne (show (1:ℕ) ≠ 2 by decide),
    getElem!_set!_ne (show (1:ℕ) ≠ 3 by decide), getElem!_set!_ne (show (2:ℕ) ≠ 3 by decide)]

/-! ## Gains, factors, and the error budget of one motor -/
noncomputable section

theorem boost_ratio_val (hL : LibmSpec) (s : State) {a b : Float32} {rb e : ℝ}
    (hr : A32 s._thrust_boost_ratio 0 0) (ha : a.IsFinite) (hb : A32 b rb e) :
    A32 (boost_ratio s a b) rb e := by
  show A32 (s._thrust_boost_ratio * a + (Float.toFloat32 1.0 - s._thrust_boost_ratio) * b) rb e
  obtain ⟨hrf, hrv⟩ := A32_exact hr
  obtain ⟨h1f, h1v⟩ := A32_exact (toF32_one hL)
  obtain ⟨m1, m2⟩ := Float32.mul_exact hrf ha f32_isFinite_0p0 (by rw [hrv, f32_toReal_0p0, zero_mul])
  obtain ⟨d1, d2⟩ := Float32.sub_exact h1f hrf f32_isFinite_1p0 (by rw [hrv, h1v, f32_toReal_1p0, sub_zero])
  have hm : A32 (s._thrust_boost_ratio * a) 0 0 := A32_of_val m1 (by rw [m2, f32_toReal_0p0])
  have hd : A32 (Float.toFloat32 1.0 - s._thrust_boost_ratio) 1 0 := A32_of_val d1 (by rw [d2, f32_toReal_1p0])
  exact zero_add_val' (one_mul_val' hb hd) hm

theorem gain_one (hL : LibmSpec) (s : Thrust_Linearization.State) (inp : Thrust_Linearization.Inputs)
    (hlm : A32 s.lift_max 1 0) (hadr : A32 inp.get_air_density_ratio 1 0) :
    A32 (Thrust_Linearization.get_compensation_gain s inp) 1 0 := by
  obtain ⟨lf, lv⟩ := A32_exact hlm
  obtain ⟨af, av⟩ := A32_exact hadr
  obtain ⟨z0f, z0v⟩ := A32_exact (toF32_zero hL)
  obtain ⟨o1f, o1v⟩ := A32_exact (toF32_one hL)
  obtain ⟨hff, hfv⟩ := A32_exact (toF32_half hL)
  obtain ⟨q5f, q5v⟩ := A32_exact (toF32_1p25 hL)
  obtain ⟨t5f, t5v⟩ := A32_exact (toF32_1p5 hL)
  have h03 := toF32_0p3 hL
  have h03b := (abs_le.1 h03.2)
  have c1 : ¬ (s.lift_max ≤ Float.toFloat32 0.0) := not_le_of lf z0f (by rw [lv, z0v]; norm_num)
  have c2 : inp.get_air_density_ratio > Float.toFloat32 0.3 := lt_of h03.1 af (by rw [av]; linarith)
  have c3 : inp.get_air_density_ratio < Float.toFloat32 1.5 := lt_of af t5f (by rw [av, t5v]; norm_num)
  have hc : constrain_value_line_float inp.get_air_density_ratio (Float.toFloat32 0.5) (Float.toFloat32 1.25)
      (Int32.toUInt32 202) = inp.get_air_density_ratio := by
    rw [FloatLib.motors_cvl]
    exact Float32.cvl_of_between af hff q5f (by rw [hfv, av]; norm_num) (by rw [q5v, av]; norm_num)
  simp only [Thrust_Linearization.get_compensation_gain, Thrust_Linearization.get_lift_max, Id.run,
    c1, c2, c3, hc, decide_true, Bool.and_self, if_true, if_false, id_pure_eq, id_bind_eq]
  have d1 : A32 (Float.toFloat32 1.0 / s.lift_max) 1 0 := div_one_val (toF32_one hL) hlm
  have d2 : A32 (Float.toFloat32 1.0 / inp.get_air_density_ratio) 1 0 := div_one_val (toF32_one hL) hadr
  exact mul_one_val d1 d2

/-- The quad-X roll, pitch, yaw factors after `normalise_rpy_factors` (motors `0 … 3`). -/
def RF : ℕ → ℝ
  | 0 => -1 / 2 | 1 => 1 / 2 | 2 => 1 / 2 | 3 => -1 / 2 | _ => 0
def PF : ℕ → ℝ
  | 0 => 1 / 2 | 1 => -1 / 2 | 2 => 1 / 2 | 3 => -1 / 2 | _ => 0
def YF : ℕ → ℝ
  | 0 => 1 / 2 | 1 => 1 / 2 | 2 => -1 / 2 | 3 => -1 / 2 | _ => 0

theorem abs_RF (i : ℕ) : |RF i| ≤ 1 / 2 := by
  unfold RF; split <;> norm_num [abs_div]
theorem abs_PF (i : ℕ) : |PF i| ≤ 1 / 2 := by
  unfold PF; split <;> norm_num [abs_div]
theorem abs_YF (i : ℕ) : |YF i| ≤ 1 / 2 := by
  unfold YF; split <;> norm_num [abs_div]

theorem B32_of {x : Float32} {r e R : ℝ} (h : A32 x r e) (hR : |r| ≤ R) : B32 x r e R := ⟨h, hR⟩

/-- Roll and pitch of one motor: `roll_thrust * rf + pitch_thrust * pf`. -/
theorem motor_V {rt pt rf pf : Float32} {r q a b : ℝ} (hrt : A32 rt r 0) (hr : |r| ≤ 3 / 20)
    (hpt : A32 pt q 0) (hq : |q| ≤ 3 / 20) (hrf : A32 rf a (1 / 10 ^ 7)) (ha : |a| ≤ 1 / 2)
    (hpf : A32 pf b (1 / 10 ^ 7)) (hb : |b| ≤ 1 / 2) :
    B32 (rt * rf + pt * pf) (r * a + q * b) (5 / 10 ^ 8) (3 / 20) := by
  have m1 := B32.mul (B32_of hrt hr) (B32_of hrf ha) (e := 2 / 10 ^ 8) (R := 3 / 40)
    (by simp only [capF]; norm_num) (by norm_num) (by norm_num)
  have m2 := B32.mul (B32_of hpt hq) (B32_of hpf hb) (e := 2 / 10 ^ 8) (R := 3 / 40)
    (by simp only [capF]; norm_num) (by norm_num) (by norm_num)
  exact B32.add m1 m2 (by norm_num) (by simp only [capF]; norm_num) (by norm_num)

/-- Adding yaw: `v + yaw_thrust * yf`. -/
theorem motor_W {v yt yf : Float32} {c y d : ℝ} (hv : B32 v c (5 / 10 ^ 8) (3 / 20))
    (hyt : A32 yt y 0) (hy : |y| ≤ 3 / 20) (hyf : A32 yf d (1 / 10 ^ 7)) (hd : |d| ≤ 1 / 2) :
    B32 (v + yt * yf) (c + y * d) (9 / 10 ^ 8) (9 / 40) := by
  have m := B32.mul (B32_of hyt hy) (B32_of hyf hd) (e := 2 / 10 ^ 8) (R := 3 / 40)
    (by simp only [capF]; norm_num) (by norm_num) (by norm_num)
  exact B32.add hv m (by norm_num) (by simp only [capF]; norm_num) (by norm_num)

/-- The output of one motor: `best_plus_adj * tf + rpy_scale * w`, with `tf = 1`, `rpy_scale = 1`. -/
theorem motor_Z {bpa tf sc w : Float32} {t c : ℝ} (hb : A32 bpa t (1 / 10 ^ 7)) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 31 / 50) (htf : A32 tf 1 0) (hsc : A32 sc 1 0) (hw : B32 w c (9 / 10 ^ 8) (9 / 40)) :
    A32 (bpa * tf + sc * w) (t + c) (3 / 10 ^ 7) := by
  have h1 := mul_one_val' hb htf
  have h2 := one_mul_val' hw.1 hsc
  refine A32.add_c h1 h2 (R := 31 / 50 + 9 / 40) ?_ (by simp only [capF]; norm_num) (by norm_num)
  have := hw.2
  rw [abs_le] at this ⊢; constructor <;> linarith

/-- `B32` with error `9e-8` and bound `9/40`: the value lies within `B = 9/40 + 9e-8`. -/
theorem B32_val_bound {x : Float32} {c e R : ℝ} (h : B32 x c e R) : |x.toReal| ≤ R + e := by
  have := h.1.abs_le; have := h.2; linarith

theorem lo_bound {w0 w1 w2 w3 : Float32} {B : ℝ}
    (h0 : w0.IsFinite) (h1 : w1.IsFinite) (h2 : w2.IsFinite) (h3 : w3.IsFinite)
    (b0 : |w0.toReal| ≤ B) (b1 : |w1.toReal| ≤ B) (b2 : |w2.toReal| ≤ B) (b3 : |w3.toReal| ≤ B) :
    (MIN_float2 w3 (MIN_float2 w2 (MIN_float2 w1 (MIN_float2 w0 (1.0 : Float32))))).IsFinite ∧
    |(MIN_float2 w3 (MIN_float2 w2 (MIN_float2 w1 (MIN_float2 w0 (1.0 : Float32))))).toReal| ≤ B := by
  obtain ⟨f0, v0⟩ := min_val h0 f32_isFinite_1p0
  obtain ⟨f1, v1⟩ := min_val h1 f0
  obtain ⟨f2, v2⟩ := min_val h2 f1
  obtain ⟨f3, v3⟩ := min_val h3 f2
  refine ⟨f3, ?_⟩
  rw [v3, v2, v1, v0, f32_toReal_1p0]
  rw [abs_le] at b0 b1 b2 b3 ⊢
  constructor
  · simp only [le_min_iff]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_left _ _).trans b0.2)))

theorem hi_bound {w0 w1 w2 w3 : Float32} {B : ℝ}
    (h0 : w0.IsFinite) (h1 : w1.IsFinite) (h2 : w2.IsFinite) (h3 : w3.IsFinite)
    (b0 : |w0.toReal| ≤ B) (b1 : |w1.toReal| ≤ B) (b2 : |w2.toReal| ≤ B) (b3 : |w3.toReal| ≤ B) :
    (MAX_float2 w3 (MAX_float2 w2 (MAX_float2 w1 (MAX_float2 w0 (-(1.0 : Float32)))))).IsFinite ∧
    |(MAX_float2 w3 (MAX_float2 w2 (MAX_float2 w1 (MAX_float2 w0 (-(1.0 : Float32)))))).toReal| ≤ B := by
  have hm1 : (-(1.0 : Float32)).IsFinite := (_root_.Float32.isFinite_neg _).2 f32_isFinite_1p0
  obtain ⟨f0, v0⟩ := max_val h0 hm1
  obtain ⟨f1, v1⟩ := max_val h1 f0
  obtain ⟨f2, v2⟩ := max_val h2 f1
  obtain ⟨f3, v3⟩ := max_val h3 f2
  refine ⟨f3, ?_⟩
  rw [v3, v2, v1, v0, _root_.Float32.toReal_neg, f32_toReal_1p0]
  rw [abs_le] at b0 b1 b2 b3 ⊢
  constructor
  · exact ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))) |>.trans' b0.1
  · simp only [max_le_iff]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem chain4 {α : Type} [Inhabited α] {a : Array α} (h : 4 ≤ a.size) (x0 x1 x2 x3 : α) :
    ((((a.set! 0 x0).set! 1 x1).set! 2 x2).set! 3 x3)[0]! = x0 ∧
    ((((a.set! 0 x0).set! 1 x1).set! 2 x2).set! 3 x3)[1]! = x1 ∧
    ((((a.set! 0 x0).set! 1 x1).set! 2 x2).set! 3 x3)[2]! = x2 ∧
    ((((a.set! 0 x0).set! 1 x1).set! 2 x2).set! 3 x3)[3]! = x3 ∧
    ((((a.set! 0 x0).set! 1 x1).set! 2 x2).set! 3 x3).size = a.size := by
  refine ⟨?_, ?_, ?_, ?_, by simp⟩
  · rw [getElem!_set!_ne (by decide), getElem!_set!_ne (by decide), getElem!_set!_ne (by decide),
      getElem!_set!_self (by omega)]
  · rw [getElem!_set!_ne (by decide), getElem!_set!_ne (by decide), getElem!_set!_self (by simp; omega)]
  · rw [getElem!_set!_ne (by decide), getElem!_set!_self (by simp; omega)]
  · rw [getElem!_set!_self (by simp; omega)]

end

/-! ## M4.1: `output_armed_stabilizing` on the region -/
section
variable (s : State) (inp : Inputs) (x : Float32)
set_option maxHeartbeats 4000000
theorem cff_out : (check_for_failed_motor s inp x)._thrust_rpyt_out = s._thrust_rpyt_out := by
  frame_gen State (fun st : State => st._thrust_rpyt_out = s._thrust_rpyt_out)
    (check_for_failed_motor s inp x) using first | rfl | assumption
theorem cff_limit : (check_for_failed_motor s inp x).limit = s.limit := by
  frame_gen State (fun st : State => st.limit = s.limit) (check_for_failed_motor s inp x)
    using first | rfl | assumption
theorem cff_throttle_out : (check_for_failed_motor s inp x)._throttle_out = s._throttle_out := by
  frame_gen State (fun st : State => st._throttle_out = s._throttle_out)
    (check_for_failed_motor s inp x) using first | rfl | assumption
theorem cff_enabled : (check_for_failed_motor s inp x).motor_enabled = s.motor_enabled := by
  frame_gen State (fun st : State => st.motor_enabled = s.motor_enabled)
    (check_for_failed_motor s inp x) using first | rfl | assumption
end

theorem Quad.with_out {s : State} (hq : Quad s) (A : Array Float32) (hA : 4 ≤ A.size) :
    Quad { s with _thrust_rpyt_out := A } :=
  ⟨hq.en0, hq.en1, hq.en2, hq.en3, hq.dis, hA⟩

set_option maxHeartbeats 8000000 in
/-- **M4.1, `AP_MotorsMatrix::output_armed_stabilizing` on the region.** Quad-X frame, no thrust
boost, boost ratio `0`, compensation gain `1`, `MOT_YAW_HEADROOM = 200`, feed-forwards `0`; the
filtered throttle `thr = get_throttle s ∈ [0.3, 0.62]`, `|roll|, |pitch|, |yaw| ≤ 0.15`,
`_throttle_thrust_max > thr`, `_throttle_avg_max ≤ 1` (finite). Then for `i < 4`,
`_thrust_rpyt_out[i] = thr + RF i·roll + PF i·pitch + YF i·yaw` within `3·10⁻⁷`; `limit` is left
as it was (the function writes `throttle_lower`, `throttle_upper`, `yaw` and, through
`set_rpy`, `roll`, `pitch`, `yaw`, each only on a branch the region excludes); `_throttle_out = thr`
within `10⁻⁷`. -/
theorem armed_stabilizing_spec (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs)
    (hq : Quad s)
    (hrf : ∀ i < 4, A32 s._roll_factor[i]! (RF i) (1 / 10 ^ 7))
    (hpf : ∀ i < 4, A32 s._pitch_factor[i]! (PF i) (1 / 10 ^ 7))
    (hyf : ∀ i < 4, A32 s._yaw_factor[i]! (YF i) (1 / 10 ^ 7))
    (htf : ∀ i < 4, A32 s._throttle_factor[i]! 1 0)
    (hboost : s._thrust_boost = false) (hratio : A32 s._thrust_boost_ratio 0 0)
    (hg : A32 (Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin) 1 0)
    (hhead : p._yaw_headroom = 200)
    (hrff : A32 s._roll_in_ff 0 0) (hpff : A32 s._pitch_in_ff 0 0) (hyff : A32 s._yaw_in_ff 0 0)
    {thr r q y : ℝ}
    (hthr : A32 (get_throttle s) thr 0) (hthr1 : 3 / 10 ≤ thr) (hthr2 : thr ≤ 31 / 50)
    (hr : A32 s._roll_in r 0) (hr1 : |r| ≤ 3 / 20)
    (hp : A32 s._pitch_in q 0) (hp1 : |q| ≤ 3 / 20)
    (hy : A32 s._yaw_in y 0) (hy1 : |y| ≤ 3 / 20)
    (htm : s._throttle_thrust_max.IsFinite) (htm1 : thr < s._throttle_thrust_max.toReal)
    (htam : s._throttle_avg_max.IsFinite) (htam1 : s._throttle_avg_max.toReal ≤ 1) :
    (∀ i < 4, A32 (output_armed_stabilizing p s inp)._thrust_rpyt_out[i]!
        (thr + RF i * r + PF i * q + YF i * y) (3 / 10 ^ 7)) ∧
    (output_armed_stabilizing p s inp).limit = s.limit ∧
    A32 (output_armed_stabilizing p s inp)._throttle_out thr (1 / 10 ^ 7) := by
  -- float facts on the inputs
  have hrt : A32 ((s._roll_in + s._roll_in_ff) *
      Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin) r 0 :=
    mul_one_val (add_zero_val' hr hrff) hg
  have hpt : A32 ((s._pitch_in + s._pitch_in_ff) *
      Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin) q 0 :=
    mul_one_val (add_zero_val' hp hpff) hg
  have hyt : A32 ((s._yaw_in + s._yaw_in_ff) *
      Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin) y 0 :=
    mul_one_val (add_zero_val' hy hyff) hg
  have htt : A32 (get_throttle s * Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin)
      thr 0 := mul_one_val hthr hg
  have httm : A32 (boost_ratio s (Float.toFloat32 1.0)
      (s._throttle_thrust_max * Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin))
      s._throttle_thrust_max.toReal 0 :=
    boost_ratio_val hL s hratio (toF32_one hL).1 (mul_one_val (A32.of_exact htm) hg)
  have htam' : A32 (s._throttle_avg_max * Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin)
      s._throttle_avg_max.toReal 0 := mul_one_val (A32.of_exact htam) hg
  obtain ⟨ttf, ttv⟩ := A32_exact htt
  obtain ⟨tmf, tmv⟩ := A32_exact httm
  have c1 : ¬ (get_throttle s * Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin ≤ 0.0) :=
    not_le_of ttf f32_isFinite_0p0 (by rw [ttv, f32_toReal_0p0]; linarith)
  have c2 : ¬ (get_throttle s * Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin ≥
      boost_ratio s (Float.toFloat32 1.0)
        (s._throttle_thrust_max * Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin)) :=
    not_le_of tmf ttf (by rw [ttv, tmv]; exact htm1)
  -- the symbolic run
  generalize hR : output_armed_stabilizing p s inp = R
  unfold output_armed_stabilizing Id.run at hR
  extract_lets s0 g rt pt yt tt tam ttm jp1 mr0 yam0 rh0 jpA tt0 jpB src sA at hR
  rw [if_neg c1] at hR
  unfold jpB at hR
  beta_reduce at hR
  rw [if_neg c2] at hR
  unfold jpA at hR
  beta_reduce at hR
  extract_lets tam1 best at hR
  rw [Contracts.Mission.id_bind_eq] at hR
  beta_reduce at hR
  extract_lets s1 ya1 yamin ya srcY at hR
  rename_i jpD sY jpE trbt jpF mrA mrB
  -- loop 1
  have hs1 : s1 = (List.range' 0 32).foldl (fun b i => step1 rt pt i b) s0 := by
    refine forIn_range_fst 32 s0 jp1 _ _ ?_
    intro i b
    simp only [step1]
    split_ifs <;> exact ⟨_, rfl⟩
  rw [loop1_eq rt pt s0 hq] at hs1
  dsimp only [s0] at hs1
  have b1 : (s1._thrust_boost && s1.motor_enabled[s1._motor_lost_index.toNat]!) = false := by
    rw [hs1]; simp [s0, hboost]
  rw [b1, if_neg (by decide)] at hR
  unfold jpE at hR
  beta_reduce at hR
  -- the yaw headroom
  have hyam0 : A32 yam0 (13421773 / 67108864) 0 := by
    show A32 (p._yaw_headroom.toFloat32 * 1e-3) _ _
    rw [hhead]; exact A32_of_val f32_isFinite_yamin f32_toReal_yamin
  have hyamin : A32 yamin (13421773 / 67108864) 0 := by
    have hr1' : A32 s1._thrust_boost_ratio 0 0 := by rw [hs1]; exact hratio
    exact boost_ratio_val hL s1 hr1' (toF32_half hL).1 hyam0
  have c3 : ¬ (yt.abs > ya) := by
    obtain ⟨yf, yv⟩ := A32_exact hyt
    obtain ⟨mf, mv⟩ := A32_exact hyamin
    exact not_abs_gt_max yf mf (by rw [yv, mv]; linarith)
  rw [if_neg c3] at hR
  unfold jpD at hR
  beta_reduce at hR
  rw [Contracts.Mission.id_bind_eq] at hR
  beta_reduce at hR
  extract_lets s2 lohi lo hi at hR
  rename_i sC srcC sD srcD sE jpG rhB
  -- loop 2
  have e2 : ((s2, lohi) : State × Float32 × Float32) =
      (List.range' 0 32).foldl (fun b i => step2 yt i b) (s1, jp1, rh0) := by
    refine forIn_range_eq_foldl (fun b : State × Float32 × Float32 => b.1._thrust_boost = false) 32
      _ _ _ ?_ ?_ ?_
    · rw [hs1]; exact hboost
    · intro i b hb
      simp only [step2]
      split_ifs with h1 h2 h3 h3
      · simp only [hb, Bool.not_false, Bool.true_or, Bool.and_true, decide_eq_true_eq] at h3
        simp only [MIN_float2, MAX_float2, Id.run, h2, h3, ite_true, ite_false, id_pure_eq]
      · simp only [hb, Bool.not_false, Bool.true_or, Bool.and_true, decide_eq_true_eq] at h3
        simp only [MIN_float2, MAX_float2, Id.run, h2, h3, ite_true, ite_false, id_pure_eq]
      · simp only [hb, Bool.not_false, Bool.true_or, Bool.and_true, decide_eq_true_eq] at h3
        simp only [MIN_float2, MAX_float2, Id.run, h2, h3, ite_true, ite_false, id_pure_eq]
      · simp only [hb, Bool.not_false, Bool.true_or, Bool.and_true, decide_eq_true_eq] at h3
        simp only [MIN_float2, MAX_float2, Id.run, h2, h3, ite_true, ite_false, id_pure_eq]
      · rfl
    · intro i b hb
      simp only [step2]
      split_ifs <;> exact hb
  rw [hs1, loop2_eq yt jp1 rh0 _ (Quad.with_out hq _ (by simp; exact hq.size)), Prod.mk.injEq,
    Prod.mk.injEq] at e2
  obtain ⟨hs2, hlo, hhi⟩ := e2
  replace hs2 : s2 = _ := hs2
  replace hlo : lo = _ := hlo
  replace hhi : hi = _ := hhi
  dsimp only at hs2
  have hb2 : ¬ (s2._thrust_boost = true) := by rw [hs2]; simp [s0, hboost]
  rw [if_neg hb2] at hR
  unfold jpG at hR
  beta_reduce at hR
  -- the motor values
  obtain ⟨a0, a1, a2, a3, asz⟩ := chain4 hq.size
    (rt * s._roll_factor[0]! + pt * s._pitch_factor[0]!)
    (rt * s._roll_factor[1]! + pt * s._pitch_factor[1]!)
    (rt * s._roll_factor[2]! + pt * s._pitch_factor[2]!)
    (rt * s._roll_factor[3]! + pt * s._pitch_factor[3]!)
  rw [a0, a1, a2, a3] at hs2 hlo hhi
  have hV : ∀ i < 4, B32 (rt * s._roll_factor[i]! + pt * s._pitch_factor[i]!)
      (r * RF i + q * PF i) (5 / 10 ^ 8) (3 / 20) := fun i hi =>
    motor_V hrt hr1 hpt hp1 (hrf i hi) (abs_RF i) (hpf i hi) (abs_PF i)
  have hW : ∀ i < 4, B32 (rt * s._roll_factor[i]! + pt * s._pitch_factor[i]! + yt * s._yaw_factor[i]!)
      (r * RF i + q * PF i + y * YF i) (9 / 10 ^ 8) (9 / 40) := fun i hi =>
    motor_W (hV i hi) hyt hy1 (hyf i hi) (abs_YF i)
  have hWb : ∀ i < 4, (rt * s._roll_factor[i]! + pt * s._pitch_factor[i]! + yt * s._yaw_factor[i]!).IsFinite ∧
      |(rt * s._roll_factor[i]! + pt * s._pitch_factor[i]! + yt * s._yaw_factor[i]!).toReal| ≤
        9 / 40 + 9 / 10 ^ 8 := fun i hi => ⟨(hW i hi).1.1, B32_val_bound (hW i hi)⟩
  obtain ⟨lof, lob⟩ := lo_bound (hWb 0 (by norm_num)).1 (hWb 1 (by norm_num)).1
    (hWb 2 (by norm_num)).1 (hWb 3 (by norm_num)).1 (hWb 0 (by norm_num)).2 (hWb 1 (by norm_num)).2
    (hWb 2 (by norm_num)).2 (hWb 3 (by norm_num)).2
  obtain ⟨hif, hib⟩ := hi_bound (hWb 0 (by norm_num)).1 (hWb 1 (by norm_num)).1
    (hWb 2 (by norm_num)).1 (hWb 3 (by norm_num)).1 (hWb 0 (by norm_num)).2 (hWb 1 (by norm_num)).2
    (hWb 2 (by norm_num)).2 (hWb 3 (by norm_num)).2
  rw [← hlo] at lof lob
  rw [← hhi] at hif hib
  -- the rest of the mixer
  extract_lets at hR
  rename_i jpI jpH rsA
  have u := u32_eq
  have hsub := A32.sub_c (A32.of_exact hif) (A32.of_exact lof) (R := 4502 / 10000) (e := 3 / 10 ^ 8)
    (by rw [abs_le] at hib lob ⊢; constructor <;> linarith) (by simp only [capF]; norm_num) (by norm_num)
  have c4 : ¬ (hi - lo > 1.0) := not_lt_of f32_isFinite_1p0 hsub.1 (by
    rw [f32_toReal_1p0]; have := (abs_le.1 hsub.2).2; rw [abs_le] at hib lob; linarith)
  rw [if_neg c4] at hR
  unfold jpH at hR
  beta_reduce at hR
  extract_lets at hR
  rename_i rsB
  obtain ⟨tmf', tmv'⟩ := A32_exact httm
  obtain ⟨t1f, t1v⟩ := cvl_val (Int32.toUInt32 248) (A32_exact htam').1 ttf tmf (by rw [ttv, tmv]; exact htm1.le)
  rw [ttv, tmv, (A32_exact htam').2] at t1v
  have ht1lo : thr ≤ tam1.toReal := by rw [t1v]; exact le_max_left _ _
  have ht1hi : tam1.toReal ≤ 1 := by
    rw [t1v]; exact max_le (by linarith) ((min_le_left _ _).trans htam1)
  have hadd := A32.add_c (A32.of_exact t1f) (A32.of_exact lof) (R := 13 / 10) (e := 1 / 10 ^ 7)
    (by rw [abs_le] at lob ⊢; constructor <;> linarith) (by simp only [capF]; norm_num) (by norm_num)
  have c5 : ¬ (tam1 + lo < Int32.toFloat32 0) := not_lt_of hadd.1 Float32.isFinite_int32_zero (by
    rw [Float32.toReal_int32_zero]; have := (abs_le.1 hadd.2).1; rw [abs_le] at lob; linarith)
  rw [if_neg c5] at hR
  unfold jpI at hR
  beta_reduce at hR
  extract_lets at hR
  rename_i hi' lo' best2 thadj jpJ jpK thadj2
  have c6 : ¬ (jp1 < 1.0) := not_lt_of f32_isFinite_1p0 f32_isFinite_1p0 le_rfl
  have hhi' : A32 hi' hi.toReal 0 := mul_one_val (A32.of_exact hif) lit_one
  have hlo' : A32 lo' lo.toReal 0 := mul_one_val (A32.of_exact lof) lit_one
  obtain ⟨lo'f, lo'v⟩ := A32_exact hlo'
  have hbest : A32 best2 (-lo.toReal) 0 :=
    A32_of_val ((_root_.Float32.isFinite_neg _).2 lo'f) (by rw [_root_.Float32.toReal_neg, lo'v])
  have hthadj := A32.sub_c htt hbest (R := 8452 / 10000) (e := 6 / 10 ^ 8)
    (by rw [abs_le] at lob ⊢; constructor <;> linarith) (by simp only [capF]; norm_num) (by norm_num)
  have c7 : ¬ (thadj < 0.0) := not_lt_of hthadj.1 f32_isFinite_0p0 (by
    rw [f32_toReal_0p0]; have := (abs_le.1 hthadj.2).1; rw [abs_le] at lob; linarith)
  have hbh := A32.add_c hbest hhi' (R := 4502 / 10000) (e := 3 / 10 ^ 8)
    (by rw [abs_le] at lob hib ⊢; constructor <;> linarith) (by simp only [capF]; norm_num) (by norm_num)
  have hrhs := A32.sub_c lit_one hbh (R := 14502 / 10000) (e := 2 / 10 ^ 7)
    (by rw [abs_le] at lob hib ⊢; constructor <;> linarith) (by simp only [capF]; norm_num) (by norm_num)
  have c8 : ¬ (thadj > 1.0 - (best2 + hi')) := not_lt_of hrhs.1 hthadj.1 (by
    have := (abs_le.1 hrhs.2).1; have := (abs_le.1 hthadj.2).2; rw [abs_le] at lob hib; linarith)
  rw [if_neg c6, if_neg c7, if_neg c8] at hR
  unfold jpJ at hR
  beta_reduce at hR
  extract_lets at hR
  rename_i bpa
  have hbpa : A32 bpa thr (1 / 10 ^ 7) := by
    have h := A32.add_c hbest hthadj (R := 31 / 50) (e := 1 / 10 ^ 7)
      (by rw [show -lo.toReal + (thr - -lo.toReal) = thr by ring, abs_of_nonneg (by linarith)]; exact hthr2)
      (by simp only [capF]; norm_num) (by norm_num)
    exact h.congr (by ring)
  rw [Contracts.Mission.id_bind_eq] at hR
  beta_reduce at hR
  extract_lets at hR
  rename_i s3 s4 s5
  -- loop 3
  have hs3 : s3 = (List.range' 0 32).foldl (fun b i => step3 bpa jp1 i b) s2 := by
    refine forIn_range_eq_foldl (fun _ => True) 32 _ _ _ trivial ?_ (fun _ _ _ => trivial)
    intro i b _
    simp only [step3]
    split_ifs <;> rfl
  rw [hs2, loop3_eq bpa jp1 _ (Quad.with_out hq _ (by simp; exact hq.size))] at hs3
  dsimp only at hs3
  have z0 : 0 < s._thrust_rpyt_out.size := by have := hq.size; omega
  have z1 : 1 < s._thrust_rpyt_out.size := by have := hq.size; omega
  have z2 : 2 < s._thrust_rpyt_out.size := by have := hq.size; omega
  have z3 : 3 < s._thrust_rpyt_out.size := by have := hq.size; omega
  simp (disch := first | decide | (simp only [size_set!]; omega)) only [getElem!_set!_self, getElem!_set!_ne] at hs3
  subst hR
  have e5 : s5._thrust_rpyt_out = s3._thrust_rpyt_out := cff_out s4 inp bpa
  have l5 : s5.limit = s3.limit := cff_limit s4 inp bpa
  have t5 : s5._throttle_out = bpa / g := cff_throttle_out s4 inp bpa
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    show A32 s5._thrust_rpyt_out[i]! _ _
    rw [e5, hs3]
    dsimp only
    have hb0 : 0 ≤ thr := by linarith
    interval_cases i
    · simp (disch := first | decide | (simp only [size_set!]; omega)) only [getElem!_set!_self, getElem!_set!_ne]
      exact (motor_Z hbpa hb0 hthr2 (htf 0 (by norm_num)) lit_one (hW 0 (by norm_num))).congr
        (by simp only [RF, PF, YF]; ring)
    · simp (disch := first | decide | (simp only [size_set!]; omega)) only [getElem!_set!_self, getElem!_set!_ne]
      exact (motor_Z hbpa hb0 hthr2 (htf 1 (by norm_num)) lit_one (hW 1 (by norm_num))).congr
        (by simp only [RF, PF, YF]; ring)
    · simp (disch := first | decide | (simp only [size_set!]; omega)) only [getElem!_set!_self, getElem!_set!_ne]
      exact (motor_Z hbpa hb0 hthr2 (htf 2 (by norm_num)) lit_one (hW 2 (by norm_num))).congr
        (by simp only [RF, PF, YF]; ring)
    · simp (disch := first | decide | (simp only [size_set!]; omega)) only [getElem!_set!_self, getElem!_set!_ne]
      exact (motor_Z hbpa hb0 hthr2 (htf 3 (by norm_num)) lit_one (hW 3 (by norm_num))).congr
        (by simp only [RF, PF, YF]; ring)
  · show s5.limit = s.limit
    rw [l5, hs3]
  · show A32 s5._throttle_out thr _
    rw [t5]
    exact div_one_val hbpa hg

/-! ## M4.2: `set_actuator_with_slew` and `thrust_to_actuator` -/
noncomputable section

/-! ## `set_actuator_with_slew` and `thrust_to_actuator` -/

/-- With both slew times `0`, `set_actuator_with_slew` is the clamp to `[0, 1]`. -/
theorem sws_zero (p : Params) (st : State) (a x : Float32) (hup : A32 p._slew_up_time 0 0)
    (hdn : A32 p._slew_dn_time 0 0) :
    set_actuator_with_slew p st a x = Float32.cvl x 0.0 1.0 := by
  obtain ⟨uf, uv⟩ := A32_exact hup
  obtain ⟨df, dv⟩ := A32_exact hdn
  have h1 : is_positive_AP_Float p._slew_up_time = false := by
    rcases h : is_positive_AP_Float p._slew_up_time with _ | _
    · rfl
    · have := (isPosAP_iff uf).1 h; rw [uv] at this; norm_num at this
  have h2 : is_positive_AP_Float p._slew_dn_time = false := by
    rcases h : is_positive_AP_Float p._slew_dn_time with _ | _
    · rfl
    · have := (isPosAP_iff df).1 h; rw [dv] at this; norm_num at this
  rw [Track.set_actuator_with_slew_eq, h1, h2]
  rfl

/-- On `[0, 1]` the clamp is the identity. -/
theorem cvl01_id {x : Float32} (hx : x.IsFinite) (h0 : 0 ≤ x.toReal) (h1 : x.toReal ≤ 1) :
    Float32.cvl x 0.0 1.0 = x :=
  Float32.cvl_of_between hx f32_isFinite_0p0 f32_isFinite_1p0 (by rw [f32_toReal_0p0]; exact h0)
    (by rw [f32_toReal_1p0]; exact h1)

/-- **`set_actuator_with_slew` with `MOT_SLEW_UP_TIME = MOT_SLEW_DN_TIME = 0`**: the clamp to
`[0, 1]` (finite, in `[0, 1]`, for every input), the identity on `[0, 1]`. -/
theorem sws_spec (p : Params) (st : State) (a x : Float32) (hup : A32 p._slew_up_time 0 0)
    (hdn : A32 p._slew_dn_time 0 0) :
    Track.Act01 (set_actuator_with_slew p st a x) ∧
      (x.IsFinite → 0 ≤ x.toReal → x.toReal ≤ 1 → set_actuator_with_slew p st a x = x) := by
  refine ⟨Track.act01_set_actuator_with_slew p st a x, fun hx h0 h1 => ?_⟩
  rw [sws_zero p st a x hup hdn, cvl01_id hx h0 h1]

/-- The battery scale: `1` when the filtered battery voltage is `1` or not positive. -/
theorem battery_scale (hL : LibmSpec) (b : Float32) (hb : b.IsFinite)
    (hb1 : b.toReal = 1 ∨ b.toReal < 2 ^ (-23 : ℤ)) :
    A32 (if is_positive_float b = true then Float.toFloat32 1.0 / b else Float.toFloat32 1.0) 1 0 := by
  rcases hb1 with h | h
  · have hp : is_positive_float b = true := (isPos_iff hb).2 (by rw [h]; norm_num)
    rw [if_pos hp]
    exact div_one_val (toF32_one hL) (A32_of_val hb h)
  · rw [if_neg (by rw [isPos_false' hb h]; decide)]
    exact toF32_one hL

/-- **`thrust_to_actuator` with `MOT_THST_EXPO = 0`, `MOT_SPIN_MIN = 0`, `MOT_SPIN_MAX = 1`,
battery scale `1`, `lift_max = 1`**: the identity on `[0, 1]` (exactly, `β = 0`). -/
theorem tta_id (hL : LibmSpec) (p : Thrust_Linearization.Params) (s : Thrust_Linearization.State)
    (hexpo : A32 p.curve_expo 0 0) (hmin : A32 p.spin_min 0 0) (hmax : A32 p.spin_max 1 0)
    (hlift : A32 s.lift_max 1 0) (hbf : s.batt_voltage_filt.output.IsFinite)
    (hbv : s.batt_voltage_filt.output.toReal = 1 ∨ s.batt_voltage_filt.output.toReal < 2 ^ (-23 : ℤ))
    {x : Float32} (hx : x.IsFinite) (h0 : 0 ≤ x.toReal) (h1 : x.toReal ≤ 1) :
    A32 (Thrust_Linearization.thrust_to_actuator p s x) x.toReal 0 := by
  obtain ⟨z0f, z0v⟩ := A32_exact (toF32_zero hL)
  obtain ⟨o1f, o1v⟩ := A32_exact (toF32_one hL)
  obtain ⟨ef, ev⟩ := A32_exact hexpo
  have hcx : constrain_value_line_float x (Float.toFloat32 0.0) (Float.toFloat32 1.0)
      (Int32.toUInt32 106) = x := by
    rw [FloatLib.motors_cvl]
    exact Float32.cvl_of_between hx z0f o1f (by rw [z0v]; exact h0) (by rw [o1v]; exact h1)
  have hce : constrain_value_line_float p.curve_expo (-Float.toFloat32 1.0) (Float.toFloat32 1.0)
      (Int32.toUInt32 126) = p.curve_expo := by
    rw [FloatLib.motors_cvl]
    exact Float32.cvl_of_between ef ((_root_.Float32.isFinite_neg _).2 o1f) o1f
      (by rw [_root_.Float32.toReal_neg, o1v, ev]; norm_num) (by rw [o1v, ev]; norm_num)
  have hz : is_zero_float p.curve_expo = true := isZero_true ef (by rw [ev]; norm_num)
  have hbs := battery_scale hL _ hbf hbv
  simp only [Thrust_Linearization.thrust_to_actuator, Thrust_Linearization.apply_thrust_curve_and_volt_scaling,
    Id.run, hcx, hce, hz, LowPassFilterFloat.get, if_true, id_pure_eq, id_bind_eq]
  have m1 : A32 (s.lift_max * x) x.toReal 0 := one_mul_val (A32.of_exact hx) hlift
  obtain ⟨maf, mav⟩ := A32_exact hmax
  obtain ⟨mif, miv⟩ := A32_exact hmin
  obtain ⟨d1, d2⟩ := Float32.sub_exact maf mif f32_isFinite_1p0 (by rw [mav, miv, f32_toReal_1p0]; ring)
  have hd : A32 (p.spin_max - p.spin_min) 1 0 := A32_of_val d1 (by rw [d2, f32_toReal_1p0])
  have key : ∀ bs : Float32, A32 bs 1 0 →
      A32 (p.spin_min + (p.spin_max - p.spin_min) * (s.lift_max * x * bs)) x.toReal 0 :=
    fun bs hbs => zero_add_val' (one_mul_val (mul_one_val m1 hbs) hd) hmin
  split_ifs with hpos
  · exact key _ (by rw [if_pos hpos] at hbs; exact hbs)
  · exact key _ (toF32_one hL)

end

/-! ## M4.3: the throttle filter; the spool logic on `THROTTLE_UNLIMITED` -/
noncomputable section

theorem lpf_apply_eq (F : AP_Motors_lib.LowPassFilterFloat.State) (x dt : Float32) (h : F.initialised = true) :
    AP_Motors_lib.LowPassFilterFloat.apply F x dt =
      ({ F with output := F.output + (x - F.output) * calc_lowpass_alpha_dt dt F.cutoff_freq },
        F.output + (x - F.output) * calc_lowpass_alpha_dt dt F.cutoff_freq) := by
  simp only [AP_Motors_lib.LowPassFilterFloat.apply, AP_Motors_lib.LowPassFilterFloat._apply, Id.run, h,
    Bool.not_true, Bool.false_eq_true, if_false, id_pure_eq, id_bind_eq]

/-- The new output of the throttle filter, `f + (u - f) α`, against `f + α (u - f)`. -/
theorem filter_val {fo ui al : Float32} {f u a : ℝ} (hf : A32 fo f 0) (hu : A32 ui u 0) (ha : A32 al a 0)
    (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    A32 (fo + (ui - fo) * al) (f + a * (u - f)) (2 / 10 ^ 7) := by
  have h1 := A32.sub_c hu hf (R := 1) (e := 6 / 10 ^ 8)
    (by rw [abs_le]; constructor <;> linarith) (by simp only [capF]; norm_num) (by norm_num)
  have h2 := A32.mul_c h1 ha (Ra := 1) (Rb := 1) (e := 12 / 10 ^ 8)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by norm_num) le_rfl (by simp only [capF]; norm_num) (by norm_num)
  have hm : 0 ≤ a * (u - f) + f := by nlinarith
  have hM : a * (u - f) + f ≤ 1 := by nlinarith
  have h3 := A32.add_c (A32.of_exact hf.1) h2 (R := 1) (e := 2 / 10 ^ 7)
    (by rw [(A32_exact hf).2, abs_le]; constructor <;> nlinarith) (by simp only [capF]; norm_num)
    (by norm_num)
  rw [(A32_exact hf).2] at h3
  exact h3.congr (by ring)

/-- **M4, the throttle filter** (`AP_MotorsMulticopter::update_throttle_filter`). Armed, with the
filter initialised and the new value inside `[0, 1]` (no reset to `0` or `1`): the filter's output
becomes `f + (u - f) α` with `α = calc_lowpass_alpha_dt(_dt_s, cutoff)`, within `2·10⁻⁷` of the real
`f + α (u - f)`; the rest of the state is unchanged except the slew-rate estimator. -/
theorem throttle_filter_spec (s : State) (inp : Inputs) (harmed : s._armed = true)
    (hinit : s._throttle_filter.initialised = true) {f u a : ℝ}
    (hf : A32 s._throttle_filter.output f 0) (hu : A32 s._throttle_in u 0)
    (ha : A32 (calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq) a 0)
    (hf0 : 1 / 1000 ≤ f) (hf1 : f ≤ 999 / 1000) (hu0 : 1 / 1000 ≤ u) (hu1 : u ≤ 999 / 1000)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∃ sl slf sr, update_throttle_filter s inp =
      { s with
        _throttle_filter := ({ s._throttle_filter with output := (s._throttle_filter.output +
          (s._throttle_in - s._throttle_filter.output) *
            calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq) })
        _throttle_slew := sl
        _throttle_slew_filter := slf
        _throttle_slew_rate := sr }) ∧
    A32 (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq) (f + a * (u - f)) (2 / 10 ^ 7) := by
  have hv := filter_val hf hu ha (by linarith) (by linarith) (by linarith) (by linarith) ha0 ha1
  have hm : 1 / 1000 ≤ f + a * (u - f) := by nlinarith
  have hM : f + a * (u - f) ≤ 999 / 1000 := by nlinarith
  have hb := abs_le.1 hv.2
  have c1 : ¬ (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq < 0.0) :=
    not_lt_of hv.1 f32_isFinite_0p0 (by rw [f32_toReal_0p0]; linarith)
  have c2 : ¬ (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq > 1.0) :=
    not_lt_of f32_isFinite_1p0 hv.1 (by rw [f32_toReal_1p0]; linarith)
  refine ⟨?_, hv⟩
  simp only [update_throttle_filter, Id.run, armed_void, harmed, lpf_apply_eq _ _ _ hinit,
    AP_Motors_lib.LowPassFilterFloat.get, c1, c2, if_true, if_false, Bool.not_true,
    Bool.false_eq_true, id_pure_eq, id_bind_eq]
  split <;> exact ⟨_, _, _, rfl⟩

/-- All five `limit` flags cleared. -/
def limitsOff : AP_Motors.AP_Motors_limit.State :=
  { roll := false, pitch := false, yaw := false, throttle_lower := false, throttle_upper := false }

/-- **`output_logic` on the `THROTTLE_UNLIMITED` path** (armed, interlock, desired
`THROTTLE_UNLIMITED`, no thrust boost, `MOT_SPOOL_TIME ≥ 0.05`): the parameters are unchanged; the
state gets all `limit` flags cleared, `_spin_up_ratio = 1`, `_throttle_thrust_max = (float) 1.0`,
the boost ratio decayed, and (whatever branch) a new `_disarm_safe_timer`. -/
theorem output_logic_unlimited (p : Params) (s : State) (harmed : s._armed = true)
    (hil : s._interlock = true) (hsp : s._spool_state = AP_Motors.SpoolState.THROTTLE_UNLIMITED)
    (hsd : s._spool_desired = AP_Motors.DesiredSpoolState.THROTTLE_UNLIMITED)
    (hboost : s._thrust_boost = false) (hsut : ¬ (p._spool_up_time < 0.05)) :
    ∃ T, output_logic p s = (p, { s with
      _disarm_safe_timer := T
      limit := limitsOff
      _spin_up_ratio := (1.0 : Float32)
      _throttle_thrust_max := Float.toFloat32 1.0
      _thrust_boost_ratio := (MAX_float2 (Float.toFloat32 0.0)
        (s._thrust_boost_ratio - s._dt_s / p._spool_up_time)) }) := by
  simp only [output_logic, Id.run, armed_void, get_interlock, harmed, hil, hsp, hsd, hboost, hsut,
    get_current_limit_max_throttle, AP_Motors.AP_Motors_limit.set_all, AP_Motors.AP_Motors_limit.set_rpy,
    AP_Motors.AP_Motors_limit.set_throttle, if_true, if_false, Bool.not_true, Bool.false_or, Bool.false_and,
    Bool.false_eq_true, id_pure_eq, id_bind_eq, bne_self_eq_false, ne_eq, not_true_eq_false]
  split <;> exact ⟨_, rfl⟩

/-- The decayed boost ratio stays `0`: `MAX((float) 0.0, 0 - dt / spool_time)` with `dt ≥ 0`. -/
theorem boost_decay (hL : LibmSpec) {r dt t : Float32} (hr : A32 r 0 0) (hdt : dt.IsFinite)
    (hdt0 : 0 ≤ dt.toReal) (hdt1 : dt.toReal ≤ 1) (ht : t.IsFinite) (ht0 : 1 / 10 ≤ t.toReal) :
    A32 (MAX_float2 (Float.toFloat32 0.0) (r - dt / t)) 0 0 := by
  obtain ⟨zf, zv⟩ := A32_exact (toF32_zero hL)
  obtain ⟨rf, rv⟩ := A32_exact hr
  have ht0' : t.toReal ≠ 0 := by intro h; rw [h] at ht0; norm_num at ht0
  have hq0 : 0 ≤ dt.toReal / t.toReal := div_nonneg hdt0 (by linarith)
  have hq1 : dt.toReal / t.toReal ≤ 10 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hm : |dt.toReal / t.toReal| ≤ maxFinite32 := by
    rw [abs_of_nonneg hq0]; have := capF_le_max32; simp only [capF] at this
    have : (10 : ℝ) ≤ 2 ^ (100 : ℤ) := by norm_num
    linarith
  have qf := (_root_.Float32.div_err_all hdt ht ht0' hm).1
  have q0 : 0 ≤ (dt / t).toReal := by
    have := (_root_.Float32.div_bracket hdt ht ht0' hm f32_isFinite_0p0).1
    rw [f32_toReal_0p0] at this; exact this hq0
  have nqf : (-(dt / t)).IsFinite := (_root_.Float32.isFinite_neg _).2 qf
  obtain ⟨xf, xv⟩ := Float32.sub_exact rf qf nqf (by rw [rv, _root_.Float32.toReal_neg]; ring)
  rw [_root_.Float32.toReal_neg] at xv
  show A32 (if Float.toFloat32 0.0 > r - dt / t then _ else _) 0 0
  by_cases hc : Float.toFloat32 0.0 > r - dt / t
  · rw [if_pos hc]; exact toF32_zero hL
  · rw [if_neg hc]
    have := not_lt.1 ((Float32.lt_iff_toReal_lt xf zf).not.1 hc)
    rw [zv, xv] at this
    exact A32_of_val xf (by rw [xv]; linarith)

theorem flag_or_false (b : Bool) :
    ((if b then (1 : Int32) else 0) ||| (if false then (1 : Int32) else 0) != 0) = b := by
  cases b <;> decide

/-- `update_external_limits` with no external limit set leaves `limit` as it is. -/
theorem uel_limit (s : State) (h : s.external_limits = {}) :
    (update_external_limits s).limit = s.limit := by
  simp only [update_external_limits, Id.run, h, flag_or_false]
  rfl

end

/-! ## `output_to_motors` on `THROTTLE_UNLIMITED` -/
noncomputable section

theorem i8_idx_fin : ∀ i : Fin 32, (Nat.toInt8 i.val).toNatClampNeg = i.val := by decide
theorem i8_idx {i : ℕ} (h : i < 32) : (Nat.toInt8 i).toNatClampNeg = i := i8_idx_fin ⟨i, h⟩
theorem i8_0 : (Nat.toInt8 0).toNatClampNeg = 0 := rfl
theorem i8_1 : (Nat.toInt8 1).toNatClampNeg = 1 := rfl
theorem i8_2 : (Nat.toInt8 2).toNatClampNeg = 2 := rfl
theorem i8_3 : (Nat.toInt8 3).toNatClampNeg = 3 := rfl

/-- Iteration `i` of `output_to_motors` (spooling and unlimited states). -/
def step4 (p : Params) (i : ℕ) (st : State) : State :=
  if st.motor_enabled[(Nat.toInt8 i).toNatClampNeg]! = true then
    { st with _actuator := (st._actuator.set! (Nat.toInt8 i).toNatClampNeg
        (set_actuator_with_slew p st st._actuator[(Nat.toInt8 i).toNatClampNeg]!
          (Thrust_Linearization.thrust_to_actuator p.thr_lin st.thr_lin
            st._thrust_rpyt_out[(Nat.toInt8 i).toNatClampNeg]!))) }
  else st

/-- **`output_to_motors` in `THROTTLE_UNLIMITED`** with zero slew times: the four enabled
actuators become `clamp(thrust_to_actuator(_thrust_rpyt_out[i]), 0, 1)`; nothing else changes. -/
theorem otm_eq (p : Params) (s : State) (o : Outputs)
    (hsp : s._spool_state = AP_Motors.SpoolState.THROTTLE_UNLIMITED)
    (en0 : s.motor_enabled[0]! = true) (en1 : s.motor_enabled[1]! = true)
    (en2 : s.motor_enabled[2]! = true) (en3 : s.motor_enabled[3]! = true)
    (dis : ∀ i, 4 ≤ i → s.motor_enabled[i]! = false)
    (hup : A32 p._slew_up_time 0 0) (hdn : A32 p._slew_dn_time 0 0) :
    (output_to_motors p s o).1 = { s with _actuator := (((((s._actuator.set! 0
      (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin s.thr_lin s._thrust_rpyt_out[0]!)
        0.0 1.0)).set! 1
      (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin s.thr_lin s._thrust_rpyt_out[1]!)
        0.0 1.0)).set! 2
      (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin s.thr_lin s._thrust_rpyt_out[2]!)
        0.0 1.0)).set! 3
      (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin s.thr_lin s._thrust_rpyt_out[3]!)
        0.0 1.0))) } := by
  simp only [output_to_motors, Id.run, hsp, id_bind_eq, id_pure_eq]
  rw [forIn_range_eq_foldl (fun _ => True) 32 s _ (step4 p) trivial
    (by intro i b _; simp only [step4]; split_ifs <;> rfl) (fun _ _ _ => trivial)]
  rw [foldl_range32 _ (fun st : State => st.motor_enabled = s.motor_enabled) _
    (by simp only [step4]; split_ifs <;> rfl)
    (by intro i b h4 h32 hb; simp only [step4]; rw [i8_idx h32, hb, dis i h4]; simp)]
  simp only [step4, i8_0, i8_1, i8_2, i8_3, en0, en1, en2, en3, if_true,
    sws_zero _ _ _ _ hup hdn, hsp]

end

/-! ## The filter coefficient in flight -/
noncomputable section

theorem isNegM_false (hL : LibmSpec) {x : Float32} (hx : x.IsFinite) (h0 : 0 ≤ x.toReal) :
    AP_Motors_lib.is_negative_float x = false :=
  isNeg_false hL hx h0

/-- `(float) M_PI` within `2·10⁻⁷` of `π`. -/
theorem pi32' (hL : LibmSpec) : A32 (Float.toFloat32 (3.1415926535897931 : Float)) Real.pi (2 / 10 ^ 7) := by
  have h := A64.toFloat32 hL (A64.of_exact f64_isFinite_3p1415926535897931)
    (by rw [f64_toReal_3p1415926535897931, abs_of_nonneg (by norm_num)]; simp only [capF]; norm_num)
  rw [f64_toReal_3p1415926535897931] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  have p1 := Real.pi_gt_d20
  have p2 := Real.pi_lt_d20
  have e := abs_sub_le (Float.toFloat32 (3.1415926535897931 : Float)).toReal
    (884279719003555 / 281474976710656) Real.pi
  have := η32_small
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 884279719003555 / 281474976710656)] at h2
  have h3 : |(884279719003555 / 281474976710656 : ℝ) - Real.pi| ≤ 1 / 10 ^ 15 := by
    rw [abs_le]; constructor <;> norm_num at p1 p2 ⊢ <;> linarith
  simp only [u32] at h2
  norm_num at h2 e ⊢
  linarith

/-- **The throttle filter's `α` in flight**: `calc_lowpass_alpha_dt(dt, 2 Hz)` with `dt` within
`10⁻⁹` of `1/400` (the 400 Hz loop) is within `4·10⁻⁸` of `dt/(dt + 1/(4π))` and within
`5·10⁻⁸` of `16352567/536870912` (the value the loop computes). -/
theorem alpha_flight (hL : LibmSpec) {dt cutoff : Float32} (hdt : A32 dt (1 / 400) (1 / 10 ^ 9))
    (hc : A32 cutoff 2 0) :
    A32 (calc_lowpass_alpha_dt dt cutoff) ((1 / 400) / (1 / 400 + 1 / (Real.pi * 2 * 2))) (4 / 10 ^ 8) ∧
    A32 (calc_lowpass_alpha_dt dt cutoff) (16352567 / 536870912) (5 / 10 ^ 8) := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  obtain ⟨cf, cv⟩ := A32_exact hc
  have hdb := abs_le.1 hdt.2
  have dpos : 0 ≤ dt.toReal := by linarith
  have n1 : AP_Motors_lib.is_negative_float dt = false := isNegM_false hL hdt.1 dpos
  have n2 : AP_Motors_lib.is_negative_float cutoff = false := isNegM_false hL cf (by rw [cv]; norm_num)
  have z1 : AP_Motors_lib.is_zero_float cutoff = false := isZero_false cf (by rw [cv]; norm_num)
  have z2 : AP_Motors_lib.is_zero_float dt = false := isZero_false hdt.1 (by
    rw [abs_of_nonneg dpos]; norm_num; linarith)
  have e : calc_lowpass_alpha_dt dt cutoff = dt / (dt + (1.0 : Float32) /
      ((Float.toFloat32 (3.1415926535897931 : Float) * Int32.toFloat32 2) * cutoff)) := by
    simp only [calc_lowpass_alpha_dt, Id.run, n1, n2, z1, z2, Bool.or_self, Bool.false_eq_true,
      if_false, id_pure_eq]
  rw [e]
  have hpi := pi32' hL
  have h2 : A32 (Int32.toFloat32 2) 2 0 := A32_of_val Float32.isFinite_int32_two Float32.toReal_int32_two
  have m1 := A32.mul_c hpi h2 (Ra := 3.1416) (Rb := 2) (e := 8 / 10 ^ 7)
    (by rw [abs_of_pos Real.pi_pos]; linarith) (by norm_num) (by norm_num) le_rfl
    (by simp only [capF]; norm_num) (by norm_num)
  have m2 := A32.mul_c m1 hc (Ra := 6.2832) (Rb := 2) (e := 24 / 10 ^ 7)
    (by rw [abs_of_pos (by positivity)]; linarith) (by norm_num) (by norm_num) le_rfl
    (by simp only [capF]; norm_num) (by norm_num)
  have d1 := A32.div_c lit_one m2 (Ra := 1) (m := 12) (Q := 1 / 12) (e := 3 / 10 ^ 8)
    (by norm_num) (by norm_num) (by rw [abs_of_pos (by positivity)]; nlinarith)
    (by norm_num) (by rw [abs_div, abs_one, abs_of_pos (by positivity)]
                      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
    (by simp only [capF]; norm_num) (by norm_num)
  have hrc0 : 0 < 1 / (Real.pi * 2 * 2) := by positivity
  have hrc1 : 1 / (Real.pi * 2 * 2) ≤ 1 / 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hrc2 : 795 / 10000 ≤ 1 / (Real.pi * 2 * 2) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have a1 := A32.add_c hdt d1 (R := 1 / 10) (e := 4 / 10 ^ 8)
    (by rw [abs_of_pos (by positivity)]; linarith) (by simp only [capF]; norm_num) (by norm_num)
  have q := A32.div_c hdt a1 (Ra := 1 / 400) (m := 8 / 100) (Q := 1 / 30) (e := 4 / 10 ^ 8)
    (by rw [abs_of_pos (by norm_num)]) (by norm_num) (by rw [abs_of_pos (by positivity)]; linarith)
    (by norm_num) (by rw [abs_div, abs_of_pos (by norm_num), abs_of_pos (by positivity)]
                      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
    (by simp only [capF]; norm_num) (by norm_num)
  refine ⟨q, ⟨q.1, ?_⟩⟩
  have hq := q.2
  have hi : |(1 / 400 : ℝ) / (1 / 400 + 1 / (Real.pi * 2 * 2)) - 16352567 / 536870912| ≤ 1 / 10 ^ 8 := by
    have p3 := Real.pi_gt_d20
    have p4 := Real.pi_lt_d20
    have hid : (1 / 400 : ℝ) / (1 / 400 + 1 / (Real.pi * 2 * 2)) = Real.pi / (Real.pi + 100) := by
      field_simp; ring
    rw [hid, abs_le]
    constructor
    · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]; nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; nlinarith
  have := abs_sub_le (dt / (dt + 1.0 / (Float.toFloat32 3.1415926535897931 * Int32.toFloat32 2 * cutoff))).toReal
    ((1 / 400 : ℝ) / (1 / 400 + 1 / (Real.pi * 2 * 2))) (16352567 / 536870912)
  linarith

end

/-! ## M4.4: one call of `AP_MotorsMulticopter::output` -/
section
variable (s : State) (inp : Inputs) (x : Float32)
set_option maxHeartbeats 4000000
theorem cff_frame : (check_for_failed_motor s inp x)._spool_state = s._spool_state ∧
    (check_for_failed_motor s inp x).motor_enabled = s.motor_enabled ∧
    (check_for_failed_motor s inp x).thr_lin = s.thr_lin ∧
    (check_for_failed_motor s inp x).external_limits = s.external_limits := by
  frame_gen State (fun st : State => st._spool_state = s._spool_state ∧ st.motor_enabled = s.motor_enabled ∧
      st.thr_lin = s.thr_lin ∧ st.external_limits = s.external_limits)
    (check_for_failed_motor s inp x) using first | exact ⟨rfl, rfl, rfl, rfl⟩ | assumption
end

set_option maxHeartbeats 4000000 in
theorem oas_frame (p : Params) (s : State) (inp : Inputs) :
    (output_armed_stabilizing p s inp)._spool_state = s._spool_state ∧
    (output_armed_stabilizing p s inp).motor_enabled = s.motor_enabled ∧
    (output_armed_stabilizing p s inp).thr_lin = s.thr_lin ∧
    (output_armed_stabilizing p s inp).external_limits = s.external_limits := by
  frame_gen State (fun st : State => st._spool_state = s._spool_state ∧ st.motor_enabled = s.motor_enabled ∧
      st.thr_lin = s.thr_lin ∧ st.external_limits = s.external_limits)
    (output_armed_stabilizing p s inp) using first
    | exact ⟨rfl, rfl, rfl, rfl⟩ | assumption
    | (obtain ⟨h1, h2, h3, h4⟩ := cff_frame _ inp _; rwa [h1, h2, h3, h4])

theorem ideal_bound (i : ℕ) {r q y : ℝ} (hr : |r| ≤ 3 / 20) (hq : |q| ≤ 3 / 20) (hy : |y| ≤ 3 / 20) :
    |RF i * r + PF i * q + YF i * y| ≤ 9 / 40 := by
  have h1 : |RF i * r| ≤ 1 / 2 * (3 / 20) := by
    rw [abs_mul]; exact mul_le_mul (abs_RF i) hr (abs_nonneg _) (by norm_num)
  have h2 : |PF i * q| ≤ 1 / 2 * (3 / 20) := by
    rw [abs_mul]; exact mul_le_mul (abs_PF i) hq (abs_nonneg _) (by norm_num)
  have h3 : |YF i * y| ≤ 1 / 2 * (3 / 20) := by
    rw [abs_mul]; exact mul_le_mul (abs_YF i) hy (abs_nonneg _) (by norm_num)
  have := abs_add_le (RF i * r + PF i * q) (YF i * y)
  have := abs_add_le (RF i * r) (PF i * q)
  linarith

theorem get_throttle_val (st : State) {t : ℝ} (h : A32 st._throttle_filter.output t 0) (h0 : 0 ≤ t)
    (h1 : t ≤ 1) : A32 (get_throttle st) t 0 := by
  obtain ⟨hf, hv⟩ := A32_exact h
  show A32 (constrain_value_line_float st._throttle_filter.output 0.0 1.0 (Int32.toUInt32 219)) t 0
  rw [FloatLib.motors_cvl, cvl01_id hf (by rw [hv]; exact h0) (by rw [hv]; exact h1)]
  exact h

/-- `armed_stabilizing_spec` for a state given through an equation, with the frame facts the
composition needs. -/
theorem armed_stabilizing_eq (hL : LibmSpec) (p : Params) {s S : State} (inp : Inputs)
    (hS : output_armed_stabilizing p s inp = S) (hq : Quad s)
    (hrf : ∀ i < 4, A32 s._roll_factor[i]! (RF i) (1 / 10 ^ 7))
    (hpf : ∀ i < 4, A32 s._pitch_factor[i]! (PF i) (1 / 10 ^ 7))
    (hyf : ∀ i < 4, A32 s._yaw_factor[i]! (YF i) (1 / 10 ^ 7))
    (htf : ∀ i < 4, A32 s._throttle_factor[i]! 1 0)
    (hboost : s._thrust_boost = false) (hratio : A32 s._thrust_boost_ratio 0 0)
    (hg : A32 (Thrust_Linearization.get_compensation_gain s.thr_lin inp.thr_lin) 1 0)
    (hhead : p._yaw_headroom = 200)
    (hrff : A32 s._roll_in_ff 0 0) (hpff : A32 s._pitch_in_ff 0 0) (hyff : A32 s._yaw_in_ff 0 0)
    {thr r q y : ℝ}
    (hthr : A32 (get_throttle s) thr 0) (hthr1 : 3 / 10 ≤ thr) (hthr2 : thr ≤ 31 / 50)
    (hr : A32 s._roll_in r 0) (hr1 : |r| ≤ 3 / 20)
    (hp : A32 s._pitch_in q 0) (hp1 : |q| ≤ 3 / 20)
    (hy : A32 s._yaw_in y 0) (hy1 : |y| ≤ 3 / 20)
    (htm : s._throttle_thrust_max.IsFinite) (htm1 : thr < s._throttle_thrust_max.toReal)
    (htam : s._throttle_avg_max.IsFinite) (htam1 : s._throttle_avg_max.toReal ≤ 1) :
    (∀ i < 4, A32 S._thrust_rpyt_out[i]! (thr + RF i * r + PF i * q + YF i * y) (3 / 10 ^ 7)) ∧
    S.limit = s.limit ∧ S._spool_state = s._spool_state ∧ S.motor_enabled = s.motor_enabled ∧
    S.thr_lin = s.thr_lin ∧ S.external_limits = s.external_limits ∧ S._actuator = s._actuator := by
  subst hS
  obtain ⟨h1, h2, -⟩ := armed_stabilizing_spec hL p s inp hq hrf hpf hyf htf hboost hratio hg hhead
    hrff hpff hyff hthr hthr1 hthr2 hr hr1 hp hp1 hy hy1 htm htm1 htam htam1
  obtain ⟨f1, f2, f3, f4⟩ := oas_frame p s inp
  exact ⟨h1, h2, f1, f2, f3, f4, Track.act_output_armed_stabilizing p s inp⟩

set_option maxHeartbeats 8000000 in
/-- **M4.4, one call of `AP_MotorsMulticopter::output`** on the `THROTTLE_UNLIMITED` path (armed,
interlock, spool state and desired spool state `THROTTLE_UNLIMITED`, `MOT_SPOOL_TIME ≥ 0.1`,
`0 ≤ _dt_s ≤ 1`, no external limits), with the mission's motor parameters (zero slew times,
`MOT_THST_EXPO = 0`, `MOT_SPIN_MIN = 0`, `MOT_SPIN_MAX = 1`, `lift_max = 1`, battery scale `1`,
air density ratio `1`) and the region: filter output `f` and throttle input `u` in
`[0.301, 0.619]`, `α ∈ [0, 1]`, `|roll|, |pitch|, |yaw| ≤ 0.15`. With `f'` the new filter output:
`f' = f + α (u - f)` within `2·10⁻⁷`; for `i < 4` the actuator is
`f' + RF i·roll + PF i·pitch + YF i·yaw` within `3·10⁻⁷` and lies in `(0, 1)`; every `limit`
flag is false. -/
theorem output_spec (hL : LibmSpec) (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (hq : Quad s) (hasz : 4 ≤ s._actuator.size)
    (hrf : ∀ i < 4, A32 s._roll_factor[i]! (RF i) (1 / 10 ^ 7))
    (hpf : ∀ i < 4, A32 s._pitch_factor[i]! (PF i) (1 / 10 ^ 7))
    (hyf : ∀ i < 4, A32 s._yaw_factor[i]! (YF i) (1 / 10 ^ 7))
    (htf : ∀ i < 4, A32 s._throttle_factor[i]! 1 0)
    (harmed : s._armed = true) (hil : s._interlock = true)
    (hsp : s._spool_state = AP_Motors.SpoolState.THROTTLE_UNLIMITED)
    (hsd : s._spool_desired = AP_Motors.DesiredSpoolState.THROTTLE_UNLIMITED)
    (hboost : s._thrust_boost = false) (hratio : A32 s._thrust_boost_ratio 0 0)
    (hext : s.external_limits = {})
    (hdt : s._dt_s.IsFinite) (hdt0 : 0 ≤ s._dt_s.toReal) (hdt1 : s._dt_s.toReal ≤ 1)
    (hsut : p._spool_up_time.IsFinite) (hsut1 : 1 / 10 ≤ p._spool_up_time.toReal)
    (hhead : p._yaw_headroom = 200)
    (hup : A32 p._slew_up_time 0 0) (hdn : A32 p._slew_dn_time 0 0)
    (hexpo : A32 p.thr_lin.curve_expo 0 0) (hmin : A32 p.thr_lin.spin_min 0 0)
    (hmax : A32 p.thr_lin.spin_max 1 0) (hlift : A32 s.thr_lin.lift_max 1 0)
    (hbf : s.thr_lin.batt_voltage_filt.output.IsFinite)
    (hbv : s.thr_lin.batt_voltage_filt.output.toReal = 1 ∨
      s.thr_lin.batt_voltage_filt.output.toReal < 2 ^ (-23 : ℤ))
    (hadr : A32 inp.thr_lin.get_air_density_ratio 1 0)
    (hrff : A32 s._roll_in_ff 0 0) (hpff : A32 s._pitch_in_ff 0 0) (hyff : A32 s._yaw_in_ff 0 0)
    (hinit : s._throttle_filter.initialised = true)
    {f u a r q y : ℝ}
    (hf : A32 s._throttle_filter.output f 0) (hf0 : 301 / 1000 ≤ f) (hf1 : f ≤ 619 / 1000)
    (hu : A32 s._throttle_in u 0) (hu0 : 301 / 1000 ≤ u) (hu1 : u ≤ 619 / 1000)
    (ha : A32 (calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq) a 0)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hr : A32 s._roll_in r 0) (hr1 : |r| ≤ 3 / 20)
    (hp : A32 s._pitch_in q 0) (hp1 : |q| ≤ 3 / 20)
    (hy : A32 s._yaw_in y 0) (hy1 : |y| ≤ 3 / 20)
    (htam : s._throttle_avg_max.IsFinite) (htam1 : s._throttle_avg_max.toReal ≤ 1) :
    A32 (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
        calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq) (f + a * (u - f)) (2 / 10 ^ 7) ∧
    (∀ i < 4, A32 (output p s o inp).2.1._actuator[i]!
        ((s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
          calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq).toReal +
          RF i * r + PF i * q + YF i * y) (3 / 10 ^ 7) ∧
      0 < (output p s o inp).2.1._actuator[i]!.toReal ∧ (output p s o inp).2.1._actuator[i]!.toReal < 1) ∧
    (output p s o inp).2.1.limit = limitsOff := by
  -- the throttle filter
  obtain ⟨⟨sl, slf, sr, hs1⟩, hfv⟩ := throttle_filter_spec s inp harmed hinit hf hu ha
    (by linarith) (by linarith) (by linarith) (by linarith) ha0 ha1
  generalize hF : s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
    calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq = F at hs1 hfv ⊢
  refine ⟨hfv, ?_⟩
  have hFb := abs_le.1 hfv.2
  have hF0 : 3 / 10 ≤ F.toReal := by nlinarith
  have hF1 : F.toReal ≤ 31 / 50 := by nlinarith
  simp only [output, Id.run, id_bind_eq, id_pure_eq]
  -- the spool logic
  have hsut' : ¬ (p._spool_up_time < 0.05) := not_lt_of hsut f32_isFinite_0p05 (by
    rw [f32_toReal_0p05]; linarith)
  obtain ⟨T, hol⟩ := output_logic_unlimited p (update_throttle_filter s inp) (by rw [hs1]; exact harmed)
    (by rw [hs1]; exact hil) (by rw [hs1]; exact hsp) (by rw [hs1]; exact hsd) (by rw [hs1]; exact hboost)
    hsut'
  rw [hol]
  dsimp only
  rw [hs1]
  dsimp only
  -- the boost ratio after the spool logic
  have hbr : A32 (MAX_float2 (Float.toFloat32 0.0) (s._thrust_boost_ratio - s._dt_s / p._spool_up_time)) 0 0 :=
    boost_decay hL hratio hdt hdt0 hdt1 hsut hsut1
  have hgain := gain_one hL s.thr_lin inp.thr_lin hlift hadr
  obtain ⟨o1f, o1v⟩ := A32_exact (toF32_one hL)
  -- the mixer
  generalize hS3 : output_armed_stabilizing p _ inp = S3
  obtain ⟨hout, hlim, hsp3, hen3, hthr3, hext3, hact3⟩ := armed_stabilizing_eq hL p inp hS3
    ⟨hq.en0, hq.en1, hq.en2, hq.en3, hq.dis, hq.size⟩ hrf hpf hyf htf hboost hbr hgain hhead
    hrff hpff hyff (get_throttle_val _ (A32.of_exact hfv.1) (by linarith) (by linarith)) hF0 hF1
    hr hr1 hp hp1 hy hy1 o1f (by rw [o1v]; linarith) htam htam1
  have hsp3' : S3._spool_state = AP_Motors.SpoolState.THROTTLE_UNLIMITED := hsp3.trans hsp
  rw [otm_eq p S3 o hsp3' (by rw [hen3]; exact hq.en0) (by rw [hen3]; exact hq.en1)
    (by rw [hen3]; exact hq.en2) (by rw [hen3]; exact hq.en3)
    (fun i h => by rw [hen3]; exact hq.dis i h) hup hdn]
  rw [Track.act_update_external_limits, uel_limit _ (by exact hext3.trans hext)]
  have hthr3' : S3.thr_lin = s.thr_lin := hthr3
  have hasz3 : 4 ≤ S3._actuator.size := by rw [hact3]; exact hasz
  obtain ⟨c0, c1, c2, c3, -⟩ := chain4 hasz3
    (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin S3.thr_lin S3._thrust_rpyt_out[0]!) 0.0 1.0)
    (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin S3.thr_lin S3._thrust_rpyt_out[1]!) 0.0 1.0)
    (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin S3.thr_lin S3._thrust_rpyt_out[2]!) 0.0 1.0)
    (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin S3.thr_lin S3._thrust_rpyt_out[3]!) 0.0 1.0)
  have key : ∀ i < 4, A32 (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin S3.thr_lin
      S3._thrust_rpyt_out[i]!) 0.0 1.0) (F.toReal + RF i * r + PF i * q + YF i * y) (3 / 10 ^ 7) ∧
      0 < (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin S3.thr_lin
        S3._thrust_rpyt_out[i]!) 0.0 1.0).toReal ∧
      (Float32.cvl (Thrust_Linearization.thrust_to_actuator p.thr_lin S3.thr_lin
        S3._thrust_rpyt_out[i]!) 0.0 1.0).toReal < 1 := by
    intro i hi
    have ho := hout i hi
    have hb := abs_le.1 ho.2
    have hib := abs_le.1 (ideal_bound i hr1 hp1 hy1)
    have v0 : 0 < S3._thrust_rpyt_out[i]!.toReal := by linarith
    have v1 : S3._thrust_rpyt_out[i]!.toReal < 1 := by linarith
    rw [hthr3']
    have ht := tta_id hL p.thr_lin s.thr_lin hexpo hmin hmax hlift hbf hbv ho.1 v0.le v1.le
    obtain ⟨tf, tv⟩ := A32_exact ht
    rw [cvl01_id tf (by rw [tv]; exact v0.le) (by rw [tv]; exact v1.le), tv]
    exact ⟨⟨tf, by rw [tv]; exact ho.2⟩, v0, v1⟩
  refine ⟨?_, hlim⟩
  intro i hi
  dsimp only
  interval_cases i
  · rw [c0]; exact key 0 (by norm_num)
  · rw [c1]; exact key 1 (by norm_num)
  · rw [c2]; exact key 2 (by norm_num)
  · rw [c3]; exact key 3 (by norm_num)

/-- **M4.4 at the call of `Vehicle.tick`**: `output w.mp w.ms #[] (motorsInputs w)` (the harness's
air density ratio `1`). -/
theorem tick_output_spec (hL : LibmSpec) (w : Vehicle.World)
    (hq : Quad w.ms) (hasz : 4 ≤ w.ms._actuator.size)
    (hrf : ∀ i < 4, A32 w.ms._roll_factor[i]! (RF i) (1 / 10 ^ 7))
    (hpf : ∀ i < 4, A32 w.ms._pitch_factor[i]! (PF i) (1 / 10 ^ 7))
    (hyf : ∀ i < 4, A32 w.ms._yaw_factor[i]! (YF i) (1 / 10 ^ 7))
    (htf : ∀ i < 4, A32 w.ms._throttle_factor[i]! 1 0)
    (harmed : w.ms._armed = true) (hil : w.ms._interlock = true)
    (hsp : w.ms._spool_state = AP_Motors.SpoolState.THROTTLE_UNLIMITED)
    (hsd : w.ms._spool_desired = AP_Motors.DesiredSpoolState.THROTTLE_UNLIMITED)
    (hboost : w.ms._thrust_boost = false) (hratio : A32 w.ms._thrust_boost_ratio 0 0)
    (hext : w.ms.external_limits = {})
    (hdt : w.ms._dt_s.IsFinite) (hdt0 : 0 ≤ w.ms._dt_s.toReal) (hdt1 : w.ms._dt_s.toReal ≤ 1)
    (hsut : w.mp._spool_up_time.IsFinite) (hsut1 : 1 / 10 ≤ w.mp._spool_up_time.toReal)
    (hhead : w.mp._yaw_headroom = 200)
    (hup : A32 w.mp._slew_up_time 0 0) (hdn : A32 w.mp._slew_dn_time 0 0)
    (hexpo : A32 w.mp.thr_lin.curve_expo 0 0) (hmin : A32 w.mp.thr_lin.spin_min 0 0)
    (hmax : A32 w.mp.thr_lin.spin_max 1 0) (hlift : A32 w.ms.thr_lin.lift_max 1 0)
    (hbf : w.ms.thr_lin.batt_voltage_filt.output.IsFinite)
    (hbv : w.ms.thr_lin.batt_voltage_filt.output.toReal = 1 ∨
      w.ms.thr_lin.batt_voltage_filt.output.toReal < 2 ^ (-23 : ℤ))
    (hadr : A32 w.h.air_density_ratio 1 0)
    (hrff : A32 w.ms._roll_in_ff 0 0) (hpff : A32 w.ms._pitch_in_ff 0 0)
    (hyff : A32 w.ms._yaw_in_ff 0 0)
    (hinit : w.ms._throttle_filter.initialised = true)
    {f u a r q y : ℝ}
    (hf : A32 w.ms._throttle_filter.output f 0) (hf0 : 301 / 1000 ≤ f) (hf1 : f ≤ 619 / 1000)
    (hu : A32 w.ms._throttle_in u 0) (hu0 : 301 / 1000 ≤ u) (hu1 : u ≤ 619 / 1000)
    (ha : A32 (calc_lowpass_alpha_dt w.ms._dt_s w.ms._throttle_filter.cutoff_freq) a 0)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hr : A32 w.ms._roll_in r 0) (hr1 : |r| ≤ 3 / 20)
    (hp : A32 w.ms._pitch_in q 0) (hp1 : |q| ≤ 3 / 20)
    (hy : A32 w.ms._yaw_in y 0) (hy1 : |y| ≤ 3 / 20)
    (htam : w.ms._throttle_avg_max.IsFinite) (htam1 : w.ms._throttle_avg_max.toReal ≤ 1) :
    A32 (w.ms._throttle_filter.output + (w.ms._throttle_in - w.ms._throttle_filter.output) *
        calc_lowpass_alpha_dt w.ms._dt_s w.ms._throttle_filter.cutoff_freq) (f + a * (u - f))
        (2 / 10 ^ 7) ∧
    (∀ i < 4, A32 (output w.mp w.ms #[] (Vehicle.motorsInputs w)).2.1._actuator[i]!
        ((w.ms._throttle_filter.output + (w.ms._throttle_in - w.ms._throttle_filter.output) *
          calc_lowpass_alpha_dt w.ms._dt_s w.ms._throttle_filter.cutoff_freq).toReal +
          RF i * r + PF i * q + YF i * y) (3 / 10 ^ 7) ∧
      0 < (output w.mp w.ms #[] (Vehicle.motorsInputs w)).2.1._actuator[i]!.toReal ∧
      (output w.mp w.ms #[] (Vehicle.motorsInputs w)).2.1._actuator[i]!.toReal < 1) ∧
    (output w.mp w.ms #[] (Vehicle.motorsInputs w)).2.1.limit = limitsOff :=
  output_spec hL w.mp w.ms #[] (Vehicle.motorsInputs w) hq hasz hrf hpf hyf htf harmed hil hsp hsd
    hboost hratio hext hdt hdt0 hdt1 hsut hsut1 hhead hup hdn hexpo hmin hmax hlift hbf hbv hadr
    hrff hpff hyff hinit hf hf0 hf1 hu hu0 hu1 ha ha0 ha1 hr hr1 hp hp1 hy hy1 htam htam1

end Contracts.Track.Mixer
