import Contracts.Track.PacingScaler

/-!
# Milestone M8, lemma P-2: the filtered scaler and its stretches below `1 − η`

The navigator filters the raw scaler (`PacingScaler.lean`) with
`_track_dt_scalar ← s + (r − s) · (dt / tc)` (`advance_track_dt_scalar`). With the course's
`WP_ACC = 1.5`, `WP_JERK = 5` and the period `dt = 0.0025f`, the coefficient is the `float`
`α = 0.0025f / (1.5f / 5f) = 1118481 / 2²⁷ ≈ 1/120` (`alpha_eval`).

* `filter_step`: one `float` step is within `10⁻⁷` of the real step `s + (r − s) α`;
* `FilterRun`: a real sequence with that property; `filter_bounds`: it stays in
  `[−c, 1 + c]`, `c = ε_f / α`;
* the deficit `D = 1 − s`: `deficit_step`, the summed form `deficit_sum` (the lag over a stretch is
  the raw deficits plus `(1/α − 1)` times the initial deficit), and the decay `deficit_decay` while
  the raw scaler is at least `ρ`;
* **`stretch_bound` (P-2)**: a stretch of ticks on which `s < 1 − η`, and on which the raw scaler is
  at least `ρ` after its first `W` ticks, is shorter than `W + n` whenever
  `(1 − α)ⁿ (1 + c) + (1 − ρ) + c < η`;
* `stretch_course`: the instance used on the course (`η = 2/5`, the smallest raw bound of
  `PacingArrive.lean`, `ρ = 0.7712`): `n = 212`.
-/

namespace Contracts.Track.Pacing

open Contracts.Mission Float.Model UnpackedFloat AC_WPNav_lib AC_WPNav

noncomputable section

/-! ## The coefficient and one `float` step -/

/-- The period of the course, `0.0025f`: the first tick's `1.0f / 400.0f` is that float. -/
theorem dt_first : (1.0 : Float32) / (400.0 : Float32) = (0.0025 : Float32) := by decide +kernel

/-- The filter coefficient `dt / tc` with `dt = 0.0025f`, `tc = 1.5f / 5f`. -/
def alphaF : Float32 := (0.0025 : Float32) / ((1.5 : Float32) / (5.0 : Float32))

/-- Its value, `1118481 / 2²⁷` (`1/α = 120.0000072`). -/
def α₀ : ℝ := 1118481 / 134217728

theorem alpha_unpack : alphaF.toModel.unpack = .finite .positive 8947848 (-30) (by decide) := by rfl

theorem alpha_eval : alphaF.IsFinite ∧ alphaF.toReal = α₀ := by
  constructor
  · rw [Float32.isFinite_iff, alpha_unpack]; rfl
  · rw [Float32.toReal, alpha_unpack]; simp [UnpackedFloat.toReal, Sign.apply, α₀]; norm_num

/-- With `WP_ACC = 1.5` and `WP_JERK = 5`, the navigator's `trackTc` is `1.5f / 5f`. -/
theorem trackTc_eq (p : Params) (hacc : get_wp_acceleration_mss p = 1.5)
    (hj : p._wp_jerk_msss = 5.0) : trackTc p = (1.5 : Float32) / (5.0 : Float32) := by
  have : is_zero_AP_Float (5.0 : Float32) = false := by decide +kernel
  simp [trackTc, hacc, hj, this]

/-- The `float` filter step with the course's coefficient is within `10⁻⁷` of the real step, for
`s` within `10⁻³` of `[0, 1]` and `r ∈ [0, 1]`. -/
theorem filter_step {s r : Float32} (hs : s.IsFinite) (hr : r.IsFinite)
    (hs1 : -(1 / 1000) ≤ s.toReal ∧ s.toReal ≤ 1 + 1 / 1000) (hr1 : 0 ≤ r.toReal ∧ r.toReal ≤ 1) :
    (s + (r - s) * alphaF).IsFinite ∧
      |(s + (r - s) * alphaF).toReal - (s.toReal + (r.toReal - s.toReal) * α₀)| ≤ 1 / 10 ^ 7 := by
  obtain ⟨fa, ea⟩ := alpha_eval
  have bs := B32.of_exact hs (R := 1 + 1 / 1000) (abs_le.2 ⟨by linarith, by linarith⟩)
  have br := B32.of_exact hr (R := 1) (abs_le.2 ⟨by linarith, by linarith⟩)
  have ba := B32.of_exact fa (R := 1 / 100) (by rw [ea, α₀]; norm_num)
  have d1 := B32.sub (e := 13 / 10 ^ 8) (R := 2 + 1 / 1000) br bs (by norm_num) (by norm_num [capF])
    (by norm_num)
  have d2 := B32.mul (e := 3 / 10 ^ 9) (R := 3 / 100) d1 ba (by norm_num [capF]) (by norm_num)
    (by norm_num)
  have d3 := B32.add (e := 7 / 10 ^ 8) (R := 26 / 25) bs d2 (by norm_num) (by norm_num [capF])
    (by norm_num)
  refine ⟨d3.1.1, ?_⟩
  have := d3.1.2
  rw [ea] at this
  exact this.trans (by norm_num)

/-! ## The real dynamics -/

/-- A run of the filter with coefficient `α` and rounding `ε_f`: `s` after each tick, `r` the raw
scaler of each tick. -/
def FilterRun (s r : ℕ → ℝ) (α εf : ℝ) : Prop :=
  ∀ t, |s (t + 1) - (s t + (r (t + 1) - s t) * α)| ≤ εf

variable {s r : ℕ → ℝ} {α εf : ℝ}

/-- The filter stays in `[−c, 1 + c]`, `c = ε_f / α`. -/
theorem filter_bounds (hα0 : 0 < α) (hα1 : α ≤ 1) (hf : FilterRun s r α εf)
    (hr : ∀ t, 0 ≤ r t ∧ r t ≤ 1) (hs0 : -(εf / α) ≤ s 0 ∧ s 0 ≤ 1 + εf / α) :
    ∀ t, -(εf / α) ≤ s t ∧ s t ≤ 1 + εf / α := by
  intro t
  induction t with
  | zero => exact hs0
  | succ t ih =>
    have h := abs_le.1 (hf t)
    have hc : α * (εf / α) = εf := by field_simp
    obtain ⟨r0, r1⟩ := hr (t + 1)
    constructor <;> nlinarith [ih.1, ih.2]

/-- The deficit `1 − s` after one step. -/
theorem deficit_step (hf : FilterRun s r α εf) (t : ℕ) :
    1 - s (t + 1) ≤ (1 - α) * (1 - s t) + α * (1 - r (t + 1)) + εf := by
  have h := (abs_le.1 (hf t)).1; nlinarith

/-- **The deficit summed over a stretch.** `α Σ (1 − s) ≤ (1 − α)(D₀ − D_n) + α Σ (1 − r) + n ε_f`. -/
theorem deficit_sum (hf : FilterRun s r α εf) (t0 : ℕ) : ∀ n : ℕ,
    α * ∑ k ∈ Finset.range n, (1 - s (t0 + k + 1)) ≤
      (1 - α) * ((1 - s t0) - (1 - s (t0 + n))) +
        α * ∑ k ∈ Finset.range n, (1 - r (t0 + k + 1)) + n * εf := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := deficit_step hf (t0 + n)
    rw [show t0 + (n + 1) = t0 + n + 1 by ring]
    push_cast
    nlinarith

/-- **The decay.** While the raw scaler is at least `ρ ≤ 1`, the deficit decays at rate `1 − α`
to `(1 − ρ) + ε_f / α`. -/
theorem deficit_decay (hα0 : 0 < α) (hα1 : α ≤ 1) (hf : FilterRun s r α εf) {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hεf : 0 ≤ εf) (t0 : ℕ) : ∀ n : ℕ, (∀ k < n, ρ ≤ r (t0 + k + 1)) →
      1 - s (t0 + n) ≤ (1 - α) ^ n * (1 - s t0) + ((1 - ρ) + εf / α) := by
  have hB : 0 ≤ (1 - ρ) + εf / α := by have := div_nonneg hεf hα0.le; linarith
  have hc : α * (εf / α) = εf := by field_simp
  -- `D − B` contracts
  have key : ∀ n : ℕ, (∀ k < n, ρ ≤ r (t0 + k + 1)) →
      1 - s (t0 + n) - ((1 - ρ) + εf / α) ≤ (1 - α) ^ n * (1 - s t0 - ((1 - ρ) + εf / α)) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hk
      have h1 := ih (fun k hk' => hk k (Nat.lt_succ_of_lt hk'))
      have h2 := deficit_step hf (t0 + n)
      have h3 := hk n (Nat.lt_succ_self n)
      rw [show t0 + n + 1 = t0 + (n + 1) by ring] at h2 h3
      have h4 : 0 ≤ 1 - α := by linarith
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left h1 h4]
  intro n hk
  have h1 := key n hk
  have h2 : 0 ≤ (1 - α) ^ n := pow_nonneg (by linarith) n
  nlinarith [mul_nonneg h2 hB]

/-- **Lemma P-2 (stretches below `1 − η`).** Let the filter run with `s ≤ 1 + c` (`c = ε_f/α`).
A stretch of ticks `t₀ … t₀ + L` on which `s < 1 − η`, and on which the raw scaler is at least
`ρ` at every tick after the first `W`, is shorter than `W + n` whenever
`(1 − α)ⁿ (1 + c) + (1 − ρ) + c < η`. -/
theorem stretch_bound (hα0 : 0 < α) (hα1 : α ≤ 1) (hf : FilterRun s r α εf) (hεf : 0 ≤ εf)
    (hs : ∀ t, -(εf / α) ≤ s t ∧ s t ≤ 1 + εf / α) {ρ η : ℝ} (hρ1 : ρ ≤ 1) {W n : ℕ}
    (hn : (1 - α) ^ n * (1 + εf / α) + ((1 - ρ) + εf / α) < η) (t0 L : ℕ)
    (hgood : ∀ k, W < k → k ≤ L → ρ ≤ r (t0 + k)) (hlow : ∀ k ≤ L, s (t0 + k) < 1 - η) :
    L < W + n := by
  by_contra hL
  push Not at hL
  have hd := deficit_decay hα0 hα1 hf hρ1 hεf (t0 + W) n (fun k hk => by
    have := hgood (W + k + 1) (by omega) (by omega)
    rwa [show t0 + (W + k + 1) = t0 + W + k + 1 by ring] at this)
  have h1 : 1 - s (t0 + W) ≤ 1 + εf / α := by linarith [(hs (t0 + W)).1]
  have h2 : 0 ≤ (1 - α) ^ n := pow_nonneg (by linarith) n
  have h3 := hlow (W + n) hL
  rw [show t0 + (W + n) = t0 + W + n by ring] at h3
  nlinarith [mul_le_mul_of_nonneg_left h1 h2]

/-- The rounding bound of the course: `c = ε_f / α₀` with `ε_f = 10⁻⁷`. -/
theorem c_course : (1 / 10 ^ 7 : ℝ) / α₀ ≤ 13 / 10 ^ 6 := by
  rw [α₀, div_le_iff₀ (by norm_num)]; norm_num

/-- **P-2 on the course.** With the coefficient `α₀`, rounding `10⁻⁷`, and raw scaler at least
`ρ = 0.7712` after the first `W` ticks of a stretch, every stretch with `s < 3/5` is shorter than
`W + 212` ticks (`0.53 s` after the raw scaler recovers). -/
theorem stretch_course (hf : FilterRun s r α₀ (1 / 10 ^ 7))
    (hs : ∀ t, -((1 / 10 ^ 7) / α₀) ≤ s t ∧ s t ≤ 1 + (1 / 10 ^ 7) / α₀) {W : ℕ} (t0 L : ℕ)
    (hgood : ∀ k, W < k → k ≤ L → 7712 / 10000 ≤ r (t0 + k))
    (hlow : ∀ k ≤ L, s (t0 + k) < 3 / 5) : L < W + 212 := by
  have hα : (0 : ℝ) < α₀ := by rw [α₀]; norm_num
  have hα1 : α₀ ≤ 1 := by rw [α₀]; norm_num
  have hc := c_course
  have hpow : (1 - α₀) ^ 212 ≤ 17 / 100 := by rw [α₀]; norm_num
  refine stretch_bound hα hα1 hf (by norm_num) hs (by norm_num) (η := 2 / 5) ?_ t0 L hgood
    (fun k hk => by have := hlow k hk; linarith)
  have : (1 - α₀) ^ 212 * (1 + 1 / 10 ^ 7 / α₀) ≤ 17 / 100 * (1 + 13 / 10 ^ 6) :=
    mul_le_mul hpow (by linarith) (by positivity) (by norm_num)
  nlinarith

/-- **The code's filter step.** Without terrain following, with `WP_ACC = 1.5`, `WP_JERK = 5`,
`dt = 0.0025f` and `_track_dt_scalar` within `10⁻³` of `[0, 1]`, the new `_track_dt_scalar` of
`advance_wp_target_along_track` is finite and within `10⁻⁷` of `s + (r − s) α₀`, where `r` is the
raw scaler of the call (`rawScaler`, in `[0, 1]` by `rawScaler_unit`). -/
theorem code_filter_step (p : Params) (st : State) (o : Outputs) (inp : Inputs)
    (hT : st._is_terrain_alt = false) (hacc : get_wp_acceleration_mss p = 1.5)
    (hj : p._wp_jerk_msss = 5.0) (hs : st._track_dt_scalar.IsFinite)
    (hs1 : -(1 / 1000) ≤ st._track_dt_scalar.toReal ∧ st._track_dt_scalar.toReal ≤ 1 + 1 / 1000) :
    let r := rawScaler (curTargetVel inp (scalerLog o)) (inp.get_pos_error_NED_m (scalerLog o))
      (inp.get_vel_estimate_NED_ms (scalerLog o)) (inp.NE_get_pos_p_kP (scalerLog o))
    let s' := (advance_wp_target_along_track p st o inp (0.0025 : Float32)).1._track_dt_scalar
    s'.IsFinite ∧ |s'.toReal - (st._track_dt_scalar.toReal +
      (r.toReal - st._track_dt_scalar.toReal) * α₀)| ≤ 1 / 10 ^ 7 := by
  intro r s'
  obtain ⟨fr, r0, r1⟩ := rawScaler_unit (curTargetVel inp (scalerLog o))
    (inp.get_pos_error_NED_m (scalerLog o)) (inp.get_vel_estimate_NED_ms (scalerLog o))
    (inp.NE_get_pos_p_kP (scalerLog o))
  have e : s' = st._track_dt_scalar + (r - st._track_dt_scalar) * alphaF := by
    show (advance_wp_target_along_track p st o inp (0.0025 : Float32)).1._track_dt_scalar = _
    rw [advance_track_dt_scalar p st o inp _ hT, trackTc_eq p hacc hj]; rfl
  rw [e]
  exact filter_step hs fr hs1 ⟨r0, r1⟩

end

end Contracts.Track.Pacing
