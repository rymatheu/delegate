import Contracts.Track.PacingArrive

/-!
# Milestone (3): liveness of the navigator without a time bound (REACH.md §3)

The navigator's S-curve clock `q` (`navProgress`, the sum of the filtered track scalers) is
advanced by the filtered scaler `s`, which follows the raw scaler `r ∈ [0, 1]` (`rawScaler_unit`)
through the first-order filter `s ← s + (r − s) α` (`code_filter_step`). This file proves:

* **`code_filter_nonneg`** (a `float` fact of the code): the stored scaler of
  `_track_dt_scalar ← s + (r − s) * (dt / tc)` stays `≥ 0` exactly when it starts `≥ 0`: every
  rounding is monotone and `0`, `-s` are floats, so `fl(r − s) ≥ −s`, `fl(fl(r − s)·α) ≥ −s`,
  `fl(s + ·) ≥ 0`. Hence `q` is nondecreasing (the filter bound `[−c, 1 + c]` of
  `filter_bounds` allows `−c`; the sign is exact).
* **`liveness`** (the LaSalle argument, in `ℝ`): if `q` cannot converge to any point outside a
  *stall set* `Z` without the raw scaler eventually staying above a level `ρ` with `ε_f < α ρ`, then
  either `q → ∞` (the clock passes the end of every table) or `q` converges to a point of `Z`.
  No time bound is involved: the contradiction is `q` bounded against `q` growing by at least
  `α ρ − ε_f > 0` per tick.
* `liveness_course`: the instance with the code's `α₀ = 1118481/2²⁷` and `ε_f = 10⁻⁷`.

`Equilibrium.lean` computes the stall set of the closed-loop model: the raw scaler at the
stalled-target equilibrium is `clamp(0.05 + 1 + d_z² (1/2 + 3/10 · a*/v*), 0, 1)` (`d` the leg
direction, `v*, a*` the S-curve speed and acceleration at the stall point), so for a horizontal leg
it is `1` at every interior point and the stall set is empty; with a vertical component it is the end
of the deceleration where `a*/v* ≤ −(3.5/d_z² + 5/3)`.
-/

namespace Contracts.Track.Reach

open Contracts.Mission Contracts.Track.Pacing Filter Topology Float.Model UnpackedFloat

/-! ## The sign of the filtered scaler (code fact) -/

theorem max32_big : (10 : ℝ) ^ 12 ≤ maxFinite32 := by
  rw [Float32.maxFinite32_eq]; norm_num

/-- **The filter keeps the scaler nonnegative, exactly.** For finite `s ∈ [0, 2]`, `r ∈ [0, 1]`,
the `float` update `s + (r - s) * alphaF` of `advance_wp_target_along_track` is finite and `≥ 0`. -/
theorem code_filter_nonneg {s r : Float32} (hs : s.IsFinite) (hr : r.IsFinite)
    (hs0 : 0 ≤ s.toReal) (hs2 : s.toReal ≤ 2) (hr0 : 0 ≤ r.toReal) (hr1 : r.toReal ≤ 1) :
    (s + (r - s) * alphaF).IsFinite ∧ 0 ≤ (s + (r - s) * alphaF).toReal := by
  obtain ⟨fa, ea⟩ := alpha_eval
  have hα0 : (0 : ℝ) < α₀ := by norm_num [α₀]
  have hα1 : α₀ ≤ 1 := by norm_num [α₀]
  have hM := max32_big
  have hns : (-s).IsFinite := (Float32.isFinite_neg s).2 hs
  have hnsv : (-s).toReal = -s.toReal := Float32.toReal_neg s
  -- d = fl(r - s)
  have hsub : |r.toReal - s.toReal| ≤ maxFinite32 := by
    rw [abs_le]; constructor <;> nlinarith
  obtain ⟨fd, ed⟩ := Float32.sub_err_all hr hs hsub
  have hd_lo : -s.toReal ≤ (r - s).toReal := by
    have := (Float32.sub_bracket hr hs hsub hns).1 (by rw [hnsv]; linarith)
    rwa [hnsv] at this
  have hd_hi : (r - s).toReal ≤ 1 := by
    have h1 := (Float32.sub_bracket hr hs hsub f32_isFinite_1p0).2
      (by rw [f32_toReal_1p0]; linarith)
    rwa [f32_toReal_1p0] at h1
  -- m = fl(d α)
  have hmul : |(r - s).toReal * alphaF.toReal| ≤ maxFinite32 := by
    rw [ea, abs_le]; constructor <;> nlinarith
  obtain ⟨fm, _⟩ := Float32.mul_err_all fd fa hmul
  have hm_lo : -s.toReal ≤ ((r - s) * alphaF).toReal := by
    have hprod : -s.toReal ≤ (r - s).toReal * alphaF.toReal := by
      rw [ea]
      rcases le_or_gt 0 (r - s).toReal with h | h
      · nlinarith
      · nlinarith
    have := (Float32.mul_bracket fd fa hmul hns).1 (by rw [hnsv]; exact hprod)
    rwa [hnsv] at this
  have hm_hi : ((r - s) * alphaF).toReal ≤ 1 := by
    have hprod : (r - s).toReal * alphaF.toReal ≤ 1 := by
      rw [ea]; nlinarith
    have := (Float32.mul_bracket fd fa hmul f32_isFinite_1p0).2 (by rw [f32_toReal_1p0]; exact hprod)
    rwa [f32_toReal_1p0] at this
  -- fl(s + m)
  have hadd : |s.toReal + ((r - s) * alphaF).toReal| ≤ maxFinite32 := by
    rw [abs_le]; constructor <;> nlinarith
  obtain ⟨ff, _⟩ := Float32.add_err_all hs fm hadd
  refine ⟨ff, ?_⟩
  have := (Float32.add_bracket hs fm hadd f32_isFinite_0p0).1 (by rw [f32_toReal_0p0]; linarith)
  rwa [f32_toReal_0p0] at this

/-! ## The liveness argument -/

variable {s r q : ℕ → ℝ} {α εf ρ : ℝ}

/-- With `s ≥ 0`, the clock is monotone. -/
theorem q_mono (hs : ∀ t, 0 ≤ s t) (hq : ∀ t, q (t + 1) = q t + s (t + 1)) : Monotone q := by
  refine monotone_nat_of_le_succ fun t => ?_
  rw [hq t]; linarith [hs (t + 1)]

/-- Once the raw scaler stays at least `ρ`, the filtered scaler is at least `α ρ − ε_f` from the
next tick on. -/
theorem s_lower (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hs : ∀ t, 0 ≤ s t) (hf : FilterRun s r α εf) {t : ℕ}
    (hr : ρ ≤ r (t + 1)) : α * ρ - εf ≤ s (t + 1) := by
  have h := hf t
  rw [abs_le] at h
  have hα : 0 ≤ 1 - α := by linarith
  have := mul_nonneg hα (hs t)
  have h2 : s t + (r (t + 1) - s t) * α = (1 - α) * s t + α * r (t + 1) := by ring
  nlinarith [mul_le_mul_of_nonneg_left hr hα0]

/-- **Liveness of the S-curve clock (no time bound).** Hypotheses:

* the code facts: `s ≥ 0` (`code_filter_nonneg`), the filter (`code_filter_step`), and the clock
  `q (t+1) = q t + s (t+1)` (`navProgress`, exact by definition);
* the closed-loop fact `HL`: whenever `q` converges to a point `q*` outside the stall set `Z`, the
  raw scaler is eventually at least `ρ`, with `ε_f < α ρ`.

Then either `q → ∞`, or `q` converges to a point of `Z`. -/
theorem liveness (hα0 : 0 < α) (hα1 : α ≤ 1) (hs : ∀ t, 0 ≤ s t) (hf : FilterRun s r α εf)
    (hq : ∀ t, q (t + 1) = q t + s (t + 1)) (Z : Set ℝ) (hρ : εf < α * ρ)
    (HL : ∀ q', q' ∉ Z → Tendsto q atTop (𝓝 q') → ∀ᶠ t in atTop, ρ ≤ r t) :
    Tendsto q atTop atTop ∨ ∃ q' ∈ Z, Tendsto q atTop (𝓝 q') := by
  have hm := q_mono hs hq
  by_cases hb : BddAbove (Set.range q)
  · right
    have hlim : Tendsto q atTop (𝓝 (⨆ t, q t)) := tendsto_atTop_ciSup hm hb
    refine ⟨⨆ t, q t, ?_, hlim⟩
    by_contra hZ
    obtain ⟨T, hT⟩ := eventually_atTop.1 (HL _ hZ hlim)
    -- from `T` on, `q` grows by at least `δ = α ρ − ε_f > 0` per tick
    set δ := α * ρ - εf with hδ
    have hδ0 : 0 < δ := by linarith
    have hgrow : ∀ n, q (T + n) + n * δ ≤ q (T + n) + n * δ ∧ q T + n * δ ≤ q (T + n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        refine ⟨le_rfl, ?_⟩
        have h1 := hq (T + n)
        have h2 := s_lower hα0.le hα1 hs hf (t := T + n) (hT (T + n + 1) (by omega))
        rw [show T + (n + 1) = T + n + 1 by omega, h1]
        push_cast
        linarith [ih.2]
    obtain ⟨M, hM⟩ := hb
    obtain ⟨n, hn⟩ := exists_nat_gt ((M - q T) / δ)
    have h1 := (hgrow n).2
    have h2 : q (T + n) ≤ M := hM ⟨T + n, rfl⟩
    have h3 : (M - q T) < n * δ := by
      rwa [div_lt_iff₀ hδ0] at hn
    linarith
  · left
    exact tendsto_atTop_atTop_of_monotone hm fun b => by
      by_contra h
      push Not at h
      exact hb ⟨b, by rintro _ ⟨t, rfl⟩; exact (h t).le⟩

/-- The instance with the code's filter: `α = α₀ = 1118481/2²⁷`, `ε_f = 10⁻⁷`; any level
`ρ ≥ 1.3·10⁻⁵` works (`ε_f/α₀ < 1.3·10⁻⁵`). -/
theorem liveness_code (hs : ∀ t, 0 ≤ s t) (hf : FilterRun s r α₀ (1 / 10 ^ 7))
    (hq : ∀ t, q (t + 1) = q t + s (t + 1)) (Z : Set ℝ) (hρ : 13 / 10 ^ 6 ≤ ρ)
    (HL : ∀ q', q' ∉ Z → Tendsto q atTop (𝓝 q') → ∀ᶠ t in atTop, ρ ≤ r t) :
    Tendsto q atTop atTop ∨ ∃ q' ∈ Z, Tendsto q atTop (𝓝 q') := by
  have h1 : (1 / 10 ^ 7 : ℝ) < α₀ * (13 / 10 ^ 6) := by norm_num [α₀]
  have h2 : α₀ * (13 / 10 ^ 6) ≤ α₀ * ρ := mul_le_mul_of_nonneg_left hρ (by norm_num [α₀])
  exact liveness (by norm_num [α₀]) (by norm_num [α₀]) hs hf hq Z (by linarith) HL

/-- The S-curve clock passes every level unless it stalls in `Z`. -/
theorem passes_or_stalls (hα0 : 0 < α) (hα1 : α ≤ 1) (hs : ∀ t, 0 ≤ s t)
    (hf : FilterRun s r α εf) (hq : ∀ t, q (t + 1) = q t + s (t + 1)) (Z : Set ℝ)
    (hρ : εf < α * ρ) (HL : ∀ q', q' ∉ Z → Tendsto q atTop (𝓝 q') → ∀ᶠ t in atTop, ρ ≤ r t)
    (Q : ℝ) : (∃ t, Q ≤ q t) ∨ ∃ q' ∈ Z, q' ≤ Q ∧ Tendsto q atTop (𝓝 q') := by
  rcases liveness hα0 hα1 hs hf hq Z hρ HL with h | ⟨q', hZ, hl⟩
  · left; exact (h.eventually (eventually_ge_atTop Q)).exists
  · by_cases hQ : ∃ t, Q ≤ q t
    · left; exact hQ
    · right
      push Not at hQ
      exact ⟨q', hZ, le_of_tendsto' hl fun t => (hQ t).le, hl⟩

end Contracts.Track.Reach
