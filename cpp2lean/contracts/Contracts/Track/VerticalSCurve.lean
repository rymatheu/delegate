import Contracts.Track.VerticalClimb
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The nominal S-curve climb (milestone M5, item 3)

`SCurve` (AP_Math, translated in `AC_WPNav_lib`) builds the acceleration phase of a leg from
three segments: increasing jerk `Jm/2 (1 - cos(π t/tj))` on `[0, tj]`, constant jerk (here of
length `t2 = Am/Jm - tj = 0`), decreasing jerk on `[tj, 2 tj]`; with the configured limits of a
vertical leg (`WP_ACC_Z = 1`, `WP_JERK = 5`, snap `5π/(2·0.1)/2`, hence `tj = 0.2 s` and
`Am = Jm tj = 1`) the jerk of each acceleration ramp is the raised-cosine pulse
`5/2 (1 - cos (5π u))` on `[0, 0.4]`, of integral `1`, and the target acceleration is that pulse
convolved with the bang-bang profile `bangRef` of the same leg (`VERTICAL.md`). So the nominal
climb from rest at S-curve time `-s₀` is

  `scurveRef s₀ L k = ∫₀^0.4 pulse u · bangRef (s₀ + u) (T1ofL L) k du`,

componentwise (position, velocity, acceleration: the convolution commutes with integration in
time). `scurve_climb` bounds the model's tracking error of this target by `0.0875 m` for every
start phase `s₀ ≥ 0` and every vertical leg `L ∈ [0.5, 0.8] m`.
-/

namespace Contracts.Track.Vertical

open MeasureTheory Set Matrix

/-! ## Weighted averages of targets -/

theorem forceOf_smul (c : ℝ) (r : ℕ → ℝ × ℝ × ℝ) (k : ℕ) :
    forceOf (fun j => c • r j) k = c • forceOf r k := by
  ext i
  simp only [forceOf, defect₁, defect₂, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Pi.sub_apply,
    Pi.smul_apply]
  ring

theorem errResp_smul (c : ℝ) (r : ℕ → ℝ × ℝ × ℝ) (k : ℕ) :
    errResp (fun j => c • r j) k = c • errResp r k := by
  have h := traj_smul AvR c 0 (forceOf r) k
  rw [smul_zero] at h
  simp only [errResp]
  rw [← h]
  congr 1
  funext j
  exact forceOf_smul c r j

/-- **Weighted averages keep the bound**: a target that is the `w`-weighted average (`w ≥ 0`,
`∫ w = 1`) of targets whose responses stay below `B` has its response below `B`. -/
theorem errResp_weighted_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (w : α → ℝ)
    (hw : ∀ u, 0 ≤ w u) (hwi : Integrable w μ) (hw1 : ∫ u, w u ∂μ = 1)
    (R : α → ℕ → ℝ × ℝ × ℝ) (r : ℕ → ℝ × ℝ × ℝ)
    (hint : ∀ k, Integrable (fun u => w u * (R u k).1) μ ∧
      Integrable (fun u => w u * (R u k).2.1) μ ∧ Integrable (fun u => w u * (R u k).2.2) μ)
    (hr : ∀ k, r k = (∫ u, w u * (R u k).1 ∂μ, ∫ u, w u * (R u k).2.1 ∂μ,
      ∫ u, w u * (R u k).2.2 ∂μ))
    {B : ℝ} (hB : ∀ᵐ u ∂μ, ∀ k, |errResp (R u) k 0| ≤ B) (k : ℕ) : |errResp r k 0| ≤ B := by
  have h := (errResp_integral μ (fun u k => w u • R u k) r
    (fun k => by simpa only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using hint k)
    (fun k => by simpa only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using hr k) k 0).2
  have e : (fun u => errResp (fun j => w u • R u j) k 0) = fun u => w u * errResp (R u) k 0 := by
    funext u; rw [errResp_smul]; rfl
  rw [h, e]
  have hg : Integrable (fun u => B * w u) μ := hwi.const_mul B
  have hle := norm_integral_le_of_norm_le (f := fun u => w u * errResp (R u) k 0) hg (hB.mono fun u hu => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw u), mul_comm]
    exact mul_le_mul_of_nonneg_right (hu k) (hw u))
  rw [Real.norm_eq_abs, integral_const_mul, hw1, mul_one] at hle
  exact hle

/-! ## The raised-cosine pulse -/

/-- The jerk pulse of an acceleration ramp of `SCurve` (`Jm = 5`, `tj = 0.2 s`, `Am = 1`), as a
probability density on `[0, 0.4]`. -/
noncomputable def pulse (u : ℝ) : ℝ := (1 - Real.cos (5 * Real.pi * u)) * (5 / 2)

theorem pulse_nonneg (u : ℝ) : 0 ≤ pulse u := by
  have := Real.cos_le_one (5 * Real.pi * u)
  unfold pulse; nlinarith

theorem pulse_le (u : ℝ) : pulse u ≤ 5 := by
  have := Real.neg_one_le_cos (5 * Real.pi * u)
  unfold pulse; nlinarith

theorem continuous_pulse : Continuous pulse := by
  unfold pulse; fun_prop

theorem integral_pulse : ∫ u in (0 : ℝ)..(2 / 5), pulse u = 1 := by
  have hc : ∫ u in (0 : ℝ)..(2 / 5), Real.cos (5 * Real.pi * u) = 0 := by
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x)
      (by positivity : (5 * Real.pi) ≠ 0), integral_cos]
    have : 5 * Real.pi * (2 / 5) = 2 * Real.pi := by ring
    simp [this]
  simp only [pulse]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_sub intervalIntegrable_const
    ((by fun_prop : Continuous fun u : ℝ => Real.cos (5 * Real.pi * u)).intervalIntegrable 0 (2 / 5)), hc]
  simp

/-! ## The nominal climb -/

/-- **The nominal S-curve climb** of a vertical leg of length `L`, from rest, at start phase
`s₀` (S-curve time `k h - s₀` at tick `k`): position, velocity and acceleration of the target. -/
noncomputable def scurveRef (s₀ L : ℝ) (k : ℕ) : ℝ × ℝ × ℝ :=
  (∫ u in (0 : ℝ)..(2 / 5), pulse u * (bangRef (s₀ + u) (T1ofL L) k).1,
   ∫ u in (0 : ℝ)..(2 / 5), pulse u * (bangRef (s₀ + u) (T1ofL L) k).2.1,
   ∫ u in (0 : ℝ)..(2 / 5), pulse u * (bangRef (s₀ + u) (T1ofL L) k).2.2)

theorem measurable_stepRef (f : ℝ → ℝ) (hf : Measurable f) (k : ℕ) :
    Measurable (fun u : ℝ => stepRef (f u) k) := by
  unfold stepRef
  refine Measurable.ite (measurableSet_le hf measurable_const) ?_ measurable_const
  fun_prop

theorem measurable_bangRef (a T1 : ℝ) (k : ℕ) : Measurable (fun u : ℝ => bangRef (a + u) T1 k) := by
  have m0 := measurable_stepRef (fun u => a + u) (by fun_prop) k
  have m1 := measurable_stepRef (fun u => a + u + T1) (by fun_prop) k
  have m2 := measurable_stepRef (fun u => a + u + T1 + 2 / 5) (by fun_prop) k
  have m3 := measurable_stepRef (fun u => a + u + 2 * T1 + 2 / 5) (by fun_prop) k
  exact ((m0.sub m1).sub m2).add m3

/-- A bound of the components of a step target on tick `k`. -/
theorem stepRef_bound (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    |(stepRef s k).1| ≤ ((k : ℝ) * per) ^ 2 / 2 ∧ |(stepRef s k).2.1| ≤ (k : ℝ) * per ∧
      |(stepRef s k).2.2| ≤ 1 := by
  have hp : (0 : ℝ) ≤ (k : ℝ) * per := by have := per_pos; positivity
  unfold stepRef
  split_ifs with h
  · have h0 : 0 ≤ (k : ℝ) * per - s := by linarith
    have h1 : (k : ℝ) * per - s ≤ (k : ℝ) * per := by linarith
    simp only [abs_of_nonneg h0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k : ℝ) * per - s) ^ 2 / 2),
      abs_one, le_refl, and_true]
    exact ⟨by nlinarith, h1⟩
  · simp [hp]; positivity

theorem bangRef_bound (s T1 : ℝ) (hs : 0 ≤ s) (hT : 0 ≤ T1) (k : ℕ) :
    |(bangRef s T1 k).1| ≤ 4 * (((k : ℝ) * per) ^ 2 / 2) ∧ |(bangRef s T1 k).2.1| ≤ 4 * ((k : ℝ) * per) ∧
      |(bangRef s T1 k).2.2| ≤ 4 := by
  obtain ⟨a1, a2, a3⟩ := stepRef_bound s hs k
  obtain ⟨b1, b2, b3⟩ := stepRef_bound (s + T1) (by linarith) k
  obtain ⟨c1, c2, c3⟩ := stepRef_bound (s + T1 + 2 / 5) (by linarith) k
  obtain ⟨d1, d2, d3⟩ := stepRef_bound (s + 2 * T1 + 2 / 5) (by linarith) k
  simp only [bangRef, Prod.fst_add, Prod.fst_sub, Prod.snd_add, Prod.snd_sub]
  simp only [abs_le] at *
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

theorem integrable_pulse_mul (a T1 : ℝ) (k : ℕ)
    (f : ℝ × ℝ × ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ u, 0 ≤ u → |f (bangRef (a + u) T1 k)| ≤ C) :
    Integrable (fun u => pulse u * f (bangRef (a + u) T1 k)) (volume.restrict (Ioc 0 (2 / 5))) := by
  refine Integrable.of_bound (C := 5 * C) ?_ ?_
  · exact (continuous_pulse.measurable.mul (hf.comp (measurable_bangRef a T1 k))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pulse_nonneg u)]
    have h1 := hC u hu.1.le
    have h0 : 0 ≤ C := (abs_nonneg _).trans h1
    exact mul_le_mul (pulse_le u) h1 (abs_nonneg _) (by norm_num)

/-- **The S-curve climb bound (milestone M5).** For every start phase `s₀ ≥ 0` and every vertical
leg `L ∈ [0.5, 0.8] m`, the vertical tracking error of the model under the nominal S-curve climb
stays below `0.0875 m` at every tick. -/
theorem scurve_climb (s₀ L : ℝ) (hs : 0 ≤ s₀) (h1 : 1 / 2 ≤ L) (h2 : L ≤ 4 / 5) (k : ℕ) :
    |errResp (scurveRef s₀ L) k 0| ≤ 875 / 10000 := by
  obtain ⟨t1, t2⟩ := T1_mem_of_L L h1 h2
  have hT : 0 ≤ T1ofL L := by linarith
  have hle : (0 : ℝ) ≤ 2 / 5 := by norm_num
  set μ := volume.restrict (Ioc (0 : ℝ) (2 / 5))
  have hint : ∀ j, Integrable (fun u => pulse u * (bangRef (s₀ + u) (T1ofL L) j).1) μ ∧
      Integrable (fun u => pulse u * (bangRef (s₀ + u) (T1ofL L) j).2.1) μ ∧
      Integrable (fun u => pulse u * (bangRef (s₀ + u) (T1ofL L) j).2.2) μ := by
    intro j
    refine ⟨integrable_pulse_mul s₀ _ j (fun x => x.1) measurable_fst _ (fun u hu =>
        (bangRef_bound _ _ (by linarith) hT j).1),
      integrable_pulse_mul s₀ _ j (fun x => x.2.1) (measurable_fst.comp measurable_snd) _
        (fun u hu => (bangRef_bound _ _ (by linarith) hT j).2.1),
      integrable_pulse_mul s₀ _ j (fun x => x.2.2) (measurable_snd.comp measurable_snd) _
        (fun u hu => (bangRef_bound _ _ (by linarith) hT j).2.2)⟩
  have hwi : Integrable pulse μ :=
    (continuous_pulse.integrableOn_Icc (a := 0) (b := 2 / 5)).mono_set Ioc_subset_Icc_self
  have hw1 : ∫ u, pulse u ∂μ = 1 := by
    rw [← intervalIntegral.integral_of_le hle, integral_pulse]
  refine errResp_weighted_bound μ pulse pulse_nonneg hwi hw1 (fun u => bangRef (s₀ + u) (T1ofL L))
    (scurveRef s₀ L) hint (fun j => ?_) ?_ k
  · simp only [scurveRef, intervalIntegral.integral_of_le hle]; rfl
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun u hu j => ?_)
    exact bang_bound_L (s₀ + u) L (by linarith [hu.1]) h1 h2 j

/-! ## Joining: nominal response plus tube -/

theorem forceOf_add (r₁ r₂ : ℕ → ℝ × ℝ × ℝ) (k : ℕ) :
    forceOf (fun j => r₁ j + r₂ j) k = forceOf r₁ k + forceOf r₂ k := by
  ext i
  simp only [forceOf, defect₁, defect₂, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- **Superposition**: the response to a sum of targets is the sum of the responses (target =
nominal + deviation). -/
theorem errResp_add (r₁ r₂ : ℕ → ℝ × ℝ × ℝ) (k : ℕ) :
    errResp (fun j => r₁ j + r₂ j) k = errResp r₁ k + errResp r₂ k := by
  have h := traj_add AvR 0 0 (forceOf r₁) (forceOf r₂) k
  rw [add_zero] at h
  simp only [errResp]
  rw [← h]
  congr 1
  funext j
  exact forceOf_add r₁ r₂ j

/-- **Nominal plus tube.** If the error coordinates follow the linear model driven by the target
`r` and a disturbance `w` (float error `β`, plant remainder, tilt coupling, trim offsets: the C-series
interface, `VERTICAL.md`) with `V (w k) ≤ c`, from zero error, then the vertical error is the
nominal response plus at most `√(γ c) / (1 - λ)`. -/
theorem tube_bound (ξ : ℕ → Fin 8 → ℝ) (r : ℕ → ℝ × ℝ × ℝ) (w : ℕ → Fin 8 → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hξ : ∀ k, ξ (k + 1) = AvR *ᵥ ξ k + forceOf r k + w k) (h0 : ξ 0 = 0)
    (hw : ∀ k, V (w k) ≤ c) (k : ℕ) :
    |ξ k 0| ≤ |errResp r k 0| + Real.sqrt ((gamv : ℝ) * (c / (1 - lamv) ^ 2)) := by
  set η : ℕ → Fin 8 → ℝ := fun k => ξ k - errResp r k
  have hη : ∀ k, η (k + 1) = AvR *ᵥ η k + w k := by
    intro k
    simp only [η, errResp, traj_succ, hξ k, mulVec_sub]
    abel
  have hη0 : V (η 0) = 0 := by simp [η, h0, errResp, V, qf]
  have h := ez_traj_le_const η w hc hη hw k
  rw [hη0, mul_zero, zero_add] at h
  have e : ξ k 0 = errResp r k 0 + η k 0 := by simp [η]
  rw [e]
  have := abs_add_le (errResp r k 0) (η k 0)
  linarith

end Contracts.Track.Vertical
