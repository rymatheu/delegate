import Contracts.Track.AttitudeCert
import Contracts.Track.VerticalCert
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Milestone (2): the composite 3D Lyapunov/ISS inequality (REACH.md §2)

The error state of the closed loop in the linear regime has three blocks: the vertical channel
(`Vertical.AvR`, 8 states, VERTICAL.md) and the two horizontal NED axes, each with its attitude
inner loop (`AttJ.AjR σ`, 14 states, `AttitudeJoint.lean`, switched by the shaping's
`sqrt_controller_accel` flag `σ`). The composite Lyapunov function is

`Vc ξ = V_j(ξ_N) + V_j(ξ_E) + μ_v V_v(ξ_D)`,  `μ_v = 38.57`

(`μ_v ≥ γ_v/γ_e`, so that one constant `γ_e` bounds the squared 3D position error by `Vc`).

The joins (the tilt coupling into the vertical channel, the heading rotation of the horizontal axes,
the plant remainder, the `float` rounding of the C-series lemmas) enter as the per-tick disturbance
`w`; their size is the hypothesis `Vc w ≤ κ Vc ξ + c₀` on the region `D = {Vc ≤ ν}` (a coupling
gain `κ` and a floor `c₀`). Results:

* `Vc_step`: `Vc (A ξ + w) ≤ λ Vc ξ + Vc w / (1 - λ)`, `λ = 0.9997`, for any modes of the two axes;
* `Vc_traj`: on `D`, with `ρ = λ + κ/(1 - λ) < 1` and `ρ ν + c₀/(1 - λ) ≤ ν`, `D` is forward
  invariant and `Vc (ξ t) ≤ ρᵗ Vc (ξ 0) + c₀ / ((1 - λ)(1 - ρ))`;
* `pos_sq_le`: `‖(e_N, e_E, e_D)‖² ≤ γ_e Vc`;
* **`hover_pes_model`** (practical exponential stability of hover at a fixed target `w`):
  from a pure position offset (`Vc ξ₀ ≤ 10¹⁵ ‖p₀ − w‖²`, `pureOffset`),
  `‖p_t − w‖ ≤ c (√ρ)ᵗ ‖p₀ − w‖ + b` with `c = √(10¹⁵ γ_e) ≤ 37.93`,
  `b = √(γ_e c₀ / ((1 - λ)(1 - ρ)))`;
* **`track_iss_model`** (tracking a moving reference): with per-coordinate disturbance bounds
  `|wᵢ| ≤ ε_t ≤ ε̄`, `‖p_t − p^T_t‖ ≤ √γ_e (√ρ)ᵗ √(Vc ξ₀) + γ ε̄`,
  `γ = √(γ_e Σ|Pc|/((1 - λ)(1 - λ)))` (κ = 0).
-/

namespace Contracts.Track.Reach

open Matrix Finset

/-- The composite error state: vertical block, north axis, east axis. -/
structure CS where
  v : Fin 8 → ℝ
  n : Fin 14 → ℝ
  e : Fin 14 → ℝ

/-- The weight of the vertical block. -/
noncomputable def μv : ℝ := 3857 / 100

/-- **The composite Lyapunov function.** -/
noncomputable def Vc (ξ : CS) : ℝ := AttJ.V ξ.n + AttJ.V ξ.e + μv * Vertical.V ξ.v

/-- The composite contraction factor (the joint axis' `λ`; the vertical one is `0.998`). -/
noncomputable def lamC : ℝ := 9997 / 10000

theorem μv_pos : 0 < μv := by norm_num [μv]
theorem lamC_pos : 0 < lamC := by norm_num [lamC]
theorem lamC_lt_one : lamC < 1 := by norm_num [lamC]
theorem lamC_eq : lamC = (AttJ.lamj : ℝ) := by norm_num [lamC, AttJ.lamj]

theorem Vc_nonneg (ξ : CS) : 0 ≤ Vc ξ := by
  unfold Vc
  have := AttJ.V_nonneg ξ.n; have := AttJ.V_nonneg ξ.e; have := Vertical.V_nonneg ξ.v
  have := μv_pos; positivity

/-- One tick of the composite linear model, modes `σn`, `σe` of the two axes, disturbance `w`. -/
noncomputable def cstep (σn σe : Fin 2) (ξ w : CS) : CS :=
  ⟨Vertical.AvR *ᵥ ξ.v + w.v, AttJ.AjR σn *ᵥ ξ.n + w.n, AttJ.AjR σe *ᵥ ξ.e + w.e⟩

/-- **The composite ISS step**: `Vc (A ξ + w) ≤ λ Vc ξ + Vc w / (1 - λ)` for all modes. -/
theorem Vc_step (σn σe : Fin 2) (ξ w : CS) :
    Vc (cstep σn σe ξ w) ≤ lamC * Vc ξ + Vc w / (1 - lamC) := by
  have hn := AttJ.V_iss_sw σn ξ.n w.n
  have he := AttJ.V_iss_sw σe ξ.e w.e
  have hv := Vertical.V_iss ξ.v w.v
  rw [← lamC_eq] at hn he
  have hv0 := Vertical.V_nonneg ξ.v
  have hw0 := Vertical.V_nonneg w.v
  have hl : (Vertical.lamv : ℝ) ≤ lamC := by norm_num [Vertical.lamv, lamC]
  have hl1 : (0 : ℝ) < 1 - lamC := by linarith [lamC_lt_one]
  have hv' : Vertical.V (Vertical.AvR *ᵥ ξ.v + w.v) ≤ lamC * Vertical.V ξ.v +
      Vertical.V w.v / (1 - lamC) := by
    have h1 : (Vertical.lamv : ℝ) * Vertical.V ξ.v ≤ lamC * Vertical.V ξ.v :=
      mul_le_mul_of_nonneg_right hl hv0
    have h2 : Vertical.V w.v / (1 - Vertical.lamv) ≤ Vertical.V w.v / (1 - lamC) :=
      div_le_div_of_nonneg_left hw0 hl1 (by linarith)
    linarith
  have hμ := μv_pos
  simp only [Vc, cstep]
  have := mul_le_mul_of_nonneg_left hv' hμ.le
  have e : (AttJ.V w.n + AttJ.V w.e + μv * Vertical.V w.v) / (1 - lamC) =
      AttJ.V w.n / (1 - lamC) + AttJ.V w.e / (1 - lamC) + μv * (Vertical.V w.v / (1 - lamC)) := by
    ring
  rw [e]; nlinarith

/-- **The step through the joins**: if the disturbance satisfies `Vc w ≤ κ Vc ξ + c₀`, then
`Vc (A ξ + w) ≤ (λ + κ/(1 - λ)) Vc ξ + c₀/(1 - λ)`. -/
theorem Vc_step_join (σn σe : Fin 2) (ξ w : CS) {κ c₀ : ℝ} (hw : Vc w ≤ κ * Vc ξ + c₀) :
    Vc (cstep σn σe ξ w) ≤ (lamC + κ / (1 - lamC)) * Vc ξ + c₀ / (1 - lamC) := by
  have h := Vc_step σn σe ξ w
  have hl1 : (0 : ℝ) < 1 - lamC := by linarith [lamC_lt_one]
  have : Vc w / (1 - lamC) ≤ (κ * Vc ξ + c₀) / (1 - lamC) := div_le_div_of_nonneg_right hw hl1.le
  have e : (κ * Vc ξ + c₀) / (1 - lamC) = κ / (1 - lamC) * Vc ξ + c₀ / (1 - lamC) := by ring
  nlinarith

/-- **Forward invariance of `D = {Vc ≤ ν}` and the exponential bound.** Along
`ξ (t+1) = A_{σ t} ξ t + w t`, with the join bound required only inside `D`: if
`ρ = λ + κ/(1 - λ) < 1` and `ρ ν + c₀/(1 - λ) ≤ ν`, a start in `D` stays in `D` and
`Vc (ξ t) ≤ ρᵗ Vc (ξ 0) + c₀/((1 - λ)(1 - ρ))`. -/
theorem Vc_traj (σn σe : ℕ → Fin 2) (ξ w : ℕ → CS) {κ c₀ ν : ℝ} (hκ : 0 ≤ κ) (hc₀ : 0 ≤ c₀)
    (hρ : lamC + κ / (1 - lamC) < 1) (hν : (lamC + κ / (1 - lamC)) * ν + c₀ / (1 - lamC) ≤ ν)
    (hstep : ∀ t, ξ (t + 1) = cstep (σn t) (σe t) (ξ t) (w t))
    (hw : ∀ t, Vc (ξ t) ≤ ν → Vc (w t) ≤ κ * Vc (ξ t) + c₀) (h0 : Vc (ξ 0) ≤ ν) (t : ℕ) :
    Vc (ξ t) ≤ ν ∧
      Vc (ξ t) ≤ (lamC + κ / (1 - lamC)) ^ t * Vc (ξ 0) +
        c₀ / ((1 - lamC) * (1 - (lamC + κ / (1 - lamC)))) := by
  set ρ := lamC + κ / (1 - lamC) with hρdef
  have hl1 : (0 : ℝ) < 1 - lamC := by linarith [lamC_lt_one]
  have hρ0 : 0 ≤ ρ := by have := lamC_pos; positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  set B := c₀ / ((1 - lamC) * (1 - ρ)) with hB
  have hBeq : ρ * B + c₀ / (1 - lamC) = B := by
    rw [hB]; field_simp; ring
  induction t with
  | zero =>
    refine ⟨h0, ?_⟩
    have : 0 ≤ B := by positivity
    simp; linarith
  | succ t ih =>
    obtain ⟨hD, hb⟩ := ih
    have hs := Vc_step_join (σn t) (σe t) (ξ t) (w t) (hw t hD)
    rw [← hstep t] at hs
    refine ⟨?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left hD hρ0
      linarith
    · have := mul_le_mul_of_nonneg_left hb hρ0
      rw [pow_succ]
      nlinarith

/-- `√(a + b) ≤ √a + √b`. -/
theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sqrt_nonneg a
  have h4 := Real.sqrt_nonneg b
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-! ## The position error -/

/-- The 3D position error read off the composite state (north, east, down). -/
noncomputable def posErr (ξ : CS) : EuclideanSpace ℝ (Fin 3) := !₂[ξ.n 0, ξ.e 0, ξ.v 0]

/-- The bound constant: `γ_e = 1438459·10⁻¹⁸`. -/
noncomputable def γe : ℝ := (AttJ.g_e : ℝ)

theorem γe_pos : 0 < γe := by norm_num [γe, AttJ.g_e]

/-- `‖posErr ξ‖² ≤ γ_e Vc ξ`. -/
theorem pos_sq_le (ξ : CS) : ‖posErr ξ‖ ^ 2 ≤ γe * Vc ξ := by
  have hn := AttJ.sq_e_le ξ.n
  have he := AttJ.sq_e_le ξ.e
  have hv := Vertical.sq_ez_le ξ.v
  have hg : (Vertical.gamv : ℝ) ≤ μv * γe := by norm_num [Vertical.gamv, μv, γe, AttJ.g_e]
  have hv' : ξ.v 0 ^ 2 ≤ γe * (μv * Vertical.V ξ.v) := by
    have := Vertical.V_nonneg ξ.v
    nlinarith
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [γe] at hv'
  simp [posErr, Fin.sum_univ_succ, Vc, γe]
  nlinarith

theorem posErr_le (ξ : CS) : ‖posErr ξ‖ ≤ Real.sqrt (γe * Vc ξ) :=
  Real.le_sqrt_of_sq_le (pos_sq_le ξ)

/-- A pure position offset: every controller and attitude state zero, the three position errors
given (the vehicle at rest and level, the controller relaxed). -/
noncomputable def pureOffset (p : EuclideanSpace ℝ (Fin 3)) : CS :=
  ⟨Pi.single 0 (p 2), Pi.single 0 (p 0), Pi.single 0 (p 1)⟩

theorem Vertical_V_single (e : ℝ) :
    Vertical.V (Pi.single 0 e) = 37977353399 * e ^ 2 := by
  simp [Vertical.V, Vertical.PvR, Vertical.castM, Vertical.Pv, Vertical.qf, dotProduct, mulVec,
    Pi.single_apply]
  ring

/-- `Vc (pureOffset p) ≤ 10¹⁵ ‖p‖²`. -/
theorem Vc_pureOffset (p : EuclideanSpace ℝ (Fin 3)) : Vc (pureOffset p) ≤ 10 ^ 15 * ‖p‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [Vc, pureOffset, AttJ.V_single, Vertical_V_single, Fin.sum_univ_succ,
    Real.norm_eq_abs, sq_abs]
  simp [μv]
  nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2)]

theorem posErr_pureOffset (p : EuclideanSpace ℝ (Fin 3)) : posErr (pureOffset p) = p := by
  ext i; fin_cases i <;> simp [posErr, pureOffset]

/-- **Hover is a practically exponentially stable equilibrium of the composite model**
(the model form of `hover_practically_exponentially_stable`). The target is fixed at `w`, the
error state `ξ` starts as a pure position offset `p₀ − w` inside `D = {Vc ≤ ν}`, and each tick is
the composite linear step with a join disturbance bounded on `D` by `κ Vc + c₀`. Then `D` is
forward invariant, `Vc (ξ (t+1)) ≤ ρ Vc (ξ t) + c₀/(1 - λ)` (`Vc_step_join`), and

`‖p_t − w‖ ≤ c (√ρ)ᵗ ‖p₀ − w‖ + b`, `c = √(10¹⁵ γ_e) ≤ 37.93`, `b = √(γ_e c₀/((1 - λ)(1 - ρ)))`,

`ρ = λ + κ/(1 - λ)`, `λ = 0.9997`. -/
theorem hover_pes_model (σn σe : ℕ → Fin 2) (ξ w : ℕ → CS) (p₀ wp : EuclideanSpace ℝ (Fin 3))
    {κ c₀ ν : ℝ} (hκ : 0 ≤ κ) (hc₀ : 0 ≤ c₀)
    (hρ : lamC + κ / (1 - lamC) < 1) (hν : (lamC + κ / (1 - lamC)) * ν + c₀ / (1 - lamC) ≤ ν)
    (hstep : ∀ t, ξ (t + 1) = cstep (σn t) (σe t) (ξ t) (w t))
    (hw : ∀ t, Vc (ξ t) ≤ ν → Vc (w t) ≤ κ * Vc (ξ t) + c₀)
    (h0 : ξ 0 = pureOffset (p₀ - wp)) (hD0 : 10 ^ 15 * ‖p₀ - wp‖ ^ 2 ≤ ν) (t : ℕ) :
    Vc (ξ t) ≤ ν ∧
      ‖posErr (ξ t)‖ ≤ Real.sqrt (10 ^ 15 * γe) * Real.sqrt (lamC + κ / (1 - lamC)) ^ t * ‖p₀ - wp‖ +
        Real.sqrt (γe * (c₀ / ((1 - lamC) * (1 - (lamC + κ / (1 - lamC)))))) := by
  set ρ := lamC + κ / (1 - lamC) with hρdef
  have hV0 : Vc (ξ 0) ≤ 10 ^ 15 * ‖p₀ - wp‖ ^ 2 := h0 ▸ Vc_pureOffset _
  obtain ⟨hD, hb⟩ := Vc_traj σn σe ξ w hκ hc₀ hρ hν hstep hw (hV0.trans hD0) t
  refine ⟨hD, ?_⟩
  have hl1 : (0 : ℝ) < 1 - lamC := by linarith [lamC_lt_one]
  have hρ0 : 0 ≤ ρ := by have := lamC_pos; positivity
  have hB : 0 ≤ c₀ / ((1 - lamC) * (1 - ρ)) := by
    have : 0 < 1 - ρ := by linarith
    positivity
  have hg := γe_pos
  calc ‖posErr (ξ t)‖ ≤ Real.sqrt (γe * Vc (ξ t)) := posErr_le _
    _ ≤ Real.sqrt (γe * (ρ ^ t * (10 ^ 15 * ‖p₀ - wp‖ ^ 2)) +
          γe * (c₀ / ((1 - lamC) * (1 - ρ)))) := by
        apply Real.sqrt_le_sqrt
        have := mul_le_mul_of_nonneg_left hV0 (pow_nonneg hρ0 t)
        nlinarith
    _ ≤ Real.sqrt (γe * (ρ ^ t * (10 ^ 15 * ‖p₀ - wp‖ ^ 2))) +
          Real.sqrt (γe * (c₀ / ((1 - lamC) * (1 - ρ)))) := sqrt_add_le' (by positivity) (by positivity)
    _ = Real.sqrt (10 ^ 15 * γe) * Real.sqrt ρ ^ t * ‖p₀ - wp‖ +
          Real.sqrt (γe * (c₀ / ((1 - lamC) * (1 - ρ)))) := by
        congr 1
        have e : γe * (ρ ^ t * (10 ^ 15 * ‖p₀ - wp‖ ^ 2)) =
            (10 ^ 15 * γe) * (Real.sqrt ρ ^ t) ^ 2 * ‖p₀ - wp‖ ^ 2 := by
          rw [← pow_mul, mul_comm t 2, pow_mul, Real.sq_sqrt hρ0]; ring
        rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The constant `c` of `hover_pes_model`: `√(10¹⁵ γ_e) ≤ 37.93`. -/
theorem c_hover_le : Real.sqrt (10 ^ 15 * γe) ≤ 3793 / 100 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num [γe, AttJ.g_e]

/-! ## The ISS form: tracking a moving reference -/

/-- `Σ |Pc|` of the composite: `2 Σ|Pj| + μ_v Σ|Pv|`. -/
noncomputable def PsumC : ℝ := 2 * (AttJ.PsumJ : ℝ) + μv * (Vertical.Psum : ℝ)

/-- A disturbance bounded by `ε` in every coordinate has `Vc w ≤ PsumC ε²`. -/
theorem Vc_le_of_abs_le (w : CS) {ε : ℝ} (hv : ∀ i, |w.v i| ≤ ε) (hn : ∀ i, |w.n i| ≤ ε)
    (he : ∀ i, |w.e i| ≤ ε) : Vc w ≤ PsumC * ε ^ 2 := by
  have h1 := AttJ.V_le_of_abs_le w.n hn
  have h2 := AttJ.V_le_of_abs_le w.e he
  have h3 := Vertical.V_le_of_abs_le w.v hv
  have := μv_pos
  simp only [Vc, PsumC]
  nlinarith

/-- **ISS tracking (model form)**: the error coordinates are taken against a moving reference
(the navigator's target triple), whose motion enters through the disturbance `w` (the target's
acceleration and its defects, VERTICAL.md §1, HORIZONTAL.md §1), together with the join terms.
If every coordinate of `w t` is at most `ε̄` while in `D`, then `D` is forward invariant and

`‖p_t − p^T_t‖ ≤ √γ_e (√λ)ᵗ √(Vc ξ₀) + γ ε̄`, `γ = √(γ_e PsumC) / (1 - λ)`. -/
theorem track_iss_model (σn σe : ℕ → Fin 2) (ξ w : ℕ → CS) {ε ν : ℝ} (hε : 0 ≤ ε)
    (hν : lamC * ν + PsumC * ε ^ 2 / (1 - lamC) ≤ ν)
    (hstep : ∀ t, ξ (t + 1) = cstep (σn t) (σe t) (ξ t) (w t))
    (hw : ∀ t, Vc (ξ t) ≤ ν →
      (∀ i, |(w t).v i| ≤ ε) ∧ (∀ i, |(w t).n i| ≤ ε) ∧ ∀ i, |(w t).e i| ≤ ε)
    (h0 : Vc (ξ 0) ≤ ν) (t : ℕ) :
    Vc (ξ t) ≤ ν ∧
      ‖posErr (ξ t)‖ ≤ Real.sqrt γe * Real.sqrt lamC ^ t * Real.sqrt (Vc (ξ 0)) +
        Real.sqrt (γe * PsumC) / (1 - lamC) * ε := by
  have hPs : 0 ≤ PsumC := by
    have := μv_pos; simp only [PsumC]; norm_num [AttJ.PsumJ, Vertical.Psum]; positivity
  have hl1 : (0 : ℝ) < 1 - lamC := by linarith [lamC_lt_one]
  have hκ : lamC + 0 / (1 - lamC) = lamC := by simp
  obtain ⟨hD, hb⟩ := Vc_traj σn σe ξ w (κ := 0) (c₀ := PsumC * ε ^ 2) le_rfl (by positivity)
    (by rw [hκ]; exact lamC_lt_one) (by rw [hκ]; linarith) hstep
    (fun t ht => by
      obtain ⟨a, b, c⟩ := hw t ht
      have := Vc_le_of_abs_le (w t) a b c
      simpa using this) h0 t
  rw [hκ] at hb
  refine ⟨hD, ?_⟩
  have hg := γe_pos
  have hl0 := lamC_pos
  have hV0 := Vc_nonneg (ξ 0)
  calc ‖posErr (ξ t)‖ ≤ Real.sqrt (γe * Vc (ξ t)) := posErr_le _
    _ ≤ Real.sqrt (γe * (lamC ^ t * Vc (ξ 0)) + γe * (PsumC * ε ^ 2 / ((1 - lamC) * (1 - lamC)))) := by
        apply Real.sqrt_le_sqrt; nlinarith
    _ ≤ Real.sqrt (γe * (lamC ^ t * Vc (ξ 0))) +
          Real.sqrt (γe * (PsumC * ε ^ 2 / ((1 - lamC) * (1 - lamC)))) := sqrt_add_le' (by positivity) (by positivity)
    _ = Real.sqrt γe * Real.sqrt lamC ^ t * Real.sqrt (Vc (ξ 0)) +
          Real.sqrt (γe * PsumC) / (1 - lamC) * ε := by
        congr 1
        · have hp : Real.sqrt (lamC ^ t) = Real.sqrt lamC ^ t := by
            rw [show lamC ^ t = (Real.sqrt lamC ^ t) ^ 2 by
              rw [← pow_mul, mul_comm t 2, pow_mul, Real.sq_sqrt hl0.le]]
            exact Real.sqrt_sq (by positivity)
          rw [Real.sqrt_mul hg.le, Real.sqrt_mul (by positivity), hp]; ring
        · have e : γe * (PsumC * ε ^ 2 / ((1 - lamC) * (1 - lamC))) =
              (γe * PsumC) * (ε / (1 - lamC)) ^ 2 := by field_simp
          rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]; ring

end Contracts.Track.Reach
