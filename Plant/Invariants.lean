module

public import Plant.Bounds
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Invariants and a priori estimates

The estimates are proved for *scaled solutions* (`ScaledSol`): curves whose derivative at each time
is `F(c · γ t, u)` for some `c ∈ [0, 1]`. A solution of `F` is one (`c = 1`), and so is a solution
of the radially truncated field `F(radialTrunc R ·, u)` (`Flow.lean`), whose truncation is a
scaling. This is what makes the truncated flow provably agree with the true one: the estimates do
not care about the truncation, so they bound the truncated solution, which therefore never reaches
the truncation radius.

* **Unit sphere.** `‖q‖²` is constant (`qnormSq_scaledSol`): `Σ qᵢ (q ⊗ (0, ω))ᵢ = 0`
  (`q_dot_scaled`).
* **Rotational energy.** `E = ωᵀ J ω` has `Ė = 2 ω · τ` (the gyroscopic term `ω · (ω × J ω)`
  vanishes, `energy_dot_scaled`), so `Ė ≤ E / h + h cτ` with
  `cτ = Σ τmaxᵢ² / Jᵢ` (`ctau`), and `E(t) + cτ h² ≤ (E(0) + cτ h²) e^{t/h}`
  (`energy_scaledSol`).
* **Velocity and position.** `|v̇ᵢ| ≤ g + amax ‖q‖²` and `|ṗᵢ| ≤ |vᵢ|`.

Over one period `[0, h]` from `x` with `‖x‖ ≤ r` these give the box `box r`
(`norm_le_box_of_scaledSol`).
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-! ## Algebraic identities of the field -/

/-- The quaternion kinematics is orthogonal to `q`, for every scaling of the state. -/
theorem q_dot_scaled (y : X) (c : ℝ) (u : Fin 4 → ℝ) :
    y 6 * vf (c • y) u 6 + y 7 * vf (c • y) u 7 + y 8 * vf (c • y) u 8 +
      y 9 * vf (c • y) u 9 = 0 := by
  simp only [vf_6, vf_7, vf_8, vf_9, Pi.smul_apply, smul_eq_mul]; ring

/-- The gyroscopic term does no work, for every scaling of the state. -/
theorem energy_dot_scaled (y : X) (c : ℝ) (u : Fin 4 → ℝ) :
    Jx * y 10 * vf (c • y) u 10 + Jy * y 11 * vf (c • y) u 11 + Jz * y 12 * vf (c • y) u 12 =
      y 10 * torqueX u + y 11 * torqueY u + y 12 * torqueZ u := by
  simp only [vf_10, vf_11, vf_12, Pi.smul_apply, smul_eq_mul]
  field_simp [Jx_pos.ne', Jy_pos.ne', Jz_pos.ne']
  ring

/-- `‖q‖²` of a scaled state. -/
theorem qnormSq_smul (c : ℝ) (y : X) : qnormSq (c • y) = c ^ 2 * qnormSq y := by
  simp only [qnormSq, Pi.smul_apply, smul_eq_mul]; ring

/-! ## Derivatives along a curve -/

theorem hasDerivAt_qnormSq {γ : ℝ → X} {γ' : X} {t : ℝ} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => qnormSq (γ s))
      (2 * (γ t 6 * γ' 6 + γ t 7 * γ' 7 + γ t 8 * γ' 8 + γ t 9 * γ' 9)) t := by
  have d := fun i => hasDerivAt_pi.1 hγ i
  have := ((((d 6).mul (d 6)).add ((d 7).mul (d 7))).add ((d 8).mul (d 8))).add ((d 9).mul (d 9))
  convert this using 1
  · funext s; simp only [qnormSq, Pi.add_apply, Pi.mul_apply]; ring
  · ring

theorem hasDerivAt_energy {γ : ℝ → X} {γ' : X} {t : ℝ} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => energy (γ s))
      (2 * (Jx * γ t 10 * γ' 10 + Jy * γ t 11 * γ' 11 + Jz * γ t 12 * γ' 12)) t := by
  have d := fun i => hasDerivAt_pi.1 hγ i
  have := ((((d 10).mul (d 10)).const_mul Jx).add (((d 11).mul (d 11)).const_mul Jy)).add
    (((d 12).mul (d 12)).const_mul Jz)
  convert this using 1
  · funext s; simp only [energy, Pi.add_apply, Pi.mul_apply]; ring
  · ring

/-! ## Scaled solutions -/

/-- `γ` solves `γ' = F(c γ, u)` on `[0, T]`, with a scaling `c ∈ [0, 1]` that may depend on the
time. -/
def ScaledSol (u : Fin 4 → ℝ) (T : ℝ) (γ : ℝ → X) : Prop :=
  ∀ t ∈ Icc 0 T, ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ HasDerivAt γ (vf (c • γ t) u) t

/-- A solution of `F` is a scaled solution. -/
theorem scaledSol_of_hasDerivAt {u : Fin 4 → ℝ} {T : ℝ} {γ : ℝ → X}
    (h : ∀ t ∈ Icc 0 T, HasDerivAt γ (vf (γ t) u) t) : ScaledSol u T γ :=
  fun t ht => ⟨1, zero_le_one, le_rfl, by simpa using h t ht⟩

/-- A real function with derivative bounded by `C` on `[0, T]` moves by at most `C t`. -/
theorem abs_sub_le_of_deriv {f g : ℝ → ℝ} {T C : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t) (hb : ∀ t ∈ Icc 0 T, |g t| ≤ C) :
    ∀ t ∈ Icc 0 T, |f t - f 0| ≤ C * t := by
  intro t ht
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f) (f' := g) (C := C)
    (fun s hs => (hd s hs).hasDerivWithinAt) (fun s hs => hb s (Ico_subset_Icc_self hs)) t ht
  simpa [Real.norm_eq_abs] using this

section scaled
variable {u : Fin 4 → ℝ} {T : ℝ} {γ : ℝ → X}

/-- **`‖q‖²` is invariant** along every scaled solution, in particular along every solution. -/
theorem qnormSq_scaledSol (hγ : ScaledSol u T γ) :
    ∀ t ∈ Icc 0 T, qnormSq (γ t) = qnormSq (γ 0) := by
  intro t ht
  have := abs_sub_le_of_deriv (f := fun s => qnormSq (γ s)) (g := fun _ => 0) (C := 0)
    (fun s hs => by
      obtain ⟨c, -, -, hd⟩ := hγ s hs
      have := hasDerivAt_qnormSq hd
      rwa [q_dot_scaled, mul_zero] at this)
    (fun _ _ => by simp) t ht
  simpa [sub_eq_zero] using this

/-- `cτ = Σ τmaxᵢ² / Jᵢ`, the torque term of the energy estimate. -/
def ctau : ℝ := (2 * lever * fmax) ^ 2 / Jx + (2 * lever * fmax) ^ 2 / Jy +
  (2 * kmkf * fmax) ^ 2 / Jz

theorem ctau_nonneg : 0 ≤ ctau := by
  have := Jx_pos; have := Jy_pos; have := Jz_pos; unfold ctau; positivity

/-- Weighted AM-GM: `2 a τ ≤ J a² / h + h τ² / J`. -/
theorem two_mul_le_weighted {J a τ : ℝ} (hJ : 0 < J) :
    2 * (a * τ) ≤ J * a ^ 2 / h + h * τ ^ 2 / J := by
  have hh := h_pos
  rw [div_add_div _ _ hh.ne' hJ.ne', le_div_iff₀ (mul_pos hh hJ)]
  nlinarith [sq_nonneg (J * a - h * τ)]

/-- The power of the torques: `2 ω · τ ≤ E / h + h cτ`. -/
theorem two_dot_torque_le (y : X) (u : Fin 4 → ℝ) :
    2 * (y 10 * torqueX u + y 11 * torqueY u + y 12 * torqueZ u) ≤ energy y / h + h * ctau := by
  have e1 := two_mul_le_weighted (a := y 10) (τ := torqueX u) Jx_pos
  have e2 := two_mul_le_weighted (a := y 11) (τ := torqueY u) Jy_pos
  have e3 := two_mul_le_weighted (a := y 12) (τ := torqueZ u) Jz_pos
  have sq_le : ∀ {a b : ℝ}, |a| ≤ b → a ^ 2 ≤ b ^ 2 := fun hab =>
    sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
  have t1 : h * torqueX u ^ 2 / Jx ≤ h * (2 * lever * fmax) ^ 2 / Jx := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sq_le (abs_torqueX_le u)) h_pos.le)
      Jx_pos.le
  have t2 : h * torqueY u ^ 2 / Jy ≤ h * (2 * lever * fmax) ^ 2 / Jy := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sq_le (abs_torqueY_le u)) h_pos.le)
      Jy_pos.le
  have t3 : h * torqueZ u ^ 2 / Jz ≤ h * (2 * kmkf * fmax) ^ 2 / Jz := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sq_le (abs_torqueZ_le u)) h_pos.le)
      Jz_pos.le
  have hE : energy y / h = Jx * y 10 ^ 2 / h + Jy * y 11 ^ 2 / h + Jz * y 12 ^ 2 / h := by
    simp only [energy]; ring
  have hC : h * ctau = h * (2 * lever * fmax) ^ 2 / Jx + h * (2 * lever * fmax) ^ 2 / Jy +
      h * (2 * kmkf * fmax) ^ 2 / Jz := by simp only [ctau]; ring
  rw [hE, hC]; linarith

/-- **Energy estimate**: `E(t) + cτ h² ≤ (E(0) + cτ h²) e^{t/h}` along every scaled solution. -/
theorem energy_scaledSol (hγ : ScaledSol u T γ) :
    ∀ t ∈ Icc 0 T, energy (γ t) + ctau * h ^ 2 ≤ (energy (γ 0) + ctau * h ^ 2) * Real.exp (t / h) := by
  have hh := h_pos
  set φ : ℝ → ℝ := fun s => (energy (γ s) + ctau * h ^ 2) * Real.exp (-s / h)
  have hderiv : ∀ s ∈ Icc 0 T, ∃ e, HasDerivAt (fun s => energy (γ s)) e s ∧
      e ≤ energy (γ s) / h + h * ctau := by
    intro s hs
    obtain ⟨c, -, -, hd⟩ := hγ s hs
    refine ⟨_, hasDerivAt_energy hd, ?_⟩
    rw [show Jx * γ s 10 * vf (c • γ s) u 10 + Jy * γ s 11 * vf (c • γ s) u 11 +
        Jz * γ s 12 * vf (c • γ s) u 12 = _ from energy_dot_scaled (γ s) c u]
    exact two_dot_torque_le (γ s) u
  choose! e he hle using hderiv
  have hexp : ∀ s, HasDerivAt (fun s : ℝ => Real.exp (-s / h)) (Real.exp (-s / h) * (-1 / h)) s :=
    fun s => by
      have := ((hasDerivAt_id s).neg.div_const h).exp
      simpa [neg_div] using this
  have hφ : ∀ s ∈ Icc 0 T, HasDerivAt φ ((e s) * Real.exp (-s / h) +
      (energy (γ s) + ctau * h ^ 2) * (Real.exp (-s / h) * (-1 / h))) s :=
    fun s hs => ((he s hs).add_const _).mul (hexp s)
  have hanti : AntitoneOn φ (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun s => (e s) * Real.exp (-s / h) +
        (energy (γ s) + ctau * h ^ 2) * (Real.exp (-s / h) * (-1 / h))) ?_ ?_ ?_
    · exact fun s hs => (hφ s hs).continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Icc] at hs
      exact (hφ s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
    · intro s hs; rw [interior_Icc] at hs
      have hs' := Ioo_subset_Icc_self hs
      have h1 := hle s hs'
      have hpos := Real.exp_pos (-s / h)
      have : e s - (energy (γ s) + ctau * h ^ 2) / h ≤ 0 := by
        have : (energy (γ s) + ctau * h ^ 2) / h = energy (γ s) / h + h * ctau := by
          field_simp
        linarith
      have := mul_nonpos_of_nonpos_of_nonneg this hpos.le
      calc _ = (e s - (energy (γ s) + ctau * h ^ 2) / h) * Real.exp (-s / h) := by ring
        _ ≤ 0 := this
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have := hanti h0 ht ht.1
  simp only [φ, neg_zero, zero_div, Real.exp_zero, mul_one] at this
  have hex : Real.exp (-t / h) * Real.exp (t / h) = 1 := by
    rw [← Real.exp_add]; simp [neg_div]
  calc energy (γ t) + ctau * h ^ 2
      = (energy (γ t) + ctau * h ^ 2) * Real.exp (-t / h) * Real.exp (t / h) := by
        rw [mul_assoc, hex, mul_one]
    _ ≤ (energy (γ 0) + ctau * h ^ 2) * Real.exp (t / h) := by
        gcongr

/-- **Velocity estimate**: each velocity coordinate moves by at most `(g + amax ‖q‖²) t`. -/
theorem v_scaledSol (hγ : ScaledSol u T γ) (j : Fin 13) (hj : j = 3 ∨ j = 4 ∨ j = 5) :
    ∀ t ∈ Icc 0 T, |γ t j - γ 0 j| ≤ (grav + amax * qnormSq (γ 0)) * t := by
  have hQ := qnormSq_scaledSol hγ
  choose! c hc0 hc1 hd using hγ
  refine abs_sub_le_of_deriv (g := fun s => vf (c s • γ s) u j)
    (fun s hs => hasDerivAt_pi.1 (hd s hs) j) fun s hs => ?_
  obtain ⟨v3, v4, v5⟩ := abs_vf_v (c s • γ s) u
  have hq : qnormSq (c s • γ s) ≤ qnormSq (γ 0) := by
    rw [qnormSq_smul, hQ s hs]
    have : c s ^ 2 ≤ 1 := by nlinarith [hc0 s hs, hc1 s hs]
    nlinarith [qnormSq_nonneg (γ 0)]
  have hA := amax_pos
  have hg := grav_pos
  rcases hj with rfl | rfl | rfl
  · exact v3.trans (by nlinarith)
  · exact v4.trans (by nlinarith)
  · exact v5.trans (by nlinarith)

/-- **Position estimate**: if the velocity coordinate `j + 3` stays below `V`, the position
coordinate `j` moves by at most `V t`. -/
theorem p_scaledSol (hγ : ScaledSol u T γ) (j : Fin 13) (hj : j = 0 ∨ j = 1 ∨ j = 2) {V : ℝ}
    (hV : ∀ t ∈ Icc 0 T, |γ t (j + 3)| ≤ V) :
    ∀ t ∈ Icc 0 T, |γ t j - γ 0 j| ≤ V * t := by
  choose! c hc0 hc1 hd using hγ
  refine abs_sub_le_of_deriv (g := fun s => vf (c s • γ s) u j)
    (fun s hs => hasDerivAt_pi.1 (hd s hs) j) fun s hs => ?_
  have key : ∀ a : ℝ, |c s * a| ≤ |a| := fun a => by
    rw [abs_mul, abs_of_nonneg (hc0 s hs)]
    exact mul_le_of_le_one_left (abs_nonneg _) (hc1 s hs)
  rcases hj with rfl | rfl | rfl
  · rw [vf_0]; exact (key _).trans (hV s hs)
  · rw [vf_1]; exact (key _).trans (hV s hs)
  · rw [vf_2]; exact (key _).trans (hV s hs)

end scaled

/-! ## The box of one period -/

/-- Velocity radius after one period from the ball of radius `r`. -/
def vB (r : ℝ) : ℝ := r + h * (grav + amax * (4 * r ^ 2))

/-- Position radius after one period from the ball of radius `r`. -/
def pB (r : ℝ) : ℝ := r + h * vB r

/-- Quaternion radius from the ball of radius `r`: `‖q‖ ≤ 2 r`. -/
def qB (r : ℝ) : ℝ := 2 * r

/-- Rate radius after one period from the ball of radius `r`, by the energy estimate. -/
def wB (r : ℝ) : ℝ := Real.sqrt (((Jx + Jy + Jz) * r ^ 2 + ctau * h ^ 2) * Real.exp 1 / Jx)

/-- **The box of one period**: every solution (and every truncated solution) from `‖x‖ ≤ r` stays
in the ball of radius `box r` over `[0, h]`. -/
def box (r : ℝ) : ℝ := max (max (pB r) (vB r)) (max (qB r) (wB r))

theorem vB_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ vB r := by
  have := h_pos; have := grav_pos; have := amax_pos; unfold vB; positivity

theorem box_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ box r :=
  le_max_of_le_left (le_max_of_le_right (vB_nonneg hr))

theorem energy_le_of_norm_le {x : X} {r : ℝ} (hx : ‖x‖ ≤ r) :
    energy x ≤ (Jx + Jy + Jz) * r ^ 2 := by
  obtain ⟨a, b, c⟩ := WBd_of_norm_le hx
  have sq_le : ∀ {a b : ℝ}, |a| ≤ b → a ^ 2 ≤ b ^ 2 := fun hab =>
    sq_le_sq' (abs_le.mp hab).1 (abs_le.mp hab).2
  have := sq_le a; have := sq_le b; have := sq_le c
  have := Jx_pos; have := Jy_pos; have := Jz_pos
  unfold energy; nlinarith

/-- **A priori bound over one period.** A scaled solution on `[0, h]` from `‖γ 0‖ ≤ r` stays in
the ball of radius `box r`. -/
theorem norm_le_box_of_scaledSol {u : Fin 4 → ℝ} {γ : ℝ → X} (hγ : ScaledSol u h γ) {r : ℝ}
    (hr : ‖γ 0‖ ≤ r) : ∀ t ∈ Icc 0 h, ‖γ t‖ ≤ box r := by
  intro t ht
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  have hh := h_pos
  have hQ0 := qnormSq_le_of_norm_le hr
  have hA := amax_pos
  have hg := grav_pos
  -- velocity
  have hv : ∀ s ∈ Icc 0 h, ∀ j : Fin 13, (j = 3 ∨ j = 4 ∨ j = 5) → |γ s j| ≤ vB r := by
    intro s hs j hj
    have h1 := v_scaledSol hγ j hj s hs
    have h2 := (abs_le_norm (γ 0) j).trans hr
    have h3 : (grav + amax * qnormSq (γ 0)) * s ≤ h * (grav + amax * (4 * r ^ 2)) := by
      have : grav + amax * qnormSq (γ 0) ≤ grav + amax * (4 * r ^ 2) := by nlinarith
      calc _ ≤ (grav + amax * (4 * r ^ 2)) * s := mul_le_mul_of_nonneg_right this hs.1
        _ ≤ (grav + amax * (4 * r ^ 2)) * h := mul_le_mul_of_nonneg_left hs.2 (by positivity)
        _ = _ := by ring
    have := abs_sub_abs_le_abs_sub (γ s j) (γ 0 j)
    unfold vB; linarith
  -- position
  have hp : ∀ j : Fin 13, (j = 0 ∨ j = 1 ∨ j = 2) → |γ t j| ≤ pB r := by
    intro j hj
    have hV : ∀ s ∈ Icc 0 h, |γ s (j + 3)| ≤ vB r := fun s hs =>
      hv s hs (j + 3) (by rcases hj with rfl | rfl | rfl <;> decide)
    have h1 := p_scaledSol hγ j hj hV t ht
    have h2 := (abs_le_norm (γ 0) j).trans hr
    have h3 : vB r * t ≤ h * vB r := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right ht.2 (vB_nonneg hr0)
    have := abs_sub_abs_le_abs_sub (γ t j) (γ 0 j)
    unfold pB; linarith
  -- quaternion
  have hq : ∀ j : Fin 13, (j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9) → |γ t j| ≤ qB r := by
    intro j hj
    have hQ := qnormSq_scaledSol hγ t ht
    have : γ t j ^ 2 ≤ (2 * r) ^ 2 := by
      have : γ t j ^ 2 ≤ qnormSq (γ t) := by
        unfold qnormSq
        rcases hj with rfl | rfl | rfl | rfl <;> nlinarith [sq_nonneg (γ t 6), sq_nonneg (γ t 7),
          sq_nonneg (γ t 8), sq_nonneg (γ t 9)]
      linarith
    rw [qB]; exact abs_le.mpr (abs_le_of_sq_le_sq' this (by linarith))
  -- rates
  have hw : ∀ j : Fin 13, (j = 10 ∨ j = 11 ∨ j = 12) → |γ t j| ≤ wB r := by
    intro j hj
    have hE := energy_scaledSol hγ t ht
    have hE0 := energy_le_of_norm_le hr
    have hexp : Real.exp (t / h) ≤ Real.exp 1 := by
      rw [Real.exp_le_exp, div_le_one hh]; exact ht.2
    have hc := ctau_nonneg
    have hEt : energy (γ t) ≤ ((Jx + Jy + Jz) * r ^ 2 + ctau * h ^ 2) * Real.exp 1 := by
      have : (energy (γ 0) + ctau * h ^ 2) * Real.exp (t / h) ≤
          ((Jx + Jy + Jz) * r ^ 2 + ctau * h ^ 2) * Real.exp 1 := by
        have := energy_nonneg (γ 0)
        exact mul_le_mul (by linarith) hexp (Real.exp_pos _).le
          (add_nonneg (mul_nonneg (by norm_num [Jx, Jy, Jz]) (sq_nonneg r))
            (mul_nonneg hc (sq_nonneg h)))
      nlinarith
    have hJ : Jx * γ t j ^ 2 ≤ energy (γ t) := by
      have := Jx_pos; have := Jy_pos; have := Jz_pos; have := Jx_le_Jz
      have hy := Jy_eq_Jx
      unfold energy
      rcases hj with rfl | rfl | rfl
      · nlinarith [sq_nonneg (γ t 11), sq_nonneg (γ t 12)]
      · rw [hy]; nlinarith [sq_nonneg (γ t 10), sq_nonneg (γ t 12)]
      · nlinarith [sq_nonneg (γ t 10), sq_nonneg (γ t 11), sq_nonneg (γ t 12)]
    apply Real.abs_le_sqrt
    rw [le_div_iff₀ Jx_pos]; linarith
  have hb := box_nonneg hr0
  refine norm_le_of_abs_le hb fun j => ?_
  have p1 : pB r ≤ box r := le_max_of_le_left (le_max_left _ _)
  have v1 : vB r ≤ box r := le_max_of_le_left (le_max_right _ _)
  have q1 : qB r ≤ box r := le_max_of_le_right (le_max_left _ _)
  have w1 : wB r ≤ box r := le_max_of_le_right (le_max_right _ _)
  fin_cases j
  · exact (hp 0 (by simp)).trans p1
  · exact (hp 1 (by simp)).trans p1
  · exact (hp 2 (by simp)).trans p1
  · exact (hv t ht 3 (by simp)).trans v1
  · exact (hv t ht 4 (by simp)).trans v1
  · exact (hv t ht 5 (by simp)).trans v1
  · exact (hq 6 (by simp)).trans q1
  · exact (hq 7 (by simp)).trans q1
  · exact (hq 8 (by simp)).trans q1
  · exact (hq 9 (by simp)).trans q1
  · exact (hw 10 (by simp)).trans w1
  · exact (hw 11 (by simp)).trans w1
  · exact (hw 12 (by simp)).trans w1

end

end Plant
