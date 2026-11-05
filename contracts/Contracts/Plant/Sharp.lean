module

public import Contracts.Plant.Euler
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The sharp one-period step

The estimates of `Flow.lean` and `Euler.lean` are too coarse for per-tick use in a closed-loop
invariant. `norm_traj_sub_le` takes the Lipschitz constant on a sup-norm ball whose radius includes
the position, and the velocity rows of `step_sub_eulerStep_le` go through a Lipschitz bound of the
down axis that loses a factor of about 40. This file proves block-wise bounds instead.

**Attitude block.** The `(q, ω)` rows of the field do not depend on `(p, v)`. On unit quaternions
and body rates at most `Ω`, they are Lipschitz with constant
`Katt Ω = max((3/2)(1 + Ω), 2 gyro Ω)`, in the sup norm of the 7 attitude coordinates
(`vf_att_lipschitz`). The rates stay below `wTA W A = W + h (A + gyro (wB W)²)` over the period
(`WBd_trajA`), where `W` bounds the initial rates and `A` the angular accelerations of the torques
(`TorqueBd`; `alphaMax` always works, `torqueBd_of_spread` gives `alphaMax · s` for actuators in an
interval of width `s`). Grönwall on this block alone gives `step_qw_gronwall`. A second-order
expansion of each attitude coordinate is `traj_att_taylor`/`step_att_taylor`.

**Translation block.** The thrust acceleration `a = accel u` is constant over the period, so
`v̇ = g e_z - a d(q(t))` and `ṗ = v` are integrated exactly. Along the flow, the down axis `d` and
the first two columns `c₀`, `c₁` of the rotation (all three are quadratic in `q`) satisfy
`ḋ = c₀ ω_y - c₁ ω_x` (`dnDot`, the exact `Dd(q)[q̇]`), and
`d̈ = c₀ (ω̇_y + ω_x ω_z) + c₁ (ω_y ω_z - ω̇_x) - d (ω_x² + ω_y²)` (`dnDDot`). The rotation rows have
unit length, so `|d̈ⱼ| ≤ Cd A Ω = √(2 (A + (Jz/Jx) Ω²)² + 4 Ω⁴)` (`abs_dnDDot_le`), with
`Jz / Jx = 31/20`. Three and four integrations give `traj_pv_sharp`/`step_pv_sharp`:

* `v(h) = v + h (g e_z - a d(q)) - a (h²/2) Dd(q)[q̇] + r_v`, `|r_v| ≤ a Cd h³ / 6`,
* `p(h) = p + h v + (h²/2)(g e_z - a d(q)) - a (h³/6) Dd(q)[q̇] + r_p`, `|r_p| ≤ a Cd h⁴ / 24`,

per NED component, from a unit quaternion. The lower-order versions `traj_pv_first` use
`|ḋⱼ| ≤ √2 Ω`, and `traj_pos_move` bounds the position change over the period by
`V t + (g + a) t² / 2` (for intersample reasoning).

**Numbers** (`W = 1` rad/s, any actuators, so `A = alphaMax = 595.75`): `Ω = 2.53`, `Cd ≤ 857`,
`|r_v| ≤ 4.93e-5` m/s (`2.19e-5` at hover thrust), `|r_p| ≤ 3.1e-8` m, `Katt = 5.295`, and the
attitude block moves by at most `1.511` per period (dominated by `h · alphaMax` in the rates). See the
examples at the end of the file and `PLANT.md`. With the actuators in `[0.30, 0.62]` (the
region `D8` of the tracking plan), `A = 0.32 alphaMax`, `Ω = 1.52`, `Cd ≤ 275` and
`|r_v| ≤ 9.8e-6` m/s.
-/

@[expose] public section

namespace Contracts.Plant

noncomputable section

open Set

/-! ## Indices, axes, torque bounds -/

/-- Position coordinate `j` (`0, 1, 2`, NED) of the flat state. -/
def pI (j : Fin 3) : Fin 13 := ⟨j.val, by omega⟩

/-- Velocity coordinate `j` (`3, 4, 5`). -/
def vI (j : Fin 3) : Fin 13 := ⟨j.val + 3, by omega⟩

/-- Quaternion coordinate `i` (`6, …, 9`). -/
def qI (i : Fin 4) : Fin 13 := ⟨i.val + 6, by omega⟩

/-- Rate coordinate `k` (`10, 11, 12`). -/
def wI (k : Fin 3) : Fin 13 := ⟨k.val + 10, by omega⟩

/-- The NED down unit vector `e_z`. -/
def ez : Fin 3 → ℝ := ![0, 0, 1]

/-- The first column of the rotation of `q` (body forward axis in NED), times `‖q‖²`. -/
def col0 (x : X) : Fin 3 → ℝ :=
  ![x 6 * x 6 + x 7 * x 7 - x 8 * x 8 - x 9 * x 9, 2 * (x 7 * x 8 + x 6 * x 9),
    2 * (x 7 * x 9 - x 6 * x 8)]

/-- The second column of the rotation of `q` (body right axis in NED), times `‖q‖²`. -/
def col1 (x : X) : Fin 3 → ℝ :=
  ![2 * (x 7 * x 8 - x 6 * x 9), x 6 * x 6 - x 7 * x 7 + x 8 * x 8 - x 9 * x 9,
    2 * (x 8 * x 9 + x 6 * x 7)]

/-- The down axis `d(q)` (third column of the rotation, times `‖q‖²`), as in `downAxis`. -/
def dn (x : X) : Fin 3 → ℝ :=
  ![2 * (x 7 * x 9 + x 6 * x 8), 2 * (x 8 * x 9 - x 6 * x 7),
    x 6 * x 6 - x 7 * x 7 - x 8 * x 8 + x 9 * x 9]

/-- The time derivative of the down axis along the flow, `Dd(q)[q̇] = R(q) (ω × e_z)`
`= c₀ ω_y - c₁ ω_x`. -/
def dnDot (x : X) (j : Fin 3) : ℝ := col0 x j * x 11 - col1 x j * x 10

/-- The second time derivative of the down axis along the flow,
`c₀ (ω̇_y + ω_x ω_z) + c₁ (ω_y ω_z - ω̇_x) - d (ω_x² + ω_y²)`. -/
def dnDDot (x : X) (u : Fin 4 → ℝ) (j : Fin 3) : ℝ :=
  col0 x j * (vf x u 11 + x 10 * x 12) + col1 x j * (x 11 * x 12 - vf x u 10) -
    dn x j * (x 10 ^ 2 + x 11 ^ 2)

theorem dn_eq_downAxis (x : X) :
    dn x 0 = (downAxis (State.ofX x).q).x ∧ dn x 1 = (downAxis (State.ofX x).q).y ∧
      dn x 2 = (downAxis (State.ofX x).q).z := ⟨rfl, rfl, rfl⟩

/-- The position rows of the field: `ṗ = v`. -/
theorem vf_pI (x : X) (u : Fin 4 → ℝ) (j : Fin 3) : vf x u (pI j) = x (vI j) := by
  fin_cases j <;> rfl

/-- The velocity rows of the field: `v̇ = g e_z - a d(q)`. -/
theorem vf_vI (x : X) (u : Fin 4 → ℝ) (j : Fin 3) :
    vf x u (vI j) = grav * ez j - accel u * dn x j := by
  fin_cases j <;> simp [vI, ez, dn, vf_3, vf_4, vf_5]
  ring

/-- The angular accelerations of the torques are at most `A`. -/
def TorqueBd (u : Fin 4 → ℝ) (A : ℝ) : Prop :=
  |torqueX u / Jx| ≤ A ∧ |torqueY u / Jy| ≤ A ∧ |torqueZ u / Jz| ≤ A

/-- Every actuator vector satisfies the torque bound `alphaMax` (the actuators are clipped). -/
theorem torqueBd_alphaMax (u : Fin 4 → ℝ) : TorqueBd u alphaMax :=
  ⟨abs_torqueX_div_le u, abs_torqueY_div_le u, abs_torqueZ_div_le u⟩

theorem TorqueBd.nonneg {u : Fin 4 → ℝ} {A : ℝ} (hA : TorqueBd u A) : 0 ≤ A :=
  (abs_nonneg _).trans hA.1

/-- **Torque bound from the actuator spread.** Actuators in an interval `[lo, lo + s] ⊆ [0, 1]`
give angular accelerations at most `alphaMax · s`. -/
theorem torqueBd_of_spread {u : Fin 4 → ℝ} {lo s : ℝ} (h0 : 0 ≤ lo) (h1 : lo + s ≤ 1)
    (hu : ∀ i, lo ≤ u i ∧ u i ≤ lo + s) : TorqueBd u (alphaMax * s) := by
  have hc : ∀ i, clip01 (u i) = u i := fun i =>
    clip01_of_mem (h0.trans (hu i).1) ((hu i).2.trans h1)
  have hs : 0 ≤ s := by linarith [(hu 0).1, (hu 0).2]
  obtain ⟨a0, b0⟩ := hu 0; obtain ⟨a1, b1⟩ := hu 1
  obtain ⟨a2, b2⟩ := hu 2; obtain ⟨a3, b3⟩ := hu 3
  have hl := lever_pos; have hf := fmax_pos; have hJ := Jx_pos
  have hαs : alphaMax * s = lever * fmax * (2 * s) / Jx := by unfold alphaMax; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hαs, abs_div, abs_of_pos hJ]
    apply div_le_div_of_nonneg_right _ hJ.le
    have e : torqueX u = lever * fmax * (-u 0 + u 1 + u 2 - u 3) := by
      simp only [torqueX, force, hc]; ring
    rw [e, abs_mul, abs_of_pos (mul_pos hl hf)]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (mul_pos hl hf).le
  · rw [hαs, abs_div, abs_of_pos Jy_pos, ← Jy_eq_Jx]
    apply div_le_div_of_nonneg_right _ Jy_pos.le
    have e : torqueY u = lever * fmax * (u 0 - u 1 + u 2 - u 3) := by
      simp only [torqueY, force, hc]; ring
    rw [e, abs_mul, abs_of_pos (mul_pos hl hf)]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (mul_pos hl hf).le
  · rw [abs_div, abs_of_pos Jz_pos, torqueZ, km_maxRPM_sq, hc, hc, hc, hc, abs_mul,
      abs_of_pos (mul_pos kmkf_pos hf)]
    have hk : |u 0 + u 1 - u 2 - u 3| ≤ 2 * s := abs_le.2 ⟨by linarith, by linarith⟩
    rw [div_le_iff₀ Jz_pos, hαs, div_mul_eq_mul_div, le_div_iff₀ hJ]
    have : kmkf * Jx ≤ lever * Jz := by norm_num [kmkf, km, kf, Jx, lever, Jz]
    have h2 : kmkf * fmax * |u 0 + u 1 - u 2 - u 3| ≤ kmkf * fmax * (2 * s) :=
      mul_le_mul_of_nonneg_left hk (mul_pos kmkf_pos hf).le
    have h3 : 0 ≤ fmax * (2 * s) := by positivity
    nlinarith

/-- Actuators at most `c ∈ [0, 1]` give a thrust acceleration at most `c · amax`. -/
theorem accel_le_mul {u : Fin 4 → ℝ} {c : ℝ} (hc : 0 ≤ c) (hu : ∀ i, u i ≤ c) :
    accel u ≤ c * amax := by
  have hcl : ∀ i, clip01 (u i) ≤ c := fun i =>
    max_le hc ((min_le_right _ _).trans (hu i))
  rw [accel, thrust_eq, ← four_fmax_div_mass, mul_div_assoc', div_le_div_iff_of_pos_right mass_pos]
  have := hcl 0; have := hcl 1; have := hcl 2; have := hcl 3
  nlinarith [fmax_pos]

/-- The rate rows of the field under a torque bound. -/
theorem abs_vf_wA (x : X) {u : Fin 4 → ℝ} {Rw A : ℝ} (hw : WBd x Rw) (hA : TorqueBd u A) :
    |vf x u 10| ≤ A + gyro * Rw ^ 2 ∧ |vf x u 11| ≤ A + gyro * Rw ^ 2 ∧
      |vf x u 12| ≤ A + gyro * Rw ^ 2 := by
  obtain ⟨x10, x11, x12⟩ := hw
  obtain ⟨t10, t11, t12⟩ := hA
  have hg : 0 ≤ gyro := by norm_num [gyro]
  have P : ∀ {i j : Fin 13}, |x i| ≤ Rw → |x j| ≤ Rw → |x i * x j| ≤ Rw ^ 2 := by
    intro i j a b; rw [abs_mul, sq]; exact mul_le_mul a b (abs_nonneg _) ((abs_nonneg _).trans a)
  have G : ∀ {c p : ℝ}, |c| ≤ gyro → |p| ≤ Rw ^ 2 → |c * p| ≤ gyro * Rw ^ 2 := by
    intro c p hc hp; rw [abs_mul]; exact mul_le_mul hc hp (abs_nonneg _) hg
  refine ⟨?_, ?_, ?_⟩
  · rw [show vf x u 10 = torqueX u / Jx + (-((Jz - Jy) / Jx)) * (x 11 * x 12) by
      rw [vf_10]; field_simp [Jx_pos.ne']; ring]
    refine (abs_add_le _ _).trans (add_le_add t10 (G ?_ (P x11 x12)))
    norm_num [Jx, Jy, Jz, gyro, abs_of_pos]
  · rw [show vf x u 11 = torqueY u / Jy + (-((Jx - Jz) / Jy)) * (x 12 * x 10) by
      rw [vf_11]; field_simp [Jy_pos.ne']; ring]
    refine (abs_add_le _ _).trans (add_le_add t11 (G ?_ (P x12 x10)))
    norm_num [Jx, Jy, Jz, gyro, abs_of_pos]
  · rw [show vf x u 12 = torqueZ u / Jz + (-((Jy - Jx) / Jz)) * (x 10 * x 11) by
      rw [vf_12]; field_simp [Jz_pos.ne']; ring]
    refine (abs_add_le _ _).trans (add_le_add t12 (G ?_ (P x10 x11)))
    norm_num [Jx, Jy, Jz, gyro]

/-! ## Rates along the trajectory -/

/-- Rate bound over one period under the torque bound `A`: `W + h (A + gyro (wB W)²)`. -/
def wTA (W A : ℝ) : ℝ := W + h * (A + gyro * wB W ^ 2)

theorem le_wTA {W A : ℝ} (hA : 0 ≤ A) : W ≤ wTA W A := by
  have : 0 ≤ h * (A + gyro * wB W ^ 2) := by
    have := h_pos
    have : (0 : ℝ) ≤ gyro := by norm_num [gyro]
    positivity
  unfold wTA; linarith

/-- **Rates along the trajectory** under the torque bound `A`: `|ωⱼ(t)| ≤ wTA W A` on `[0, h]`. -/
theorem WBd_trajA {x : X} {u : Fin 4 → ℝ} {W A : ℝ} (hW : WBd x W) (hA : TorqueBd u A) :
    ∀ t ∈ Icc 0 h, WBd (traj x u t) (wTA W A) := by
  intro t ht
  have hd : ∀ j, ∀ r ∈ Icc 0 h, HasDerivAt (fun r => traj x u r j) (vf (traj x u r) u j) r :=
    fun j r hr => hasDerivAt_pi.1 (traj_hasDerivAt x u r hr) j
  have bw := fun r hr => abs_vf_wA (traj x u r) (WBd_traj_energy hW r hr) hA
  have hM : 0 ≤ A + gyro * wB W ^ 2 := by
    have := hA.nonneg
    have : (0 : ℝ) ≤ gyro := by norm_num [gyro]
    positivity
  have one : ∀ j, |x j| ≤ W → (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ A + gyro * wB W ^ 2) →
      |traj x u t j| ≤ wTA W A := by
    intro j hx hb
    have h1 := abs_sub_le_of_deriv (hd j) hb t ht
    simp only [traj_zero] at h1
    have h2 : (A + gyro * wB W ^ 2) * t ≤ h * (A + gyro * wB W ^ 2) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right ht.2 hM
    have := abs_sub_abs_le_abs_sub (traj x u t j) (x j)
    unfold wTA; linarith
  obtain ⟨w10, w11, w12⟩ := hW
  exact ⟨one 10 w10 fun r hr => (bw r hr).1, one 11 w11 fun r hr => (bw r hr).2.1,
    one 12 w12 fun r hr => (bw r hr).2.2⟩

theorem WBd_mono {x : X} {R R' : ℝ} (h : WBd x R) (hR : R ≤ R') : WBd x R' :=
  ⟨h.1.trans hR, h.2.1.trans hR, h.2.2.trans hR⟩

theorem QBd_one_of_unit {x : X} (hq : qnormSq x = 1) : QBd x 1 := by
  simpa using QBd_of_qnormSq_le (le_of_eq hq)

/-! ## Taylor expansions with bounded remainder -/

/-- If `f' = g` on `[0, T]` and `|g - p| ≤ B'` where `P' = p`, `B' ` is the derivative of `B` and
`B 0 = 0`, then `|f t - f 0 - (P t - P 0)| ≤ B t` on `[0, T]`. -/
theorem abs_sub_poly_le {f g P p B B' : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t) (hP : ∀ t, HasDerivAt P (p t) t)
    (hB : ∀ t, HasDerivAt B (B' t) t) (hB0 : B 0 = 0)
    (hb : ∀ t ∈ Icc 0 T, |g t - p t| ≤ B' t) :
    ∀ t ∈ Icc 0 T, |f t - f 0 - (P t - P 0)| ≤ B t := by
  intro t ht
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t => f t - f 0 - (P t - P 0)) (f' := fun t => g t - p t) (a := 0) (b := T)
    (B := B) (B' := B')
    (fun s hs => (((hf s hs).sub_const (f 0)).sub ((hP s).sub_const (P 0))).continuousAt
      |>.continuousWithinAt)
    (fun s hs => (((hf s (Ico_subset_Icc_self hs)).sub_const (f 0)).sub
      ((hP s).sub_const (P 0))).hasDerivWithinAt)
    (by simp [hB0]) hB
    (fun s hs => by rw [Real.norm_eq_abs]; exact hb s (Ico_subset_Icc_self hs)) ht
  simpa [Real.norm_eq_abs] using this

/-- Second order: `|g t - g 0| ≤ C t` gives `|f t - f 0 - t g 0| ≤ C t² / 2`. -/
theorem taylor2 {f g : ℝ → ℝ} {T C : ℝ} (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc 0 T, |g t - g 0| ≤ C * t) :
    ∀ t ∈ Icc 0 T, |f t - f 0 - t * g 0| ≤ C * t ^ 2 / 2 := by
  intro t ht
  have := abs_sub_poly_le (P := fun s => s * g 0) (p := fun _ => g 0)
    (B := fun s => C * s ^ 2 / 2) (B' := fun s => C * s) hf
    (fun s => hasDerivAt_mul_const (g 0))
    (fun s => by convert ((hasDerivAt_pow 2 s).const_mul C).div_const 2 using 1; ring)
    (by simp) hg t ht
  simpa using this

/-- Third order: `|g t - g 0 - t k| ≤ C t² / 2` gives
`|f t - f 0 - t g 0 - (t² / 2) k| ≤ C t³ / 6`. -/
theorem taylor3 {f g : ℝ → ℝ} {T C k : ℝ} (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc 0 T, |g t - g 0 - t * k| ≤ C * t ^ 2 / 2) :
    ∀ t ∈ Icc 0 T, |f t - f 0 - t * g 0 - t ^ 2 / 2 * k| ≤ C * t ^ 3 / 6 := by
  intro t ht
  have := abs_sub_poly_le (P := fun s => s * g 0 + s ^ 2 / 2 * k) (p := fun s => g 0 + s * k)
    (B := fun s => C * s ^ 3 / 6) (B' := fun s => C * s ^ 2 / 2) hf
    (fun s => by
      convert (hasDerivAt_mul_const (g 0)).add (((hasDerivAt_pow 2 s).div_const 2).mul_const k)
        using 1
      push_cast; ring)
    (fun s => by convert ((hasDerivAt_pow 3 s).const_mul C).div_const 6 using 1; push_cast; ring)
    (by simp) (fun s hs => by simpa [sub_sub] using hg s hs) t ht
  have e : f t - f 0 - (t * g 0 + t ^ 2 / 2 * k - (0 * g 0 + 0 ^ 2 / 2 * k)) =
      f t - f 0 - t * g 0 - t ^ 2 / 2 * k := by ring
  simpa only [e] using this

/-- Fourth order: `|g t - g 0 - t k₁ - (t² / 2) k₂| ≤ C t³ / 6` gives
`|f t - f 0 - t g 0 - (t² / 2) k₁ - (t³ / 6) k₂| ≤ C t⁴ / 24`. -/
theorem taylor4 {f g : ℝ → ℝ} {T C k₁ k₂ : ℝ} (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hg : ∀ t ∈ Icc 0 T, |g t - g 0 - t * k₁ - t ^ 2 / 2 * k₂| ≤ C * t ^ 3 / 6) :
    ∀ t ∈ Icc 0 T,
      |f t - f 0 - t * g 0 - t ^ 2 / 2 * k₁ - t ^ 3 / 6 * k₂| ≤ C * t ^ 4 / 24 := by
  intro t ht
  have := abs_sub_poly_le (P := fun s => s * g 0 + s ^ 2 / 2 * k₁ + s ^ 3 / 6 * k₂)
    (p := fun s => g 0 + s * k₁ + s ^ 2 / 2 * k₂)
    (B := fun s => C * s ^ 4 / 24) (B' := fun s => C * s ^ 3 / 6) hf
    (fun s => by
      convert ((hasDerivAt_mul_const (g 0)).add (((hasDerivAt_pow 2 s).div_const 2).mul_const k₁)).add
        (((hasDerivAt_pow 3 s).div_const 6).mul_const k₂) using 1
      push_cast; ring)
    (fun s => by convert ((hasDerivAt_pow 4 s).const_mul C).div_const 24 using 1; push_cast; ring)
    (by simp) (fun s hs => by
      have e : g s - (g 0 + s * k₁ + s ^ 2 / 2 * k₂) = g s - g 0 - s * k₁ - s ^ 2 / 2 * k₂ := by
        ring
      rw [e]; exact hg s hs) t ht
  have e : f t - f 0 - (t * g 0 + t ^ 2 / 2 * k₁ + t ^ 3 / 6 * k₂ -
      (0 * g 0 + 0 ^ 2 / 2 * k₁ + 0 ^ 3 / 6 * k₂)) =
      f t - f 0 - t * g 0 - t ^ 2 / 2 * k₁ - t ^ 3 / 6 * k₂ := by ring
  simpa only [e] using this

/-! ## Derivatives of the rotation columns along a solution -/

section deriv
variable {u : Fin 4 → ℝ} {γ : ℝ → X} {t : ℝ}

private theorem hd_mul (hγ : HasDerivAt γ (vf (γ t) u) t) (i k : Fin 13) :
    HasDerivAt (fun s => γ s i * γ s k) (vf (γ t) u i * γ t k + γ t i * vf (γ t) u k) t :=
  (hasDerivAt_pi.1 hγ i).mul (hasDerivAt_pi.1 hγ k)

/-- `ċ₀ = R (ω × e_x) = c₁ ω_z - d ω_y`. -/
theorem hasDerivAt_col0 (hγ : HasDerivAt γ (vf (γ t) u) t) (j : Fin 3) :
    HasDerivAt (fun s => col0 (γ s) j) (col1 (γ t) j * γ t 12 - dn (γ t) j * γ t 11) t := by
  have M := hd_mul hγ
  fin_cases j
  · convert (((M 6 6).add (M 7 7)).sub (M 8 8)).sub (M 9 9) using 1
    · funext s; simp [col0]
    · simp [col1, dn, vf_6, vf_7, vf_8, vf_9]; ring
  · convert ((M 7 8).add (M 6 9)).const_mul 2 using 1
    · funext s; simp [col0]
    · simp [col1, dn, vf_6, vf_7, vf_8, vf_9]; ring
  · convert ((M 7 9).sub (M 6 8)).const_mul 2 using 1
    · funext s; simp [col0]
    · simp [col1, dn, vf_6, vf_7, vf_8, vf_9]; ring

/-- `ċ₁ = R (ω × e_y) = d ω_x - c₀ ω_z`. -/
theorem hasDerivAt_col1 (hγ : HasDerivAt γ (vf (γ t) u) t) (j : Fin 3) :
    HasDerivAt (fun s => col1 (γ s) j) (dn (γ t) j * γ t 10 - col0 (γ t) j * γ t 12) t := by
  have M := hd_mul hγ
  fin_cases j
  · convert ((M 7 8).sub (M 6 9)).const_mul 2 using 1
    · funext s; simp [col1]
    · simp [col0, dn, vf_6, vf_7, vf_8, vf_9]; ring
  · convert (((M 6 6).sub (M 7 7)).add (M 8 8)).sub (M 9 9) using 1
    · funext s; simp [col1]
    · simp [col0, dn, vf_6, vf_7, vf_8, vf_9]; ring
  · convert ((M 8 9).add (M 6 7)).const_mul 2 using 1
    · funext s; simp [col1]
    · simp [col0, dn, vf_6, vf_7, vf_8, vf_9]; ring

/-- `ḋ = R (ω × e_z) = c₀ ω_y - c₁ ω_x` (`dnDot`). -/
theorem hasDerivAt_dn (hγ : HasDerivAt γ (vf (γ t) u) t) (j : Fin 3) :
    HasDerivAt (fun s => dn (γ s) j) (dnDot (γ t) j) t := by
  have M := hd_mul hγ
  fin_cases j
  · convert ((M 7 9).add (M 6 8)).const_mul 2 using 1
    · funext s; simp [dn]
    · simp [dnDot, col0, col1, vf_6, vf_7, vf_8, vf_9]; ring
  · convert ((M 8 9).sub (M 6 7)).const_mul 2 using 1
    · funext s; simp [dn]
    · simp [dnDot, col0, col1, vf_6, vf_7, vf_8, vf_9]; ring
  · convert (((M 6 6).sub (M 7 7)).sub (M 8 8)).add (M 9 9) using 1
    · funext s; simp [dn]
    · simp [dnDot, col0, col1, vf_6, vf_7, vf_8, vf_9]; ring

/-- `d/dt Dd(q)[q̇] = dnDDot`. -/
theorem hasDerivAt_dnDot (hγ : HasDerivAt γ (vf (γ t) u) t) (j : Fin 3) :
    HasDerivAt (fun s => dnDot (γ s) j) (dnDDot (γ t) u j) t := by
  have := ((hasDerivAt_col0 hγ j).mul (hasDerivAt_pi.1 hγ 11)).sub
    ((hasDerivAt_col1 hγ j).mul (hasDerivAt_pi.1 hγ 10))
  convert this using 1
  · funext s; simp only [dnDot, Pi.sub_apply, Pi.mul_apply]
  · simp only [dnDDot]; ring

end deriv

/-! ## Bounds through the rotation rows -/

/-- The rows of the (unnormalized) rotation have length `‖q‖²`. -/
theorem row_sq (x : X) (j : Fin 3) :
    col0 x j ^ 2 + col1 x j ^ 2 + dn x j ^ 2 = qnormSq x ^ 2 := by
  fin_cases j <;> simp [col0, col1, dn, qnormSq] <;> ring

/-- **Cauchy-Schwarz with a rotation row**: for a unit quaternion,
`|c₀ⱼ a + c₁ⱼ b + dⱼ c| ≤ √(a² + b² + c²)`. -/
theorem abs_row_le {x : X} (hq : qnormSq x = 1) (j : Fin 3) (a b c : ℝ) :
    |col0 x j * a + col1 x j * b + dn x j * c| ≤ Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  apply Real.abs_le_sqrt
  have hr := row_sq x j
  rw [hq, one_pow] at hr
  set r0 := col0 x j; set r1 := col1 x j; set r2 := dn x j
  nlinarith [sq_nonneg (r0 * b - r1 * a), sq_nonneg (r0 * c - r2 * a), sq_nonneg (r1 * c - r2 * b)]

/-- **First derivative of the down axis**: `|ḋⱼ| ≤ √2 Ω` for a unit quaternion and rates at most
`Ω`. -/
theorem abs_dnDot_le {x : X} {Ω : ℝ} (hq : qnormSq x = 1) (hw : WBd x Ω) (j : Fin 3) :
    |dnDot x j| ≤ Real.sqrt 2 * Ω := by
  obtain ⟨w10, w11, -⟩ := hw
  have hΩ : 0 ≤ Ω := (abs_nonneg _).trans w10
  have e : dnDot x j = col0 x j * x 11 + col1 x j * (-x 10) + dn x j * 0 := by
    simp only [dnDot]; ring
  rw [e]
  refine (abs_row_le hq j _ _ _).trans ?_
  have s10 := sq_le_sq' (abs_le.mp w10).1 (abs_le.mp w10).2
  have s11 := sq_le_sq' (abs_le.mp w11).1 (abs_le.mp w11).2
  calc Real.sqrt (x 11 ^ 2 + (-x 10) ^ 2 + 0 ^ 2) ≤ Real.sqrt (2 * Ω ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt 2 * Ω := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hΩ]

/-- The constant of the second derivative of the down axis:
`Cd A Ω = √(2 (A + (31/20) Ω²)² + 4 Ω⁴)`, `31/20 = Jz / Jx`. -/
def Cd (A Ω : ℝ) : ℝ := Real.sqrt (2 * (A + 31 / 20 * Ω ^ 2) ^ 2 + 4 * Ω ^ 4)

theorem Cd_nonneg (A Ω : ℝ) : 0 ≤ Cd A Ω := Real.sqrt_nonneg _

/-- `Cd` is monotone. -/
theorem Cd_mono {A A' Ω Ω' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (hΩ : 0 ≤ Ω) (hΩΩ : Ω ≤ Ω') :
    Cd A Ω ≤ Cd A' Ω' := by
  unfold Cd
  apply Real.sqrt_le_sqrt
  have h2 : Ω ^ 2 ≤ Ω' ^ 2 := pow_le_pow_left₀ hΩ hΩΩ 2
  have h4 : Ω ^ 4 ≤ Ω' ^ 4 := pow_le_pow_left₀ hΩ hΩΩ 4
  have h0 : 0 ≤ A + 31 / 20 * Ω ^ 2 := by positivity
  have h1 : A + 31 / 20 * Ω ^ 2 ≤ A' + 31 / 20 * Ω' ^ 2 := by linarith
  nlinarith

/-- **Second derivative of the down axis**: `|d̈ⱼ| ≤ Cd A Ω` for a unit quaternion, rates at most
`Ω` and angular accelerations of the torques at most `A`. -/
theorem abs_dnDDot_le {x : X} {u : Fin 4 → ℝ} {A Ω : ℝ} (hq : qnormSq x = 1) (hw : WBd x Ω)
    (hA : TorqueBd u A) (j : Fin 3) : |dnDDot x u j| ≤ Cd A Ω := by
  obtain ⟨w10, w11, w12⟩ := hw
  obtain ⟨t10, t11, -⟩ := hA
  have hΩ : 0 ≤ Ω := (abs_nonneg _).trans w10
  have z0 : vf x u 11 + x 10 * x 12 = torqueY u / Jy + 31 / 20 * (x 10 * x 12) := by
    rw [vf_11]; field_simp; norm_num [Jx, Jy, Jz]; ring
  have z1 : x 11 * x 12 - vf x u 10 = -(torqueX u / Jx) + 31 / 20 * (x 11 * x 12) := by
    rw [vf_10]; field_simp; norm_num [Jx, Jy, Jz]; ring
  have P : ∀ {i k : Fin 13}, |x i| ≤ Ω → |x k| ≤ Ω → |x i * x k| ≤ Ω ^ 2 := by
    intro i k a b; rw [abs_mul, sq]; exact mul_le_mul a b (abs_nonneg _) hΩ
  have b0 : |vf x u 11 + x 10 * x 12| ≤ A + 31 / 20 * Ω ^ 2 := by
    rw [z0]; refine (abs_add_le _ _).trans (add_le_add t11 ?_)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 31 / 20)]
    exact mul_le_mul_of_nonneg_left (P w10 w12) (by norm_num)
  have b1 : |x 11 * x 12 - vf x u 10| ≤ A + 31 / 20 * Ω ^ 2 := by
    rw [z1]; refine (abs_add_le _ _).trans (add_le_add (by rwa [abs_neg]) ?_)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 31 / 20)]
    exact mul_le_mul_of_nonneg_left (P w11 w12) (by norm_num)
  have b2 : |-(x 10 ^ 2 + x 11 ^ 2)| ≤ 2 * Ω ^ 2 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have := P w10 w10; have := P w11 w11
    rw [abs_mul_self] at *
    nlinarith [sq_abs (x 10), sq_abs (x 11), abs_mul_abs_self (x 10), abs_mul_abs_self (x 11)]
  have e : dnDDot x u j = col0 x j * (vf x u 11 + x 10 * x 12) +
      col1 x j * (x 11 * x 12 - vf x u 10) + dn x j * (-(x 10 ^ 2 + x 11 ^ 2)) := by
    simp only [dnDDot]; ring
  rw [e]
  refine (abs_row_le hq j _ _ _).trans (Real.sqrt_le_sqrt ?_)
  have s0 := sq_le_sq' (abs_le.mp b0).1 (abs_le.mp b0).2
  have s1 := sq_le_sq' (abs_le.mp b1).1 (abs_le.mp b1).2
  have s2 := sq_le_sq' (abs_le.mp b2).1 (abs_le.mp b2).2
  nlinarith

/-! ## The translation block: exact integration -/

section pv
variable {x : X} {u : Fin 4 → ℝ} {W A Ω : ℝ}

/-- Along the trajectory, the quaternion stays a unit quaternion and the rates stay below `Ω`. -/
theorem traj_unit_rates (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBd u A)
    (hΩ : wTA W A ≤ Ω) :
    ∀ t ∈ Icc 0 h, qnormSq (traj x u t) = 1 ∧ WBd (traj x u t) Ω := fun t ht =>
  ⟨(qnormSq_traj x u t ht).trans hq, WBd_mono (WBd_trajA hW hA t ht) hΩ⟩

/-- **The down axis along the trajectory**, to first and second order:
`|d(t) - d(0)| ≤ √2 Ω t` and `|d(t) - d(0) - t ḋ(0)| ≤ Cd A Ω t² / 2`. -/
theorem traj_dn (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBd u A) (hΩ : wTA W A ≤ Ω)
    (j : Fin 3) : ∀ t ∈ Icc 0 h,
      |dn (traj x u t) j - dn x j| ≤ Real.sqrt 2 * Ω * t ∧
      |dn (traj x u t) j - dn x j - t * dnDot x j| ≤ Cd A Ω * t ^ 2 / 2 := by
  have hur := traj_unit_rates hq hW hA hΩ
  have hd1 : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => dn (traj x u s) j) (dnDot (traj x u s) j) s :=
    fun s hs => hasDerivAt_dn (traj_hasDerivAt x u s hs) j
  have hd2 : ∀ s ∈ Icc 0 h,
      HasDerivAt (fun s => dnDot (traj x u s) j) (dnDDot (traj x u s) u j) s :=
    fun s hs => hasDerivAt_dnDot (traj_hasDerivAt x u s hs) j
  have m1 := abs_sub_le_of_deriv hd1 (fun s hs => abs_dnDot_le (hur s hs).1 (hur s hs).2 j)
  have m2 := abs_sub_le_of_deriv hd2 (fun s hs => abs_dnDDot_le (hur s hs).1 (hur s hs).2 hA j)
  have t2 := taylor2 hd1 m2
  simp only [traj_zero] at m1 t2
  exact fun t ht => ⟨m1 t ht, t2 t ht⟩

/-- **The sharp step of the translation block, along the period.** From a unit quaternion with
body rates at most `W`, under angular accelerations of the torques at most `A`, with
`Ω ≥ wTA W A`, for `t ∈ [0, h]` and each NED component `j`:
* `v(t) = v + t (g e_z - a d(q)) - a (t²/2) Dd(q)[q̇] + r_v`, `|r_v| ≤ a Cd A Ω t³ / 6`,
* `p(t) = p + t v + (t²/2)(g e_z - a d(q)) - a (t³/6) Dd(q)[q̇] + r_p`,
  `|r_p| ≤ a Cd A Ω t⁴ / 24`,
where `a = accel u` is the thrust acceleration (constant over the period). -/
theorem traj_pv_sharp (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBd u A)
    (hΩ : wTA W A ≤ Ω) (j : Fin 3) : ∀ t ∈ Icc 0 h,
      |traj x u t (vI j) - (x (vI j) + t * (grav * ez j - accel u * dn x j) -
          accel u * (t ^ 2 / 2) * dnDot x j)| ≤ accel u * Cd A Ω * t ^ 3 / 6 ∧
      |traj x u t (pI j) - (x (pI j) + t * x (vI j) + t ^ 2 / 2 * (grav * ez j - accel u * dn x j) -
          accel u * (t ^ 3 / 6) * dnDot x j)| ≤ accel u * Cd A Ω * t ^ 4 / 24 := by
  have ha := accel_nonneg u
  have hdn := traj_dn hq hW hA hΩ j
  have hdv : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => traj x u s (vI j)) (vf (traj x u s) u (vI j)) s :=
    fun s hs => hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (vI j)
  have hdp : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => traj x u s (pI j)) (traj x u s (vI j)) s :=
    fun s hs => by
      have := hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (pI j)
      rwa [vf_pI] at this
  -- the velocity rows to third order
  have hv := taylor3 (k := -(accel u * dnDot x j)) (C := accel u * Cd A Ω) hdv (fun s hs => by
    simp only [vf_vI, traj_zero]
    have e : grav * ez j - accel u * dn (traj x u s) j - (grav * ez j - accel u * dn x j) -
        s * -(accel u * dnDot x j) =
        -(accel u * (dn (traj x u s) j - dn x j - s * dnDot x j)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg ha]
    calc accel u * |dn (traj x u s) j - dn x j - s * dnDot x j|
        ≤ accel u * (Cd A Ω * s ^ 2 / 2) := mul_le_mul_of_nonneg_left (hdn s hs).2 ha
      _ = _ := by ring)
  simp only [vf_vI, traj_zero] at hv
  -- the position rows to fourth order
  have hp := taylor4 (k₁ := grav * ez j - accel u * dn x j) (k₂ := -(accel u * dnDot x j))
    (C := accel u * Cd A Ω) hdp (fun s hs => by
      simp only [traj_zero]; exact hv s hs)
  simp only [traj_zero] at hp
  intro t ht
  constructor
  · have e : traj x u t (vI j) - (x (vI j) + t * (grav * ez j - accel u * dn x j) -
        accel u * (t ^ 2 / 2) * dnDot x j) = traj x u t (vI j) - x (vI j) -
        t * (grav * ez j - accel u * dn x j) - t ^ 2 / 2 * -(accel u * dnDot x j) := by ring
    rw [e]; exact hv t ht
  · have e : traj x u t (pI j) - (x (pI j) + t * x (vI j) +
        t ^ 2 / 2 * (grav * ez j - accel u * dn x j) - accel u * (t ^ 3 / 6) * dnDot x j) =
        traj x u t (pI j) - x (pI j) - t * x (vI j) -
        t ^ 2 / 2 * (grav * ez j - accel u * dn x j) - t ^ 3 / 6 * -(accel u * dnDot x j) := by
      ring
    rw [e]; exact hp t ht

/-- **The sharp step of the translation block** (`step_pv_sharp`): the case `t = h` of
`traj_pv_sharp`. -/
theorem step_pv_sharp (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBd u A)
    (hΩ : wTA W A ≤ Ω) (j : Fin 3) :
    |step x u (vI j) - (x (vI j) + h * (grav * ez j - accel u * dn x j) -
        accel u * (h ^ 2 / 2) * dnDot x j)| ≤ accel u * Cd A Ω * h ^ 3 / 6 ∧
    |step x u (pI j) - (x (pI j) + h * x (vI j) + h ^ 2 / 2 * (grav * ez j - accel u * dn x j) -
        accel u * (h ^ 3 / 6) * dnDot x j)| ≤ accel u * Cd A Ω * h ^ 4 / 24 :=
  traj_pv_sharp hq hW hA hΩ j h ⟨h_pos.le, le_rfl⟩

/-- **The translation block to one order less**, with the remainder through `|ḋ| ≤ √2 Ω`:
`|v(t) - v - t (g e_z - a d(q))| ≤ a √2 Ω t² / 2` and
`|p(t) - p - t v - (t²/2)(g e_z - a d(q))| ≤ a √2 Ω t³ / 6`. -/
theorem traj_pv_first (hq : qnormSq x = 1) (hW : WBd x W) (hA : TorqueBd u A)
    (hΩ : wTA W A ≤ Ω) (j : Fin 3) : ∀ t ∈ Icc 0 h,
      |traj x u t (vI j) - (x (vI j) + t * (grav * ez j - accel u * dn x j))| ≤
        accel u * (Real.sqrt 2 * Ω) * t ^ 2 / 2 ∧
      |traj x u t (pI j) - (x (pI j) + t * x (vI j) + t ^ 2 / 2 * (grav * ez j - accel u * dn x j))|
        ≤ accel u * (Real.sqrt 2 * Ω) * t ^ 3 / 6 := by
  have ha := accel_nonneg u
  have hdn := traj_dn hq hW hA hΩ j
  have hdv : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => traj x u s (vI j)) (vf (traj x u s) u (vI j)) s :=
    fun s hs => hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (vI j)
  have hdp : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => traj x u s (pI j)) (traj x u s (vI j)) s :=
    fun s hs => by
      have := hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (pI j)
      rwa [vf_pI] at this
  have hv := taylor2 (C := accel u * (Real.sqrt 2 * Ω)) hdv (fun s hs => by
    simp only [vf_vI, traj_zero]
    have e : grav * ez j - accel u * dn (traj x u s) j - (grav * ez j - accel u * dn x j) =
        -(accel u * (dn (traj x u s) j - dn x j)) := by ring
    rw [e, abs_neg, abs_mul, abs_of_nonneg ha, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hdn s hs).1 ha)
  simp only [vf_vI, traj_zero] at hv
  have hp := taylor3 (k := grav * ez j - accel u * dn x j) (C := accel u * (Real.sqrt 2 * Ω)) hdp
    (fun s hs => by simp only [traj_zero]; exact hv s hs)
  simp only [traj_zero] at hp
  intro t ht
  constructor
  · rw [show traj x u t (vI j) - (x (vI j) + t * (grav * ez j - accel u * dn x j)) =
      traj x u t (vI j) - x (vI j) - t * (grav * ez j - accel u * dn x j) by ring]
    exact hv t ht
  · rw [show traj x u t (pI j) - (x (pI j) + t * x (vI j) +
      t ^ 2 / 2 * (grav * ez j - accel u * dn x j)) = traj x u t (pI j) - x (pI j) -
      t * x (vI j) - t ^ 2 / 2 * (grav * ez j - accel u * dn x j) by ring]
    exact hp t ht

/-- The velocity rows of the field are at most `g + a` from a unit quaternion. -/
theorem abs_vf_vI_le (hq : qnormSq x = 1) (j : Fin 3) :
    |vf x u (vI j)| ≤ grav + accel u := by
  rw [vf_vI]
  have ha := accel_nonneg u
  obtain ⟨d0, d1, d2⟩ := abs_down_le x
  rw [hq] at d0 d1 d2
  have hd : |dn x j| ≤ 1 := by
    fin_cases j
    exacts [d0, d1, d2]
  have hz : |ez j| ≤ 1 := by fin_cases j <;> simp [ez]
  have h1 : |grav * ez j| ≤ grav := by
    rw [abs_mul, abs_of_pos grav_pos]; nlinarith [grav_pos, abs_nonneg (ez j)]
  have h2 : |accel u * dn x j| ≤ accel u := by
    rw [abs_mul, abs_of_nonneg ha]; nlinarith [abs_nonneg (dn x j)]
  calc |grav * ez j - accel u * dn x j| ≤ |grav * ez j| + |accel u * dn x j| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

/-- **Position change over the period** (intersample corridor): for velocity components at most
`V` and a unit quaternion, every position component moves by at most `V t + (g + a) t² / 2` on
`[0, h]`, and every velocity component by at most `(g + a) t`. -/
theorem traj_pos_move (hq : qnormSq x = 1) {V : ℝ} (hV : VBd x V) (j : Fin 3) :
    ∀ t ∈ Icc 0 h, |traj x u t (vI j) - x (vI j)| ≤ (grav + accel u) * t ∧
      |traj x u t (pI j) - x (pI j)| ≤ V * t + (grav + accel u) * t ^ 2 / 2 := by
  have hdv : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => traj x u s (vI j)) (vf (traj x u s) u (vI j)) s :=
    fun s hs => hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (vI j)
  have hdp : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => traj x u s (pI j)) (traj x u s (vI j)) s :=
    fun s hs => by
      have := hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) (pI j)
      rwa [vf_pI] at this
  have hv := abs_sub_le_of_deriv hdv
    (fun s hs => abs_vf_vI_le ((qnormSq_traj x u s hs).trans hq) j)
  simp only [traj_zero] at hv
  have hp := taylor2 hdp (fun s hs => by simp only [traj_zero]; exact hv s hs)
  simp only [traj_zero] at hp
  have hx : |x (vI j)| ≤ V := by
    obtain ⟨a, b, c⟩ := hV; fin_cases j
    exacts [a, b, c]
  intro t ht
  refine ⟨hv t ht, ?_⟩
  have h1 := hp t ht
  have h2 : |t * x (vI j)| ≤ V * t := by
    rw [abs_mul, abs_of_nonneg ht.1, mul_comm]; exact mul_le_mul_of_nonneg_right hx ht.1
  calc |traj x u t (pI j) - x (pI j)|
      = |(traj x u t (pI j) - x (pI j) - t * x (vI j)) + t * x (vI j)| := by ring_nf
    _ ≤ |traj x u t (pI j) - x (pI j) - t * x (vI j)| + |t * x (vI j)| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- `traj_pos_move` at the end of the period. -/
theorem step_pos_move (hq : qnormSq x = 1) {V : ℝ} (hV : VBd x V) (j : Fin 3) :
    |step x u (vI j) - x (vI j)| ≤ (grav + accel u) * h ∧
      |step x u (pI j) - x (pI j)| ≤ V * h + (grav + accel u) * h ^ 2 / 2 :=
  traj_pos_move hq hV j h ⟨h_pos.le, le_rfl⟩

end pv

/-! ## The attitude block -/

/-- The attitude block `(q, ω)` of a state, coordinates `6, …, 12`, with the sup norm. -/
def att (x : X) : Fin 7 → ℝ := fun i => x ⟨i.val + 6, by omega⟩

/-- **The Lipschitz constant of the attitude block of the field** on unit quaternions and rates at
most `Ω`: `max((3/2)(1 + Ω), 2 gyro Ω)`. No position or velocity enters. -/
def Katt (Ω : ℝ) : ℝ := max ((3 / 2) * (1 + Ω)) (2 * gyro * Ω)

theorem Katt_pos {Ω : ℝ} (hΩ : 0 ≤ Ω) : 0 < Katt Ω :=
  lt_max_of_lt_left (by positivity)

/-- The attitude block of the field at a state: at most `attF0 W A` from a unit quaternion with
rates at most `W` under the torque bound `A`. -/
def attF0 (W A : ℝ) : ℝ := max ((3 / 2) * W) (A + gyro * W ^ 2)

theorem abs_le_att_norm (x : X) (i : Fin 7) : |x ⟨i.val + 6, by omega⟩| ≤ ‖att x‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm (att x) i

private theorem att_coords {x y : X} {D : ℝ} (hD : ‖att x - att y‖ ≤ D) :
    QBd (x - y) D ∧ WBd (x - y) D := by
  have c : ∀ i : Fin 7, |(x - y) ⟨i.val + 6, by omega⟩| ≤ D := fun i => by
    have := norm_le_pi_norm (att x - att y) i
    rw [Real.norm_eq_abs] at this
    exact this.trans hD
  exact ⟨⟨c 0, c 1, c 2, c 3⟩, ⟨c 4, c 5, c 6⟩⟩

/-- **The attitude block of the field is Lipschitz** with constant `Katt Ω`, in the sup norm of
the attitude coordinates, between a state with a quaternion in the unit cube and rates at most `Ω`
and a state with rates at most `Ω`. -/
theorem vf_att_lipschitz {x y : X} (u : Fin 4 → ℝ) {Ω : ℝ} (hx : QBd x 1) (hwx : WBd x Ω)
    (hwy : WBd y Ω) : ‖att (vf x u) - att (vf y u)‖ ≤ Katt Ω * ‖att x - att y‖ := by
  set D := ‖att x - att y‖
  have hD : 0 ≤ D := norm_nonneg _
  have hΩ : 0 ≤ Ω := (abs_nonneg _).trans hwx.1
  obtain ⟨dq, dw⟩ := att_coords (le_refl D)
  have hq := vf_sub_q (u := u) hx hwy dq dw
  have hw := vf_sub_w (u := u) hwx hwy dw
  have kq : (3 / 2) * (1 * D + Ω * D) ≤ Katt Ω * D := by
    rw [show (3 / 2) * (1 * D + Ω * D) = (3 / 2) * (1 + Ω) * D by ring]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hD
  have kw : gyro * (2 * Ω * D) ≤ Katt Ω * D := by
    rw [show gyro * (2 * Ω * D) = 2 * gyro * Ω * D by ring]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hD
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Katt_pos hΩ).le hD)).2 fun i => ?_
  rw [Real.norm_eq_abs, Pi.sub_apply]
  fin_cases i
  · exact hq.1.trans kq
  · exact hq.2.1.trans kq
  · exact hq.2.2.1.trans kq
  · exact hq.2.2.2.trans kq
  · exact hw.1.trans kw
  · exact hw.2.1.trans kw
  · exact hw.2.2.trans kw

/-- The attitude block of the field at the initial state. -/
theorem norm_att_vf_le {x : X} {u : Fin 4 → ℝ} {W A : ℝ} (hq : qnormSq x = 1) (hW : WBd x W)
    (hA : TorqueBd u A) : ‖att (vf x u)‖ ≤ attF0 W A := by
  have hb := abs_vf_q x u (QBd_one_of_unit hq) hW
  have hw := abs_vf_wA x hW hA
  have hW0 : 0 ≤ W := (abs_nonneg _).trans hW.1
  have kq : (3 / 2) * (1 * W) ≤ attF0 W A := by
    rw [one_mul]; exact le_max_left _ _
  have kw : A + gyro * W ^ 2 ≤ attF0 W A := le_max_right _ _
  refine (pi_norm_le_iff_of_nonneg ((by positivity : (0 : ℝ) ≤ (3 / 2) * W).trans
    (le_max_left _ _))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · exact hb.1.trans kq
  · exact hb.2.1.trans kq
  · exact hb.2.2.1.trans kq
  · exact hb.2.2.2.trans kq
  · exact hw.1.trans kw
  · exact hw.2.1.trans kw
  · exact hw.2.2.trans kw

/-- **Grönwall on the attitude block alone**, along the period:
`‖(q, ω)(t) - (q, ω)(0)‖ ≤ gronwallBound 0 (Katt Ω) ‖(q̇, ω̇)(0)‖ t`. -/
theorem traj_qw_gronwall {x : X} {u : Fin 4 → ℝ} {W A Ω : ℝ} (hq : qnormSq x = 1)
    (hW : WBd x W) (hA : TorqueBd u A) (hΩ : wTA W A ≤ Ω) :
    ∀ t ∈ Icc 0 h, ‖att (traj x u t) - att x‖ ≤ gronwallBound 0 (Katt Ω) ‖att (vf x u)‖ t := by
  have hur := traj_unit_rates hq hW hA hΩ
  have hWx : WBd x Ω := WBd_mono hW ((le_wTA hA.nonneg).trans hΩ)
  have hd : ∀ s ∈ Icc 0 h, HasDerivAt (fun s => att (traj x u s)) (att (vf (traj x u s) u)) s :=
    fun s hs => hasDerivAt_pi.2 fun i => hasDerivAt_pi.1 (traj_hasDerivAt x u s hs) _
  intro t ht
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s => att (traj x u s) - att x)
    (f' := fun s => att (vf (traj x u s) u)) (δ := 0) (K := Katt Ω) (ε := ‖att (vf x u)‖)
    (a := 0) (b := h)
    (fun s hs => ((hd s hs).sub_const _).continuousAt.continuousWithinAt)
    (fun s hs => ((hd s (Ico_subset_Icc_self hs)).sub_const _).hasDerivWithinAt)
    (by simp [traj_zero])
    (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      have h1 := vf_att_lipschitz u (QBd_one_of_unit (hur s hs').1) (hur s hs').2 hWx
      calc ‖att (vf (traj x u s) u)‖
          = ‖(att (vf (traj x u s) u) - att (vf x u)) + att (vf x u)‖ := by rw [sub_add_cancel]
        _ ≤ ‖att (vf (traj x u s) u) - att (vf x u)‖ + ‖att (vf x u)‖ := norm_add_le _ _
        _ ≤ _ := by linarith) t ht
  simpa using this

/-- **The attitude block over one period** (`step_qw_gronwall`):
`‖(q, ω)(h) - (q, ω)(0)‖ ≤ attF0 W A / Katt Ω · (e^{Katt Ω · h} - 1)`, with the Grönwall
constant `Katt Ω` of the attitude block only. -/
theorem step_qw_gronwall {x : X} {u : Fin 4 → ℝ} {W A Ω : ℝ} (hq : qnormSq x = 1)
    (hW : WBd x W) (hA : TorqueBd u A) (hΩ : wTA W A ≤ Ω) :
    ‖att (step x u) - att x‖ ≤ attF0 W A / Katt Ω * (Real.exp (Katt Ω * h) - 1) := by
  have hΩ0 : 0 ≤ Ω := ((abs_nonneg _).trans hW.1).trans ((le_wTA hA.nonneg).trans hΩ)
  have hK := Katt_pos hΩ0
  have := traj_qw_gronwall hq hW hA hΩ h ⟨h_pos.le, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK.ne'] at this
  simp only [zero_mul, zero_add] at this
  refine this.trans ?_
  have he : 0 ≤ Real.exp (Katt Ω * h) - 1 := by
    have := Real.add_one_le_exp (Katt Ω * h)
    have : 0 ≤ Katt Ω * h := mul_nonneg hK.le h_pos.le
    linarith
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (norm_att_vf_le hq hW hA) hK.le) he

/-- Bound of `|q̇ⱼ|` on unit quaternions with rates at most `Ω`. -/
def Mq1 (Ω : ℝ) : ℝ := (3 / 2) * Ω

/-- Bound of `|ω̇ⱼ|` with rates at most `Ω` under the torque bound `A`. -/
def Mw1 (A Ω : ℝ) : ℝ := A + gyro * Ω ^ 2

/-- Lipschitz-in-time constant of the quaternion rows of the field along the period. -/
def cQ (A Ω : ℝ) : ℝ := (3 / 2) * (Mw1 A Ω + Ω * Mq1 Ω)

/-- Lipschitz-in-time constant of the rate rows of the field along the period. -/
def cW (A Ω : ℝ) : ℝ := gyro * (2 * Ω * Mw1 A Ω)

/-- **The attitude block to second order**, coordinate by coordinate, along the period:
`|q(t) - q - t q̇| ≤ cQ t² / 2`, `|ω(t) - ω - t ω̇| ≤ cW t² / 2`, together with the first-order
moves `|q(t) - q| ≤ Mq1 t`, `|ω(t) - ω| ≤ Mw1 t`. -/
theorem traj_att_taylor {x : X} {u : Fin 4 → ℝ} {W A Ω : ℝ} (hq : qnormSq x = 1)
    (hW : WBd x W) (hA : TorqueBd u A) (hΩ : wTA W A ≤ Ω) : ∀ t ∈ Icc 0 h,
      (∀ i : Fin 4, |traj x u t (qI i) - x (qI i)| ≤ Mq1 Ω * t ∧
        |traj x u t (qI i) - x (qI i) - t * vf x u (qI i)| ≤ cQ A Ω * t ^ 2 / 2) ∧
      (∀ k : Fin 3, |traj x u t (wI k) - x (wI k)| ≤ Mw1 A Ω * t ∧
        |traj x u t (wI k) - x (wI k) - t * vf x u (wI k)| ≤ cW A Ω * t ^ 2 / 2) := by
  have hur := traj_unit_rates hq hW hA hΩ
  have hΩ0 : 0 ≤ Ω := ((abs_nonneg _).trans hW.1).trans ((le_wTA hA.nonneg).trans hΩ)
  have hd : ∀ j, ∀ r ∈ Icc 0 h, HasDerivAt (fun r => traj x u r j) (vf (traj x u r) u j) r :=
    fun j r hr => hasDerivAt_pi.1 (traj_hasDerivAt x u r hr) j
  have bq := fun r hr => abs_vf_q (traj x u r) u (QBd_one_of_unit (hur r hr).1) (hur r hr).2
  have bw := fun r hr => abs_vf_wA (traj x u r) (hur r hr).2 hA
  -- first-order moves
  have mq : ∀ j, (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ (3 / 2) * (1 * Ω)) →
      ∀ t ∈ Icc 0 h, |traj x u t j - x j| ≤ Mq1 Ω * t := fun j hb t ht => by
    have := abs_sub_le_of_deriv (hd j) hb t ht
    simpa [traj_zero, Mq1] using this
  have mw : ∀ j, (∀ r ∈ Icc 0 h, |vf (traj x u r) u j| ≤ A + gyro * Ω ^ 2) →
      ∀ t ∈ Icc 0 h, |traj x u t j - x j| ≤ Mw1 A Ω * t := fun j hb t ht => by
    have := abs_sub_le_of_deriv (hd j) hb t ht
    simpa [traj_zero, Mw1] using this
  have hmq : ∀ t ∈ Icc 0 h, QBd (traj x u t - x) (Mq1 Ω * t) := fun t ht =>
    ⟨mq 6 (fun r hr => (bq r hr).1) t ht, mq 7 (fun r hr => (bq r hr).2.1) t ht,
      mq 8 (fun r hr => (bq r hr).2.2.1) t ht, mq 9 (fun r hr => (bq r hr).2.2.2) t ht⟩
  have hmw : ∀ t ∈ Icc 0 h, WBd (traj x u t - x) (Mw1 A Ω * t) := fun t ht =>
    ⟨mw 10 (fun r hr => (bw r hr).1) t ht, mw 11 (fun r hr => (bw r hr).2.1) t ht,
      mw 12 (fun r hr => (bw r hr).2.2) t ht⟩
  have hWx : WBd x Ω := WBd_mono hW ((le_wTA hA.nonneg).trans hΩ)
  -- the field rows are Lipschitz in time
  have lq : ∀ t ∈ Icc 0 h, ∀ i : Fin 4,
      |vf (traj x u t) u (qI i) - vf x u (qI i)| ≤ cQ A Ω * t := by
    intro t ht i
    have := vf_sub_q (u := u) (QBd_one_of_unit (hur t ht).1) hWx (hmq t ht) (hmw t ht)
    have e : (3 / 2) * (1 * (Mw1 A Ω * t) + Ω * (Mq1 Ω * t)) = cQ A Ω * t := by
      unfold cQ; ring
    rw [e] at this
    fin_cases i
    exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
  have lw : ∀ t ∈ Icc 0 h, ∀ k : Fin 3,
      |vf (traj x u t) u (wI k) - vf x u (wI k)| ≤ cW A Ω * t := by
    intro t ht k
    have := vf_sub_w (u := u) (hur t ht).2 hWx (hmw t ht)
    have e : gyro * (2 * Ω * (Mw1 A Ω * t)) = cW A Ω * t := by unfold cW; ring
    rw [e] at this
    fin_cases k
    exacts [this.1, this.2.1, this.2.2]
  intro t ht
  refine ⟨fun i => ⟨?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩
  · have := hmq t ht
    fin_cases i
    exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
  · have := taylor2 (hd (qI i)) (fun s hs => by simpa [traj_zero] using lq s hs i) t ht
    simpa [traj_zero] using this
  · have := hmw t ht
    fin_cases k
    exacts [this.1, this.2.1, this.2.2]
  · have := taylor2 (hd (wI k)) (fun s hs => by simpa [traj_zero] using lw s hs k) t ht
    simpa [traj_zero] using this

/-! ## Evaluated constants (`W = 1` rad/s) -/

theorem alphaMax_eq : alphaMax = 2 * lever * (thrust2weight * grav * mass / 4) / Jx := by
  rw [alphaMax, fmax_eq]

theorem alphaMax_le_num : alphaMax ≤ 59576 / 100 := by
  rw [alphaMax_eq]; norm_num [lever, thrust2weight, grav, mass, Jx]

theorem alphaMax_ge_num : 59575 / 100 ≤ alphaMax := by
  rw [alphaMax_eq]; norm_num [lever, thrust2weight, grav, mass, Jx]

theorem amax_le_num : amax ≤ 22066 / 1000 := by norm_num [amax, thrust2weight, grav]

/-- `wB 1 ≤ 5`: the energy box of one period from rates at most `1` rad/s. -/
theorem wB_one_le : wB 1 ≤ 5 := by
  rw [wB, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have he := Real.exp_one_lt_d9
  have hc : ctau = (2 * lever * (thrust2weight * grav * mass / 4)) ^ 2 / Jx +
      (2 * lever * (thrust2weight * grav * mass / 4)) ^ 2 / Jy +
      (2 * kmkf * (thrust2weight * grav * mass / 4)) ^ 2 / Jz := by rw [ctau, fmax_eq]
  rw [hc, div_le_iff₀ Jx_pos]
  have hpos : 0 ≤ (Jx + Jy + Jz) * 1 ^ 2 + ((2 * lever * (thrust2weight * grav * mass / 4)) ^ 2 / Jx +
      (2 * lever * (thrust2weight * grav * mass / 4)) ^ 2 / Jy +
      (2 * kmkf * (thrust2weight * grav * mass / 4)) ^ 2 / Jz) * h ^ 2 := by
    norm_num [Jx, Jy, Jz, lever, thrust2weight, grav, mass, kmkf, km, kf, h]
  calc _ ≤ ((Jx + Jy + Jz) * 1 ^ 2 + ((2 * lever * (thrust2weight * grav * mass / 4)) ^ 2 / Jx +
      (2 * lever * (thrust2weight * grav * mass / 4)) ^ 2 / Jy +
      (2 * kmkf * (thrust2weight * grav * mass / 4)) ^ 2 / Jz) * h ^ 2) * 2.7182818286 :=
        mul_le_mul_of_nonneg_left he.le hpos
    _ ≤ _ := by norm_num [Jx, Jy, Jz, lever, thrust2weight, grav, mass, kmkf, km, kf, h]

/-- The rate bound over one period at `W = 1` rad/s under the full torque: `Ω = 2.53` rad/s. -/
theorem wTA_one_alphaMax_le : wTA 1 alphaMax ≤ 253 / 100 := by
  have hw := wB_one_le
  have hw0 : 0 ≤ wB 1 := Real.sqrt_nonneg _
  have : wB 1 ^ 2 ≤ 25 := by nlinarith
  have ha := alphaMax_le_num
  unfold wTA; norm_num [h, gyro] at *; nlinarith

theorem Cd_alphaMax_le : Cd alphaMax (253 / 100) ≤ 857 := by
  refine (Cd_mono alphaMax_pos.le alphaMax_le_num (by norm_num) le_rfl).trans ?_
  rw [Cd, Real.sqrt_le_iff]; norm_num

/-- At `W = 1` rad/s and any actuators: `|r_v| ≤ 4.93·10⁻⁵` m/s per component per tick. -/
example (u : Fin 4 → ℝ) : accel u * Cd alphaMax (253 / 100) * h ^ 3 / 6 ≤ 4.93e-5 := by
  have := accel_le u; have := accel_nonneg u; have := Cd_alphaMax_le
  have := Cd_nonneg alphaMax (253 / 100); have := amax_le_num
  have : accel u * Cd alphaMax (253 / 100) ≤ 22066 / 1000 * 857 := by nlinarith
  norm_num [h] at *; nlinarith

/-- At hover thrust (`a = g`): `|r_v| ≤ 2.19·10⁻⁵` m/s. -/
example : grav * Cd alphaMax (253 / 100) * h ^ 3 / 6 ≤ 2.19e-5 := by
  have := Cd_alphaMax_le; have := Cd_nonneg alphaMax (253 / 100)
  norm_num [h, grav] at *; nlinarith

/-- At `W = 1` rad/s and any actuators: `|r_p| ≤ 3.1·10⁻⁸` m per component per tick. -/
example (u : Fin 4 → ℝ) : accel u * Cd alphaMax (253 / 100) * h ^ 4 / 24 ≤ 3.1e-8 := by
  have := accel_le u; have := accel_nonneg u; have := Cd_alphaMax_le
  have := Cd_nonneg alphaMax (253 / 100); have := amax_le_num
  have : accel u * Cd alphaMax (253 / 100) ≤ 22066 / 1000 * 857 := by nlinarith
  norm_num [h] at *; nlinarith

/-- The full statement at `W = 1` rad/s for any actuators. -/
example {x : X} {u : Fin 4 → ℝ} (hq : qnormSq x = 1) (hW : WBd x 1) (j : Fin 3) :
    |step x u (vI j) - (x (vI j) + h * (grav * ez j - accel u * dn x j) -
        accel u * (h ^ 2 / 2) * dnDot x j)| ≤ 4.93e-5 := by
  refine (step_pv_sharp hq hW (torqueBd_alphaMax u) wTA_one_alphaMax_le j).1.trans ?_
  have := accel_le u; have := accel_nonneg u; have := Cd_alphaMax_le
  have := Cd_nonneg alphaMax (253 / 100); have := amax_le_num
  have : accel u * Cd alphaMax (253 / 100) ≤ 22066 / 1000 * 857 := by nlinarith
  norm_num [h] at *; nlinarith

/-- The attitude Lipschitz constant at `Ω = 2.53`: `Katt = 5.295`. -/
example : Katt (253 / 100) = 5295 / 1000 := by
  norm_num [Katt, gyro]

/-- The attitude block moves by at most `1.511` per period at `W = 1` rad/s (the rates change by up
to `h · alphaMax = 1.49` rad/s under the full torque). -/
example {x : X} {u : Fin 4 → ℝ} (hq : qnormSq x = 1) (hW : WBd x 1) :
    ‖att (step x u) - att x‖ ≤ 1.511 := by
  refine (step_qw_gronwall hq hW (torqueBd_alphaMax u) wTA_one_alphaMax_le).trans ?_
  have hK : Katt (253 / 100) = 5295 / 1000 := by norm_num [Katt, gyro]
  have hF : attF0 1 alphaMax ≤ 59631 / 100 := by
    have := alphaMax_le_num; unfold attF0; rw [max_le_iff]; norm_num [gyro]; linarith
  have hF0 : 0 ≤ attF0 1 alphaMax := le_max_of_le_left (by norm_num)
  have hx : |(5295 / 1000 : ℝ) * h| ≤ 1 := by norm_num [h, abs_of_pos]
  have he := Real.abs_exp_sub_one_sub_id_le hx
  have he' : Real.exp (5295 / 1000 * h) - 1 ≤ 5295 / 1000 * h + (5295 / 1000 * h) ^ 2 := by
    have := (abs_le.mp he).2; linarith
  have he0 : 0 ≤ Real.exp (5295 / 1000 * h) - 1 := by
    have := Real.add_one_le_exp (5295 / 1000 * h); have : (0 : ℝ) ≤ 5295 / 1000 * h := by
      norm_num [h]
    linarith
  rw [hK]
  calc attF0 1 alphaMax / (5295 / 1000) * (Real.exp (5295 / 1000 * h) - 1)
      ≤ 59631 / 100 / (5295 / 1000) * (5295 / 1000 * h + (5295 / 1000 * h) ^ 2) := by
        gcongr
    _ ≤ 1.511 := by norm_num [h]

/-- The second-order attitude constants at `W = 1` rad/s, `Ω = 2.53`, full torque:
`cQ h² / 2 ≤ 2.86·10⁻³`, `cW h² / 2 ≤ 5.22·10⁻³` rad/s. -/
example : cQ alphaMax (253 / 100) * h ^ 2 / 2 ≤ 2.86e-3 ∧
    cW alphaMax (253 / 100) * h ^ 2 / 2 ≤ 5.22e-3 := by
  have := alphaMax_le_num
  simp only [cQ, cW, Mw1, Mq1]
  constructor <;> (norm_num [gyro, h]; linarith)

/-- The intersample position move at `|v| ≤ 1.5` m/s and any actuators: `3.85·10⁻³` m. -/
example (u : Fin 4 → ℝ) : 1.5 * h + (grav + accel u) * h ^ 2 / 2 ≤ 3.85e-3 := by
  have := accel_le u; have := amax_le_num
  norm_num [h, grav] at *; linarith

/-! Under a reduced torque: actuators in `[0.30, 0.62]` (spread `0.32`) give `A = 0.32 alphaMax`
`≤ 190.7`, hence `Ω = 1.52` at `W = 1` and `Cd ≤ 275`; the thrust acceleration is at most
`0.62 amax`, so `|r_v| ≤ 9.8·10⁻⁶` m/s. -/

theorem wTA_one_spread_le : wTA 1 (alphaMax * (32 / 100)) ≤ 152 / 100 := by
  have hw := wB_one_le
  have hw0 : 0 ≤ wB 1 := Real.sqrt_nonneg _
  have : wB 1 ^ 2 ≤ 25 := by nlinarith
  have ha := alphaMax_le_num
  unfold wTA; norm_num [h, gyro] at *; nlinarith

theorem Cd_spread_le : Cd (alphaMax * (32 / 100)) (152 / 100) ≤ 275 := by
  have ha := alphaMax_le_num
  refine (Cd_mono (by have := alphaMax_pos; positivity) (show alphaMax * (32 / 100) ≤ 19065 / 100
    by linarith) (by norm_num) le_rfl).trans ?_
  rw [Cd, Real.sqrt_le_iff]; norm_num

example {x : X} {u : Fin 4 → ℝ} (hq : qnormSq x = 1) (hW : WBd x 1)
    (hu : ∀ i, 30 / 100 ≤ u i ∧ u i ≤ 30 / 100 + 32 / 100) (j : Fin 3) :
    |step x u (vI j) - (x (vI j) + h * (grav * ez j - accel u * dn x j) -
        accel u * (h ^ 2 / 2) * dnDot x j)| ≤ 9.8e-6 := by
  refine (step_pv_sharp hq hW (torqueBd_of_spread (by norm_num) (by norm_num) hu)
    wTA_one_spread_le j).1.trans ?_
  have := accel_le_mul (u := u) (c := 62 / 100) (by norm_num) (fun i => by linarith [(hu i).2])
  have := accel_nonneg u; have := Cd_spread_le
  have := Cd_nonneg (alphaMax * (32 / 100)) (152 / 100); have := amax_le_num
  have : accel u * Cd (alphaMax * (32 / 100)) (152 / 100) ≤ 62 / 100 * (22066 / 1000) * 275 := by
    nlinarith
  norm_num [h] at *; nlinarith

end

end Contracts.Plant
