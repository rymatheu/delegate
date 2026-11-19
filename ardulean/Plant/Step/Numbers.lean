module

public import Plant.Step.InputSens
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Evaluated constants of the X500

The library's statements carry the model constants symbolically; this file evaluates them with the X500's numbers
(`Plant.Model.Constants`), each as an inequality proved by `norm_num` from the literals, and instantiates the main
per-period bounds at a reference state: rates at most `W = 1` rad/s, any commands (`A = alphaMax`).

| quantity | value |
|---|---|
| `fmax` | 8.54858 N |
| `amax = 4 fmax / m` | 16.5645 m/s² |
| `alphaMax = 2 lever fmax / Jx` | 137.303 rad/s² |
| `gyro = (Jz - Jx)/Jx`, `Jz / Jx` | 0.84615 (11/13), 1.84615 (24/13) |
| `1 - e^{-h/tauUp}` (thrust step response over one period) | 0.18127 |
| `lagM1 tauUp h`, `lagM2 tauUp h`, `lagM3 tauUp h` | 2.341e-4 s, 1.983e-7 s², 1.252e-10 s³ |
| `wB 1`, `wTA 1 alphaMax` (rate bound over a period from 1 rad/s) | 3.331, 1.367 rad/s |
| `Cd alphaMax 1.37` | 199.1 |

**Input sensitivity per unit command error, one period** (`step_input_sens_num`, from `W = 1` rad/s): thrust
`≤ 0.1815` (`≤ 1.552` N), rates `≤ 0.0650` rad/s, quaternion `≤ 8.7e-5`, velocity `≤ 3.91e-3` m/s, position
`≤ 3.48e-6` m. **Sharp translation remainder** (`step_pv_sharp_num`): `|r_v| ≤ 8.63e-6` m/s, `|r_p| ≤ 5.4e-9` m.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set

/-! ## The constants -/

theorem fmax_num : 8.54857 ≤ fmax ∧ fmax ≤ 8.54859 := by
  rw [fmax_eq]; constructor <;> norm_num [thrust2weight, grav, mass]

theorem alphaMax_eq : alphaMax = 2 * lever * (thrust2weight * grav * mass / 4) / Jx := by
  rw [alphaMax, fmax_eq]

theorem alphaMax_num : 137.30 ≤ alphaMax ∧ alphaMax ≤ 137.31 := by
  rw [alphaMax_eq]; constructor <;> norm_num [lever, thrust2weight, grav, mass, Jx]

theorem amax_num : 16.5645 ≤ amax ∧ amax ≤ 16.5646 := by
  constructor <;> norm_num [amax, thrust2weight, grav]

theorem alphaMax_le_num : alphaMax ≤ 137.31 := alphaMax_num.2
theorem alphaMax_ge_num : 137.30 ≤ alphaMax := alphaMax_num.1
theorem amax_le_num : amax ≤ 16.5646 := amax_num.2

theorem gyro_num : gyro ≤ 0.84616 := by norm_num [gyro, Jx, Jz]

theorem JzJx_num : Jz / Jx ≤ 1.84616 := by norm_num [Jx, Jz]

theorem kmkf_num : 0.0159999 ≤ kmkf ∧ kmkf ≤ 0.0160001 := by
  constructor <;> norm_num [kmkf, km, kf]

/-- The hover thrust fraction `1 / thrust2weight`. -/
theorem hover_num : 0.59202 ≤ 1 / thrust2weight ∧ 1 / thrust2weight ≤ 0.59203 := by
  constructor <;> norm_num [thrust2weight]

/-! ## The lag over one period -/

theorem h_div_tauUp : -h / tauUp = -(1 / 5) := by norm_num [h, tauUp]

/-- **The thrust step response over one period**: `1 - e^{-h/tauUp} ∈ [0.1812, 0.1815]`. -/
theorem lagM0_h_num : 0.1812 ≤ lagM0 tauUp h ∧ lagM0 tauUp h ≤ 0.1815 := by
  rw [lagM0, h_div_tauUp]
  obtain ⟨a, b⟩ := exp_neg_fifth
  constructor <;> linarith

theorem lagM1_h_num : 2.31e-4 ≤ lagM1 tauUp h ∧ lagM1 tauUp h ≤ 2.35e-4 := by
  obtain ⟨a, b⟩ := lagM0_h_num
  have e : lagM1 tauUp h = h - tauUp * lagM0 tauUp h := by rw [lagM1, lagM0]
  rw [e]
  generalize lagM0 tauUp h = L at a b ⊢
  constructor <;> norm_num [h, tauUp] <;> linarith

theorem lagM2_h_le : lagM2 tauUp h ≤ 2.0834e-7 :=
  (lagM2_le tauUp_pos h_pos.le).trans (by norm_num [h, tauUp])

theorem lagM3_h_le : lagM3 tauUp h ≤ 1.3021e-10 :=
  (lagM3_le tauUp_pos h_pos.le).trans (by norm_num [h, tauUp])

/-- **One period of the lag in newtons**: a unit command step moves a propeller's thrust by at most
`fmax (1 - e^{-h/tauUp}) ≤ 1.552` N. -/
theorem fmax_lagM0_h_le : fmax * lagM0 tauUp h ≤ 1.552 := by
  obtain ⟨-, b⟩ := lagM0_h_num
  obtain ⟨-, c⟩ := fmax_num
  have := lagM0_nonneg (τ := tauUp) tauUp_pos h_pos.le
  nlinarith [fmax_pos]

/-! ## Rates over one period from `W = 1` rad/s -/

theorem ctau_num : ctau ≤ 819 := by
  have hc : ctau = (2 * lever * (thrust2weight * grav * mass / 4)) ^ 2 / Jx +
      (2 * lever * (thrust2weight * grav * mass / 4)) ^ 2 / Jy +
      (2 * kmkf * (thrust2weight * grav * mass / 4)) ^ 2 / Jz := by rw [ctau, fmax_eq]
  rw [hc]; norm_num [lever, thrust2weight, grav, mass, Jx, Jy, Jz, kmkf, km, kf]

/-- `wB 1 ≤ 3.34`: the energy box of one period from rates at most `1` rad/s. -/
theorem wB_one_le : wB 1 ≤ 3.34 := by
  rw [wB, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have he := Real.exp_one_lt_d9
  have hc := ctau_num
  have hc0 := ctau_nonneg
  have hJ : Jx + Jy + Jz = 0.08333333333333335 := by norm_num [Jx, Jy, Jz]
  rw [hJ, div_le_iff₀ Jx_pos]
  have : ((0.08333333333333335 : ℝ) * 1 ^ 2 + ctau * h ^ 2) * Real.exp 1 ≤
      ((0.08333333333333335 : ℝ) * 1 ^ 2 + 819 * h ^ 2) * 2.7182818286 := by
    apply mul_le_mul _ he.le (Real.exp_pos 1).le (by norm_num [h])
    have : ctau * h ^ 2 ≤ 819 * h ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg h)
    linarith
  refine this.trans ?_
  norm_num [h, Jx]

/-- The rate bound over one period at `W = 1` rad/s under the full torque: `Ω = 1.37` rad/s. -/
theorem wTA_one_alphaMax_le : wTA 1 alphaMax ≤ 137 / 100 := by
  have hw := wB_one_le
  have hw0 : 0 ≤ wB 1 := Real.sqrt_nonneg _
  have : wB 1 ^ 2 ≤ 3.34 ^ 2 := by nlinarith
  have ha := alphaMax_num.2
  have hg := gyro_num
  have hg0 := gyro_nonneg
  have : gyro * wB 1 ^ 2 ≤ 0.84616 * 3.34 ^ 2 := mul_le_mul hg this (sq_nonneg _) (by norm_num)
  unfold wTA; norm_num [h] at *; nlinarith

/-! ## The exponential factors -/

private theorem exp_le_quad {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le (x := y) (by rw [abs_of_nonneg h0]; exact h1)
  have := (abs_le.mp this).2
  linarith

theorem expKw_num : Real.exp (2 * gyro * (137 / 100) * h) ≤ 1.00584 := by
  have hg := gyro_num; have hg0 := gyro_nonneg
  have hy : 2 * gyro * (137 / 100) * h ≤ 0.0057962 := by norm_num [h]; nlinarith
  have hy0 : 0 ≤ 2 * gyro * (137 / 100) * h := by have := h_pos; positivity
  refine (exp_le_quad hy0 (by linarith)).trans ?_
  nlinarith

theorem expKq_num : Real.exp ((3 / 2 + 2 * gyro) * (137 / 100) * h) ≤ 1.01106 := by
  have hg := gyro_num; have hg0 := gyro_nonneg
  have hy : (3 / 2 + 2 * gyro) * (137 / 100) * h ≤ 0.010934 := by norm_num [h]; nlinarith
  have hy0 : 0 ≤ (3 / 2 + 2 * gyro) * (137 / 100) * h := by have := h_pos; positivity
  refine (exp_le_quad hy0 (by linarith)).trans ?_
  nlinarith

/-! ## The input sensitivity per unit command error -/

theorem sensW_num (δ : ℝ) (hδ : 0 ≤ δ) : sensW (137 / 100) δ h ≤ 0.0650 * δ := by
  unfold sensW
  have ha := alphaMax_num.2; have ha0 := alphaMax_pos
  have hm := lagM1_h_num.2; have hm0 := lagM1_nonneg (τ := tauUp) tauUp_pos h_pos.le
  have he := expKw_num; have he0 := Real.exp_pos (2 * gyro * (137 / 100) * h)
  have : alphaMax * lagM1 tauUp h * Real.exp (2 * gyro * (137 / 100) * h) ≤ 137.31 * 2.35e-4 * 1.00584 := by
    apply mul_le_mul (mul_le_mul ha hm hm0 (by norm_num)) he he0.le (by norm_num)
  nlinarith

theorem sensQ_num (δ : ℝ) (hδ : 0 ≤ δ) : sensQ (137 / 100) δ h ≤ 8.7e-5 * δ := by
  unfold sensQ
  have ha := alphaMax_num.2; have ha0 := alphaMax_pos
  have hm := lagM2_h_le; have hm0 := lagM2_nonneg (τ := tauUp) tauUp_pos h_pos.le
  have he := expKq_num; have he0 := Real.exp_pos ((3 / 2 + 2 * gyro) * (137 / 100) * h)
  have : alphaMax * lagM2 tauUp h * Real.exp ((3 / 2 + 2 * gyro) * (137 / 100) * h) ≤
      137.31 * 2.0834e-7 * 1.01106 := by
    apply mul_le_mul (mul_le_mul ha hm hm0 (by norm_num)) he he0.le (by norm_num)
  nlinarith

theorem sensV_num (δ : ℝ) (hδ : 0 ≤ δ) : sensV (137 / 100) δ h ≤ 3.91e-3 * δ := by
  unfold sensV
  have ha := alphaMax_num.2; have ha0 := alphaMax_pos
  have hA := amax_num.2; have hA0 := amax_pos
  have hm1 := lagM1_h_num.2; have hm10 := lagM1_nonneg (τ := tauUp) tauUp_pos h_pos.le
  have hm := lagM3_h_le; have hm0 := lagM3_nonneg (τ := tauUp) tauUp_pos h_pos.le
  have he := expKq_num; have he0 := Real.exp_pos ((3 / 2 + 2 * gyro) * (137 / 100) * h)
  have h1 : alphaMax * lagM3 tauUp h * Real.exp ((3 / 2 + 2 * gyro) * (137 / 100) * h) ≤
      137.31 * 1.3021e-10 * 1.01106 := by
    apply mul_le_mul (mul_le_mul ha hm hm0 (by norm_num)) he he0.le (by norm_num)
  have h2 : lagM1 tauUp h + 24 * alphaMax * lagM3 tauUp h *
      Real.exp ((3 / 2 + 2 * gyro) * (137 / 100) * h) ≤ 2.35e-4 + 24 * (137.31 * 1.3021e-10 * 1.01106) := by
    nlinarith
  have h3 : 0 ≤ lagM1 tauUp h + 24 * alphaMax * lagM3 tauUp h *
      Real.exp ((3 / 2 + 2 * gyro) * (137 / 100) * h) := by positivity
  have := mul_le_mul hA h2 h3 (by norm_num)
  nlinarith

theorem sensP_num (δ : ℝ) (hδ : 0 ≤ δ) : sensP (137 / 100) δ h ≤ 3.48e-6 * δ := by
  unfold sensP
  have ha := alphaMax_num.2; have ha0 := alphaMax_pos
  have hA := amax_num.2; have hA0 := amax_pos
  have hm2 := lagM2_h_le; have hm20 := lagM2_nonneg (τ := tauUp) tauUp_pos h_pos.le
  have hm := lagM3_h_le; have hm0 := lagM3_nonneg (τ := tauUp) tauUp_pos h_pos.le
  have he := expKq_num; have he0 := Real.exp_pos ((3 / 2 + 2 * gyro) * (137 / 100) * h)
  have hh : h = 0.0025 := by norm_num [h]
  have h1 : alphaMax * (h * lagM3 tauUp h) * Real.exp ((3 / 2 + 2 * gyro) * (137 / 100) * h) ≤
      137.31 * (0.0025 * 1.3021e-10) * 1.01106 := by
    apply mul_le_mul (mul_le_mul ha (mul_le_mul (le_of_eq hh) hm hm0 (by norm_num))
      (by have := h_pos; positivity) (by norm_num)) he he0.le (by norm_num)
  have h2 : lagM2 tauUp h + 24 * alphaMax * (h * lagM3 tauUp h) *
      Real.exp ((3 / 2 + 2 * gyro) * (137 / 100) * h) ≤
      2.0834e-7 + 24 * (137.31 * (0.0025 * 1.3021e-10) * 1.01106) := by nlinarith
  have h3 : 0 ≤ lagM2 tauUp h + 24 * alphaMax * (h * lagM3 tauUp h) *
      Real.exp ((3 / 2 + 2 * gyro) * (137 / 100) * h) := by have := h_pos; positivity
  have := mul_le_mul hA h2 h3 (by norm_num)
  nlinarith

/-- **The sharp input sensitivity of the X500 over one period**, from a unit quaternion, rates at most `1` rad/s
and thrusts in `[0, 1]⁴`, per unit command error `δ = ‖u - w‖`: thrusts `≤ 0.1815 δ`, rates `≤ 0.0650 δ` rad/s,
quaternion `≤ 8.7e-5 δ`, velocity `≤ 3.91e-3 δ` m/s, position `≤ 3.48e-6 δ` m. -/
theorem step_input_sens_num {x : X} {u w : Fin 4 → ℝ} (hq : qnormSq x = 1) (hW : WBd x 1) :
    FBd (step x u - step x w) (0.1815 * ‖u - w‖) ∧
      ‖rates (step x u) - rates (step x w)‖ ≤ 0.0650 * ‖u - w‖ ∧
      ‖quat (step x u) - quat (step x w)‖ ≤ 8.7e-5 * ‖u - w‖ ∧
      (∀ j : Fin 3, |step x u (vI j) - step x w (vI j)| ≤ 3.91e-3 * ‖u - w‖) ∧
      (∀ j : Fin 3, |step x u (pI j) - step x w (pI j)| ≤ 3.48e-6 * ‖u - w‖) := by
  obtain ⟨hf, hr, hqq, hv, hp⟩ := step_input_sens (u := u) (w := w) hq hW wTA_one_alphaMax_le
  have hδ := norm_nonneg (u - w)
  have hm : lagM0 tauUp h * ‖u - w‖ ≤ 0.1815 * ‖u - w‖ := mul_le_mul_of_nonneg_right lagM0_h_num.2 hδ
  obtain ⟨a, b, c, d⟩ := hf
  exact ⟨⟨a.trans hm, b.trans hm, c.trans hm, d.trans hm⟩, hr.trans (sensW_num _ hδ),
    hqq.trans (sensQ_num _ hδ), fun j => (hv j).trans (sensV_num _ hδ), fun j => (hp j).trans (sensP_num _ hδ)⟩

/-! ## The sharp translation step -/

theorem Cd_alphaMax_le : Cd alphaMax (137 / 100) ≤ 200 := by
  have ha := alphaMax_num.2
  have hJ := JzJx_num
  have hJ0 := JzJx_pos
  unfold Cd
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have h1 : alphaMax + Jz / Jx * (137 / 100) ^ 2 ≤ 137.31 + 1.84616 * (137 / 100) ^ 2 := by nlinarith
  have h0 : 0 ≤ alphaMax + Jz / Jx * (137 / 100) ^ 2 := by have := alphaMax_pos; positivity
  have := mul_le_mul h1 h1 h0 (by norm_num)
  nlinarith

/-- **The sharp step of the translation block for the X500** at `W = 1` rad/s, any commands, thrusts in
`[0, 1]⁴`: the velocity rows are within `8.63e-6` m/s and the position rows within `5.4e-9` m of the expansion with
the lagged thrust in closed form. -/
theorem step_pv_sharp_num {x : X} {u : Fin 4 → ℝ} (hq : qnormSq x = 1) (hW : WBd x 1) (hf : ThrustRange x)
    (j : Fin 3) :
    |step x u (vI j) - (x (vI j) + h * (grav * ez j) - accK1 x u h * dn x j - accK2 x u h * dnDot x j)|
      ≤ 8.63e-6 ∧
    |step x u (pI j) - (x (pI j) + h * x (vI j) + h ^ 2 / 2 * (grav * ez j) - accK3 x u h * dn x j -
        accK4 x u h * dnDot x j)| ≤ 5.4e-9 := by
  obtain ⟨a, b⟩ := step_pv_sharp hq hW (torqueBdT_alphaMax x u) hf wTA_one_alphaMax_le j
  have hC := Cd_alphaMax_le; have hC0 := Cd_nonneg alphaMax (137 / 100)
  have hA := amax_num.2; have hA0 := amax_pos
  have : amax * Cd alphaMax (137 / 100) ≤ 16.5646 * 200 := mul_le_mul hA hC hC0 (by norm_num)
  constructor
  · refine a.trans ?_; norm_num [h]; nlinarith
  · refine b.trans ?_; norm_num [h]; nlinarith

/-! Under a reduced torque: thrusts and commands in `[0.30, 0.62]` (spread `0.32`) give `A = 0.32 alphaMax ≤ 43.94`
along the period (`torqueBdT_of_spread`), hence `Ω = 1.14` at `W = 1` and `Cd ≤ 66`, so `|r_v| ≤ 2.86e-6` m/s. -/

theorem wTA_one_spread_le : wTA 1 (alphaMax * (32 / 100)) ≤ 114 / 100 := by
  have hw := wB_one_le
  have hw0 : 0 ≤ wB 1 := Real.sqrt_nonneg _
  have : wB 1 ^ 2 ≤ 3.34 ^ 2 := by nlinarith
  have ha := alphaMax_num.2
  have hg := gyro_num
  have hg0 := gyro_nonneg
  have : gyro * wB 1 ^ 2 ≤ 0.84616 * 3.34 ^ 2 := mul_le_mul hg this (sq_nonneg _) (by norm_num)
  unfold wTA; norm_num [h] at *; nlinarith

theorem Cd_spread_le : Cd (alphaMax * (32 / 100)) (114 / 100) ≤ 66 := by
  have ha := alphaMax_num.2
  have hJ := JzJx_num
  have hJ0 := JzJx_pos
  unfold Cd
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have h1 : alphaMax * (32 / 100) + Jz / Jx * (114 / 100) ^ 2 ≤ 137.31 * (32 / 100) + 1.84616 * (114 / 100) ^ 2 := by
    nlinarith
  have h0 : 0 ≤ alphaMax * (32 / 100) + Jz / Jx * (114 / 100) ^ 2 := by have := alphaMax_pos; positivity
  have := mul_le_mul h1 h1 h0 (by norm_num)
  nlinarith

/-- The sharp velocity rows under the reduced torque: `|r_v| ≤ 2.86e-6` m/s. -/
theorem step_pv_sharp_spread_num {x : X} {u : Fin 4 → ℝ} (hq : qnormSq x = 1) (hW : WBd x 1)
    (hf : ThrustRange x) (hx : ∀ i, 30 / 100 ≤ thr x i ∧ thr x i ≤ 30 / 100 + 32 / 100)
    (hu : ∀ i, 30 / 100 ≤ u i ∧ u i ≤ 30 / 100 + 32 / 100) (j : Fin 3) :
    |step x u (vI j) - (x (vI j) + h * (grav * ez j) - accK1 x u h * dn x j - accK2 x u h * dnDot x j)|
      ≤ 2.86e-6 := by
  refine (step_pv_sharp hq hW (torqueBdT_of_spread (by norm_num) (by norm_num) hx hu) hf
    wTA_one_spread_le j).1.trans ?_
  have hC := Cd_spread_le; have hC0 := Cd_nonneg (alphaMax * (32 / 100)) (114 / 100)
  have hA := amax_num.2; have hA0 := amax_pos
  have : amax * Cd (alphaMax * (32 / 100)) (114 / 100) ≤ 16.5646 * 66 := mul_le_mul hA hC hC0 (by norm_num)
  norm_num [h]; nlinarith

/-- The attitude Lipschitz constant at `Ω = 1.37`: `Katt = 3.555`. -/
theorem Katt_num : Katt (137 / 100) = 3.555 := by
  have hg := gyro_num; have hg0 := gyro_nonneg
  unfold Katt
  rw [max_eq_left (by nlinarith)]; norm_num

/-- The intersample position move at `|v| ≤ 1.5` m/s and any commands: `3.84e-3` m per period. -/
theorem pos_move_num : 1.5 * h + (grav + amax) * h ^ 2 / 2 ≤ 3.84e-3 := by
  have := amax_num.2
  norm_num [h, grav]; linarith

end

end Plant
