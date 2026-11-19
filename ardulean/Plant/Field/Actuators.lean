module

public import Plant.Field.Bounds

/-!
# The thrust-to-wrench map and the commands

The map from the four normalized propeller thrusts to the total thrust and the body torques `(T, τx, τy, τz)`
(`wrench`) is the composition of the clip to `[0, 1]⁴` (`clipV`, inactive on the physical range) and a linear map,
the mixer `mix` (`wrench_eq_mix`). With the X500's geometry (motor slots front right CCW, rear left CCW, front left
CW, rear right CW, lever `0.174` m, `km/kf = 0.016` m) the mixer's sign matrix is
```
  T  :  1  1  1  1        (× fmax)
  τx : -1  1  1 -1        (× lever · fmax)
  τy :  1 -1  1 -1        (× lever · fmax)
  τz :  1  1 -1 -1        (× kmkf · fmax)
```
with orthogonal rows of squared length 4, so the mixer is invertible with the explicit inverse `unmix`
(`unmix_mix`, `mix_unmix`), and the set of wrenches the thrusts reach is exactly `{w | unmix w ∈ [0, 1]⁴}`
(`range_wrench`). Thrust is monotone in each propeller (`force_mono`, `thrust_mono`, `accel_mono`); equal thrusts give
zero torque and the thrust acceleration `amax · c` (`torque_const`, `accel_const`), and the hover thrust is
`1 / thrust2weight` (`accel_const_eq_grav_iff`). The thrust acceleration is `amax`-Lipschitz and each angular
acceleration `2 alphaMax`-Lipschitz in the thrusts (sup norm on `Fin 4 → ℝ`, `abs_accel_sub_le`, …).

**The commands** reach the field only through the motor rows: the commanded thrust of slot `i` is `clip01 uᵢ`, and
`‖F(y, u) - F(y, w)‖ ≤ ‖u - w‖ / tauUp` (`norm_vf_sub_input_le`); the rigid body sees a command change only through
the lagged thrusts. Everything here is structural; the facts of the X500 numbers used are `Jy = Jx` and
`kmkf · Jx ≤ lever · Jz` (yaw against roll authority).
-/

@[expose] public section

namespace Plant

noncomputable section

/-! ## Monotonicity of the clip -/

theorem clip01_mono {a b : ℝ} (hab : a ≤ b) : clip01 a ≤ clip01 b :=
  max_le_max le_rfl (min_le_min le_rfl hab)

/-! ## Monotonicity of the thrust -/

/-- **Each motor's force is monotone in its command.** -/
theorem force_mono {u w : Fin 4 → ℝ} {i : Fin 4} (hi : u i ≤ w i) : force u i ≤ force w i :=
  mul_le_mul_of_nonneg_left (clip01_mono hi) fmax_pos.le

/-- **The thrust is monotone in the commands.** -/
theorem thrust_mono {u w : Fin 4 → ℝ} (huw : ∀ i, u i ≤ w i) : thrust u ≤ thrust w := by
  unfold thrust
  have := force_mono (huw 0); have := force_mono (huw 1); have := force_mono (huw 2)
  have := force_mono (huw 3); linarith

/-- The thrust acceleration is monotone in the commands. -/
theorem accel_mono {u w : Fin 4 → ℝ} (huw : ∀ i, u i ≤ w i) : accel u ≤ accel w :=
  div_le_div_of_nonneg_right (thrust_mono huw) mass_pos.le

/-- The thrust acceleration in the clipped commands: `amax / 4` per unit command. -/
theorem accel_eq (u : Fin 4 → ℝ) :
    accel u = amax / 4 * (clip01 (u 0) + clip01 (u 1) + clip01 (u 2) + clip01 (u 3)) := by
  rw [accel, thrust_eq, ← four_fmax_div_mass]; field_simp

/-- The yaw torque in the clipped commands. -/
theorem torqueZ_eq (u : Fin 4 → ℝ) :
    torqueZ u = kmkf * fmax * (clip01 (u 0) + clip01 (u 1) - clip01 (u 2) - clip01 (u 3)) := by
  rw [torqueZ, km_maxRPM_sq]

/-! ## The mixer and its inverse -/

/-- The clipped commands. -/
def clipV (u : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => clip01 (u i)

/-- **The actuator map**: total thrust and the three body torques of the commands. -/
def wrench (u : Fin 4 → ℝ) : Fin 4 → ℝ := ![thrust u, torqueX u, torqueY u, torqueZ u]

/-- **The mixer**: the linear map from thrust fractions to `(T, τx, τy, τz)`. -/
def mix (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![fmax * (c 0 + c 1 + c 2 + c 3), lever * fmax * (-c 0 + c 1 + c 2 - c 3),
    lever * fmax * (c 0 - c 1 + c 2 - c 3), kmkf * fmax * (c 0 + c 1 - c 2 - c 3)]

/-- **The inverse mixer**: the thrust fractions of a wrench. -/
def unmix (w : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let a := w 0 / fmax
  let b := w 1 / (lever * fmax)
  let c := w 2 / (lever * fmax)
  let d := w 3 / (kmkf * fmax)
  ![(a - b + c + d) / 4, (a + b - c + d) / 4, (a + b + c - d) / 4, (a - b - c - d) / 4]

/-- **The actuator map is the mixer of the clipped commands.** -/
theorem wrench_eq_mix (u : Fin 4 → ℝ) : wrench u = mix (clipV u) := by
  funext i
  fin_cases i <;> simp [wrench, mix, clipV, thrust_eq, torqueX, torqueY, torqueZ_eq, force] <;> ring

/-- The mixer is additive. -/
theorem mix_add (c d : Fin 4 → ℝ) : mix (c + d) = mix c + mix d := by
  funext i; fin_cases i <;> simp [mix] <;> ring

/-- The mixer is homogeneous. -/
theorem mix_smul (a : ℝ) (c : Fin 4 → ℝ) : mix (a • c) = a • mix c := by
  funext i; fin_cases i <;> simp [mix] <;> ring

/-- **`unmix` inverts the mixer** (left inverse). -/
theorem unmix_mix (c : Fin 4 → ℝ) : unmix (mix c) = c := by
  have hf := fmax_pos.ne'; have hl := lever_pos.ne'; have hk := kmkf_pos.ne'
  funext i; fin_cases i <;> simp [unmix, mix] <;> field_simp <;> ring

/-- **`unmix` inverts the mixer** (right inverse). -/
theorem mix_unmix (w : Fin 4 → ℝ) : mix (unmix w) = w := by
  have hf := fmax_pos.ne'; have hl := lever_pos.ne'; have hk := kmkf_pos.ne'
  funext i; fin_cases i <;> simp [unmix, mix] <;> field_simp <;> ring

/-- **The commands are determined by the wrench** within `[0, 1]⁴`: `unmix (wrench u)` is the
vector of clipped commands. -/
theorem unmix_wrench (u : Fin 4 → ℝ) : unmix (wrench u) = clipV u := by
  rw [wrench_eq_mix, unmix_mix]

/-- **The exact image of the actuator map**: the wrenches the commands reach are those whose
thrust fractions lie in `[0, 1]⁴`. -/
theorem range_wrench : Set.range wrench = {w | ∀ i, 0 ≤ unmix w i ∧ unmix w i ≤ 1} := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩ i
    rw [unmix_wrench]; exact ⟨clip01_nonneg _, clip01_le_one _⟩
  · intro hw
    refine ⟨unmix w, ?_⟩
    have : clipV (unmix w) = unmix w := funext fun i => clip01_of_mem (hw i).1 (hw i).2
    rw [wrench_eq_mix, this, mix_unmix]

/-! ## Equal commands and hover -/

/-- **Equal commands give zero torque.** -/
theorem torque_const (c : ℝ) :
    torqueX (fun _ => c) = 0 ∧ torqueY (fun _ => c) = 0 ∧ torqueZ (fun _ => c) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [torqueX, torqueY, torqueZ, force] <;> ring

/-- Equal commands `c` give the thrust acceleration `amax · clip01 c`. -/
theorem accel_const (c : ℝ) : accel (fun _ => c) = amax * clip01 c := by
  rw [accel_eq]; ring

/-- **The hover command**: equal commands `c ∈ [0, 1]` balance gravity exactly when
`c = 1 / thrust2weight`. -/
theorem accel_const_eq_grav_iff {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    accel (fun _ => c) = grav ↔ c = 1 / thrust2weight := by
  have ht := thrust2weight_pos
  rw [accel_const, clip01_of_mem h0 h1, amax]
  constructor
  · intro hc; field_simp; nlinarith [grav_pos]
  · intro hc; rw [hc]; field_simp

/-! ## Dependence of the field on the commands -/

/-- One clipped command moves by at most the sup-norm distance of the commands. -/
theorem abs_clip01_sub_le_norm (u w : Fin 4 → ℝ) (i : Fin 4) :
    |clip01 (u i) - clip01 (w i)| ≤ ‖u - w‖ :=
  (abs_clip01_sub_le _ _).trans (by
    rw [← Real.norm_eq_abs, ← Pi.sub_apply]; exact norm_le_pi_norm (u - w) i)

private theorem four_le {u w : Fin 4 → ℝ} :
    (-‖u - w‖ ≤ clip01 (u 0) - clip01 (w 0) ∧ clip01 (u 0) - clip01 (w 0) ≤ ‖u - w‖) ∧
    (-‖u - w‖ ≤ clip01 (u 1) - clip01 (w 1) ∧ clip01 (u 1) - clip01 (w 1) ≤ ‖u - w‖) ∧
    (-‖u - w‖ ≤ clip01 (u 2) - clip01 (w 2) ∧ clip01 (u 2) - clip01 (w 2) ≤ ‖u - w‖) ∧
    (-‖u - w‖ ≤ clip01 (u 3) - clip01 (w 3) ∧ clip01 (u 3) - clip01 (w 3) ≤ ‖u - w‖) :=
  ⟨abs_le.mp (abs_clip01_sub_le_norm u w 0), abs_le.mp (abs_clip01_sub_le_norm u w 1),
    abs_le.mp (abs_clip01_sub_le_norm u w 2), abs_le.mp (abs_clip01_sub_le_norm u w 3)⟩

/-- **The thrust acceleration is `amax`-Lipschitz in the commands.** -/
theorem abs_accel_sub_le (u w : Fin 4 → ℝ) : |accel u - accel w| ≤ amax * ‖u - w‖ := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := four_le (u := u) (w := w)
  have e : accel u - accel w = amax / 4 * ((clip01 (u 0) - clip01 (w 0)) +
      (clip01 (u 1) - clip01 (w 1)) + (clip01 (u 2) - clip01 (w 2)) +
      (clip01 (u 3) - clip01 (w 3))) := by rw [accel_eq, accel_eq]; ring
  have hs : |(clip01 (u 0) - clip01 (w 0)) + (clip01 (u 1) - clip01 (w 1)) +
      (clip01 (u 2) - clip01 (w 2)) + (clip01 (u 3) - clip01 (w 3))| ≤ 4 * ‖u - w‖ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [e, abs_mul, abs_of_pos (by have := amax_pos; positivity)]
  calc amax / 4 * _ ≤ amax / 4 * (4 * ‖u - w‖) :=
        mul_le_mul_of_nonneg_left hs (by have := amax_pos; positivity)
    _ = _ := by ring

/-- **The roll angular acceleration of the torques moves by at most `2 alphaMax ‖u - w‖`.** -/
theorem abs_torqueX_div_sub_le (u w : Fin 4 → ℝ) :
    |torqueX u / Jx - torqueX w / Jx| ≤ 2 * alphaMax * ‖u - w‖ := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := four_le (u := u) (w := w)
  have hc : 0 < lever * fmax / Jx := by have := lever_pos; have := fmax_pos; have := Jx_pos; positivity
  have e : torqueX u / Jx - torqueX w / Jx = lever * fmax / Jx * (-(clip01 (u 0) - clip01 (w 0)) +
      (clip01 (u 1) - clip01 (w 1)) + (clip01 (u 2) - clip01 (w 2)) -
      (clip01 (u 3) - clip01 (w 3))) := by simp only [torqueX, force]; ring
  have hs : |-(clip01 (u 0) - clip01 (w 0)) + (clip01 (u 1) - clip01 (w 1)) +
      (clip01 (u 2) - clip01 (w 2)) - (clip01 (u 3) - clip01 (w 3))| ≤ 4 * ‖u - w‖ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [e, abs_mul, abs_of_pos hc]
  calc lever * fmax / Jx * _ ≤ lever * fmax / Jx * (4 * ‖u - w‖) :=
        mul_le_mul_of_nonneg_left hs hc.le
    _ = _ := by rw [alphaMax]; ring

/-- **The pitch angular acceleration of the torques moves by at most `2 alphaMax ‖u - w‖`.** -/
theorem abs_torqueY_div_sub_le (u w : Fin 4 → ℝ) :
    |torqueY u / Jy - torqueY w / Jy| ≤ 2 * alphaMax * ‖u - w‖ := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := four_le (u := u) (w := w)
  have hc : 0 < lever * fmax / Jy := by have := lever_pos; have := fmax_pos; have := Jy_pos; positivity
  have e : torqueY u / Jy - torqueY w / Jy = lever * fmax / Jy * ((clip01 (u 0) - clip01 (w 0)) -
      (clip01 (u 1) - clip01 (w 1)) + (clip01 (u 2) - clip01 (w 2)) -
      (clip01 (u 3) - clip01 (w 3))) := by simp only [torqueY, force]; ring
  have hs : |(clip01 (u 0) - clip01 (w 0)) - (clip01 (u 1) - clip01 (w 1)) +
      (clip01 (u 2) - clip01 (w 2)) - (clip01 (u 3) - clip01 (w 3))| ≤ 4 * ‖u - w‖ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  rw [e, abs_mul, abs_of_pos hc]
  calc lever * fmax / Jy * _ ≤ lever * fmax / Jy * (4 * ‖u - w‖) :=
        mul_le_mul_of_nonneg_left hs hc.le
    _ = _ := by rw [alphaMax, Jy_eq_Jx]; ring

/-- **The yaw angular acceleration of the torques moves by at most `2 alphaMax ‖u - w‖`.** -/
theorem abs_torqueZ_div_sub_le (u w : Fin 4 → ℝ) :
    |torqueZ u / Jz - torqueZ w / Jz| ≤ 2 * alphaMax * ‖u - w‖ := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩ := four_le (u := u) (w := w)
  have hc : 0 < kmkf * fmax / Jz := by have := kmkf_pos; have := fmax_pos; have := Jz_pos; positivity
  have e : torqueZ u / Jz - torqueZ w / Jz = kmkf * fmax / Jz * ((clip01 (u 0) - clip01 (w 0)) +
      (clip01 (u 1) - clip01 (w 1)) - (clip01 (u 2) - clip01 (w 2)) -
      (clip01 (u 3) - clip01 (w 3))) := by rw [torqueZ_eq, torqueZ_eq]; ring
  have hs : |(clip01 (u 0) - clip01 (w 0)) + (clip01 (u 1) - clip01 (w 1)) -
      (clip01 (u 2) - clip01 (w 2)) - (clip01 (u 3) - clip01 (w 3))| ≤ 4 * ‖u - w‖ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hk : kmkf * fmax / Jz ≤ lever * fmax / Jx := by
    rw [div_le_div_iff₀ Jz_pos Jx_pos]
    have := kmkf_Jx_le_lever_Jz
    nlinarith [fmax_pos]
  rw [e, abs_mul, abs_of_pos hc]
  calc kmkf * fmax / Jz * _ ≤ lever * fmax / Jx * (4 * ‖u - w‖) :=
        mul_le_mul hk hs (abs_nonneg _) (by have := lever_pos; have := fmax_pos; have := Jx_pos; positivity)
    _ = _ := by rw [alphaMax]; ring

/-- **The field is Lipschitz in the commands**: `‖F(y, u) - F(y, w)‖ ≤ ‖u - w‖ / tauUp`. Only the motor rows
depend on the commands. -/
theorem norm_vf_sub_input_le (y : X) (u w : Fin 4 → ℝ) : ‖vf y u - vf y w‖ ≤ ‖u - w‖ / tauUp := by
  have hn := norm_nonneg (u - w)
  have hk : 0 ≤ ‖u - w‖ / tauUp := div_nonneg hn tauUp_pos.le
  have m : ∀ i : Fin 4, ∀ p : ℝ, |lagRate (clip01 (u i)) p - lagRate (clip01 (w i)) p| ≤ ‖u - w‖ / tauUp :=
    fun i p => (abs_lagRate_sub_cmd_le _ _ p).trans
      (div_le_div_of_nonneg_right (abs_clip01_sub_le_norm u w i) tauUp_pos.le)
  refine norm_le_of_abs_le hk fun j => ?_
  simp only [Pi.sub_apply]
  fin_cases j
  all_goals first
    | (simp only [Fin.reduceFinMk, Fin.isValue, vf_0, vf_1, vf_2, vf_3, vf_4, vf_5, vf_6, vf_7, vf_8, vf_9,
        vf_10, vf_11, vf_12, sub_self, abs_zero]; exact hk)
    | exact m _ _

end

end Plant
