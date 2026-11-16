module

public import Plant.Field.Bounds

/-!
# The actuator map

The map from the four held commands to the thrust and the body torques `(T, τx, τy, τz)`
(`wrench`) is the composition of the clip to `[0, 1]⁴` (`clipV`) and a linear map, the mixer
`mix` (`wrench_eq_mix`). The mixer's sign matrix
```
  T  :  1  1  1  1        (× fmax)
  τx : -1  1  1 -1        (× lever · fmax)
  τy :  1 -1  1 -1        (× lever · fmax)
  τz :  1  1 -1 -1        (× kmkf · fmax)
```
has orthogonal rows of squared length 4, so the mixer is invertible with the explicit inverse
`unmix` (`unmix_mix`, `mix_unmix`), and the set of wrenches the commands reach is exactly
`{w | unmix w ∈ [0, 1]⁴}` (`range_wrench`). Thrust is monotone in each command
(`force_mono`, `thrust_mono`, `accel_mono`); equal commands give zero torque and the thrust
acceleration `amax · c` (`torque_const`, `accel_const`), and the hover command is
`1 / thrust2weight` (`accel_const_eq_grav_iff`).

The field depends on the commands through `accel` and the torques only, and both are Lipschitz in
the commands (sup norm on `Fin 4 → ℝ`): `|accel u - accel w| ≤ amax ‖u - w‖`, each angular
acceleration of the torques moves by at most `2 alphaMax ‖u - w‖`, and hence
`‖F(y, u) - F(y, w)‖ ≤ Kin Q ‖u - w‖` when `‖q‖² ≤ Q` (`norm_vf_sub_input_le`). Everything here is
structural; the only fact of the CF2X numbers used is `kmkf · Jx ≤ lever · Jz` (yaw against roll
authority), through `abs_torqueZ_div_le`'s argument.
-/

@[expose] public section

namespace Plant

noncomputable section

/-! ## Monotonicity and Lipschitz continuity of the clip -/

theorem clip01_mono {a b : ℝ} (hab : a ≤ b) : clip01 a ≤ clip01 b :=
  max_le_max le_rfl (min_le_min le_rfl hab)

/-- The clip is 1-Lipschitz. -/
theorem abs_clip01_sub_le (a b : ℝ) : |clip01 a - clip01 b| ≤ |a - b| := by
  unfold clip01
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [min_comm 1, min_comm 1]
  have := abs_min_sub_min_le_max a 1 b 1
  simpa using this

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
  have ht : 0 < thrust2weight := by norm_num [thrust2weight]
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
    have : kmkf * Jx ≤ lever * Jz := by norm_num [kmkf, km, kf, Jx, lever, Jz]
    nlinarith [fmax_pos]
  rw [e, abs_mul, abs_of_pos hc]
  calc kmkf * fmax / Jz * _ ≤ lever * fmax / Jx * (4 * ‖u - w‖) :=
        mul_le_mul hk hs (abs_nonneg _) (by have := lever_pos; have := fmax_pos; have := Jx_pos; positivity)
    _ = _ := by rw [alphaMax]; ring

/-- The input constant of the field at `‖q‖² ≤ Q`: `max (amax Q) (2 alphaMax)`. -/
def Kin (Q : ℝ) : ℝ := max (amax * Q) (2 * alphaMax)

theorem Kin_nonneg (Q : ℝ) : 0 ≤ Kin Q := le_max_of_le_right (by have := alphaMax_pos; positivity)

/-- **The field is Lipschitz in the commands**: at a state with `‖q‖² ≤ Q`,
`‖F(y, u) - F(y, w)‖ ≤ Kin Q · ‖u - w‖`. Only the velocity rows (through the thrust) and the rate
rows (through the torques) depend on the commands. -/
theorem norm_vf_sub_input_le (y : X) (u w : Fin 4 → ℝ) {Q : ℝ} (hQ : qnormSq y ≤ Q) :
    ‖vf y u - vf y w‖ ≤ Kin Q * ‖u - w‖ := by
  have hn := norm_nonneg (u - w)
  have hK := Kin_nonneg Q
  obtain ⟨d3, d4, d5⟩ := abs_down_le y
  have ha := abs_accel_sub_le u w
  have kq : amax * ‖u - w‖ * qnormSq y ≤ Kin Q * ‖u - w‖ := by
    have : amax * qnormSq y ≤ Kin Q :=
      (mul_le_mul_of_nonneg_left hQ amax_pos.le).trans (le_max_left _ _)
    nlinarith
  have kw : 2 * alphaMax * ‖u - w‖ ≤ Kin Q * ‖u - w‖ :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hn
  have vrow : ∀ D : ℝ, |D| ≤ qnormSq y →
      |-(accel u) * D - -(accel w) * D| ≤ Kin Q * ‖u - w‖ := fun D hD => by
    have e : -(accel u) * D - -(accel w) * D = -((accel u - accel w) * D) := by ring
    rw [e, abs_neg, abs_mul]
    calc |accel u - accel w| * |D| ≤ amax * ‖u - w‖ * qnormSq y :=
          mul_le_mul ha hD (abs_nonneg _) (by have := amax_pos; positivity)
      _ ≤ _ := kq
  have z : |(0 : ℝ)| ≤ Kin Q * ‖u - w‖ := by rw [abs_zero]; positivity
  have r5 : |vf y u 5 - vf y w 5| ≤ Kin Q * ‖u - w‖ := by
    rw [vf_5, vf_5]
    have := vrow _ d5
    rwa [show grav + -accel u * (y 6 * y 6 - y 7 * y 7 - y 8 * y 8 + y 9 * y 9) -
      (grav + -accel w * (y 6 * y 6 - y 7 * y 7 - y 8 * y 8 + y 9 * y 9)) =
      -accel u * (y 6 * y 6 - y 7 * y 7 - y 8 * y 8 + y 9 * y 9) -
      -accel w * (y 6 * y 6 - y 7 * y 7 - y 8 * y 8 + y 9 * y 9) by ring]
  have r10 : |vf y u 10 - vf y w 10| ≤ Kin Q * ‖u - w‖ := by
    rw [vf_10, vf_10, show (torqueX u - (y 11 * (Jz * y 12) - y 12 * (Jy * y 11))) / Jx -
      (torqueX w - (y 11 * (Jz * y 12) - y 12 * (Jy * y 11))) / Jx =
      torqueX u / Jx - torqueX w / Jx by ring]
    exact (abs_torqueX_div_sub_le u w).trans kw
  have r11 : |vf y u 11 - vf y w 11| ≤ Kin Q * ‖u - w‖ := by
    rw [vf_11, vf_11, show (torqueY u - (y 12 * (Jx * y 10) - y 10 * (Jz * y 12))) / Jy -
      (torqueY w - (y 12 * (Jx * y 10) - y 10 * (Jz * y 12))) / Jy =
      torqueY u / Jy - torqueY w / Jy by ring]
    exact (abs_torqueY_div_sub_le u w).trans kw
  have r12 : |vf y u 12 - vf y w 12| ≤ Kin Q * ‖u - w‖ := by
    rw [vf_12, vf_12, show (torqueZ u - (y 10 * (Jy * y 11) - y 11 * (Jx * y 10))) / Jz -
      (torqueZ w - (y 10 * (Jy * y 11) - y 11 * (Jx * y 10))) / Jz =
      torqueZ u / Jz - torqueZ w / Jz by ring]
    exact (abs_torqueZ_div_sub_le u w).trans kw
  have r3 : |vf y u 3 - vf y w 3| ≤ Kin Q * ‖u - w‖ := by rw [vf_3, vf_3]; exact vrow _ d3
  have r4 : |vf y u 4 - vf y w 4| ≤ Kin Q * ‖u - w‖ := by rw [vf_4, vf_4]; exact vrow _ d4
  have r0 : |vf y u 0 - vf y w 0| ≤ Kin Q * ‖u - w‖ := by rw [vf_0, vf_0, sub_self]; exact z
  have r1 : |vf y u 1 - vf y w 1| ≤ Kin Q * ‖u - w‖ := by rw [vf_1, vf_1, sub_self]; exact z
  have r2 : |vf y u 2 - vf y w 2| ≤ Kin Q * ‖u - w‖ := by rw [vf_2, vf_2, sub_self]; exact z
  have r6 : |vf y u 6 - vf y w 6| ≤ Kin Q * ‖u - w‖ := by rw [vf_6, vf_6, sub_self]; exact z
  have r7 : |vf y u 7 - vf y w 7| ≤ Kin Q * ‖u - w‖ := by rw [vf_7, vf_7, sub_self]; exact z
  have r8 : |vf y u 8 - vf y w 8| ≤ Kin Q * ‖u - w‖ := by rw [vf_8, vf_8, sub_self]; exact z
  have r9 : |vf y u 9 - vf y w 9| ≤ Kin Q * ‖u - w‖ := by rw [vf_9, vf_9, sub_self]; exact z
  refine norm_le_of_abs_le (by positivity) fun j => ?_
  simp only [Pi.sub_apply]
  fin_cases j
  exacts [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12]

end

end Plant
