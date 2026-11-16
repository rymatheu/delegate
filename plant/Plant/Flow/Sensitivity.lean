module

public import Plant.Flow.Flow
public import Plant.Field.Actuators

/-!
# Sensitivity of the step to the initial state and to the held input

Two trajectories over one period, from `x` under `u` and from `y` under `w`, with `‖x‖, ‖y‖ ≤ r`,
stay in the ball of radius `box r`, where `F(·, u)` is `Klip (box r)`-Lipschitz
(`vf_lipschitz_ball`), and the field moves with the input by at most `Kin Q ‖u - w‖` on states with
`‖q‖² ≤ Q` (`norm_vf_sub_input_le`; `‖q‖²` is constant along a trajectory). Grönwall's inequality
gives, for `t ∈ [0, h]` (`norm_traj_sub_traj_le`),
```
‖Φ_u(t, x) - Φ_w(t, y)‖ ≤ gronwallBound ‖x - y‖ K (Kin (‖q_y‖²) ‖u - w‖) t
                       = ‖x - y‖ e^{K t} + Kin ‖u - w‖ (e^{K t} - 1) / K,     K = Klip (box r).
```
At `t = h` this is the joint Lipschitz bound of the step (`norm_step_sub_step_le_exp`); with
`x = y` it turns an actuator error into a state error (`norm_step_sub_input_le`), and with `u = w`
the step is `e^{K h}`-Lipschitz on the ball (`step_lipschitzOnWith`). Consequences: the step is
continuous in the state (`continuous_step`) and jointly in the state and the input
(`continuous_step_uncurry`). No CF2X number enters the statements.
-/

@[expose] public section

namespace Plant

noncomputable section

open Set Metric

/-- **Joint Grönwall bound over one period**, in the initial state and the held input. -/
theorem norm_traj_sub_traj_le {x y : X} {u w : Fin 4 → ℝ} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ∀ t ∈ Icc 0 h, ‖traj x u t - traj y w t‖ ≤
      gronwallBound ‖x - y‖ (Klip (box r)) (Kin (qnormSq y) * ‖u - w‖) t := by
  intro t ht
  have hR : box ‖x‖ ≤ box r := box_mono (norm_nonneg x) hx
  have hR' : box ‖y‖ ≤ box r := box_mono (norm_nonneg y) hy
  have := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => traj x u t - traj y w t)
    (f' := fun t => vf (traj x u t) u - vf (traj y w t) w) (δ := ‖x - y‖) (K := Klip (box r))
    (ε := Kin (qnormSq y) * ‖u - w‖) (a := 0) (b := h)
    ((traj_continuousOn x u).sub (traj_continuousOn y w))
    (fun s hs => ((traj_hasDerivAt x u s (Ico_subset_Icc_self hs)).sub
      (traj_hasDerivAt y w s (Ico_subset_Icc_self hs))).hasDerivWithinAt)
    (by simp [traj_zero])
    (fun s hs => by
      have hs' := Ico_subset_Icc_self hs
      have h1 := vf_lipschitz_ball u ((traj_norm_le x u s hs').trans hR)
        ((traj_norm_le y w s hs').trans hR')
      have h2 := norm_vf_sub_input_le (traj y w s) u w (le_of_eq (qnormSq_traj y w s hs'))
      calc ‖vf (traj x u s) u - vf (traj y w s) w‖ =
            ‖(vf (traj x u s) u - vf (traj y w s) u) + (vf (traj y w s) u - vf (traj y w s) w)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := add_le_add h1 h2) t ht
  simpa using this

/-- **Joint sensitivity of the step**: `‖step x u - step y w‖ ≤ gronwallBound ‖x - y‖ K ε h`. -/
theorem norm_step_sub_step_le {x y : X} {u w : Fin 4 → ℝ} {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖step x u - step y w‖ ≤
      gronwallBound ‖x - y‖ (Klip (box r)) (Kin (qnormSq y) * ‖u - w‖) h :=
  norm_traj_sub_traj_le hx hy h ⟨h_pos.le, le_rfl⟩

/-- **Joint sensitivity of the step, written out**:
`‖step x u - step y w‖ ≤ ‖x - y‖ e^{K h} + Kin (‖q_y‖²) ‖u - w‖ (e^{K h} - 1) / K`,
`K = Klip (box r)`, for `‖x‖, ‖y‖ ≤ r`. -/
theorem norm_step_sub_step_le_exp {x y : X} {u w : Fin 4 → ℝ} {r : ℝ} (hx : ‖x‖ ≤ r)
    (hy : ‖y‖ ≤ r) :
    ‖step x u - step y w‖ ≤ ‖x - y‖ * Real.exp (Klip (box r) * h) +
      Kin (qnormSq y) * ‖u - w‖ / Klip (box r) * (Real.exp (Klip (box r) * h) - 1) := by
  have hr : 0 ≤ r := (norm_nonneg x).trans hx
  have := norm_step_sub_step_le (u := u) (w := w) hx hy
  rwa [gronwallBound_of_K_ne_0 (Klip_pos (box_nonneg hr)).ne'] at this

/-- **An input error becomes a state error**: from the same state, two held inputs give steps at
most `Kin (‖q‖²) ‖u - w‖ (e^{K h} - 1) / K` apart, `K = Klip (box ‖x‖)`. -/
theorem norm_step_sub_input_le (x : X) (u w : Fin 4 → ℝ) :
    ‖step x u - step x w‖ ≤
      Kin (qnormSq x) * ‖u - w‖ / Klip (box ‖x‖) * (Real.exp (Klip (box ‖x‖) * h) - 1) := by
  have := norm_step_sub_step_le_exp (u := u) (w := w) (le_refl ‖x‖) (le_refl ‖x‖)
  simpa using this

/-- The input sensitivity through the crude factor `h e^{K h}`:
`‖step x u - step x w‖ ≤ Kin (‖q‖²) h e^{K h} ‖u - w‖`. -/
theorem norm_step_sub_input_le_mul (x : X) (u w : Fin 4 → ℝ) :
    ‖step x u - step x w‖ ≤
      Kin (qnormSq x) * h * Real.exp (Klip (box ‖x‖) * h) * ‖u - w‖ := by
  refine (norm_step_sub_input_le x u w).trans ?_
  set K := Klip (box ‖x‖)
  have hK : 0 < K := Klip_pos (box_nonneg (norm_nonneg x))
  have hkin := Kin_nonneg (qnormSq x)
  have hn := norm_nonneg (u - w)
  -- e^{K h} - 1 ≤ K h e^{K h}
  have he : Real.exp (K * h) - 1 ≤ K * h * Real.exp (K * h) := by
    have := Real.add_one_le_exp (-(K * h))
    have hpos := Real.exp_pos (K * h)
    have e : Real.exp (-(K * h)) * Real.exp (K * h) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  calc Kin (qnormSq x) * ‖u - w‖ / K * (Real.exp (K * h) - 1)
      ≤ Kin (qnormSq x) * ‖u - w‖ / K * (K * h * Real.exp (K * h)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by field_simp

/-- **The step is Lipschitz in the state** on the ball of radius `r`:
`‖step x u - step y u‖ ≤ e^{K h} ‖x - y‖`, `K = Klip (box r)`. -/
theorem norm_step_sub_state_le {x y : X} (u : Fin 4 → ℝ) {r : ℝ} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖step x u - step y u‖ ≤ Real.exp (Klip (box r) * h) * ‖x - y‖ := by
  have := norm_step_sub_step_le (u := u) (w := u) hx hy
  rw [sub_self, norm_zero, mul_zero, gronwallBound_ε0] at this
  linarith

/-- The step is `e^{K h}`-Lipschitz on the closed ball of radius `r` (`K = Klip (box r)`). -/
theorem step_lipschitzOnWith (u : Fin 4 → ℝ) (r : ℝ) :
    LipschitzOnWith (Real.toNNReal (Real.exp (Klip (box r) * h))) (fun x => step x u)
      (closedBall 0 r) := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le]
  exact norm_step_sub_state_le u (mem_closedBall_zero_iff.1 ha) (mem_closedBall_zero_iff.1 hb)

/-- **The step is continuous in the state.** -/
theorem continuous_step (u : Fin 4 → ℝ) : Continuous (fun x => step x u) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  refine (step_lipschitzOnWith u (‖x‖ + 1)).continuousOn.continuousAt ?_
  refine Filter.mem_of_superset (ball_mem_nhds x one_pos) fun y hy => ?_
  rw [mem_ball, dist_eq_norm] at hy
  rw [mem_closedBall_zero_iff]
  have := norm_sub_norm_le y x
  linarith

/-- **The step is jointly continuous in the state and the held input.** -/
theorem continuous_step_uncurry : Continuous (fun p : X × (Fin 4 → ℝ) => step p.1 p.2) := by
  refine continuous_iff_continuousAt.2 fun ⟨x, u⟩ => ?_
  set r := ‖x‖ + 1
  set K := Klip (box r)
  set E := Real.exp (K * h)
  set C := Kin (qnormSq x) / K * (E - 1)
  have hK : 0 < K := Klip_pos (box_nonneg (by positivity))
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hg : Continuous fun p : X × (Fin 4 → ℝ) => ‖p.1 - x‖ * E + C * ‖p.2 - u‖ := by fun_prop
  have hg0 := hg.tendsto (x, u)
  simp only [sub_self, norm_zero, zero_mul, mul_zero, add_zero] at hg0
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hg0
  have hnb : ∀ᶠ p : X × (Fin 4 → ℝ) in nhds (x, u), ‖p.1‖ ≤ r := by
    have : ∀ᶠ p : X × (Fin 4 → ℝ) in nhds (x, u), p.1 ∈ ball x 1 :=
      (continuous_fst.tendsto (x, u)).eventually (ball_mem_nhds x one_pos)
    filter_upwards [this] with p hp
    rw [mem_ball, dist_eq_norm] at hp
    have := norm_sub_norm_le p.1 x
    linarith
  filter_upwards [hnb] with p hp
  have := norm_step_sub_step_le_exp (u := p.2) (w := u) hp (le_add_of_nonneg_right zero_le_one)
  calc ‖step p.1 p.2 - step x u‖ ≤ _ := this
    _ = ‖p.1 - x‖ * E + C * ‖p.2 - u‖ := by simp only [C, E, K]; ring

end

end Plant
