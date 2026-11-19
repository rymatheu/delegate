import Contracts.Track.Reach.Liveness
import Contracts.Track.Reach.Equilibrium

/-!
# Milestone (4): reach from liveness and convergence (REACH.md §4)

* `stall_scaler_ge` (code level, the `HL` step of `liveness` at a stall point of speed at least
  `0.1` m/s): if the vehicle's state is within `δ` (along the track) of the stalled equilibrium whose
  stalled ratio is `R ≤ 1`, the code's raw scaler is at least `min 1 (0.05 + R − 5δ/(2|v_T|) − 10⁻³)`;
  on a horizontal leg (`R = 1`, `stall_ratio_ge_one`) and `δ ≤ 0.004`, at least `0.9`.
* `reach_model`: the reach theorem in `ℝ` from the code facts of the clock (`code_filter_nonneg`,
  `code_filter_step`, `navProgress`), the closed-loop facts (`HL`: off the stall set a converging
  clock lets the raw scaler recover; `HS`: when the clock converges to `q*` the vehicle converges to
  within `b_S` of `Γ(q*)`; `HE`: when the clock passes every level, the vehicle ends within `b_E` of
  `w'`), and the geometry of the stall set (within `d_Z` of `w'`):
  `∃ T, ∀ t ≥ T, ‖p_t − w'‖ ≤ max b_E (d_Z + b_S)`.
-/

namespace Contracts.Track.Reach

open Contracts.Mission Contracts.Track.Pacing Filter Topology

/-- **The raw scaler near a stalled equilibrium** (code level). `vT`, `pe`, `ve` are the three
`float` vectors the code reads (`get_vel_desired`, `get_pos_error`, `get_vel_estimate`), `R ≤ 1` the
stalled ratio (`stall_ratio`), and the vehicle within `δ` of the equilibrium along the track:
`ve·vT ≥ −δ|vT|` (at rest up to `δ`) and `pe·vT ≤ −(2R/3)|vT|² + δ|vT|` (ahead of the target by
`R·v/kP` up to `δ`). -/
theorem stall_scaler_ge (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32) (hkPf : kP.IsFinite)
    (hkP : kP.toReal = 3 / 2) (hvT : Fin3 vT 3) (hpe : Fin3 pe 4) (hve : Fin3 ve 3)
    {R δ : ℝ} (hR : R ≤ 1) (hδ : 0 ≤ δ) (hL : 1 / 10 ≤ len3 vT)
    (hv : -(δ * len3 vT) ≤ dot3 ve vT)
    (hp : dot3 pe vT ≤ -(2 * R / 3) * len3 vT ^ 2 + δ * len3 vT) :
    min 1 (1 / 20 + R - 5 * δ / (2 * len3 vT) - 1 / 1000) ≤ (rawScaler vT pe ve kP).toReal := by
  set L := len3 vT with hLdef
  have hL0 : 0 < L := by linarith
  have h := rawScaler_ge vT pe ve kP hkPf hkP hvT hpe hve (vmin := L) (εv := L + δ)
    (εe := -(2 * R / 3) * L + δ) hL le_rfl
    (by nlinarith) (by rw [← len3_sq]; nlinarith) (by rw [hLdef] at hp ⊢; nlinarith)
  have e : 21 / 20 - (L + δ + 3 / 2 * (-(2 * R / 3) * L + δ)) / L - 1 / 1000 =
      1 / 20 + R - 5 * δ / (2 * L) - 1 / 1000 := by
    field_simp; ring
  rwa [e] at h

/-- On a horizontal leg (`R = 1`) with the vehicle within `δ ≤ 0.004` of the stalled equilibrium and
`|v_T| ≥ 0.1`, the raw scaler is at least `0.9`. -/
theorem stall_scaler_horizontal (vT pe ve : AC_WPNav_lib.Vector3f.State) (kP : Float32)
    (hkPf : kP.IsFinite) (hkP : kP.toReal = 3 / 2) (hvT : Fin3 vT 3) (hpe : Fin3 pe 4)
    (hve : Fin3 ve 3) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 4 / 1000) (hL : 1 / 10 ≤ len3 vT)
    (hv : -(δ * len3 vT) ≤ dot3 ve vT)
    (hp : dot3 pe vT ≤ -(2 / 3) * len3 vT ^ 2 + δ * len3 vT) :
    9 / 10 ≤ (rawScaler vT pe ve kP).toReal := by
  have h := stall_scaler_ge vT pe ve kP hkPf hkP hvT hpe hve (R := 1) le_rfl hδ hL hv
    (by simpa using hp)
  have hq : 5 * δ / (2 * len3 vT) ≤ 1 / 10 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have : (9 : ℝ) / 10 ≤ min 1 (1 / 20 + 1 - 5 * δ / (2 * len3 vT) - 1 / 1000) :=
    le_min (by norm_num) (by linarith)
  linarith

/-- **Reach (model level).** The clock facts of the code, the closed-loop facts `HL`, `HS`, `HE`,
and the stall set's geometry give `◇□ (‖p − w'‖ ≤ max b_E (d_Z + b_S))`. -/
theorem reach_model {P : Type*} [PseudoMetricSpace P] (p : ℕ → P) (w' : P) (Γ : ℝ → P)
    {s r q : ℕ → ℝ} {ρ dZ bS bE : ℝ}
    (hs : ∀ t, 0 ≤ s t) (hf : FilterRun s r α₀ (1 / 10 ^ 7))
    (hq : ∀ t, q (t + 1) = q t + s (t + 1)) (Z : Set ℝ) (hρ : 13 / 10 ^ 6 ≤ ρ)
    (hZ : ∀ q' ∈ Z, dist (Γ q') w' ≤ dZ)
    (HL : ∀ q', q' ∉ Z → Tendsto q atTop (𝓝 q') → ∀ᶠ t in atTop, ρ ≤ r t)
    (HS : ∀ q', Tendsto q atTop (𝓝 q') → ∀ᶠ t in atTop, dist (p t) (Γ q') ≤ bS)
    (HE : Tendsto q atTop atTop → ∀ᶠ t in atTop, dist (p t) w' ≤ bE) :
    ∃ T, ∀ t ≥ T, dist (p t) w' ≤ max bE (dZ + bS) := by
  rcases liveness_code hs hf hq Z hρ HL with h | ⟨q', hq', hl⟩
  · obtain ⟨T, hT⟩ := eventually_atTop.1 (HE h)
    exact ⟨T, fun t ht => (hT t ht).trans (le_max_left _ _)⟩
  · obtain ⟨T, hT⟩ := eventually_atTop.1 (HS q' hl)
    refine ⟨T, fun t ht => ?_⟩
    have := dist_triangle (p t) (Γ q') w'
    have := hT t ht
    have := hZ q' hq'
    exact le_trans (by linarith) (le_max_right _ _)

end Contracts.Track.Reach
