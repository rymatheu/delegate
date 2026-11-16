import Contracts.Track.Reach.GlueLoop

/-!
# The leg theorem, part (2): the tracking tube along a moving reference

REACH.md §9. The two channels of INDUCTION.md (`ξV`, `ξH` of `Induction/Run.lean`) follow their
exact models driven by the reference: `ξ (t + 1) = A ξ t + forceOf r t + w t`, with
`forceOf r t = asp • B − d₁ • e₀ − d₂ • e₁` (target acceleration, and the two defects of the target
sequence: `d₁ = sp' − sp − h vsp − h²/2 asp`, `d₂ = vsp' − vsp − h asp`). The channels are linear
in the reference, so the error is bounded by the ℓ1 gains of the reference directions times the
reference's limits, plus the ℓ1 tube of the disturbance (`εHL`, `εVL`), plus the peak-weighted start:

`|o ⬝ ξ (t₀ + N)| ≤ Σ P ε₀ + Σ_m |o Aᵐ B| · |asp| + Σ_m |o Aᵐ e₀| · |d₁| + Σ_m |o Aᵐ e₁| · |d₂| + Σ G ε`
(`forced_eq`, `out_le`; the reference terms by `env_le` with a constant envelope (`env_const`) or
an envelope that vanishes after the reference stops (`env_tail`)).

**The direction `B` is the one that matters.** The feed-forward and the error kinematics of the
target acceleration cancel to first order (`A v + B = v` for the acceleration-shift direction
`vAcc`, `Ah_vAcc`), so the ℓ1 gain of the position error in the direction `B` is `0.030`
(`GB 0`), against `Σⱼ GH 0 j |Bⱼ| = 0.37` per coordinate. The command rate `c₁ − c₂` is bounded in
the shifted coordinates `ζ = ξ − asp • vAcc`, driven by the jerk `Δasp` (`zeta_step`).

**The box** (`BoxL`): INDUCTION's flight box with the position error widened for the leg (`bHL`:
`|e| ≤ 0.15`, `|ev| ≤ 0.5`, `|I| ≤ 5`, the command `|c₁| ≤ 4`, its rate `|c₁ − c₂| ≤ 0.05`;
vertically `bV`: `|ez| ≤ 0.1`, `|ev| ≤ 0.5`, `|I| ≤ 0.5`, `|f|, |u| ≤ 0.12`). The command and its
rate are the class of the attitude contract (M4, `CmdOK`) and are kept; the position error enters
the horizontal controller's tick only through `NERegion.e` (`‖e‖ ≤ 0.4`). `leg_box` proves the box at
every tick up to the horizon `hzn = 6000` by strong induction (the box up to `t` gives the per-tick
facts at `t`, which bound the outputs at `t + 1`), from the abstract hypotheses `LegModel` (the model
steps, the start, and the per-tick bounds while the box has held). The position error, its
velocity and the integrator close through the plain ℓ1 envelopes (`0.143 ≤ 0.15`, `0.414 ≤ 0.5`,
`0.414 ≤ 5`); the command through the shifted coordinates `ζ = ξ − asp • vAcc` (`2.99 ≤ 4`); the
command rate through `ζ₂ = ζ − d₂ • u₂`, where `u₂` is the steady state of a constant velocity defect
(`A_h u₂ = u₂ + e₁`), driven by the change of the defect per tick (`0.0462 ≤ 0.05`). Vertically
`0.073, 0.175, 0.028, 0.038, 0.044`.

**The velocity defect** `d₂` of the code's target sequence is up to `7.68·10⁻⁴` per tick (the time
warp `_track_dt_scalar` of the S-curve, REACH.md §9.4): through the plain envelope its contribution
to the position error is `8·10⁻⁴ · 74.3 = 0.059`. The decay arguments (the completion and the hold)
carry it through its sum over the run (`Σ |d₂| ≤ 1/4`, measured `0.240`) and the peak of the tail of
the response (`env_tail_l1`).

**The gains of the reference directions** (`GB`, `GJ`, `GBV`, `GC1` and the tails at `Mc = 416` and
`Mt = 1728` ticks) are certified (`refGains_certified`, LegGains.lean). The per-coordinate gains
`PV`, `GV`, `PH`, `GH` are the certified ones (`Glue.peakV'`, `gainV'`, `peakH'`, `gainH'`).
-/

namespace Contracts.Track.Reach.Leg

open Matrix Finset Contracts.Track.Induction Contracts.Track.Reach.Glue

noncomputable section

/-! ## Constants -/

/-- The horizon of the leg statement: `4800 + 1200` ticks. -/
def hzn : ℕ := 6000

/-- The tick at which the tube starts (after the takeover and the first tick from hover). -/
def ts : ℕ := 2

/-- The decay time of the completion argument: `Mc` ticks after the leg's S-curve has finished the
vehicle is within `0.099` of `w'`. -/
def Mc : ℕ := 416

/-- The decay time of the hold window: the window starts `Mt` ticks after the target stops. -/
def Mt : ℕ := 1728

/-- The leg box of the horizontal outputs `e, ev, I, c₁, c₁ − c₂`: INDUCTION's `bH` with the position
error widened from `0.1` to `0.15` (the horizontal controller's region asks `‖e‖ ≤ 0.4`). -/
def bHL : Fin 5 → ℝ := ![15 / 100, 1 / 2, 5, 4, 1 / 20]

/-- The acceleration-shift direction `(0, 0, 0, 0, 0, 1, 1, 1, 1)`: the attitude-lag state and the
three commands all equal to the target acceleration. -/
def vAcc : Fin 9 → ℝ := ![0, 0, 0, 0, 0, 1, 1, 1, 1]

/-- Per-tick disturbance of a horizontal axis on the leg (INDUCTION.md's `εH`, which is
`Glue.εHh`): the controller and plant rows and the attitude deviation `εη = 0.01` m/s² through
`eAcc`. -/
def εHL : Fin 9 → ℝ := ![22 / 10 ^ 8, 25 / 10 ^ 6, 37 / 10 ^ 7, 231 / 10 ^ 6, 62 / 10 ^ 8, 0,
  161 / 10 ^ 6, 0, 0]

/-- Per-tick disturbance of the vertical channel on the leg: INDUCTION.md's `εV` plus the
structured part (plant remainder, tilt coupling and boost deviation) at leg tilts, `≤ 0.03` m/s²
through `(h²/2, h)` (ten times the hover value of `Glue.εVh`). -/
def εVL : Fin 8 → ℝ := ![11 / 10 ^ 8, 76 / 10 ^ 6, 2 / 10 ^ 7, 42 / 10 ^ 7, 2 / 10 ^ 7, 1 / 10 ^ 7,
  32 / 10 ^ 7, 4 / 10 ^ 7]

/-- The start of the tube, horizontal (`e, ev, E, D, I, a, c₁, c₂, c₃` at tick 2; INDUCTION.md's
`ε0H`). Measured (all campaigns, 2026-11-06): `e ≤ 2.2·10⁻¹⁰`, `ev ≤ 1.5·10⁻⁷`, the commands `c₁`,
`c₂` (the acceleration targets of ticks 1 and 0) `≤ 2.3·10⁻⁵`, `2.8·10⁻⁶`, `c₃ = 0`; `E`, `D`, `I`,
`a` are not logged (the horizontal channel is at rest: the trim sink is vertical). -/
def ε0HL : Fin 9 → ℝ := ![1 / 10 ^ 6, 1 / 10 ^ 6, 1 / 10 ^ 5, 1 / 10 ^ 4, 1 / 10 ^ 5, 1 / 10 ^ 5,
  1 / 10 ^ 4, 1 / 10 ^ 4, 1 / 10 ^ 4]

/-- The start of the tube, vertical (`ez, ev, eV, eA, I, f, u, w` at tick 2). INDUCTION.md's `ε0V`
with two entries widened on 2026-11-06 (REACH.md §9.4, finding 11): the velocity error `ev` to
`10⁻⁵` (was `10⁻⁶`; measured `4.90–5.03·10⁻⁶` on every run of the three campaigns) and the
acceleration-PID error `eA` to `2·10⁻³` (was `10⁻⁵`; computed `2.34·10⁻⁴`). The cause is the trim:
`MOT_THST_HOVER 0.4444` (`0.44440001` as `float`) against the plant's hover fraction `1/2.25` is a
thrust deficit of `10⁻⁴`, so the vehicle sinks at `9.80·10⁻⁴` m/s² from tick 0 (the traces'
`az_d = −9.80567` from tick 1): `|ev| = 2h · 9.8·10⁻⁴` at tick 2, and the 20 Hz error filter of the
acceleration PID (`α = 0.239`) holds `α · 9.80·10⁻⁴` of the sampled sink (a priori at most the sink
plus the target, `≤ 10⁻³`). The other entries: `ez` measured `≤ 1.3·10⁻⁷`, `w` (mean held actuator
minus `1/2.25`) measured `4.45·10⁻⁵`; `eV`, `I`, `f`, `u` are not logged (estimated `1.8·10⁻⁷`,
`4.4·10⁻⁵`, `4.4·10⁻⁵`, `≤ 4.4·10⁻⁵`). -/
def ε0VL : Fin 8 → ℝ := ![1 / 10 ^ 6, 1 / 10 ^ 5, 1 / 10 ^ 5, 2 / 10 ^ 3, 1 / 10 ^ 4, 1 / 10 ^ 4,
  1 / 10 ^ 4, 1 / 10 ^ 4]

/-- ℓ1 gains of the horizontal outputs `e, ev, I, c₁, c₁ − c₂` in the direction `B_h` (measured
`0.02998, 0.1654, 0.03870, 2.237`; the last entry bounds `c₁ − c₂` by `c₁` and `c₂`, unused). -/
def GB : Fin 5 → ℝ := ![306 / 10000, 169 / 1000, 395 / 10000, 229 / 100, 45 / 10]

/-- ℓ1 gain of the command rate `c₁ − c₂` in the direction `vAcc` (measured `2.237`). -/
def GJ : ℝ := 229 / 100

/-- ℓ1 gains of the vertical outputs `ez, ev, I, f, u` in the direction `B_v` (measured
`0.1160, 0.2900, 0.05043, 0.06752, 0.07915`). -/
def GBV : Fin 5 → ℝ := ![119 / 1000, 296 / 1000, 515 / 10000, 689 / 10000, 808 / 10000]

/-- ℓ1 gain of the command `c₁` in the direction `vAcc` (certified `60.5422`). -/
def GC1 : ℝ := 6055 / 100

/-- **The u₂ direction**: the steady state of a constant velocity defect, `A_h u₂ = u₂ + e₁`. -/
def u2 : Fin 9 → ℝ := ![1 / 3, -1 / 2, 0, 0, 400, 400, 400, 400, 400]

/-- `|u₂|`. -/
def u2a : Fin 9 → ℝ := ![1 / 3, 1 / 2, 0, 0, 400, 400, 400, 400, 400]

/-- Tails past `Mc` of the horizontal position error: in the directions `B_h` and `e₀` the ℓ1 tails,
in the direction `e₁` the peak of the tail (certified, LegGains.lean: the state after `Mc` ticks
weighted by the certified per-coordinate gains `GH 0`, `PH 0`). -/
def TBc : ℝ := 1679 / 100000
def T0c : ℝ := 928 / 10
def P1c : ℝ := 5575 / 100000

/-- Tails past `Mt` of the horizontal position error (as `TBc`, `T0c`, `P1c`). -/
def TB : ℝ := 1118 / 1000000
def T0 : ℝ := 481 / 100
def P1 : ℝ := 186 / 10000

/-- ℓ1 tails past `Mt` of the vertical position error in the directions `B_v`, `e₀`, `e₁`. -/
def TBV : ℝ := 2173 / 1000000
def TV0 : ℝ := 549 / 100
def TV1 : ℝ := 475 / 1000

/-! ## The response in a direction -/

/-- The response of output `o` to the initial state `D` after `m` ticks. -/
def rsp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (o D : Fin n → ℝ) (m : ℕ) : ℝ :=
  o ⬝ᵥ ((A ^ m) *ᵥ D)

theorem rsp_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (o : Fin n → ℝ) (j : Fin n) (m : ℕ) :
    rsp A o (Pi.single j 1) m = resp A o m j := rfl

/-! ## The forced response of a linear channel -/

section Gen

variable {n : ℕ}

/-- **The forced response**: from `t₀`, `ξ' = A ξ + c₁ D₁ + c₂ D₂ + c₃ D₃ + w`. -/
theorem forced_eq (A : Matrix (Fin n) (Fin n) ℝ) (ξ w : ℕ → Fin n → ℝ) (c₁ c₂ c₃ : ℕ → ℝ)
    (D₁ D₂ D₃ : Fin n → ℝ) (t₀ : ℕ)
    (h : ∀ t, t₀ ≤ t → ξ (t + 1) = A *ᵥ ξ t + (c₁ t • D₁ + c₂ t • D₂ + c₃ t • D₃ + w t))
    (o : Fin n → ℝ) (N : ℕ) :
    o ⬝ᵥ ξ (t₀ + N) = o ⬝ᵥ ((A ^ N) *ᵥ ξ t₀) +
      ∑ k ∈ range N, c₁ (t₀ + k) * rsp A o D₁ (N - 1 - k) +
      ∑ k ∈ range N, c₂ (t₀ + k) * rsp A o D₂ (N - 1 - k) +
      ∑ k ∈ range N, c₃ (t₀ + k) * rsp A o D₃ (N - 1 - k) +
      ∑ k ∈ range N, o ⬝ᵥ ((A ^ (N - 1 - k)) *ᵥ w (t₀ + k)) := by
  rw [eta_eq_sum A ξ _ t₀ h N, dotProduct_add, dotProduct_sum]
  simp only [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul,
    Finset.sum_add_distrib, rsp]
  ring

/-- The free response, through the peak gains. -/
theorem free_le (A : Matrix (Fin n) (Fin n) ℝ) (o x x0 P : Fin n → ℝ) (N : ℕ)
    (hx : ∀ j, |x j| ≤ x0 j) (hP : ∀ j m, |resp A o m j| ≤ P j) :
    |o ⬝ᵥ ((A ^ N) *ᵥ x)| ≤ ∑ j, P j * x0 j := by
  refine (abs_dot_mulVec_le A o x x0 N hx).trans (Finset.sum_le_sum fun j _ => ?_)
  have h0 : 0 ≤ x0 j := (abs_nonneg _).trans (hx j)
  calc x0 j * |resp A o N j| ≤ x0 j * P j := mul_le_mul_of_nonneg_left (hP j N) h0
    _ = P j * x0 j := mul_comm _ _

/-- The convolution of a disturbance bounded per coordinate, through the ℓ1 gains. -/
theorem conv_le (A : Matrix (Fin n) (Fin n) ℝ) (o : Fin n → ℝ) (w : ℕ → Fin n → ℝ) (t₀ N : ℕ)
    (ε G : Fin n → ℝ) (hε : ∀ j, 0 ≤ ε j) (hw : ∀ k < N, ∀ j, |w (t₀ + k) j| ≤ ε j)
    (hG : ∀ j N, ∑ m ∈ range N, |resp A o m j| ≤ G j) :
    |∑ k ∈ range N, o ⬝ᵥ ((A ^ (N - 1 - k)) *ᵥ w (t₀ + k))| ≤ ∑ j, G j * ε j := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range N, |o ⬝ᵥ ((A ^ (N - 1 - k)) *ᵥ w (t₀ + k))|
      ≤ ∑ k ∈ range N, ∑ j, ε j * |resp A o (N - 1 - k) j| :=
        Finset.sum_le_sum fun k hk => abs_dot_mulVec_le A o _ ε _ (hw k (mem_range.mp hk))
    _ = ∑ j, ε j * ∑ k ∈ range N, |resp A o (N - 1 - k) j| := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ = ∑ j, ε j * ∑ m ∈ range N, |resp A o m j| := by
        congr 1; ext j; congr 1
        exact Finset.sum_range_reflect (fun m => |resp A o m j|) N
    _ ≤ ∑ j, G j * ε j := Finset.sum_le_sum fun j _ => by
        rw [mul_comm (G j)]; exact mul_le_mul_of_nonneg_left (hG j N) (hε j)

/-- **The output bound**: free response, three reference terms, and the disturbance tube. -/
theorem out_le (A : Matrix (Fin n) (Fin n) ℝ) (ξ w : ℕ → Fin n → ℝ) (c₁ c₂ c₃ : ℕ → ℝ)
    (D₁ D₂ D₃ : Fin n → ℝ) (t₀ : ℕ)
    (h : ∀ t, t₀ ≤ t → ξ (t + 1) = A *ᵥ ξ t + (c₁ t • D₁ + c₂ t • D₂ + c₃ t • D₃ + w t))
    (o : Fin n → ℝ) (N : ℕ) (x0 P G ε : Fin n → ℝ) (hx : ∀ j, |ξ t₀ j| ≤ x0 j)
    (hP : ∀ j m, |resp A o m j| ≤ P j) (hG : ∀ j N, ∑ m ∈ range N, |resp A o m j| ≤ G j)
    (hε : ∀ j, 0 ≤ ε j) (hw : ∀ k < N, ∀ j, |w (t₀ + k) j| ≤ ε j) {B₁ B₂ B₃ : ℝ}
    (h₁ : |∑ k ∈ range N, c₁ (t₀ + k) * rsp A o D₁ (N - 1 - k)| ≤ B₁)
    (h₂ : |∑ k ∈ range N, c₂ (t₀ + k) * rsp A o D₂ (N - 1 - k)| ≤ B₂)
    (h₃ : |∑ k ∈ range N, c₃ (t₀ + k) * rsp A o D₃ (N - 1 - k)| ≤ B₃) :
    |o ⬝ᵥ ξ (t₀ + N)| ≤ ∑ j, P j * x0 j + B₁ + B₂ + B₃ + ∑ j, G j * ε j := by
  rw [forced_eq A ξ w c₁ c₂ c₃ D₁ D₂ D₃ t₀ h o N]
  have h0 := free_le A o (ξ t₀) x0 P N hx hP
  have h4 := conv_le A o w t₀ N ε G hε hw hG
  refine (abs_add_le _ _).trans ?_
  refine add_le_add ?_ h4
  refine (abs_add_le _ _).trans (add_le_add ?_ h₃)
  refine (abs_add_le _ _).trans (add_le_add ?_ h₂)
  exact (abs_add_le _ _).trans (add_le_add h0 h₁)

end Gen

/-! ## Envelopes of the reference -/

/-- **A reference term through an envelope** `|c (t₀ + k)| ≤ E (N − 1 − k)`. -/
theorem env_le (g c E : ℕ → ℝ) (t₀ N : ℕ) (hc : ∀ k < N, |c (t₀ + k)| ≤ E (N - 1 - k)) :
    |∑ k ∈ range N, c (t₀ + k) * g (N - 1 - k)| ≤ ∑ m ∈ range N, E m * |g m| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range N, |c (t₀ + k) * g (N - 1 - k)|
      ≤ ∑ k ∈ range N, E (N - 1 - k) * |g (N - 1 - k)| := Finset.sum_le_sum fun k hk => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc k (mem_range.1 hk)) (abs_nonneg _)
    _ = ∑ m ∈ range N, E m * |g m| := Finset.sum_range_reflect (fun m => E m * |g m|) N

/-- **A constant envelope**: `|c| ≤ X` on the ticks, `ℓ1` gain `≤ G`. -/
theorem env_const (g c : ℕ → ℝ) (t₀ N : ℕ) {X G : ℝ} (hX : 0 ≤ X)
    (hc : ∀ k < N, |c (t₀ + k)| ≤ X) (hG : ∑ m ∈ range N, |g m| ≤ G) :
    |∑ k ∈ range N, c (t₀ + k) * g (N - 1 - k)| ≤ X * G := by
  refine (env_le g c (fun _ => X) t₀ N hc).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hG hX

/-- **An envelope that vanishes from tick `L` on**: if `c` is zero from `L`, `|c| ≤ X` before, and
the output tick `t₀ + N` is at least `M` ticks after `L`, only the tail of the response past `M`
counts. -/
theorem env_tail (g c : ℕ → ℝ) (t₀ N L M : ℕ) {X T : ℝ} (hX : 0 ≤ X)
    (hc : ∀ k < N, |c (t₀ + k)| ≤ X) (hz : ∀ t, L ≤ t → c t = 0) (hNL : L + M ≤ t₀ + N)
    (hT : ∀ K, ∑ m ∈ range K, |g (M + m)| ≤ T) :
    |∑ k ∈ range N, c (t₀ + k) * g (N - 1 - k)| ≤ X * T := by
  have hE : ∀ k < N, |c (t₀ + k)| ≤ (fun m => if m < M then 0 else X) (N - 1 - k) := by
    intro k hk
    by_cases hm : N - 1 - k < M
    · simp only [hm, if_true]
      rw [hz (t₀ + k) (by omega), abs_zero]
    · simp only [hm, if_false]; exact hc k hk
  refine (env_le g c (fun m => if m < M then 0 else X) t₀ N hE).trans ?_
  by_cases hMN : M ≤ N
  swap
  · have h0 : ∑ m ∈ range N, (if m < M then (0 : ℝ) else X) * |g m| = 0 :=
      Finset.sum_eq_zero fun m hm => by simp [show m < M by have := mem_range.1 hm; omega]
    rw [h0]
    exact mul_nonneg hX (by simpa using hT 0)
  obtain ⟨K, rfl⟩ : ∃ K, N = M + K := ⟨N - M, by omega⟩
  rw [Finset.sum_range_add]
  have h1 : ∑ m ∈ range M, (if m < M then (0 : ℝ) else X) * |g m| = 0 :=
    Finset.sum_eq_zero fun m hm => by simp [mem_range.1 hm]
  have h2 : ∑ m ∈ range K, (if M + m < M then (0 : ℝ) else X) * |g (M + m)| =
      X * ∑ m ∈ range K, |g (M + m)| := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by simp
  rw [h1, h2, zero_add]
  exact mul_le_mul_of_nonneg_left (hT K) hX

/-! ## The acceleration shift -/

/-- **The feed-forward cancels the kinematics**: `A_h vAcc + B_h = vAcc` (the steady state of a
constant target acceleration has the lag state and the commands equal to it, and no error). -/
theorem Ah_vAcc : Horizontal.AhR *ᵥ vAcc + Horizontal.BhR = vAcc := by
  ext i
  fin_cases i <;>
    simp [Horizontal.AhR, Horizontal.BhR, Horizontal.Ah, Horizontal.Bh, Horizontal.rowEp,
      Horizontal.rowEv, Horizontal.rowE, Horizontal.rowD, Horizontal.rowI, Horizontal.rowC,
      Horizontal.rowA, vAcc, mulVec, dotProduct, Fin.sum_univ_succ] <;>
    norm_num

/-- The command-rate output does not see the shift. -/
theorem outH4_vAcc : outH 4 ⬝ᵥ vAcc = 0 := by
  rw [show outH 4 = Pi.single 6 1 - Pi.single 7 1 from rfl, sub_dotProduct, single_dotProduct,
    single_dotProduct]
  simp [vAcc]

theorem vAcc_nonneg (j : Fin 9) : 0 ≤ vAcc j := by
  fin_cases j <;> simp [vAcc]

/-- **The shifted coordinates** `ζ = ξ − asp • vAcc` are driven by the jerk `Δasp`. -/
theorem zeta_step (ξ w : ℕ → Fin 9 → ℝ) (a d₁ d₂ : ℕ → ℝ) (t : ℕ)
    (h : ξ (t + 1) = Horizontal.AhR *ᵥ ξ t + (a t • Horizontal.BhR + (-d₁ t) • Horizontal.e0 +
      (-d₂ t) • Horizontal.e1 + w t)) :
    ξ (t + 1) - a (t + 1) • vAcc = Horizontal.AhR *ᵥ (ξ t - a t • vAcc) +
      ((-(a (t + 1) - a t)) • vAcc + (-d₁ t) • Horizontal.e0 + (-d₂ t) • Horizontal.e1 + w t) := by
  have hv := Ah_vAcc
  have e : Horizontal.AhR *ᵥ (a t • vAcc) = a t • vAcc - a t • Horizontal.BhR := by
    rw [mulVec_smul, show Horizontal.AhR *ᵥ vAcc = vAcc - Horizontal.BhR from eq_sub_of_add_eq hv,
      smul_sub]
  rw [h, mulVec_sub, e]
  module

/-! ## The velocity-defect shift -/

/-- **The steady state of a constant velocity defect**: `A_h u₂ = u₂ + e₁` (the integrator, the lag
state and the commands at 400 per unit defect per tick, the errors at `1/3`, `−1/2`). -/
theorem Ah_u2 : Horizontal.AhR *ᵥ u2 = u2 + Horizontal.e1 := by
  ext i
  fin_cases i <;>
    simp [Horizontal.AhR, Horizontal.Ah, Horizontal.rowEp, Horizontal.rowEv, Horizontal.rowE,
      Horizontal.rowD, Horizontal.rowI, Horizontal.rowC, Horizontal.rowA, Horizontal.kpPos,
      Horizontal.e1, u2, mulVec, dotProduct, Fin.sum_univ_succ, Horizontal.per] <;>
    ring

/-- The command-rate output does not see the velocity-defect shift. -/
theorem outH4_u2 : outH 4 ⬝ᵥ u2 = 0 := by
  rw [show outH 4 = Pi.single 6 1 - Pi.single 7 1 from rfl, sub_dotProduct, single_dotProduct,
    single_dotProduct]
  simp [u2]

theorem u2_abs (j : Fin 9) : |u2 j| ≤ u2a j := by
  fin_cases j <;> simp [u2, u2a]; norm_num [abs_of_nonneg]

theorem u2a_nonneg (j : Fin 9) : 0 ≤ u2a j := by
  fin_cases j <;> simp [u2a]

/-- **The doubly shifted coordinates** `ζ₂ = ξ − asp • vAcc − d₂ • u₂` are driven by the jerk, the
position defect and the change of the velocity defect `Δd₂`. -/
theorem zeta2_step (ξ w : ℕ → Fin 9 → ℝ) (a d₁ d₂ : ℕ → ℝ) (t : ℕ)
    (h : ξ (t + 1) = Horizontal.AhR *ᵥ ξ t + (a t • Horizontal.BhR + (-d₁ t) • Horizontal.e0 +
      (-d₂ t) • Horizontal.e1 + w t)) :
    ξ (t + 1) - a (t + 1) • vAcc - d₂ (t + 1) • u2 =
      Horizontal.AhR *ᵥ (ξ t - a t • vAcc - d₂ t • u2) +
      ((-(a (t + 1) - a t)) • vAcc + (-d₁ t) • Horizontal.e0 + (-(d₂ (t + 1) - d₂ t)) • u2 +
        w t) := by
  have hv := Ah_vAcc
  have e : Horizontal.AhR *ᵥ (a t • vAcc) = a t • vAcc - a t • Horizontal.BhR := by
    rw [mulVec_smul, show Horizontal.AhR *ᵥ vAcc = vAcc - Horizontal.BhR from eq_sub_of_add_eq hv,
      smul_sub]
  have e2 : Horizontal.AhR *ᵥ (d₂ t • u2) = d₂ t • u2 + d₂ t • Horizontal.e1 := by
    rw [mulVec_smul, Ah_u2, smul_add]
  rw [h, mulVec_sub, mulVec_sub, e, e2]
  module

/-- Row 7 of `A_h` copies coordinate 6 (the command delay). -/
theorem Ah_row7 (w : Fin 9 → ℝ) : (Horizontal.AhR *ᵥ w) 7 = w 6 := by
  simp [Horizontal.AhR, Horizontal.Ah, mulVec, dotProduct, Fin.sum_univ_succ]

/-- **The response of the command rate to `u₂` is the `c₁` response to `e₁`, one tick later.** -/
theorem rate_u2 (m : ℕ) :
    rsp Horizontal.AhR (outH 4) u2 (m + 1) = rsp Horizontal.AhR (outH 3) Horizontal.e1 m := by
  have e4 : outH 4 = Pi.single 6 1 - Pi.single 7 1 := rfl
  have e3 : outH 3 = Pi.single 6 1 := rfl
  have h6 : (Horizontal.AhR ^ (m + 1) *ᵥ u2) 6 =
      (Horizontal.AhR ^ m *ᵥ u2) 6 + (Horizontal.AhR ^ m *ᵥ Horizontal.e1) 6 := by
    rw [pow_succ, ← mulVec_mulVec, Ah_u2, mulVec_add]; rfl
  have h7 : (Horizontal.AhR ^ (m + 1) *ᵥ u2) 7 = (Horizontal.AhR ^ m *ᵥ u2) 6 := by
    rw [pow_succ', ← mulVec_mulVec, Ah_row7]
  simp only [rsp, e4, e3, sub_dotProduct, single_dotProduct, one_mul]
  rw [h6, h7]
  ring

/-- The ℓ1 gain of the command rate in the direction `u₂` is the `c₁` gain of `e₁`. -/
theorem gainU2 (N : ℕ) : ∑ m ∈ range N, |rsp Horizontal.AhR (outH 4) u2 m| ≤ GH 3 1 := by
  rcases N with _ | N
  · simp only [Finset.range_zero, Finset.sum_empty]; norm_num [GH]
  · rw [Finset.sum_range_succ']
    have h0 : rsp Horizontal.AhR (outH 4) u2 0 = 0 := by
      simp [rsp, outH4_u2]
    simp only [rate_u2, h0, abs_zero, add_zero]
    exact gainH' 3 1 N

/-! ## The box and the model -/

/-- **The leg box** at tick `t` (INDUCTION's vertical box `bV`; the horizontal box `bHL`). -/
def BoxL (ξV : ℕ → Fin 8 → ℝ) (ξH : ℕ → Fin 2 → Fin 9 → ℝ) (t : ℕ) : Prop :=
  (∀ o, |outV o ⬝ᵥ ξV t| ≤ bV o) ∧ ∀ a o, |outH o ⬝ᵥ ξH t a| ≤ bHL o

/-- The per-tick bounds of the reference and the disturbance, uniform over the run (leg, loiter,
hold): target acceleration `≤ 1.501` per axis (the float limit `1.5000003`), its change `≤ 0.013` per
tick (jerk `5` is `0.0125`), position defect `≤ 1.3·10⁻⁴`, velocity defect `≤ 8·10⁻⁴` and its change
`≤ 1.1·10⁻⁵` per tick; vertically acceleration `≤ 0.5`, defects `≤ 10⁻⁵`, `2·10⁻⁵`; the
disturbances within `εVL`, `εHL`. -/
structure TickBounds (ξV wV : ℕ → Fin 8 → ℝ) (aZ d1Z d2Z : ℕ → ℝ)
    (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (aH d1H d2H : ℕ → Fin 2 → ℝ) (t : ℕ) : Prop where
  bwV : ∀ j, |wV t j| ≤ εVL j
  bwH : ∀ a j, |wH t a j| ≤ εHL j
  baZ : |aZ t| ≤ 1 / 2
  bd1Z : |d1Z t| ≤ 1 / 10 ^ 5
  bd2Z : |d2Z t| ≤ 2 / 10 ^ 5
  baH : ∀ a, |aH t a| ≤ 1501 / 1000
  bjH : ∀ a, |aH (t + 1) a - aH t a| ≤ 13 / 1000
  bd1H : ∀ a, |d1H t a| ≤ 13 / 10 ^ 5
  bd2H : ∀ a, |d2H t a| ≤ 8 / 10 ^ 4
  bdd2H : ∀ a, |d2H (t + 1) a - d2H t a| ≤ 11 / 10 ^ 6

/-- **The model of the leg** from `t₀`: the two channels follow their models driven by the
reference, start in the tube's start region, and meet `TickBounds` at every tick before the
horizon while the box has held since `t₀`. -/
structure LegModel (ξV wV : ℕ → Fin 8 → ℝ) (aZ d1Z d2Z : ℕ → ℝ)
    (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (aH d1H d2H : ℕ → Fin 2 → ℝ) (t₀ : ℕ) : Prop where
  stepV : ∀ t, t₀ ≤ t → ξV (t + 1) = Vertical.AvR *ᵥ ξV t +
    (aZ t • Vertical.BvR + (-d1Z t) • Vertical.e0 + (-d2Z t) • Vertical.e1 + wV t)
  stepH : ∀ t, t₀ ≤ t → ∀ a, ξH (t + 1) a = Horizontal.AhR *ᵥ ξH t a +
    (aH t a • Horizontal.BhR + (-d1H t a) • Horizontal.e0 + (-d2H t a) • Horizontal.e1 + wH t a)
  initV : ∀ j, |ξV t₀ j| ≤ ε0VL j
  initH : ∀ a j, |ξH t₀ a j| ≤ ε0HL j
  initA : ∀ a, |aH t₀ a| ≤ 1 / 1000
  initD : ∀ a, |d2H t₀ a| ≤ 1 / 10 ^ 6
  tick : ∀ t, t₀ ≤ t → t < hzn → (∀ k, t₀ ≤ k → k ≤ t → BoxL ξV ξH k) →
    TickBounds ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t

/-- The certified numbers of the reference directions (`refGains_certified`, LegGains.lean). -/
structure RefGains : Prop where
  gainB : ∀ o N, ∑ m ∈ range N, |rsp Horizontal.AhR (outH o) Horizontal.BhR m| ≤ GB o
  gainJ : ∀ N, ∑ m ∈ range N, |rsp Horizontal.AhR (outH 4) vAcc m| ≤ GJ
  gainC1 : ∀ N, ∑ m ∈ range N, |rsp Horizontal.AhR (outH 3) vAcc m| ≤ GC1
  gainBV : ∀ o N, ∑ m ∈ range N, |rsp Vertical.AvR (outV o) Vertical.BvR m| ≤ GBV o
  tailBc : ∀ N, ∑ m ∈ range N, |rsp Horizontal.AhR (outH 0) Horizontal.BhR (Mc + m)| ≤ TBc
  tail0c : ∀ N, ∑ m ∈ range N, |rsp Horizontal.AhR (outH 0) Horizontal.e0 (Mc + m)| ≤ T0c
  peak1c : ∀ m, |rsp Horizontal.AhR (outH 0) Horizontal.e1 (Mc + m)| ≤ P1c
  tailB : ∀ N, ∑ m ∈ range N, |rsp Horizontal.AhR (outH 0) Horizontal.BhR (Mt + m)| ≤ TB
  tail0 : ∀ N, ∑ m ∈ range N, |rsp Horizontal.AhR (outH 0) Horizontal.e0 (Mt + m)| ≤ T0
  peak1 : ∀ m, |rsp Horizontal.AhR (outH 0) Horizontal.e1 (Mt + m)| ≤ P1
  tailBV : ∀ N, ∑ m ∈ range N, |rsp Vertical.AvR (outV 0) Vertical.BvR (Mt + m)| ≤ TBV
  tail0V : ∀ N, ∑ m ∈ range N, |rsp Vertical.AvR (outV 0) Vertical.e0 (Mt + m)| ≤ TV0
  tail1V : ∀ N, ∑ m ∈ range N, |rsp Vertical.AvR (outV 0) Vertical.e1 (Mt + m)| ≤ TV1

/-! ## The per-coordinate gains of the defect directions -/

theorem gH0 (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp Horizontal.AhR (outH o) Horizontal.e0 m| ≤ GH o 0 :=
  gainH' o 0 N

theorem gH1 (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp Horizontal.AhR (outH o) Horizontal.e1 m| ≤ GH o 1 :=
  gainH' o 1 N

theorem gV0 (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp Vertical.AvR (outV o) Vertical.e0 m| ≤ GV o 0 :=
  gainV' o 0 N

theorem gV1 (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp Vertical.AvR (outV o) Vertical.e1 m| ≤ GV o 1 :=
  gainV' o 1 N

/-- A negated reference term through a constant envelope. -/
theorem env_const_neg (g c : ℕ → ℝ) (t₀ N : ℕ) {X G : ℝ} (hX : 0 ≤ X)
    (hc : ∀ k < N, |c (t₀ + k)| ≤ X) (hG : ∑ m ∈ range N, |g m| ≤ G) :
    |∑ k ∈ range N, (fun t => -c t) (t₀ + k) * g (N - 1 - k)| ≤ X * G :=
  env_const g (fun t => -c t) t₀ N hX (fun k hk => by simpa [abs_neg] using hc k hk) hG

/-- A negated reference term through a vanishing envelope. -/
theorem env_tail_neg (g c : ℕ → ℝ) (t₀ N L M : ℕ) {X T : ℝ} (hX : 0 ≤ X)
    (hc : ∀ k < N, |c (t₀ + k)| ≤ X) (hz : ∀ t, L ≤ t → c t = 0) (hNL : L + M ≤ t₀ + N)
    (hT : ∀ K, ∑ m ∈ range K, |g (M + m)| ≤ T) :
    |∑ k ∈ range N, (fun t => -c t) (t₀ + k) * g (N - 1 - k)| ≤ X * T :=
  env_tail g (fun t => -c t) t₀ N L M hX (fun k hk => by simpa [abs_neg] using hc k hk)
    (fun t ht => by simp [hz t ht]) hNL hT

/-- **An envelope that is small from tick `L` on**: `|c| ≤ X` everywhere, `|c| ≤ Y` from `L` to the
output tick; the old part counts through the tail past `M`, the recent part through the full gain. -/
theorem env_tail2 (g c : ℕ → ℝ) (t₀ N L M : ℕ) {X Y T G : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hc : ∀ k < N, |c (t₀ + k)| ≤ X) (hz : ∀ t, L ≤ t → t < t₀ + N → |c t| ≤ Y)
    (hNL : L + M ≤ t₀ + N)
    (hT : ∀ K, ∑ m ∈ range K, |g (M + m)| ≤ T) (hG : ∑ m ∈ range N, |g m| ≤ G) :
    |∑ k ∈ range N, c (t₀ + k) * g (N - 1 - k)| ≤ X * T + Y * G := by
  set c₁ : ℕ → ℝ := fun t => if L ≤ t then 0 else c t
  set c₂ : ℕ → ℝ := fun t => if L ≤ t then c t else 0
  have hsplit : ∑ k ∈ range N, c (t₀ + k) * g (N - 1 - k) =
      ∑ k ∈ range N, c₁ (t₀ + k) * g (N - 1 - k) + ∑ k ∈ range N, c₂ (t₀ + k) * g (N - 1 - k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c₁, c₂]; split_ifs <;> ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine env_tail g c₁ t₀ N L M hX (fun k hk => ?_) (fun t ht => by simp [c₁, ht]) hNL hT
    simp only [c₁]; split_ifs
    · simpa using hX
    · exact hc k hk
  · refine env_const g c₂ t₀ N hY (fun k hk => ?_) hG
    simp only [c₂]; split_ifs with h
    · exact hz _ h (by omega)
    · simpa using hY

theorem env_tail2_neg (g c : ℕ → ℝ) (t₀ N L M : ℕ) {X Y T G : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hc : ∀ k < N, |c (t₀ + k)| ≤ X) (hz : ∀ t, L ≤ t → t < t₀ + N → |c t| ≤ Y)
    (hNL : L + M ≤ t₀ + N)
    (hT : ∀ K, ∑ m ∈ range K, |g (M + m)| ≤ T) (hG : ∑ m ∈ range N, |g m| ≤ G) :
    |∑ k ∈ range N, (fun t => -c t) (t₀ + k) * g (N - 1 - k)| ≤ X * T + Y * G :=
  env_tail2 g (fun t => -c t) t₀ N L M hX hY (fun k hk => by simpa [abs_neg] using hc k hk)
    (fun t ht ht' => by simpa [abs_neg] using hz t ht ht') hNL hT hG

/-- **An envelope summable over the run**: `Σ |c| ≤ S` over the window, `|c| ≤ Y` from `L` to the
output tick; the old part counts through the peak `P` of the response past `M` (the sum of the
forcing times the peak of the tail), the recent part through the full gain. -/
theorem env_tail_l1 (g c : ℕ → ℝ) (t₀ N L M : ℕ) {S P Y G : ℝ} (hP : 0 ≤ P) (hY : 0 ≤ Y)
    (hS : ∑ k ∈ range N, |c (t₀ + k)| ≤ S) (hz : ∀ t, L ≤ t → t < t₀ + N → |c t| ≤ Y)
    (hNL : L + M ≤ t₀ + N) (hg : ∀ m, |g (M + m)| ≤ P) (hG : ∑ m ∈ range N, |g m| ≤ G) :
    |∑ k ∈ range N, c (t₀ + k) * g (N - 1 - k)| ≤ S * P + Y * G := by
  set c₁ : ℕ → ℝ := fun t => if L ≤ t then 0 else c t
  set c₂ : ℕ → ℝ := fun t => if L ≤ t then c t else 0
  have hsplit : ∑ k ∈ range N, c (t₀ + k) * g (N - 1 - k) =
      ∑ k ∈ range N, c₁ (t₀ + k) * g (N - 1 - k) + ∑ k ∈ range N, c₂ (t₀ + k) * g (N - 1 - k) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [c₁, c₂]; split_ifs <;> ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range N, |c₁ (t₀ + k) * g (N - 1 - k)|
        ≤ ∑ k ∈ range N, |c (t₀ + k)| * P := Finset.sum_le_sum fun k hk => by
          have hk' := mem_range.1 hk
          simp only [c₁]; split_ifs with h
          · simp only [zero_mul, abs_zero]; exact mul_nonneg (abs_nonneg _) hP
          · rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            have := hg (N - 1 - k - M)
            rwa [show M + (N - 1 - k - M) = N - 1 - k by omega] at this
      _ = (∑ k ∈ range N, |c (t₀ + k)|) * P := by rw [Finset.sum_mul]
      _ ≤ S * P := mul_le_mul_of_nonneg_right hS hP
  · refine env_const g c₂ t₀ N hY (fun k hk => ?_) hG
    simp only [c₂]; split_ifs with h
    · exact hz _ h (by omega)
    · simpa using hY

theorem env_tail_l1_neg (g c : ℕ → ℝ) (t₀ N L M : ℕ) {S P Y G : ℝ} (hP : 0 ≤ P) (hY : 0 ≤ Y)
    (hS : ∑ k ∈ range N, |c (t₀ + k)| ≤ S) (hz : ∀ t, L ≤ t → t < t₀ + N → |c t| ≤ Y)
    (hNL : L + M ≤ t₀ + N) (hg : ∀ m, |g (M + m)| ≤ P) (hG : ∑ m ∈ range N, |g m| ≤ G) :
    |∑ k ∈ range N, (fun t => -c t) (t₀ + k) * g (N - 1 - k)| ≤ S * P + Y * G :=
  env_tail_l1 g (fun t => -c t) t₀ N L M hP hY (by simpa [abs_neg] using hS)
    (fun t ht ht' => by simpa [abs_neg] using hz t ht ht') hNL hg hG

/-! ## The box closes -/

theorem boxH_close (o : Fin 5) (ho : o.val < 3) :
    ∑ j, PH o j * ε0HL j + 1501 / 1000 * GB o + 13 / 10 ^ 5 * GH o 0 + 8 / 10 ^ 4 * GH o 1 +
      ∑ j, GH o j * εHL j ≤ bHL o := by
  fin_cases o <;> simp_all [PH, GH, ε0HL, εHL, GB, bHL, Fin.sum_univ_succ] <;> norm_num

theorem boxC1_close :
    1501 / 1000 + 13 / 1000 + (∑ j, PH 3 j * (ε0HL j + 1 / 1000 * vAcc j) + 13 / 1000 * GC1 +
      13 / 10 ^ 5 * GH 3 0 + 8 / 10 ^ 4 * GH 3 1 + ∑ j, GH 3 j * εHL j) ≤ bHL 3 := by
  simp [PH, GH, ε0HL, εHL, GC1, bHL, vAcc, Fin.sum_univ_succ]; norm_num

theorem boxRate_close :
    ∑ j, PH 4 j * (ε0HL j + 1 / 1000 * vAcc j + 1 / 10 ^ 6 * u2a j) + 13 / 1000 * GJ +
      13 / 10 ^ 5 * GH 4 0 + 11 / 10 ^ 6 * GH 3 1 + ∑ j, GH 4 j * εHL j ≤ bHL 4 := by
  simp [PH, GH, ε0HL, εHL, GJ, bHL, vAcc, u2a, Fin.sum_univ_succ]; norm_num

theorem boxV_close (o : Fin 5) :
    ∑ j, PV o j * ε0VL j + 1 / 2 * GBV o + 1 / 10 ^ 5 * GV o 0 + 2 / 10 ^ 5 * GV o 1 +
      ∑ j, GV o j * εVL j ≤ bV o := by
  fin_cases o <;> simp [PV, GV, ε0VL, εVL, GBV, bV, Fin.sum_univ_eight] <;> norm_num

theorem εHL_nonneg (j : Fin 9) : 0 ≤ εHL j := by fin_cases j <;> simp [εHL] <;> norm_num
theorem εVL_nonneg (j : Fin 8) : 0 ≤ εVL j := by fin_cases j <;> simp [εVL] <;> norm_num

theorem outH3_vAcc : outH 3 ⬝ᵥ vAcc = 1 := by
  rw [show outH 3 = Pi.single 6 1 from rfl, single_dotProduct]
  simp [vAcc]

/-! ## Forward invariance of the box along the leg -/

section Box

variable {ξV wV : ℕ → Fin 8 → ℝ} {aZ d1Z d2Z : ℕ → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ}
  {aH d1H d2H : ℕ → Fin 2 → ℝ} {t₀ : ℕ}

/-- The horizontal output `o` of axis `a` at `t₀ + N`, with the reference terms bounded by `BA`,
`B1`, `B2`, from the per-tick disturbance bound. -/
theorem outH_bound (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (a : Fin 2) (o : Fin 5)
    (N : ℕ) (hw : ∀ k < N, ∀ j, |wH (t₀ + k) a j| ≤ εHL j) {BA B1 B2 : ℝ}
    (hA : |∑ k ∈ range N, (fun t => aH t a) (t₀ + k) *
      rsp Horizontal.AhR (outH o) Horizontal.BhR (N - 1 - k)| ≤ BA)
    (h1 : |∑ k ∈ range N, (fun t => -d1H t a) (t₀ + k) *
      rsp Horizontal.AhR (outH o) Horizontal.e0 (N - 1 - k)| ≤ B1)
    (h2 : |∑ k ∈ range N, (fun t => -d2H t a) (t₀ + k) *
      rsp Horizontal.AhR (outH o) Horizontal.e1 (N - 1 - k)| ≤ B2) :
    |outH o ⬝ᵥ ξH (t₀ + N) a| ≤ ∑ j, PH o j * ε0HL j + BA + B1 + B2 + ∑ j, GH o j * εHL j :=
  out_le Horizontal.AhR (fun t => ξH t a) (fun t => wH t a) (fun t => aH t a)
    (fun t => -d1H t a) (fun t => -d2H t a) Horizontal.BhR Horizontal.e0 Horizontal.e1 t₀
    (fun t ht => hM.stepH t ht a) (outH o) N ε0HL (PH o) (GH o) εHL (hM.initH a)
    (fun j m => peakH' o j m) (fun j N => gainH' o j N) εHL_nonneg hw hA h1 h2

/-- The vertical output `o` at `t₀ + N`. -/
theorem outV_bound (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (o : Fin 5)
    (N : ℕ) (hw : ∀ k < N, ∀ j, |wV (t₀ + k) j| ≤ εVL j) {BA B1 B2 : ℝ}
    (hA : |∑ k ∈ range N, aZ (t₀ + k) * rsp Vertical.AvR (outV o) Vertical.BvR (N - 1 - k)| ≤ BA)
    (h1 : |∑ k ∈ range N, (fun t => -d1Z t) (t₀ + k) *
      rsp Vertical.AvR (outV o) Vertical.e0 (N - 1 - k)| ≤ B1)
    (h2 : |∑ k ∈ range N, (fun t => -d2Z t) (t₀ + k) *
      rsp Vertical.AvR (outV o) Vertical.e1 (N - 1 - k)| ≤ B2) :
    |outV o ⬝ᵥ ξV (t₀ + N)| ≤ ∑ j, PV o j * ε0VL j + BA + B1 + B2 + ∑ j, GV o j * εVL j :=
  out_le Vertical.AvR ξV wV aZ (fun t => -d1Z t) (fun t => -d2Z t) Vertical.BvR Vertical.e0
    Vertical.e1 t₀ hM.stepV (outV o) N ε0VL (PV o) (GV o) εVL hM.initV
    (fun j m => peakV' o j m) (fun j N => gainV' o j N) εVL_nonneg hw hA h1 h2

/-- **The command of axis `a` at `t₀ + N`**, in the shifted coordinates `ζ = ξ − asp • vAcc`:
`c₁ = asp + c₁(ζ)`, and `ζ` is driven by the jerk. -/
theorem c1_bound (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) (a : Fin 2)
    (N : ℕ) (hT : ∀ k < N, TickBounds ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k)) :
    |outH 3 ⬝ᵥ ξH (t₀ + N) a| ≤ bHL 3 := by
  set ζ : ℕ → Fin 9 → ℝ := fun t => ξH t a - aH t a • vAcc with hζ
  have hstep : ∀ t, t₀ ≤ t → ζ (t + 1) = Horizontal.AhR *ᵥ ζ t +
      ((fun t => -(aH (t + 1) a - aH t a)) t • vAcc + (fun t => -d1H t a) t • Horizontal.e0 +
        (fun t => -d2H t a) t • Horizontal.e1 + (fun t => wH t a) t) := fun t ht =>
    zeta_step (fun t => ξH t a) (fun t => wH t a) (fun t => aH t a) (fun t => d1H t a)
      (fun t => d2H t a) t (hM.stepH t ht a)
  have hx : ∀ j, |ζ t₀ j| ≤ ε0HL j + 1 / 1000 * vAcc j := by
    intro j
    have h1 := hM.initH a j
    have h2 := hM.initA a
    have hv := vAcc_nonneg j
    simp only [hζ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hv]
    nlinarith [abs_nonneg (aH t₀ a)]
  have e : outH 3 ⬝ᵥ ξH (t₀ + N) a = outH 3 ⬝ᵥ ζ (t₀ + N) + aH (t₀ + N) a := by
    simp only [hζ, dotProduct_sub, dotProduct_smul, outH3_vAcc, smul_eq_mul, mul_one]
    ring
  have hA : |aH (t₀ + N) a| ≤ 1501 / 1000 + 13 / 1000 := by
    rcases N with _ | k
    · have := hM.initA a; simp only [add_zero]; linarith
    · have h1 := (hT k (by omega)).baH a
      have h2 := (hT k (by omega)).bjH a
      rw [show t₀ + (k + 1) = t₀ + k + 1 by omega]
      have := abs_sub_abs_le_abs_sub (aH (t₀ + k + 1) a) (aH (t₀ + k) a)
      linarith
  rw [e]
  have B := out_le Horizontal.AhR ζ (fun t => wH t a) (fun t => -(aH (t + 1) a - aH t a))
    (fun t => -d1H t a) (fun t => -d2H t a) vAcc Horizontal.e0 Horizontal.e1 t₀ hstep (outH 3) N
    (fun j => ε0HL j + 1 / 1000 * vAcc j) (PH 3) (GH 3) εHL hx (fun j m => peakH' 3 j m)
    (fun j N => gainH' 3 j N) εHL_nonneg (fun k hk j => (hT k hk).bwH a j)
    (env_const_neg _ (fun t => aH (t + 1) a - aH t a) t₀ N (by norm_num)
      (fun k hk => (hT k hk).bjH a) (hg.gainC1 N))
    (env_const_neg _ (fun t => d1H t a) t₀ N (by norm_num) (fun k hk => (hT k hk).bd1H a)
      (gH0 3 N))
    (env_const_neg _ (fun t => d2H t a) t₀ N (by norm_num) (fun k hk => (hT k hk).bd2H a)
      (gH1 3 N))
  have C := boxC1_close
  have := abs_add_le (outH 3 ⬝ᵥ ζ (t₀ + N)) (aH (t₀ + N) a)
  linarith

/-- **The command rate of axis `a` at `t₀ + N`**, in the doubly shifted coordinates
`ζ₂ = ξ − asp • vAcc − d₂ • u₂` (the rate sees neither shift), driven by the jerk, the position
defect and the change of the velocity defect. -/
theorem rate_bound (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) (a : Fin 2)
    (N : ℕ) (hT : ∀ k < N, TickBounds ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k)) :
    |outH 4 ⬝ᵥ ξH (t₀ + N) a| ≤ bHL 4 := by
  set ζ : ℕ → Fin 9 → ℝ := fun t => ξH t a - aH t a • vAcc - d2H t a • u2 with hζ
  have hstep : ∀ t, t₀ ≤ t → ζ (t + 1) = Horizontal.AhR *ᵥ ζ t +
      ((fun t => -(aH (t + 1) a - aH t a)) t • vAcc + (fun t => -d1H t a) t • Horizontal.e0 +
        (fun t => -(d2H (t + 1) a - d2H t a)) t • u2 + (fun t => wH t a) t) := fun t ht =>
    zeta2_step (fun t => ξH t a) (fun t => wH t a) (fun t => aH t a) (fun t => d1H t a)
      (fun t => d2H t a) t (hM.stepH t ht a)
  have hx : ∀ j, |ζ t₀ j| ≤ ε0HL j + 1 / 1000 * vAcc j + 1 / 10 ^ 6 * u2a j := by
    intro j
    have h1 := hM.initH a j
    have h2 := hM.initA a
    have h3 := hM.initD a
    have hv := vAcc_nonneg j
    have hu := u2_abs j
    have hu0 := u2a_nonneg j
    simp only [hζ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_sub _ _).trans ?_) ?_
    · rw [abs_mul, abs_of_nonneg hv]
      nlinarith [abs_nonneg (aH t₀ a)]
    · rw [abs_mul]
      nlinarith [abs_nonneg (d2H t₀ a), abs_nonneg (u2 j)]
  have e : outH 4 ⬝ᵥ ξH (t₀ + N) a = outH 4 ⬝ᵥ ζ (t₀ + N) := by
    simp only [hζ, dotProduct_sub, dotProduct_smul, outH4_vAcc, outH4_u2, smul_zero, sub_zero]
  rw [e]
  have B := out_le Horizontal.AhR ζ (fun t => wH t a) (fun t => -(aH (t + 1) a - aH t a))
    (fun t => -d1H t a) (fun t => -(d2H (t + 1) a - d2H t a)) vAcc Horizontal.e0 u2 t₀ hstep
    (outH 4) N (fun j => ε0HL j + 1 / 1000 * vAcc j + 1 / 10 ^ 6 * u2a j) (PH 4) (GH 4) εHL hx
    (fun j m => peakH' 4 j m) (fun j N => gainH' 4 j N) εHL_nonneg
    (fun k hk j => (hT k hk).bwH a j)
    (env_const_neg _ (fun t => aH (t + 1) a - aH t a) t₀ N (by norm_num)
      (fun k hk => (hT k hk).bjH a) (hg.gainJ N))
    (env_const_neg _ (fun t => d1H t a) t₀ N (by norm_num) (fun k hk => (hT k hk).bd1H a)
      (gH0 4 N))
    (env_const_neg _ (fun t => d2H (t + 1) a - d2H t a) t₀ N (by norm_num)
      (fun k hk => (hT k hk).bdd2H a) (gainU2 N))
  have C := boxRate_close
  linarith

/-- **The box holds at every tick up to the horizon** (strong induction). -/
theorem leg_box (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) :
    ∀ N, t₀ + N ≤ hzn → BoxL ξV ξH (t₀ + N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    have hT : ∀ k < N, TickBounds ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k) := fun k hk =>
      hM.tick (t₀ + k) (by omega) (by omega) (fun k' h1 h2 => by
        obtain ⟨m, rfl⟩ : ∃ m, k' = t₀ + m := ⟨k' - t₀, by omega⟩
        exact ih m (by omega) (by omega))
    refine ⟨fun o => ?_, fun a o => ?_⟩
    · have B := outV_bound hM o N (fun k hk j => (hT k hk).bwV j)
        (env_const _ aZ t₀ N (by norm_num) (fun k hk => (hT k hk).baZ) (hg.gainBV o N))
        (env_const_neg _ d1Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd1Z) (gV0 o N))
        (env_const_neg _ d2Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd2Z) (gV1 o N))
      have C := boxV_close o
      linarith
    · by_cases h4 : o = 4
      · subst h4; exact rate_bound hM hg a N hT
      by_cases h3 : o = 3
      · subst h3; exact c1_bound hM hg a N hT
      have ho : o.val < 3 := by
        have := o.isLt
        have h4' : o.val ≠ 4 := fun h => h4 (Fin.ext h)
        have h3' : o.val ≠ 3 := fun h => h3 (Fin.ext h)
        omega
      have B := outH_bound hM a o N (fun k hk j => (hT k hk).bwH a j)
        (env_const _ (fun t => aH t a) t₀ N (by norm_num) (fun k hk => (hT k hk).baH a)
          (hg.gainB o N))
        (env_const_neg _ (fun t => d1H t a) t₀ N (by norm_num) (fun k hk => (hT k hk).bd1H a)
          (gH0 o N))
        (env_const_neg _ (fun t => d2H t a) t₀ N (by norm_num) (fun k hk => (hT k hk).bd2H a)
          (gH1 o N))
      have C := boxH_close o ho
      linarith

/-- With the box at every tick, the per-tick bounds hold at every tick before the horizon. -/
theorem leg_ticks (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) :
    ∀ t, t₀ ≤ t → t < hzn → TickBounds ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t := fun t h1 h2 =>
  hM.tick t h1 h2 fun k hk1 hk2 => by
    obtain ⟨m, rfl⟩ : ∃ m, k = t₀ + m := ⟨k - t₀, by omega⟩
    exact leg_box hM hg m (by omega)

end Box

/-! ## The tracking tube along the leg, the completion check, and the hold -/

/-- The disturbance and start part of the horizontal position error. -/
def τe : ℝ := ∑ j, PH 0 j * ε0HL j + ∑ j, GH 0 j * εHL j

/-- The disturbance and start part of the vertical position error. -/
def τz : ℝ := ∑ j, PV 0 j * ε0VL j + ∑ j, GV 0 j * εVL j

/-- The vertical position error on the leg. -/
def vzL : ℝ := 1 / 1000 * GBV 0 + 1 / 10 ^ 8 * GV 0 0 + 1 / 10 ^ 7 * GV 0 1 + τz

/-- The horizontal position error `Mc` ticks after the leg's S-curve has finished (before the
completion): the tails past `Mc` of the leg's reference terms (the velocity defect through its sum
over the run, `≤ 1/4`, and the peak of its tail), the full gains on the residual forcing of the
finished S-curve, and the tube. -/
def hC : ℝ := 1501 / 1000 * TBc + 1 / 10 ^ 6 * GB 0 + (13 / 10 ^ 5 * T0c + 1 / 10 ^ 8 * GH 0 0) +
  (1 / 4 * P1c + 3 / 10 ^ 6 * GH 0 1) + τe

/-- The horizontal position error once the reference has stopped for `Mt` ticks. -/
def hT : ℝ := 1501 / 1000 * TB + 1 / 10 ^ 6 * GB 0 + (13 / 10 ^ 5 * T0 + 3 / 10 ^ 9 * GH 0 0) +
  (1 / 4 * P1 + 3 / 10 ^ 6 * GH 0 1) + τe

/-- The vertical position error once the reference has stopped for `Mt` ticks. -/
def vT : ℝ := 1 / 2 * TBV + 1 / 10 ^ 6 * GBV 0 + (1 / 10 ^ 5 * TV0 + 3 / 10 ^ 9 * GV 0 0) +
  (2 / 10 ^ 5 * TV1 + 3 / 10 ^ 6 * GV 0 1) + τz

theorem τe_le : τe ≤ 2504 / 1000000 := by
  simp [τe, PH, GH, ε0HL, εHL, Fin.sum_univ_succ]; norm_num
theorem τe_nonneg : 0 ≤ τe := by
  simp [τe, PH, GH, ε0HL, εHL, Fin.sum_univ_succ]; norm_num
theorem vzL_le : vzL ≤ 791 / 100000 := by
  simp [vzL, τz, GBV, PV, GV, ε0VL, εVL, Fin.sum_univ_eight]; norm_num
theorem hC_le : hC ≤ 54 / 1000 := by
  simp [hC, τe, TBc, T0c, P1c, GB, PH, GH, ε0HL, εHL, Fin.sum_univ_succ]; norm_num
theorem hT_le : hT ≤ 971 / 100000 := by
  simp [hT, τe, TB, T0, P1, GB, PH, GH, ε0HL, εHL, Fin.sum_univ_succ]; norm_num
theorem vT_le : vT ≤ 922 / 100000 := by
  simp [vT, τz, TBV, TV0, TV1, GBV, PV, GV, ε0VL, εVL, Fin.sum_univ_eight]; norm_num

theorem outH0_dot (v : Fin 9 → ℝ) : outH 0 ⬝ᵥ v = v 0 := by
  rw [show outH 0 = Pi.single 0 1 from rfl, single_dotProduct, one_mul]

theorem outV0_dot (v : Fin 8 → ℝ) : outV 0 ⬝ᵥ v = v 0 := by
  rw [show outV 0 = Pi.single 0 1 from rfl, single_dotProduct, one_mul]

section Tube

variable {ξV wV : ℕ → Fin 8 → ℝ} {aZ d1Z d2Z : ℕ → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ}
  {aH d1H d2H : ℕ → Fin 2 → ℝ} {t₀ : ℕ}

/-- **The vertical tube on the leg**: the vertical target constant up to its `float` rounding
(acceleration `≤ 10⁻³`, defects `≤ 10⁻⁸`, `10⁻⁷`), the vertical error is at most `vzL ≤ 7.91` mm. -/
theorem leg_z (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) (Tc : ℕ)
    (hc : ∀ t, t₀ ≤ t → t < Tc → |aZ t| ≤ 1 / 1000 ∧ |d1Z t| ≤ 1 / 10 ^ 8 ∧ |d2Z t| ≤ 1 / 10 ^ 7)
    (N : ℕ) (hN : t₀ + N ≤ Tc) (hNz : t₀ + N ≤ hzn) :
    |ξV (t₀ + N) 0| ≤ vzL := by
  have hT := leg_ticks hM hg
  have B := outV_bound hM 0 N (fun k hk j => (hT (t₀ + k) (by omega) (by omega)).bwV j)
    (env_const _ aZ t₀ N (by norm_num) (fun k hk => (hc (t₀ + k) (by omega) (by omega)).1)
      (hg.gainBV 0 N))
    (env_const_neg _ d1Z t₀ N (by norm_num)
      (fun k hk => (hc (t₀ + k) (by omega) (by omega)).2.1) (gV0 0 N))
    (env_const_neg _ d2Z t₀ N (by norm_num)
      (fun k hk => (hc (t₀ + k) (by omega) (by omega)).2.2) (gV1 0 N))
  rw [outV0_dot] at B
  have e : vzL = ∑ j, PV 0 j * ε0VL j + 1 / 1000 * GBV 0 + 1 / 10 ^ 8 * GV 0 0 +
      1 / 10 ^ 7 * GV 0 1 + ∑ j, GV 0 j * εVL j := by
    simp only [vzL, τz]; ring
  rw [e]; exact B

/-- **The horizontal error `Mc` ticks after the leg's S-curve has finished**: if from tick `L` to
the output tick the target acceleration and the defects are below `10⁻⁶`, `10⁻⁸`, `3·10⁻⁶`, and the
velocity defect sums to at most `1/4` over the run, then `Mc` ticks after `L` the position error is
at most `hC ≤ 0.054`. -/
theorem tail_e_c (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) (L : ℕ)
    (a : Fin 2) (N : ℕ)
    (hz : ∀ t, L ≤ t → t < t₀ + N →
      |aH t a| ≤ 1 / 10 ^ 6 ∧ |d1H t a| ≤ 1 / 10 ^ 8 ∧ |d2H t a| ≤ 3 / 10 ^ 6)
    (hS : ∑ k ∈ range N, |d2H (t₀ + k) a| ≤ 1 / 4)
    (hNL : L + Mc ≤ t₀ + N) (hNz : t₀ + N ≤ hzn) :
    |ξH (t₀ + N) a 0| ≤ hC := by
  have hT' := leg_ticks hM hg
  have B := outH_bound hM a 0 N (fun k hk j => (hT' (t₀ + k) (by omega) (by omega)).bwH a j)
    (env_tail2 _ (fun t => aH t a) t₀ N L Mc (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).baH a)
      (fun t ht ht' => (hz t ht ht').1) hNL hg.tailBc (hg.gainB 0 N))
    (env_tail2_neg _ (fun t => d1H t a) t₀ N L Mc (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).bd1H a)
      (fun t ht ht' => (hz t ht ht').2.1) hNL hg.tail0c (gH0 0 N))
    (env_tail_l1_neg _ (fun t => d2H t a) t₀ N L Mc (by norm_num [P1c]) (by norm_num) hS
      (fun t ht ht' => (hz t ht ht').2.2) hNL hg.peak1c (gH1 0 N))
  rw [outH0_dot] at B
  have e : hC = ∑ j, PH 0 j * ε0HL j + (1501 / 1000 * TBc + 1 / 10 ^ 6 * GB 0) +
      (13 / 10 ^ 5 * T0c + 1 / 10 ^ 8 * GH 0 0) + (1 / 4 * P1c + 3 / 10 ^ 6 * GH 0 1) +
      ∑ j, GH 0 j * εHL j := by
    simp only [hC, τe]; ring
  rw [e]; exact B

/-- **The horizontal error after the reference stops**: if from tick `L` on the target
acceleration and the defects are below `10⁻⁶`, `3·10⁻⁹`, `3·10⁻⁶` (the target held), and the
velocity defect sums to at most `1/4` over the run, then `Mt` ticks later the position error is at
most `hT ≤ 9.71` mm. -/
theorem tail_e (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) (L : ℕ)
    (a : Fin 2)
    (hz : ∀ t, L ≤ t → |aH t a| ≤ 1 / 10 ^ 6 ∧ |d1H t a| ≤ 3 / 10 ^ 9 ∧ |d2H t a| ≤ 3 / 10 ^ 6)
    (N : ℕ) (hS : ∑ k ∈ range N, |d2H (t₀ + k) a| ≤ 1 / 4)
    (hNL : L + Mt ≤ t₀ + N) (hNz : t₀ + N ≤ hzn) :
    |ξH (t₀ + N) a 0| ≤ hT := by
  have hT' := leg_ticks hM hg
  have B := outH_bound hM a 0 N (fun k hk j => (hT' (t₀ + k) (by omega) (by omega)).bwH a j)
    (env_tail2 _ (fun t => aH t a) t₀ N L Mt (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).baH a)
      (fun t ht _ => (hz t ht).1) hNL hg.tailB (hg.gainB 0 N))
    (env_tail2_neg _ (fun t => d1H t a) t₀ N L Mt (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).bd1H a)
      (fun t ht _ => (hz t ht).2.1) hNL hg.tail0 (gH0 0 N))
    (env_tail_l1_neg _ (fun t => d2H t a) t₀ N L Mt (by norm_num [P1]) (by norm_num) hS
      (fun t ht _ => (hz t ht).2.2) hNL hg.peak1 (gH1 0 N))
  rw [outH0_dot] at B
  have e : hT = ∑ j, PH 0 j * ε0HL j + (1501 / 1000 * TB + 1 / 10 ^ 6 * GB 0) +
      (13 / 10 ^ 5 * T0 + 3 / 10 ^ 9 * GH 0 0) + (1 / 4 * P1 + 3 / 10 ^ 6 * GH 0 1) +
      ∑ j, GH 0 j * εHL j := by
    simp only [hT, τe]; ring
  rw [e]; exact B

/-- **The vertical error after the reference stops**: at most `vT ≤ 9.21` mm. -/
theorem tail_z (hM : LegModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) (L : ℕ)
    (hz : ∀ t, L ≤ t → |aZ t| ≤ 1 / 10 ^ 6 ∧ |d1Z t| ≤ 3 / 10 ^ 9 ∧ |d2Z t| ≤ 3 / 10 ^ 6) (N : ℕ)
    (hNL : L + Mt ≤ t₀ + N) (hNz : t₀ + N ≤ hzn) :
    |ξV (t₀ + N) 0| ≤ vT := by
  have hT' := leg_ticks hM hg
  have B := outV_bound hM 0 N (fun k hk j => (hT' (t₀ + k) (by omega) (by omega)).bwV j)
    (env_tail2 _ aZ t₀ N L Mt (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).baZ) (fun t ht _ => (hz t ht).1) hNL
      hg.tailBV (hg.gainBV 0 N))
    (env_tail2_neg _ d1Z t₀ N L Mt (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).bd1Z) (fun t ht _ => (hz t ht).2.1) hNL
      hg.tail0V (gV0 0 N))
    (env_tail2_neg _ d2Z t₀ N L Mt (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).bd2Z) (fun t ht _ => (hz t ht).2.2) hNL
      hg.tail1V (gV1 0 N))
  rw [outV0_dot] at B
  have e : vT = ∑ j, PV 0 j * ε0VL j + (1 / 2 * TBV + 1 / 10 ^ 6 * GBV 0) +
      (1 / 10 ^ 5 * TV0 + 3 / 10 ^ 9 * GV 0 0) + (2 / 10 ^ 5 * TV1 + 3 / 10 ^ 6 * GV 0 1) +
      ∑ j, GV 0 j * εVL j := by
    simp only [vT, τz]; ring
  rw [e]; exact B

end Tube

/-! ## Three axes -/

/-- **The 3D error at the completion check is below 7.7 cm.** -/
theorem complete_3d {e₀ e₁ ez : ℝ} (h₀ : |e₀| ≤ hC) (h₁ : |e₁| ≤ hC) (hz : |ez| ≤ vzL) :
    e₀ ^ 2 + e₁ ^ 2 + ez ^ 2 ≤ (77 / 1000) ^ 2 := by
  have a0 : e₀ ^ 2 ≤ (54 / 1000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₀.trans hC_le) 2
  have a1 : e₁ ^ 2 ≤ (54 / 1000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₁.trans hC_le) 2
  have az : ez ^ 2 ≤ (791 / 100000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hz.trans vzL_le) 2
  nlinarith

/-- **The 3D error in the hold window is below 1.66 cm.** -/
theorem hold_3d {e₀ e₁ ez : ℝ} (h₀ : |e₀| ≤ hT) (h₁ : |e₁| ≤ hT) (hz : |ez| ≤ vT) :
    e₀ ^ 2 + e₁ ^ 2 + ez ^ 2 ≤ (166 / 10000) ^ 2 := by
  have a0 : e₀ ^ 2 ≤ (971 / 100000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₀.trans hT_le) 2
  have a1 : e₁ ^ 2 ≤ (971 / 100000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₁.trans hT_le) 2
  have az : ez ^ 2 ≤ (922 / 100000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hz.trans vT_le) 2
  nlinarith

end

end Contracts.Track.Reach.Leg
