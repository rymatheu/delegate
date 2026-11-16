import Contracts.Track.Induction.NominalGainV
import Contracts.Track.Induction.NominalGainH
import Contracts.Track.Reach.Composite

/-!
# The glue of hover, parts (2)–(4): the corrected statement with ℓ1 tubes, and its constants

REACH.md §"Glue". `HoverGlue` (Loop.lean) is false as stated (`GlueFalse.lean`), and its
`Vc`-ball form cannot carry the code's floors (the `acosf` quantization of the commanded tilt alone
is `Vc ≈ 3.6·10⁵ ≫ 179`, `GlueFalse.lean`, REACH.md §"Glue"). This file states the hover glue in the
form INDUCTION.md uses (per-row disturbance bounds, ℓ1 and peak gains of the exact models) and
proves the hover statement from it.

**The readouts** (part (2)) are those of `Induction/Run.lean`: `ξV w₀ x t` (vertical,
`Vertical.errOf (vabs …)`: plant `z`, `vz` against the target, `_pid_vel_d_m._error`,
`_pid_accel_d_m._error`, the integrator minus its trim `hover − 1/2.25`, the throttle filter,
`_throttle_in`, the mean held actuator) and `ξH w₀ x t a` (one NE axis, `Horizontal.errOf (habs …)`:
plant position and velocity against the target, `_pid_vel_ne_m`'s error, derivative and integrator,
the attitude-lag state `aLag`, the last three commands). With the target held at `wp`, their
position coordinates are `pos − wp` (`ξV_pos`, `ξH_pos`).

**The model-level theorem** (`hover_box`, part (3)): if from a tick `t₀` the two channels follow
`A_v`, `A_h` with disturbances bounded per coordinate by `εVh`, `εHh` whenever the state is in the
box `BoxT` (`bVh`, `bHh`), and the start is a position offset `d` with `|d_i| ≤ 0.021` plus
deviations within `ε0Vh`, `ε0Hh`, then the box holds at every tick (forward invariance through one
tick, by strong induction on the ℓ1 tube) and every watched output is within its free response plus
its tube `Σ P ε₀ + Σ G ε`. `hover_box_gen` does the same from any start in the weighted-ℓ1
region `RegionG`.

**The constants** (part (4); stated on the loop in `GlueLoop.lean`): `λ = 0.9997` per tick (the horizontal
certificate; vertical `0.998`), `c = √(γ_h P_h,00) ≤ 3.47` (vertical `1.452`), `b ≤ 3.9 mm`
(`√(2·2.51² + 1.08²)` mm), region `|d_i| ≤ 2.1 cm` per axis (binding: the command-rate box
`|c₁ − c₂| ≤ 0.05`, peak gain `2.3`; the vertical admits `9.7 cm`).
-/

namespace Contracts.Track.Reach.Glue

open Matrix Finset Contracts.Track.Induction Contracts.Track.Induction.Nominal

noncomputable section

/-! ## The certified gains (as in `Nominal.lean`, without its corner part) -/

theorem peakV' (o : Fin 5) (j : Fin 8) (m : ℕ) : |resp Vertical.AvR (outV o) m j| ≤ PV o j := by
  rw [PV_eq]
  fin_cases o
  · exact GainV.out0.2 j m
  · exact GainV.out1.2 j m
  · exact GainV.out2.2 j m
  · exact GainV.out3.2 j m
  · exact GainV.out4.2 j m

theorem gainV' (o : Fin 5) (j : Fin 8) (N : ℕ) :
    ∑ m ∈ range N, |resp Vertical.AvR (outV o) m j| ≤ GV o j := by
  rw [GV_eq]
  fin_cases o
  · exact GainV.out0.1 j N
  · exact GainV.out1.1 j N
  · exact GainV.out2.1 j N
  · exact GainV.out3.1 j N
  · exact GainV.out4.1 j N

theorem peakH' (o : Fin 5) (j : Fin 9) (m : ℕ) : |resp Horizontal.AhR (outH o) m j| ≤ PH o j := by
  rw [PH_eq]
  fin_cases o
  · exact GainH.out0.2 j m
  · exact GainH.out1.2 j m
  · exact GainH.out2.2 j m
  · exact GainH.out3.2 j m
  · exact GainH.out4.2 j m

theorem gainH' (o : Fin 5) (j : Fin 9) (N : ℕ) :
    ∑ m ∈ range N, |resp Horizontal.AhR (outH o) m j| ≤ GH o j := by
  rw [GH_eq]
  fin_cases o
  · exact GainH.out0.1 j N
  · exact GainH.out1.1 j N
  · exact GainH.out2.1 j N
  · exact GainH.out3.1 j N
  · exact GainH.out4.1 j N

/-! ## One channel: free response of the offset plus the tube -/

section Chan

variable {n : ℕ}

/-- **The tube around the free response of an offset.** From `t₀`, `ξ (t + 1) = A ξ t + w t`; the
start is the offset `d` in coordinate `i₀` plus a deviation within `e0`; the disturbances are within
`e` for `N` ticks. Then output `o` at `t₀ + N` is within `Σ P e0 + Σ G e` of `d` times the response of
`o` to the unit offset. -/
theorem chan_tube (A : Matrix (Fin n) (Fin n) ℝ) (ξ w : ℕ → Fin n → ℝ) (t₀ N : ℕ) (i₀ : Fin n)
    (d : ℝ) (hstep : ∀ t, t₀ ≤ t → ξ (t + 1) = A *ᵥ ξ t + w t) (o e0 e P G : Fin n → ℝ)
    (he : ∀ j, 0 ≤ e j) (h0 : ∀ j, |ξ t₀ j - (Pi.single i₀ d : Fin n → ℝ) j| ≤ e0 j)
    (hw : ∀ k < N, ∀ j, |w (t₀ + k) j| ≤ e j)
    (hP : ∀ j m, |resp A o m j| ≤ P j) (hG : ∀ j N, ∑ m ∈ range N, |resp A o m j| ≤ G j) :
    |o ⬝ᵥ ξ (t₀ + N) - d * resp A o N i₀| ≤ ∑ j, P j * e0 j + ∑ j, G j * e j := by
  set η : ℕ → Fin n → ℝ := fun t => ξ t - (A ^ (t - t₀)) *ᵥ Pi.single i₀ d with hη
  have hη' : ∀ t, t₀ ≤ t → η (t + 1) = A *ᵥ η t + w t := by
    intro t ht
    simp only [hη, hstep t ht, mulVec_sub, mulVec_mulVec]
    rw [show t + 1 - t₀ = (t - t₀) + 1 by omega, pow_succ']
    abel
  have hη0 : η t₀ = ξ t₀ - Pi.single i₀ d := by
    simp only [hη, Nat.sub_self, pow_zero, one_mulVec]
  have h0' : ∀ j, |η t₀ j| ≤ e0 j := by
    intro j; rw [hη0, Pi.sub_apply]; exact h0 j
  have T := tube_out A η w t₀ N hη' o e0 e P G he h0' hw hP hG
  have e1 : o ⬝ᵥ η (t₀ + N) = o ⬝ᵥ ξ (t₀ + N) - d * resp A o N i₀ := by
    simp only [hη, dotProduct_sub, Nat.add_sub_cancel_left, resp]
    congr 1
    rw [show (Pi.single i₀ d : Fin n → ℝ) = d • Pi.single i₀ 1 by
      ext j; simp [Pi.single_apply]]
    rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
  rw [← e1]; exact T

end Chan

/-! ## The hover constants -/

/-- Box of the vertical outputs `ez, ev, I, f, u` (INDUCTION.md's `bV`). -/
def bVh : Fin 5 → ℝ := ![1 / 10, 1 / 2, 1 / 2, 3 / 25, 3 / 25]

/-- Box of the horizontal outputs `e, ev, I, c₁, c₁ − c₂`; the command `|c₁| ≤ 0.5` m/s² (tilt
`≤ 0.051` rad), tighter than the flight box's `4`, so that the tilt coupling into the vertical
channel is a small disturbance. -/
def bHh : Fin 5 → ℝ := ![1 / 10, 1 / 2, 5, 1 / 2, 1 / 20]

/-- Per-tick disturbance of the vertical channel at hover, per coordinate: INDUCTION.md's `εV`
(the code's `βcode` at the region's magnitudes) plus the structured part `CtrlV.wS` at hover (plant
remainder and tilt coupling `≤ 3·10⁻³` m/s² through `(h²/2, h)`, the sampled specific force's
`float` floor `≤ 7.4·10⁻⁷` m/s² through `αA`). -/
def εVh : Fin 8 → ℝ := ![1 / 10 ^ 8, 76 / 10 ^ 7, 2 / 10 ^ 7, 42 / 10 ^ 7, 2 / 10 ^ 7, 1 / 10 ^ 7,
  32 / 10 ^ 7, 4 / 10 ^ 7]

/-- Per-tick disturbance of a horizontal axis at hover: INDUCTION.md's `εH` (controller and plant
rows, the attitude deviation `≤ 0.01` m/s² from the lag law, which covers the `acosf` tilt
quantization `≤ 2.4·10⁻³` m/s²). -/
def εHh : Fin 9 → ℝ := ![22 / 10 ^ 8, 25 / 10 ^ 6, 37 / 10 ^ 7, 231 / 10 ^ 6, 62 / 10 ^ 8, 0,
  161 / 10 ^ 6, 0, 0]

/-- The start's deviation from the pure offset, vertical (`0` on the position coordinate): the
trims (`hover − 1/2.25` against the integrator, the throttle filter, `_throttle_in`, the held
actuators) and the relaxed controller. -/
def ε0Vh : Fin 8 → ℝ := ![0, 1 / 10 ^ 6, 1 / 10 ^ 5, 1 / 10 ^ 5, 1 / 10 ^ 4, 1 / 10 ^ 4,
  1 / 10 ^ 4, 1 / 10 ^ 4]

/-- The start's deviation from the pure offset, horizontal. -/
def ε0Hh : Fin 9 → ℝ := ![0, 1 / 10 ^ 6, 1 / 10 ^ 5, 1 / 10 ^ 4, 1 / 10 ^ 5, 1 / 10 ^ 5,
  1 / 10 ^ 4, 1 / 10 ^ 4, 1 / 10 ^ 4]

/-- The admissible offset per axis. -/
def dMax : ℝ := 21 / 1000

theorem εVh_nonneg (j : Fin 8) : 0 ≤ εVh j := by fin_cases j <;> simp [εVh] <;> norm_num
theorem εHh_nonneg (j : Fin 9) : 0 ≤ εHh j := by fin_cases j <;> simp [εHh] <;> norm_num

/-- **The region closes (vertical)**: offset, start deviation and tube inside the box. -/
theorem regionV (o : Fin 5) :
    PV o 0 * dMax + (∑ j, PV o j * ε0Vh j + ∑ j, GV o j * εVh j) ≤ bVh o := by
  fin_cases o <;> simp [PV, GV, ε0Vh, εVh, bVh, dMax, Fin.sum_univ_eight] <;> norm_num

/-- **The region closes (horizontal).** -/
theorem regionH (o : Fin 5) :
    PH o 0 * dMax + (∑ j, PH o j * ε0Hh j + ∑ j, GH o j * εHh j) ≤ bHh o := by
  fin_cases o <;> simp [PH, GH, ε0Hh, εHh, bHh, dMax, Fin.sum_univ_succ] <;> norm_num

/-- The position tube, vertical: `≤ 1.08` mm. -/
theorem tubeV0 : ∑ j, PV 0 j * ε0Vh j + ∑ j, GV 0 j * εVh j ≤ 108 / 100000 := by
  simp [PV, GV, ε0Vh, εVh, Fin.sum_univ_eight]; norm_num

/-- The position tube, horizontal: `≤ 2.51` mm. -/
theorem tubeH0 : ∑ j, PH 0 j * ε0Hh j + ∑ j, GH 0 j * εHh j ≤ 251 / 100000 := by
  simp [PH, GH, ε0Hh, εHh, Fin.sum_univ_succ]; norm_num

/-! ## The model-level hover theorem -/

/-- The region at tick `t`: every watched output inside its box. -/
def BoxT (ξV : ℕ → Fin 8 → ℝ) (ξH : ℕ → Fin 2 → Fin 9 → ℝ) (t : ℕ) : Prop :=
  (∀ o, |outV o ⬝ᵥ ξV t| ≤ bVh o) ∧ ∀ a o, |outH o ⬝ᵥ ξH t a| ≤ bHh o

/-- **The hover hypotheses on the error coordinates** from tick `t₀`: the model steps, the start
(position offset `d`, NED, plus deviations), and the per-row disturbance bounds inside the box. -/
structure HoverModel (ξV wV : ℕ → Fin 8 → ℝ) (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (t₀ : ℕ)
    (d : Fin 3 → ℝ) : Prop where
  stepV : ∀ t, t₀ ≤ t → ξV (t + 1) = Vertical.AvR *ᵥ ξV t + wV t
  stepH : ∀ t, t₀ ≤ t → ∀ a, ξH (t + 1) a = Horizontal.AhR *ᵥ ξH t a + wH t a
  initV : ∀ j, |ξV t₀ j - (Pi.single 0 (d 2) : Fin 8 → ℝ) j| ≤ ε0Vh j
  initH : ∀ a j, |ξH t₀ a j - (Pi.single 0 (d a.castSucc) : Fin 9 → ℝ) j| ≤ ε0Hh j
  dist : ∀ t, t₀ ≤ t → (∀ k, t₀ ≤ k → k ≤ t → BoxT ξV ξH k) →
    (∀ j, |wV t j| ≤ εVh j) ∧ ∀ a j, |wH t a j| ≤ εHh j

/-- **Forward invariance of the box, and the output bounds** (strong induction over the ticks:
the box at ticks `t₀ … t₀ + N − 1` (the history) bounds the disturbances there, the tube then bounds the outputs
at `t₀ + N`, which the region condition puts back in the box). -/
theorem hover_box {ξV wV : ℕ → Fin 8 → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ} {t₀ : ℕ}
    {d : Fin 3 → ℝ} (hM : HoverModel ξV wV ξH wH t₀ d) (hd : ∀ i, |d i| ≤ dMax) (N : ℕ) :
    BoxT ξV ξH (t₀ + N) ∧
      (∀ o, |outV o ⬝ᵥ ξV (t₀ + N) - d 2 * resp Vertical.AvR (outV o) N 0| ≤
        ∑ j, PV o j * ε0Vh j + ∑ j, GV o j * εVh j) ∧
      ∀ a o, |outH o ⬝ᵥ ξH (t₀ + N) a - d a.castSucc * resp Horizontal.AhR (outH o) N 0| ≤
        ∑ j, PH o j * ε0Hh j + ∑ j, GH o j * εHh j := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hw : ∀ k < N, (∀ j, |wV (t₀ + k) j| ≤ εVh j) ∧ ∀ a j, |wH (t₀ + k) a j| ≤ εHh j :=
      fun k hk => hM.dist (t₀ + k) (by omega) (fun k' hk1 hk2 => by
        obtain ⟨m, rfl⟩ : ∃ m, k' = t₀ + m := ⟨k' - t₀, by omega⟩
        exact (ih m (by omega)).1)
    have bV : ∀ o, |outV o ⬝ᵥ ξV (t₀ + N) - d 2 * resp Vertical.AvR (outV o) N 0| ≤
        ∑ j, PV o j * ε0Vh j + ∑ j, GV o j * εVh j := fun o =>
      chan_tube Vertical.AvR ξV wV t₀ N 0 (d 2) hM.stepV (outV o) ε0Vh εVh (PV o) (GV o)
        εVh_nonneg hM.initV (fun k hk => (hw k hk).1) (fun j m => peakV' o j m)
        (fun j N => gainV' o j N)
    have bH : ∀ a o, |outH o ⬝ᵥ ξH (t₀ + N) a - d a.castSucc * resp Horizontal.AhR (outH o) N 0| ≤
        ∑ j, PH o j * ε0Hh j + ∑ j, GH o j * εHh j := fun a o =>
      chan_tube Horizontal.AhR (fun t => ξH t a) (fun t => wH t a) t₀ N 0 (d a.castSucc)
        (fun t ht => hM.stepH t ht a) (outH o) ε0Hh εHh (PH o) (GH o) εHh_nonneg (hM.initH a)
        (fun k hk => (hw k hk).2 a) (fun j m => peakH' o j m) (fun j N => gainH' o j N)
    refine ⟨⟨fun o => ?_, fun a o => ?_⟩, bV, bH⟩
    · have h1 := bV o
      have h2 : |d 2 * resp Vertical.AvR (outV o) N 0| ≤ PV o 0 * dMax := by
        rw [abs_mul, mul_comm]
        exact mul_le_mul (peakV' o 0 N) (hd 2) (abs_nonneg _)
          ((abs_nonneg _).trans (peakV' o 0 N))
      have h3 := regionV o
      have := abs_sub_abs_le_abs_sub (outV o ⬝ᵥ ξV (t₀ + N)) (d 2 * resp Vertical.AvR (outV o) N 0)
      linarith
    · have h1 := bH a o
      have h2 : |d a.castSucc * resp Horizontal.AhR (outH o) N 0| ≤ PH o 0 * dMax := by
        rw [abs_mul, mul_comm]
        exact mul_le_mul (peakH' o 0 N) (hd _) (abs_nonneg _)
          ((abs_nonneg _).trans (peakH' o 0 N))
      have h3 := regionH o
      have := abs_sub_abs_le_abs_sub (outH o ⬝ᵥ ξH (t₀ + N) a)
        (d a.castSucc * resp Horizontal.AhR (outH o) N 0)
      linarith

/-! ## The free response decays: the Lyapunov certificates -/

theorem V_pow_le (m : ℕ) (x : Fin 8 → ℝ) :
    Vertical.V ((Vertical.AvR ^ m) *ᵥ x) ≤ ((Vertical.lamv : ℝ) ^ 2) ^ m * Vertical.V x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← mulVec_mulVec, pow_succ]
    have hl : (0 : ℝ) ≤ (Vertical.lamv : ℝ) ^ 2 := by positivity
    calc Vertical.V (Vertical.AvR *ᵥ ((Vertical.AvR ^ m) *ᵥ x))
        ≤ (Vertical.lamv : ℝ) ^ 2 * Vertical.V ((Vertical.AvR ^ m) *ᵥ x) := Vertical.V_A _
      _ ≤ (Vertical.lamv : ℝ) ^ 2 * (((Vertical.lamv : ℝ) ^ 2) ^ m * Vertical.V x) :=
          mul_le_mul_of_nonneg_left ih hl
      _ = _ := by ring

theorem Vh_pow_le (m : ℕ) (x : Fin 9 → ℝ) :
    Horizontal.V ((Horizontal.AhR ^ m) *ᵥ x) ≤ ((Horizontal.lamh : ℝ) ^ 2) ^ m * Horizontal.V x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← mulVec_mulVec, pow_succ]
    have hl : (0 : ℝ) ≤ (Horizontal.lamh : ℝ) ^ 2 := by positivity
    calc Horizontal.V (Horizontal.AhR *ᵥ ((Horizontal.AhR ^ m) *ᵥ x))
        ≤ (Horizontal.lamh : ℝ) ^ 2 * Horizontal.V ((Horizontal.AhR ^ m) *ᵥ x) := Horizontal.V_A _
      _ ≤ (Horizontal.lamh : ℝ) ^ 2 * (((Horizontal.lamh : ℝ) ^ 2) ^ m * Horizontal.V x) :=
          mul_le_mul_of_nonneg_left ih hl
      _ = _ := by ring

theorem Vh_single (e : ℝ) : Horizontal.V (Pi.single 0 e) = 1000000000000 * e ^ 2 := by
  simp [Horizontal.V, Horizontal.PhR, Horizontal.castM, Horizontal.Ph, Vertical.qf, dotProduct,
    mulVec, Pi.single_apply]
  ring

/-- `|resp A_v e₀ m 0| ≤ √(γ_v P_v,00) λ_v^m`, with `√(γ_v P_v,00) ≤ 1.452`. -/
theorem respV_decay (m : ℕ) :
    |resp Vertical.AvR (outV 0) m 0| ≤ 1452 / 1000 * (Vertical.lamv : ℝ) ^ m := by
  have hr : resp Vertical.AvR (outV 0) m 0 = ((Vertical.AvR ^ m) *ᵥ Pi.single 0 1) 0 := by
    simp [resp, outV, dotProduct, Pi.single_apply]
  have h1 := Vertical.sq_ez_le ((Vertical.AvR ^ m) *ᵥ Pi.single 0 1)
  have h2 := V_pow_le m (Pi.single 0 1)
  rw [Reach.Vertical_V_single, one_pow, mul_one] at h2
  have hg : (0 : ℝ) ≤ (Vertical.gamv : ℝ) := by norm_num [Vertical.gamv]
  rw [hr]
  have hx : ((Vertical.lamv : ℝ) ^ 2) ^ m = ((Vertical.lamv : ℝ) ^ m) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hl0 : (0 : ℝ) ≤ (Vertical.lamv : ℝ) := by norm_num [Vertical.lamv]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc _ ≤ (Vertical.gamv : ℝ) * Vertical.V _ := h1
    _ ≤ (Vertical.gamv : ℝ) * (((Vertical.lamv : ℝ) ^ 2) ^ m * 37977353399) :=
        mul_le_mul_of_nonneg_left h2 hg
    _ = ((Vertical.gamv : ℝ) * 37977353399) * ((Vertical.lamv : ℝ) ^ m) ^ 2 := by rw [hx]; ring
    _ ≤ (1452 / 1000) ^ 2 * ((Vertical.lamv : ℝ) ^ m) ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num [Vertical.gamv]) (by positivity)
    _ = (1452 / 1000 * (Vertical.lamv : ℝ) ^ m) ^ 2 := by ring

/-- `|resp A_h e₀ m 0| ≤ √(γ_h P_h,00) λ_h^m`, with `√(γ_h P_h,00) ≤ 3.47`. -/
theorem respH_decay (m : ℕ) :
    |resp Horizontal.AhR (outH 0) m 0| ≤ 347 / 100 * (Horizontal.lamh : ℝ) ^ m := by
  have hr : resp Horizontal.AhR (outH 0) m 0 = ((Horizontal.AhR ^ m) *ᵥ Pi.single 0 1) 0 := by
    simp [resp, outH, dotProduct, Pi.single_apply]
  have h1 := Horizontal.sq_e_le ((Horizontal.AhR ^ m) *ᵥ Pi.single 0 1)
  have h2 := Vh_pow_le m (Pi.single 0 1)
  rw [Vh_single, one_pow, mul_one] at h2
  have hg : (0 : ℝ) ≤ (Horizontal.gamh : ℝ) := by norm_num [Horizontal.gamh]
  rw [hr]
  have hx : ((Horizontal.lamh : ℝ) ^ 2) ^ m = ((Horizontal.lamh : ℝ) ^ m) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hl0 : (0 : ℝ) ≤ (Horizontal.lamh : ℝ) := by norm_num [Horizontal.lamh]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc _ ≤ (Horizontal.gamh : ℝ) * Horizontal.V _ := h1
    _ ≤ (Horizontal.gamh : ℝ) * (((Horizontal.lamh : ℝ) ^ 2) ^ m * 1000000000000) :=
        mul_le_mul_of_nonneg_left h2 hg
    _ = ((Horizontal.gamh : ℝ) * 1000000000000) * ((Horizontal.lamh : ℝ) ^ m) ^ 2 := by rw [hx]; ring
    _ ≤ (347 / 100) ^ 2 * ((Horizontal.lamh : ℝ) ^ m) ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num [Horizontal.gamh]) (by positivity)
    _ = (347 / 100 * (Horizontal.lamh : ℝ) ^ m) ^ 2 := by ring

/-! ## The general start: any state in the weighted-ℓ1 region -/

/-- **The tube around the free response of any start**: output `o` at `t₀ + N` is within `Σ G e`
of the free response `o ⬝ Aᴺ ξ t₀`. -/
theorem chan_tube_gen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ξ w : ℕ → Fin n → ℝ) (t₀ N : ℕ)
    (hstep : ∀ t, t₀ ≤ t → ξ (t + 1) = A *ᵥ ξ t + w t) (o e G : Fin n → ℝ)
    (he : ∀ j, 0 ≤ e j) (hw : ∀ k < N, ∀ j, |w (t₀ + k) j| ≤ e j)
    (hG : ∀ j N, ∑ m ∈ range N, |resp A o m j| ≤ G j) :
    |o ⬝ᵥ ξ (t₀ + N) - o ⬝ᵥ ((A ^ N) *ᵥ ξ t₀)| ≤ ∑ j, G j * e j := by
  set η : ℕ → Fin n → ℝ := fun t => ξ t - (A ^ (t - t₀)) *ᵥ ξ t₀ with hη
  have hη' : ∀ t, t₀ ≤ t → η (t + 1) = A *ᵥ η t + w t := by
    intro t ht
    simp only [hη, hstep t ht, mulVec_sub, mulVec_mulVec]
    rw [show t + 1 - t₀ = (t - t₀) + 1 by omega, pow_succ']
    abel
  have h0' : ∀ j, |η t₀ j| ≤ 0 := by
    intro j; simp [hη]
  have hP : ∀ j m, |resp A o m j| ≤ G j := fun j m =>
    (Finset.single_le_sum (f := fun m => |resp A o m j|) (fun _ _ => abs_nonneg _)
      (Finset.self_mem_range_succ m)).trans (hG j (m + 1))
  have T := tube_out A η w t₀ N hη' o 0 e G G he h0' hw hP hG
  have e1 : o ⬝ᵥ η (t₀ + N) = o ⬝ᵥ ξ (t₀ + N) - o ⬝ᵥ ((A ^ N) *ᵥ ξ t₀) := by
    simp only [hη, dotProduct_sub, Nat.add_sub_cancel_left]
  rw [← e1]; simpa using T

/-- The hover hypotheses from a general start: the model steps and the per-row disturbance bounds
inside the box. -/
structure HoverModelG (ξV wV : ℕ → Fin 8 → ℝ) (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (t₀ : ℕ) : Prop where
  stepV : ∀ t, t₀ ≤ t → ξV (t + 1) = Vertical.AvR *ᵥ ξV t + wV t
  stepH : ∀ t, t₀ ≤ t → ∀ a, ξH (t + 1) a = Horizontal.AhR *ᵥ ξH t a + wH t a
  dist : ∀ t, t₀ ≤ t → (∀ k, t₀ ≤ k → k ≤ t → BoxT ξV ξH k) →
    (∀ j, |wV t j| ≤ εVh j) ∧ ∀ a j, |wH t a j| ≤ εHh j

/-- **The region of a general start**: the peak-weighted ℓ1 size of the start plus the tube inside
the box, for every watched output. -/
def RegionG (xV : Fin 8 → ℝ) (xH : Fin 2 → Fin 9 → ℝ) : Prop :=
  (∀ o, ∑ j, PV o j * |xV j| + ∑ j, GV o j * εVh j ≤ bVh o) ∧
    ∀ a o, ∑ j, PH o j * |xH a j| + ∑ j, GH o j * εHh j ≤ bHh o

/-- **Forward invariance of the box from a general start in `RegionG`**, and every output within
`Σ G ε` of its free response. -/
theorem hover_box_gen {ξV wV : ℕ → Fin 8 → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ} {t₀ : ℕ}
    (hM : HoverModelG ξV wV ξH wH t₀) (hR : RegionG (ξV t₀) (ξH t₀)) (N : ℕ) :
    BoxT ξV ξH (t₀ + N) ∧
      (∀ o, |outV o ⬝ᵥ ξV (t₀ + N) - outV o ⬝ᵥ ((Vertical.AvR ^ N) *ᵥ ξV t₀)| ≤
        ∑ j, GV o j * εVh j) ∧
      ∀ a o, |outH o ⬝ᵥ ξH (t₀ + N) a - outH o ⬝ᵥ ((Horizontal.AhR ^ N) *ᵥ ξH t₀ a)| ≤
        ∑ j, GH o j * εHh j := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hw : ∀ k < N, (∀ j, |wV (t₀ + k) j| ≤ εVh j) ∧ ∀ a j, |wH (t₀ + k) a j| ≤ εHh j :=
      fun k hk => hM.dist (t₀ + k) (by omega) (fun k' hk1 hk2 => by
        obtain ⟨m, rfl⟩ : ∃ m, k' = t₀ + m := ⟨k' - t₀, by omega⟩
        exact (ih m (by omega)).1)
    have bV : ∀ o, |outV o ⬝ᵥ ξV (t₀ + N) - outV o ⬝ᵥ ((Vertical.AvR ^ N) *ᵥ ξV t₀)| ≤
        ∑ j, GV o j * εVh j := fun o =>
      chan_tube_gen Vertical.AvR ξV wV t₀ N hM.stepV (outV o) εVh (GV o) εVh_nonneg
        (fun k hk => (hw k hk).1) (fun j N => gainV' o j N)
    have bH : ∀ a o, |outH o ⬝ᵥ ξH (t₀ + N) a - outH o ⬝ᵥ ((Horizontal.AhR ^ N) *ᵥ ξH t₀ a)| ≤
        ∑ j, GH o j * εHh j := fun a o =>
      chan_tube_gen Horizontal.AhR (fun t => ξH t a) (fun t => wH t a) t₀ N
        (fun t ht => hM.stepH t ht a) (outH o) εHh (GH o) εHh_nonneg
        (fun k hk => (hw k hk).2 a) (fun j N => gainH' o j N)
    refine ⟨⟨fun o => ?_, fun a o => ?_⟩, bV, bH⟩
    · have h1 := bV o
      have h2 : |outV o ⬝ᵥ ((Vertical.AvR ^ N) *ᵥ ξV t₀)| ≤ ∑ j, PV o j * |ξV t₀ j| := by
        refine (abs_dot_mulVec_le _ _ _ (fun j => |ξV t₀ j|) N (fun j => le_rfl)).trans ?_
        refine Finset.sum_le_sum fun j _ => ?_
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (peakV' o j N) (abs_nonneg _)
      have h3 := hR.1 o
      have := abs_sub_abs_le_abs_sub (outV o ⬝ᵥ ξV (t₀ + N)) (outV o ⬝ᵥ ((Vertical.AvR ^ N) *ᵥ ξV t₀))
      linarith
    · have h1 := bH a o
      have h2 : |outH o ⬝ᵥ ((Horizontal.AhR ^ N) *ᵥ ξH t₀ a)| ≤ ∑ j, PH o j * |ξH t₀ a j| := by
        refine (abs_dot_mulVec_le _ _ _ (fun j => |ξH t₀ a j|) N (fun j => le_rfl)).trans ?_
        refine Finset.sum_le_sum fun j _ => ?_
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (peakH' o j N) (abs_nonneg _)
      have h3 := hR.2 a o
      have := abs_sub_abs_le_abs_sub (outH o ⬝ᵥ ξH (t₀ + N) a)
        (outH o ⬝ᵥ ((Horizontal.AhR ^ N) *ᵥ ξH t₀ a))
      linarith

/-- The free position response of a general start decays: `|(A_vᴺ x)₀| ≤ √(γ_v V_v x) λ_vᴺ`. -/
theorem freeV_decay (N : ℕ) (x : Fin 8 → ℝ) :
    |((Vertical.AvR ^ N) *ᵥ x) 0| ≤ Real.sqrt ((Vertical.gamv : ℝ) * Vertical.V x) *
      (Vertical.lamv : ℝ) ^ N := by
  have h1 := Vertical.sq_ez_le ((Vertical.AvR ^ N) *ᵥ x)
  have h2 := V_pow_le N x
  have hg : (0 : ℝ) ≤ (Vertical.gamv : ℝ) := by norm_num [Vertical.gamv]
  have hl0 : (0 : ℝ) ≤ (Vertical.lamv : ℝ) := by norm_num [Vertical.lamv]
  have hV := Vertical.V_nonneg x
  have hx : ((Vertical.lamv : ℝ) ^ 2) ^ N = ((Vertical.lamv : ℝ) ^ N) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc _ ≤ (Vertical.gamv : ℝ) * Vertical.V _ := h1
    _ ≤ (Vertical.gamv : ℝ) * (((Vertical.lamv : ℝ) ^ 2) ^ N * Vertical.V x) :=
        mul_le_mul_of_nonneg_left h2 hg
    _ = _ := by rw [hx]; ring

/-- The free position response of a general start decays: `|(A_hᴺ x)₀| ≤ √(γ_h V_h x) λ_hᴺ`. -/
theorem freeH_decay (N : ℕ) (x : Fin 9 → ℝ) :
    |((Horizontal.AhR ^ N) *ᵥ x) 0| ≤ Real.sqrt ((Horizontal.gamh : ℝ) * Horizontal.V x) *
      (Horizontal.lamh : ℝ) ^ N := by
  have h1 := Horizontal.sq_e_le ((Horizontal.AhR ^ N) *ᵥ x)
  have h2 := Vh_pow_le N x
  have hg : (0 : ℝ) ≤ (Horizontal.gamh : ℝ) := by norm_num [Horizontal.gamh]
  have hl0 : (0 : ℝ) ≤ (Horizontal.lamh : ℝ) := by norm_num [Horizontal.lamh]
  have hV := Horizontal.V_nonneg x
  have hx : ((Horizontal.lamh : ℝ) ^ 2) ^ N = ((Horizontal.lamh : ℝ) ^ N) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  calc _ ≤ (Horizontal.gamh : ℝ) * Horizontal.V _ := h1
    _ ≤ (Horizontal.gamh : ℝ) * (((Horizontal.lamh : ℝ) ^ 2) ^ N * Horizontal.V x) :=
        mul_le_mul_of_nonneg_left h2 hg
    _ = _ := by rw [hx]; ring

/-- The position tubes of a general start: vertical `≤ 0.93` mm, horizontal `≤ 2.51` mm. -/
theorem tubeV0g : ∑ j, GV 0 j * εVh j ≤ 93 / 100000 := by
  simp [GV, εVh, Fin.sum_univ_eight]; norm_num

theorem tubeH0g : ∑ j, GH 0 j * εHh j ≤ 251 / 100000 := by
  simp [GH, εHh, Fin.sum_univ_succ]; norm_num

end

end Contracts.Track.Reach.Glue
