import Contracts.Track.Reach.SafeRule
import Contracts.Track.Reach.LegNav

/-!
# The safety theorem, horizontal-leg world (REACH.md §11)

```
theorem tracking_safe_h (sense32 senseP w₀) (p₀ : P3) (w' : Vector3p.State) (ψ₀ : ℝ)
    (hP : LegParams w₀) (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP)
    (hL : LibmSpec) (hF : TrackFacts sense32 senseP w₀ p₀ ψ₀) (T : ℕ) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang_t 0 (.always 0 T (track δH))⟩
```

The paper's safety statement ("for any reference trajectory generated within the navigator
acceleration limits, the vehicle position never exceeds the instantaneous reference by more than a
certified margin") on the closed loop of the world of §9 (`LegParams`, `PSC_D_ACC_P 0.05`): from
hover at `p₀`, at every tick `t ≤ T`, for every `T`, `‖p_t − sp_t‖ ≤ δH = 0.2156`, where `sp_t` is
the position target the controller writes at tick `t` (`posTarget`, part of the loop state, so
`track δ` is a signal predicate on `X`, defined like `near`). `tracking_safe_h_forever` is the
unbounded form.

**The margin.** The box `BoxL` closes per axis at the plain ℓ1 envelopes of the reference limits:
horizontally `|e| ≤ 0.1433` (`posH_close`: start `2.9·10⁻⁶`, target acceleration `1.501 · 0.0306`,
position defect `1.3·10⁻⁴ · 272`, velocity defect `8·10⁻⁴ · 74.3`, rows `0.0025`), vertically
`|ez| ≤ 0.0735` (`posVS_close`). The invariant family carries these per-axis bounds next to the box
(`SBox`), and `δH = 0.2156 ≥ √(2 · 0.1433² + 0.0735²) = 0.21557`. From the box sizes alone
(`0.15`, `0.1`) it would be `√0.055 = 0.2345`.

**Measured** (per tick, `‖p − sp‖` over every tick of every run, the trace's `x_n y_e z_d` against
`sp_n sp_e sp_d`, scratchpad `safe/measure.py`): horizontal campaign (204 legs at 0.05):
`0.04187`. Against `δH = 0.2156`. The course flight at 0.05 (`sim/out/ref-course-1ms`, `0.0870`,
vertical `0.0848`) is outside the hypotheses: it starts on the ground and its navigator limits exceed
`TrackFacts`'s (horizontal acceleration `2.12`, vertical `1.0`, vertical defects `1.4·10⁻⁴`,
`7.4·10⁻⁴`).

**The horizon.** The box induction is uniform in the tick: every gain is certified for every
length `N` (`RefGains`, `gainH'`, `gainV'`), so nothing in the proof bounds the tick. The facts are
stated at every tick (`TrackRun.tick` has no horizon; after the loiter the navigator holds the
target and the reference limits hold with the defects below `10⁻⁸`), and the theorem holds for every
`T`. The leg theorem's `LegRun.tick` stops at `hzn = 6000` only because its formula ends there.

**The invariant rule.** The always is discharged by `Contracts.STL.implements_always_of_invariant`
through `implements_always_of_prefix` (SafeRule.lean) on the history state: `I τ` is the set of
prefixes of length `τ` of behaviors from hover on which every such behavior has had `SBox` on
`[2, τ]`, `R` is one tick of `Mloop` on prefixes (`histStep`). The family cannot be stated on `X`
alone: the readouts `ξV`, `ξH` read `run w₀ x t`, the controller's world reconstructed from all
earlier samples, and the box at `t + 1` needs the box at every earlier tick (the envelopes are
convolutions over the past). The inductive step is the step of `leg_box`'s strong induction
(`sbox_step`), the target inclusion is `err_le_of_sbox`, and the ticks 0 and 1 (before the tube
starts) are the field `early`.

**`TrackFacts`** holds only per-tick facts: `early`, `init`, `tick` (no completion, loiter, hold,
navigator phase, nor `d2sum`: the box does not use it). Assumed against measured (max over the 204
horizontal legs, every tick from 2 on, scratchpad `safe/refs.py`, `safe/init.py`, `safe/initw.py`):

| field | assumed | measured |
|---|---|---|
| `early` | `err ≤ 10⁻⁶` at ticks 0, 1 | `4.1·10⁻⁹` |
| `init` horizontal | `ε0HL`; `|asp| ≤ 10⁻³`; `|d₂| ≤ 10⁻⁶` | `e 1.4·10⁻¹⁰`, `ev 9.2·10⁻⁸` (others not logged); `4.9·10⁻⁵`; `7.5·10⁻⁸` |
| `init` vertical | `ε0VS = (10⁻⁶, 10⁻⁵, 10⁻⁵, 2·10⁻³, 10⁻⁴ ×4)` | `ez 1.4·10⁻⁸`, `ev 4.90·10⁻⁶`, `eA ≈ 2.34·10⁻⁴` (computed: the 20 Hz filter on the sampled `9.80·10⁻⁴` m/s² sink), `w 4.43·10⁻⁵` |
| `tick` horizontal | `1.501`, `0.013`, `1.3·10⁻⁴`, `8·10⁻⁴`, `1.1·10⁻⁵` | `1.5` (configured max), `0.0125003`, `1.2583·10⁻⁴`, `7.6813·10⁻⁴`, `1.0070·10⁻⁵` |
| `tick` vertical | `0.5`, `10⁻⁵`, `2·10⁻⁵` | `0.0282`, `2.44·10⁻⁶`, `1.889·10⁻⁵` |
| `tick` rows | `legWV ≤ εVL`, `legWH ≤ εHL` while `BoxL` holds | not observable in the trace (§9.3) |

**The vertical start** `ε0VS` is the repaired `ε0VL` (`ε0VS_eq`). Until 2026-11-06 `LegRun.init` asked
`|ξV 2 1| ≤ 10⁻⁶` (the vertical velocity error at tick 2) and `|ξV 2 3| ≤ 10⁻⁵` (the acceleration
PID's error); the traces give `4.90–5.03·10⁻⁶` for the first (the vehicle sinks at `9.80·10⁻⁴` m/s²
from tick 0: `MOT_THST_HOVER 0.4444` against the plant's `1/2.25`), and the code's filter gives
`2.34·10⁻⁴` for the second. Both entries are now `10⁻⁵` and `2·10⁻³`.
-/

namespace Contracts.Track.Reach.Safe

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue Contracts.Track.Reach.Leg

noncomputable section

/-! ## The formula -/

/-- `track δ`: the vehicle is within `δ` of the instantaneous position target (the target the
controller writes at the tick; `errLE δ` of the specification, spelled out like `near`). -/
def track (δ : ℝ) : Formula X := .atom fun x => δ - dist (pos x) (posTarget x)

@[simp] theorem sat_track {δ : ℝ} {x : ℕ → X} {t : ℕ} :
    sat x t (track δ) ↔ dist (pos (x t)) (posTarget (x t)) ≤ δ := by simp [track]

/-- The hover assumption reads tick 0 only. -/
theorem ahover_tick0 (p₀ : P3) (ψ₀ : ℝ) :
    ∀ x y : ℕ → X, x 0 = y 0 → x ∈ Ahover p₀ ψ₀ → y ∈ Ahover p₀ ψ₀ := by
  intro x y h hx
  simpa [Ahover, h] using hx

/-! ## The start and the per-axis position bounds -/

/-- **The start of the vertical channel at tick 2** (`ez, ev, eV, eA, I, f, u, w`): `ε0VL` with the
velocity entry `10⁻⁵` (measured `5.03·10⁻⁶`) and the acceleration-error entry `2·10⁻³` (computed
`2.34·10⁻⁴`; a priori at most the sampled sink `9.81·10⁻⁴` plus the target). -/
def ε0VS : Fin 8 → ℝ := ![1 / 10 ^ 6, 1 / 10 ^ 5, 1 / 10 ^ 5, 2 / 10 ^ 3, 1 / 10 ^ 4, 1 / 10 ^ 4,
  1 / 10 ^ 4, 1 / 10 ^ 4]

/-- The per-axis horizontal position bound. -/
def eHS : ℝ := 1433 / 10000

/-- The vertical position bound at `PSC_D_ACC_P 0.05`. -/
def eVS : ℝ := 735 / 10000

/-- **The margin of the horizontal-leg world**: `√(2 · 0.1433² + 0.0735²) ≤ 0.2156`. -/
def δH : ℝ := 2156 / 10000

/-- `ε0VS` is the start of the leg theorems, `ε0VL` (repaired). -/
theorem ε0VS_eq : ε0VS = ε0VL := rfl

theorem posH_close :
    ∑ j, PH 0 j * ε0HL j + 1501 / 1000 * GB 0 + 13 / 10 ^ 5 * GH 0 0 + 8 / 10 ^ 4 * GH 0 1 +
      ∑ j, GH 0 j * εHL j ≤ eHS := by
  simp [PH, GH, ε0HL, εHL, GB, eHS, Fin.sum_univ_succ]; norm_num

theorem boxVS_close (o : Fin 5) :
    ∑ j, PV o j * ε0VS j + 1 / 2 * GBV o + 1 / 10 ^ 5 * GV o 0 + 2 / 10 ^ 5 * GV o 1 +
      ∑ j, GV o j * εVL j ≤ bV o := by
  fin_cases o <;> simp [PV, GV, ε0VS, εVL, GBV, bV, Fin.sum_univ_eight] <;> norm_num

theorem posVS_close :
    ∑ j, PV 0 j * ε0VS j + 1 / 2 * GBV 0 + 1 / 10 ^ 5 * GV 0 0 + 2 / 10 ^ 5 * GV 0 1 +
      ∑ j, GV 0 j * εVL j ≤ eVS := by
  simp [PV, GV, ε0VS, εVL, GBV, eVS, Fin.sum_univ_eight]; norm_num

/-! ## One horizontal axis -/

/-- The per-tick bounds of one horizontal axis (the horizontal fields of `TickBounds`). -/
structure HB (w : ℕ → Fin 9 → ℝ) (aa d1 d2 : ℕ → ℝ) (t : ℕ) : Prop where
  bw : ∀ j, |w t j| ≤ εHL j
  ba : |aa t| ≤ 1501 / 1000
  bj : |aa (t + 1) - aa t| ≤ 13 / 1000
  bd1 : |d1 t| ≤ 13 / 10 ^ 5
  bd2 : |d2 t| ≤ 8 / 10 ^ 4
  bdd2 : |d2 (t + 1) - d2 t| ≤ 11 / 10 ^ 6

/-- The model of one horizontal axis from `t₀` (the horizontal fields of `LegModel`). -/
structure HModel (ξ w : ℕ → Fin 9 → ℝ) (aa d1 d2 : ℕ → ℝ) (t₀ : ℕ) : Prop where
  step : ∀ t, t₀ ≤ t → ξ (t + 1) = Horizontal.AhR *ᵥ ξ t +
    (aa t • Horizontal.BhR + (-d1 t) • Horizontal.e0 + (-d2 t) • Horizontal.e1 + w t)
  init : ∀ j, |ξ t₀ j| ≤ ε0HL j
  initA : |aa t₀| ≤ 1 / 1000
  initD : |d2 t₀| ≤ 1 / 10 ^ 6

theorem hb_of_tick {ξV wV : ℕ → Fin 8 → ℝ} {aZ d1Z d2Z : ℕ → ℝ}
    {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ} {aH d1H d2H : ℕ → Fin 2 → ℝ} {t : ℕ}
    (h : TickBounds ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t) (a : Fin 2) :
    HB (fun t => wH t a) (fun t => aH t a) (fun t => d1H t a) (fun t => d2H t a) t :=
  ⟨h.bwH a, h.baH a, h.bjH a, h.bd1H a, h.bd2H a, h.bdd2H a⟩

section Axis

variable {ξ w : ℕ → Fin 9 → ℝ} {aa d1 d2 : ℕ → ℝ} {t₀ : ℕ}

/-- The outputs `e, ev, I` of the axis (LegTube's `outH_bound` with the plain envelopes). -/
theorem axis_out (hM : HModel ξ w aa d1 d2 t₀) (hg : RefGains) (o : Fin 5) (N : ℕ)
    (hT : ∀ k < N, HB w aa d1 d2 (t₀ + k)) :
    |outH o ⬝ᵥ ξ (t₀ + N)| ≤ ∑ j, PH o j * ε0HL j + 1501 / 1000 * GB o + 13 / 10 ^ 5 * GH o 0 +
      8 / 10 ^ 4 * GH o 1 + ∑ j, GH o j * εHL j :=
  out_le Horizontal.AhR ξ w aa (fun t => -d1 t) (fun t => -d2 t) Horizontal.BhR Horizontal.e0
    Horizontal.e1 t₀ hM.step (outH o) N ε0HL (PH o) (GH o) εHL hM.init
    (fun j m => peakH' o j m) (fun j N => gainH' o j N) εHL_nonneg (fun k hk j => (hT k hk).bw j)
    (env_const _ aa t₀ N (by norm_num) (fun k hk => (hT k hk).ba) (hg.gainB o N))
    (env_const_neg _ d1 t₀ N (by norm_num) (fun k hk => (hT k hk).bd1) (gH0 o N))
    (env_const_neg _ d2 t₀ N (by norm_num) (fun k hk => (hT k hk).bd2) (gH1 o N))

/-- The command of the axis (LegTube's `c1_bound` on one axis). -/
theorem axis_c1 (hM : HModel ξ w aa d1 d2 t₀) (hg : RefGains) (N : ℕ)
    (hT : ∀ k < N, HB w aa d1 d2 (t₀ + k)) : |outH 3 ⬝ᵥ ξ (t₀ + N)| ≤ bHL 3 := by
  set ζ : ℕ → Fin 9 → ℝ := fun t => ξ t - aa t • vAcc with hζ
  have hstep : ∀ t, t₀ ≤ t → ζ (t + 1) = Horizontal.AhR *ᵥ ζ t +
      ((fun t => -(aa (t + 1) - aa t)) t • vAcc + (fun t => -d1 t) t • Horizontal.e0 +
        (fun t => -d2 t) t • Horizontal.e1 + w t) := fun t ht =>
    zeta_step ξ w aa d1 d2 t (hM.step t ht)
  have hx : ∀ j, |ζ t₀ j| ≤ ε0HL j + 1 / 1000 * vAcc j := by
    intro j
    have h1 := hM.init j
    have h2 := hM.initA
    have hv := vAcc_nonneg j
    simp only [hζ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hv]
    nlinarith [abs_nonneg (aa t₀)]
  have e : outH 3 ⬝ᵥ ξ (t₀ + N) = outH 3 ⬝ᵥ ζ (t₀ + N) + aa (t₀ + N) := by
    simp only [hζ, dotProduct_sub, dotProduct_smul, outH3_vAcc, smul_eq_mul, mul_one]
    ring
  have hA : |aa (t₀ + N)| ≤ 1501 / 1000 + 13 / 1000 := by
    rcases N with _ | k
    · have := hM.initA; simp only [add_zero]; linarith
    · have h1 := (hT k (by omega)).ba
      have h2 := (hT k (by omega)).bj
      rw [show t₀ + (k + 1) = t₀ + k + 1 by omega]
      have := abs_sub_abs_le_abs_sub (aa (t₀ + k + 1)) (aa (t₀ + k))
      linarith
  rw [e]
  have B := out_le Horizontal.AhR ζ w (fun t => -(aa (t + 1) - aa t))
    (fun t => -d1 t) (fun t => -d2 t) vAcc Horizontal.e0 Horizontal.e1 t₀ hstep (outH 3) N
    (fun j => ε0HL j + 1 / 1000 * vAcc j) (PH 3) (GH 3) εHL hx (fun j m => peakH' 3 j m)
    (fun j N => gainH' 3 j N) εHL_nonneg (fun k hk j => (hT k hk).bw j)
    (env_const_neg _ (fun t => aa (t + 1) - aa t) t₀ N (by norm_num)
      (fun k hk => (hT k hk).bj) (hg.gainC1 N))
    (env_const_neg _ d1 t₀ N (by norm_num) (fun k hk => (hT k hk).bd1) (gH0 3 N))
    (env_const_neg _ d2 t₀ N (by norm_num) (fun k hk => (hT k hk).bd2) (gH1 3 N))
  have C := boxC1_close
  have := abs_add_le (outH 3 ⬝ᵥ ζ (t₀ + N)) (aa (t₀ + N))
  linarith

/-- The command rate of the axis (LegTube's `rate_bound` on one axis). -/
theorem axis_rate (hM : HModel ξ w aa d1 d2 t₀) (hg : RefGains) (N : ℕ)
    (hT : ∀ k < N, HB w aa d1 d2 (t₀ + k)) : |outH 4 ⬝ᵥ ξ (t₀ + N)| ≤ bHL 4 := by
  set ζ : ℕ → Fin 9 → ℝ := fun t => ξ t - aa t • vAcc - d2 t • u2 with hζ
  have hstep : ∀ t, t₀ ≤ t → ζ (t + 1) = Horizontal.AhR *ᵥ ζ t +
      ((fun t => -(aa (t + 1) - aa t)) t • vAcc + (fun t => -d1 t) t • Horizontal.e0 +
        (fun t => -(d2 (t + 1) - d2 t)) t • u2 + w t) := fun t ht =>
    zeta2_step ξ w aa d1 d2 t (hM.step t ht)
  have hx : ∀ j, |ζ t₀ j| ≤ ε0HL j + 1 / 1000 * vAcc j + 1 / 10 ^ 6 * u2a j := by
    intro j
    have h1 := hM.init j
    have h2 := hM.initA
    have h3 := hM.initD
    have hv := vAcc_nonneg j
    have hu := u2_abs j
    have hu0 := u2a_nonneg j
    simp only [hζ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_sub _ _).trans ?_) ?_
    · rw [abs_mul, abs_of_nonneg hv]
      nlinarith [abs_nonneg (aa t₀)]
    · rw [abs_mul]
      nlinarith [abs_nonneg (d2 t₀), abs_nonneg (u2 j)]
  have e : outH 4 ⬝ᵥ ξ (t₀ + N) = outH 4 ⬝ᵥ ζ (t₀ + N) := by
    simp only [hζ, dotProduct_sub, dotProduct_smul, outH4_vAcc, outH4_u2, smul_zero, sub_zero]
  rw [e]
  have B := out_le Horizontal.AhR ζ w (fun t => -(aa (t + 1) - aa t))
    (fun t => -d1 t) (fun t => -(d2 (t + 1) - d2 t)) vAcc Horizontal.e0 u2 t₀ hstep
    (outH 4) N (fun j => ε0HL j + 1 / 1000 * vAcc j + 1 / 10 ^ 6 * u2a j) (PH 4) (GH 4) εHL hx
    (fun j m => peakH' 4 j m) (fun j N => gainH' 4 j N) εHL_nonneg
    (fun k hk j => (hT k hk).bw j)
    (env_const_neg _ (fun t => aa (t + 1) - aa t) t₀ N (by norm_num)
      (fun k hk => (hT k hk).bj) (hg.gainJ N))
    (env_const_neg _ d1 t₀ N (by norm_num) (fun k hk => (hT k hk).bd1) (gH0 4 N))
    (env_const_neg _ (fun t => d2 (t + 1) - d2 t) t₀ N (by norm_num)
      (fun k hk => (hT k hk).bdd2) (gainU2 N))
  have C := boxRate_close
  linarith

/-- **One horizontal axis at `t₀ + N`**: the box `bHL` and the position bound `0.1433`. -/
theorem axis_box (hM : HModel ξ w aa d1 d2 t₀) (hg : RefGains) (N : ℕ)
    (hT : ∀ k < N, HB w aa d1 d2 (t₀ + k)) :
    (∀ o, |outH o ⬝ᵥ ξ (t₀ + N)| ≤ bHL o) ∧ |ξ (t₀ + N) 0| ≤ eHS := by
  refine ⟨fun o => ?_, ?_⟩
  · by_cases h4 : o = 4
    · subst h4; exact axis_rate hM hg N hT
    by_cases h3 : o = 3
    · subst h3; exact axis_c1 hM hg N hT
    have ho : o.val < 3 := by
      have := o.isLt
      have h4' : o.val ≠ 4 := fun h => h4 (Fin.ext h)
      have h3' : o.val ≠ 3 := fun h => h3 (Fin.ext h)
      omega
    exact (axis_out hM hg o N hT).trans (boxH_close o ho)
  · have := (axis_out hM hg 0 N hT).trans posH_close
    rwa [outH0_dot] at this

end Axis

/-! ## The world of §9: the model, the box step, the margin -/

/-- **The safety box** at tick `k`: `BoxL` and the per-axis position bounds. -/
def SBox (ξV : ℕ → Fin 8 → ℝ) (ξH : ℕ → Fin 2 → Fin 9 → ℝ) (k : ℕ) : Prop :=
  BoxL ξV ξH k ∧ (∀ a, |ξH k a 0| ≤ eHS) ∧ |ξV k 0| ≤ eVS

/-- The model of the loop from `t₀` (`LegModel` with the start `ε0VS` and without the per-tick
facts, which the box step takes as a hypothesis). -/
structure SModel (ξV wV : ℕ → Fin 8 → ℝ) (aZ d1Z d2Z : ℕ → ℝ)
    (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (aH d1H d2H : ℕ → Fin 2 → ℝ) (t₀ : ℕ) : Prop where
  stepV : ∀ t, t₀ ≤ t → ξV (t + 1) = Vertical.AvR *ᵥ ξV t +
    (aZ t • Vertical.BvR + (-d1Z t) • Vertical.e0 + (-d2Z t) • Vertical.e1 + wV t)
  stepH : ∀ t, t₀ ≤ t → ∀ a, ξH (t + 1) a = Horizontal.AhR *ᵥ ξH t a +
    (aH t a • Horizontal.BhR + (-d1H t a) • Horizontal.e0 + (-d2H t a) • Horizontal.e1 + wH t a)
  initV : ∀ j, |ξV t₀ j| ≤ ε0VS j
  initH : ∀ a j, |ξH t₀ a j| ≤ ε0HL j
  initA : ∀ a, |aH t₀ a| ≤ 1 / 1000
  initD : ∀ a, |d2H t₀ a| ≤ 1 / 10 ^ 6

section Step

variable {ξV wV : ℕ → Fin 8 → ℝ} {aZ d1Z d2Z : ℕ → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ}
  {aH d1H d2H : ℕ → Fin 2 → ℝ} {t₀ : ℕ}

/-- **The step of the box induction** (the step of `leg_box`'s strong induction, any `N`): the
per-tick facts on `[t₀, t₀ + N)` give the safety box at `t₀ + N`. -/
theorem sbox_step (hM : SModel ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) (N : ℕ)
    (hT : ∀ k < N, TickBounds ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k)) :
    SBox ξV ξH (t₀ + N) := by
  have hV : ∀ o, |outV o ⬝ᵥ ξV (t₀ + N)| ≤ ∑ j, PV o j * ε0VS j + 1 / 2 * GBV o +
      1 / 10 ^ 5 * GV o 0 + 2 / 10 ^ 5 * GV o 1 + ∑ j, GV o j * εVL j := fun o =>
    out_le Vertical.AvR ξV wV aZ (fun t => -d1Z t) (fun t => -d2Z t) Vertical.BvR Vertical.e0
      Vertical.e1 t₀ hM.stepV (outV o) N ε0VS (PV o) (GV o) εVL hM.initV
      (fun j m => peakV' o j m) (fun j N => gainV' o j N) εVL_nonneg
      (fun k hk j => (hT k hk).bwV j)
      (env_const _ aZ t₀ N (by norm_num) (fun k hk => (hT k hk).baZ) (hg.gainBV o N))
      (env_const_neg _ d1Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd1Z) (gV0 o N))
      (env_const_neg _ d2Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd2Z) (gV1 o N))
  have hH : ∀ a, (∀ o, |outH o ⬝ᵥ ξH (t₀ + N) a| ≤ bHL o) ∧ |ξH (t₀ + N) a 0| ≤ eHS := fun a =>
    axis_box (ξ := fun t => ξH t a) ⟨fun t ht => hM.stepH t ht a, hM.initH a, hM.initA a,
      hM.initD a⟩ hg N fun k hk => hb_of_tick (hT k hk) a
  refine ⟨⟨fun o => (hV o).trans (boxVS_close o), fun a o => (hH a).1 o⟩, fun a => (hH a).2, ?_⟩
  have := (hV 0).trans posVS_close
  rwa [outV0_dot] at this

end Step

/-- **The margin**: the safety box bounds the tracking error by `δH`. -/
theorem norm3_le {e₀ e₁ ez eh ev δ : ℝ} (h₀ : |e₀| ≤ eh) (h₁ : |e₁| ≤ eh) (hz : |ez| ≤ ev)
    (hδ : 2 * eh ^ 2 + ev ^ 2 ≤ δ ^ 2) (hδ0 : 0 ≤ δ) :
    Real.sqrt (e₀ ^ 2 + e₁ ^ 2 + ez ^ 2) ≤ δ := by
  rw [Real.sqrt_le_left hδ0]
  have a₀ := sq_le_sq' (neg_le_of_abs_le h₀) (le_of_abs_le h₀)
  have a₁ := sq_le_sq' (neg_le_of_abs_le h₁) (le_of_abs_le h₁)
  have az := sq_le_sq' (neg_le_of_abs_le hz) (le_of_abs_le hz)
  linarith

/-! ## The facts and the theorem -/

/-- **The per-tick facts of one behavior from hover** (no navigator phase, no completion, loiter or
hold, no sum over the run). Assumed against measured: the table of the module docstring. -/
structure TrackRun (w₀ : Vehicle.World) (x : ℕ → X) : Prop where
  /-- **Before the tube** (ticks 0 and 1: the takeover at hover and the first tick): the vehicle is
  within `10⁻⁶` of the target (measured `≤ 1.2·10⁻⁷` on every campaign, `4.1·10⁻⁹` on the
  horizontal one). -/
  early : ∀ t < ts, err (x t) ≤ 1 / 10 ^ 6
  /-- **The start of the tube** (tick 2): the vertical readouts within `ε0VS` (velocity error
  measured `≤ 5.03·10⁻⁶`, position error `≤ 1.3·10⁻⁷`, acceleration-PID error computed
  `2.34·10⁻⁴`, mean held actuator `4.43·10⁻⁵`), the horizontal within `ε0HL` (position error
  `≤ 2.2·10⁻¹⁰`, velocity error `≤ 1.5·10⁻⁷`), the target acceleration `≤ 10⁻³` (measured
  `≤ 7.6·10⁻⁵`), the velocity defect `≤ 10⁻⁶` (measured `≤ 1.2·10⁻⁷`). -/
  init : (∀ j, |ξV w₀ x ts j| ≤ ε0VS j) ∧ (∀ a j, |ξH w₀ x ts a j| ≤ ε0HL j) ∧
    (∀ a, |aH w₀ x ts a| ≤ 1 / 1000) ∧ ∀ a, |d2H w₀ x ts a| ≤ 1 / 10 ^ 6
  /-- **The tick glue and the reference limits at every tick while the box holds** (`TickBounds`,
  as `LegRun.tick` with no horizon). Measured: the table of the module docstring. -/
  tick : ∀ t, ts ≤ t → (∀ k, ts ≤ k → k ≤ t → BoxL (ξV w₀ x) (ξH w₀ x) k) →
    TickBounds (ξV w₀ x) (legWV w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) t

/-- **The facts of the safety theorem** (the one named hypothesis): `TrackRun` for every behavior
of the loop from hover. -/
structure TrackFacts (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p₀ : P3)
    (ψ₀ : ℝ) : Prop where
  run : ∀ x ∈ Mloop sense32 senseP w₀ ∩ Reach.Ahover p₀ ψ₀, TrackRun w₀ x

section Loop

variable {w₀ : Vehicle.World} {x : ℕ → X}

/-- The model of a behavior with the facts, from tick 2. -/
theorem smodel_of_run (hx : TrackRun w₀ x) :
    SModel (ξV w₀ x) (legWV w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) ts where
  stepV t _ := by
    simp only [legWV, Vertical.forceOf, aZ, d1Z, d2Z, neg_smul]
    abel
  stepH t _ a := by
    simp only [legWH, Horizontal.forceOf, aH, d1H, d2H, neg_smul]
    abel
  initV := hx.init.1
  initH := hx.init.2.1
  initA := hx.init.2.2.1
  initD := hx.init.2.2.2

/-- **The inductive step on the loop**: the safety box on `[2, τ)` gives it at `τ`. -/
theorem sbox_run (hx : TrackRun w₀ x) (τ : ℕ) (hτ : ts ≤ τ)
    (hprev : ∀ k, ts ≤ k → k < τ → SBox (ξV w₀ x) (ξH w₀ x) k) : SBox (ξV w₀ x) (ξH w₀ x) τ := by
  obtain ⟨N, rfl⟩ : ∃ N, τ = ts + N := ⟨τ - ts, by omega⟩
  exact sbox_step (smodel_of_run hx) refGains_certified N fun k hk =>
    hx.tick (ts + k) (by omega) fun k' h1 h2 => (hprev k' h1 (by omega)).1

/-- **The target inclusion**: inside the safety box the tracking error is at most `δH`. -/
theorem err_le_of_sbox (τ : ℕ) (h : SBox (ξV w₀ x) (ξH w₀ x) τ) : err (x τ) ≤ δH := by
  rw [err_eq (w₀ := w₀) τ]
  exact norm3_le (h.2.1 0) (h.2.1 1) h.2.2 (by norm_num [eHS, eVS, δH]) (by norm_num [δH])

end Loop

/-- **The safety theorem, horizontal-leg world** (REACH.md §11): from hover at `p₀`, at every tick
of `[0, T]`, for every `T`, the vehicle is within `δH = 0.2156` of the instantaneous position
target. By the invariant rule on histories (`implements_always_of_prefix`, an instance of
`implements_always_of_invariant`) with the safety box as the family. `hP`, `hW`, `hS`, `hL` are the
context in which the fields of `TrackFacts` are discharged; the proof does not use them. -/
theorem tracking_safe_h (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (_hP : LegParams w₀)
    (_hW : ReachWorld w₀ w') (_hS : Plant.CopterSense sense32 senseP) (_hL : LibmSpec)
    (hF : TrackFacts sense32 senseP w₀ p₀ ψ₀) (T : ℕ) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang_t 0 (.always 0 T (track δH))⟩ :=
  implements_always_of_prefix (ahover_tick0 p₀ ψ₀) (fun x k => SBox (ξV w₀ x) (ξH w₀ x) k) ts
    (fun x => δH - dist (pos x) (posTarget x)) T
    (fun x hx τ hτ hprev => sbox_run (hF.run x hx) τ hτ hprev)
    (fun x hx τ hτ => by
      have := (hF.run x hx).early τ hτ
      have : err (x τ) ≤ δH := this.trans (by norm_num [δH])
      simpa [err] using this)
    (fun x hx τ _ h => by
      have := err_le_of_sbox (w₀ := w₀) τ h
      simpa [err] using this)

/-- **The unbounded form**: at every tick. -/
theorem tracking_safe_h_forever (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (hP : LegParams w₀)
    (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : TrackFacts sense32 senseP w₀ p₀ ψ₀) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang (track δH)⟩ := by
  intro x hx t
  have := tracking_safe_h sense32 senseP w₀ p₀ w' ψ₀ hP hW hS hL hF t hx
  exact (sat_always.1 this) t (by omega) (by omega)

end

end Contracts.Track.Reach.Safe
