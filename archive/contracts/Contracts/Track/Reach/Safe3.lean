import Contracts.Track.Reach.Safe
import Contracts.Track.Reach.Leg3

/-!
# The safety theorem, 3D world at `PSC_D_ACC_P 0.25` (REACH.md §11)

```
theorem tracking_safe (sense32 senseP w₀) (p₀ : P3) (w' : Vector3p.State) (ψ₀ : ℝ)
    (hP : LegParams3 w₀) (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP)
    (hL : LibmSpec) (hF : TrackFacts3 sense32 senseP w₀ p₀ ψ₀) (T : ℕ) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang_t 0 (.always 0 T (track δ3))⟩
```

From hover at `p₀`, at every tick `t ≤ T`, for every `T`, `‖p_t − sp_t‖ ≤ δ3 = 0.2668` in the world
of §10 (`LegParams3`, vertical acceleration gain 0.25, a reference that moves on all three axes
within the navigator's limits). `tracking_safe_forever` is the unbounded form.

**The margin.** Horizontally the axis of Safe.lean (`|e| ≤ 0.1433`); vertically the plain ℓ1
envelopes of the vertical limits through the model `VerticalHi`: `|ez| ≤ 0.1735` (`posV3S_close`:
target acceleration `1.001 · 0.0434`, defects `1.3·10⁻⁴ · 401 + 8·10⁻⁴ · 88.5`, rows `0.0069`, start
`6·10⁻⁵`), inside `BoxL3`'s `0.2`. `δ3 = 0.2668 ≥ √(2 · 0.1433² + 0.1735²) = 0.26678`; from the
box sizes alone (`0.15`, `0.2`) it would be `√0.085 = 0.2916`.

**Measured** (`‖p − sp‖` per tick over every tick of every run, scratchpad `safe/measure.py`): 3D
campaign (426 legs at 0.25): `0.04181`; random campaign (300 random legs at 0.25, and 20 runs of
the Lean vehicle): `0.04271`. Against `δ3 = 0.2668`.

**The horizon, the rule, the start**: as in Safe.lean. The box induction is uniform in the tick
(certified gains for every `N`); `TrackRun3.tick` has no horizon; the always is discharged by
`implements_always_of_prefix` (an instance of `implements_always_of_invariant` on the history state)
with `SBox3` as the family and the step of `leg_box3`'s induction (`sbox3_step`) as the inductive
step. The vertical start is `ε0VS = ε0VL` (repaired 2026-11-06: `LegRun3.init`'s velocity entry was
`10⁻⁶` against `5.03·10⁻⁶` measured).

**`TrackFacts3`**: `early`, `init`, `tick` only. Assumed against measured (max over the 3D and the
random campaigns, every tick from 2 on, scratchpad `safe/refs.py`, `safe/init.py`):

| field | assumed | measured |
|---|---|---|
| `early` | `err ≤ 10⁻⁶` at ticks 0, 1 | `1.22·10⁻⁷` |
| `init` | `ε0VS`, `ε0HL`; `|asp|, |asp_z| ≤ 10⁻³`; `|d₂| ≤ 10⁻⁶` | `ez 1.3·10⁻⁷`, `ev 5.03·10⁻⁶`, `eA ≈ 2.34·10⁻⁴` (computed), `w 4.45·10⁻⁵`; `7.6·10⁻⁵`, `7.0·10⁻⁵`; `1.2·10⁻⁷` |
| `tick` horizontal | `1.501`, `0.013`, `1.3·10⁻⁴`, `8·10⁻⁴`, `1.1·10⁻⁵` | `1.5` (configured max), `0.0125003`, `1.2585·10⁻⁴`, `7.6819·10⁻⁴`, `1.0402·10⁻⁵` |
| `tick` vertical | `1.001`, `0.013`, `1.3·10⁻⁴`, `8·10⁻⁴` | `1.0` (configured max), `0.0125002`, `6.98·10⁻⁵`, `4.017·10⁻⁴` |
| `tick` rows | `legWV3 ≤ εVL3`, `legWH ≤ εHL` while `BoxL3` holds | not observable in the trace (§10.3) |
-/

namespace Contracts.Track.Reach.Safe

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue Contracts.Track.Reach.Leg Contracts.Track.Reach.Leg3

noncomputable section

/-! ## The vertical channel at `PSC_D_ACC_P 0.25` -/

/-- The vertical position bound at `PSC_D_ACC_P 0.25`. -/
def eVS3 : ℝ := 1735 / 10000

/-- **The margin of the 3D world**: `√(2 · 0.1433² + 0.1735²) ≤ 0.2668`. -/
def δ3 : ℝ := 2668 / 10000

theorem boxV3S_close (o : Fin 5) (ho : o.val < 4) :
    ∑ j, PVH o j * ε0VS j + 1001 / 1000 * GBV3 o + 13 / 10 ^ 5 * GVH o 0 + 8 / 10 ^ 4 * GVH o 1 +
      ∑ j, GVH o j * εVL3 j ≤ bV3 o := by
  fin_cases o <;> simp_all [PVH, GVH, PVHq, GVHq, ε0VS, εVL3, GBV3, bV3, Fin.sum_univ_eight] <;>
    norm_num

theorem posV3S_close :
    ∑ j, PVH 0 j * ε0VS j + 1001 / 1000 * GBV3 0 + 13 / 10 ^ 5 * GVH 0 0 + 8 / 10 ^ 4 * GVH 0 1 +
      ∑ j, GVH 0 j * εVL3 j ≤ eVS3 := by
  simp [PVH, GVH, PVHq, GVHq, ε0VS, εVL3, GBV3, eVS3, Fin.sum_univ_eight]; norm_num

theorem boxU3S_close :
    (1001 / 1000 + 13 / 1000) * (454 / 10000) + (∑ j, PVH 4 j * (ε0VS j + 1 / 1000 * vAVa j) +
      13 / 1000 * GC1V + 13 / 10 ^ 5 * GVH 4 0 + 8 / 10 ^ 4 * GVH 4 1 + ∑ j, GVH 4 j * εVL3 j) ≤
      bV3 4 := by
  simp [PVH, GVH, PVHq, GVHq, ε0VS, εVL3, GC1V, vAVa, bV3, Fin.sum_univ_eight]; norm_num

/-- **The safety box of the 3D world** at tick `k`: `BoxL3` and the per-axis position bounds. -/
def SBox3 (ξV : ℕ → Fin 8 → ℝ) (ξH : ℕ → Fin 2 → Fin 9 → ℝ) (k : ℕ) : Prop :=
  BoxL3 ξV ξH k ∧ (∀ a, |ξH k a 0| ≤ eHS) ∧ |ξV k 0| ≤ eVS3

/-- The model of the 3D loop from `t₀` (`LegModel3` with the start `ε0VS`, without the per-tick
facts). -/
structure SModel3 (ξV wV : ℕ → Fin 8 → ℝ) (aZ d1Z d2Z : ℕ → ℝ)
    (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (aH d1H d2H : ℕ → Fin 2 → ℝ) (t₀ : ℕ) : Prop where
  stepV : ∀ t, t₀ ≤ t → ξV (t + 1) = VerticalHi.AvR *ᵥ ξV t +
    (aZ t • VerticalHi.BvR + (-d1Z t) • Vertical.e0 + (-d2Z t) • Vertical.e1 + wV t)
  stepH : ∀ t, t₀ ≤ t → ∀ a, ξH (t + 1) a = Horizontal.AhR *ᵥ ξH t a +
    (aH t a • Horizontal.BhR + (-d1H t a) • Horizontal.e0 + (-d2H t a) • Horizontal.e1 + wH t a)
  initV : ∀ j, |ξV t₀ j| ≤ ε0VS j
  initH : ∀ a j, |ξH t₀ a j| ≤ ε0HL j
  initA : ∀ a, |aH t₀ a| ≤ 1 / 1000
  initAZ : |aZ t₀| ≤ 1 / 1000
  initD : ∀ a, |d2H t₀ a| ≤ 1 / 10 ^ 6

theorem hb_of_tick3 {ξV wV : ℕ → Fin 8 → ℝ} {aZ d1Z d2Z : ℕ → ℝ}
    {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ} {aH d1H d2H : ℕ → Fin 2 → ℝ} {t : ℕ}
    (h : TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t) (a : Fin 2) :
    HB (fun t => wH t a) (fun t => aH t a) (fun t => d1H t a) (fun t => d2H t a) t :=
  ⟨h.bwH a, h.baH a, h.bjH a, h.bd1H a, h.bd2H a, h.bdd2H a⟩

section Step

variable {ξV wV : ℕ → Fin 8 → ℝ} {aZ d1Z d2Z : ℕ → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ}
  {aH d1H d2H : ℕ → Fin 2 → ℝ} {t₀ : ℕ}

/-- The throttle `u` (Leg3Tube's `u_bound` with the start `ε0VS`). -/
theorem u_boundS (hM : SModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains3)
    (N : ℕ) (hT : ∀ k < N, TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k)) :
    |outV 4 ⬝ᵥ ξV (t₀ + N)| ≤ bV3 4 := by
  set ζ : ℕ → Fin 8 → ℝ := fun t => ξV t - aZ t • VerticalHi.vAccV with hζ
  have hstep : ∀ t, t₀ ≤ t → ζ (t + 1) = VerticalHi.AvR *ᵥ ζ t +
      ((fun t => -(aZ (t + 1) - aZ t)) t • VerticalHi.vAccV + (fun t => -d1Z t) t • Vertical.e0 +
        (fun t => -d2Z t) t • Vertical.e1 + wV t) := fun t ht =>
    zetaV_step ξV wV aZ d1Z d2Z t (hM.stepV t ht)
  have hx : ∀ j, |ζ t₀ j| ≤ ε0VS j + 1 / 1000 * vAVa j := by
    intro j
    have h1 := hM.initV j
    have h2 := hM.initAZ
    have hv := vAccV_abs j
    have hv0 := vAVa_nonneg j
    simp only [hζ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    nlinarith [abs_nonneg (aZ t₀), abs_nonneg (VerticalHi.vAccV j)]
  have e : outV 4 ⬝ᵥ ξV (t₀ + N) =
      outV 4 ⬝ᵥ ζ (t₀ + N) + aZ (t₀ + N) * (-1 / (Vertical.amax : ℝ)) := by
    simp only [hζ, dotProduct_sub, dotProduct_smul, outV4_vAccV, smul_eq_mul]
    ring
  have hA : |aZ (t₀ + N)| ≤ 1001 / 1000 + 13 / 1000 := by
    rcases N with _ | k
    · have := hM.initAZ; simp only [add_zero]; linarith
    · have h1 := (hT k (by omega)).baZ
      have h2 := (hT k (by omega)).bjZ
      rw [show t₀ + (k + 1) = t₀ + k + 1 by omega]
      have := abs_sub_abs_le_abs_sub (aZ (t₀ + k + 1)) (aZ (t₀ + k))
      linarith
  rw [e]
  have B := out_le VerticalHi.AvR ζ wV (fun t => -(aZ (t + 1) - aZ t)) (fun t => -d1Z t)
    (fun t => -d2Z t) VerticalHi.vAccV Vertical.e0 Vertical.e1 t₀ hstep (outV 4) N
    (fun j => ε0VS j + 1 / 1000 * vAVa j) (PVH 4) (GVH 4) εVL3 hx (fun j m => peakVH' 4 j m)
    (fun j N => gainVH' 4 j N) εVL3_nonneg (fun k hk j => (hT k hk).bwV j)
    (env_const_neg _ (fun t => aZ (t + 1) - aZ t) t₀ N (by norm_num)
      (fun k hk => (hT k hk).bjZ) (hg.gainU N))
    (env_const_neg _ d1Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd1Z) (gVH0 4 N))
    (env_const_neg _ d2Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd2Z) (gVH1 4 N))
  have C := boxU3S_close
  have hI := inv_amax_le
  have hI0 : 0 ≤ 1 / (Vertical.amax : ℝ) := by
    norm_num [Vertical.amax, Vertical.tw, Vertical.grav]
  have h3 : |aZ (t₀ + N) * (-1 / (Vertical.amax : ℝ))| ≤
      (1001 / 1000 + 13 / 1000) * (454 / 10000) := by
    rw [abs_mul, neg_div, abs_neg, abs_of_nonneg hI0]
    exact mul_le_mul hA hI hI0 (by norm_num)
  have := abs_add_le (outV 4 ⬝ᵥ ζ (t₀ + N)) (aZ (t₀ + N) * (-1 / (Vertical.amax : ℝ)))
  linarith

/-- **The step of the 3D box induction** (the step of `leg_box3`'s strong induction, any `N`). -/
theorem sbox3_step (hM : SModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains)
    (hg3 : RefGains3) (N : ℕ)
    (hT : ∀ k < N, TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k)) :
    SBox3 ξV ξH (t₀ + N) := by
  have hV : ∀ o, |outV o ⬝ᵥ ξV (t₀ + N)| ≤ ∑ j, PVH o j * ε0VS j + 1001 / 1000 * GBV3 o +
      13 / 10 ^ 5 * GVH o 0 + 8 / 10 ^ 4 * GVH o 1 + ∑ j, GVH o j * εVL3 j := fun o =>
    out_le VerticalHi.AvR ξV wV aZ (fun t => -d1Z t) (fun t => -d2Z t) VerticalHi.BvR Vertical.e0
      Vertical.e1 t₀ hM.stepV (outV o) N ε0VS (PVH o) (GVH o) εVL3 hM.initV
      (fun j m => peakVH' o j m) (fun j N => gainVH' o j N) εVL3_nonneg
      (fun k hk j => (hT k hk).bwV j)
      (env_const _ aZ t₀ N (by norm_num) (fun k hk => (hT k hk).baZ) (hg3.gainBV o N))
      (env_const_neg _ d1Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd1Z) (gVH0 o N))
      (env_const_neg _ d2Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd2Z) (gVH1 o N))
  have hH : ∀ a, (∀ o, |outH o ⬝ᵥ ξH (t₀ + N) a| ≤ bHL o) ∧ |ξH (t₀ + N) a 0| ≤ eHS := fun a =>
    axis_box (ξ := fun t => ξH t a) ⟨fun t ht => hM.stepH t ht a, hM.initH a, hM.initA a,
      hM.initD a⟩ hg N fun k hk => hb_of_tick3 (hT k hk) a
  refine ⟨⟨fun o => ?_, fun a o => (hH a).1 o⟩, fun a => (hH a).2, ?_⟩
  · by_cases h4 : o = 4
    · subst h4; exact u_boundS hM hg3 N hT
    have ho : o.val < 4 := by
      have := o.isLt
      have h4' : o.val ≠ 4 := fun h => h4 (Fin.ext h)
      omega
    exact (hV o).trans (boxV3S_close o ho)
  · have := (hV 0).trans posV3S_close
    rwa [outV0_dot] at this

end Step

/-! ## The facts and the theorem -/

/-- **The per-tick facts of one 3D behavior from hover** (no navigator phase, no completion,
loiter or hold, no sum over the run). Assumed against measured: the table of the module
docstring. -/
structure TrackRun3 (w₀ : Vehicle.World) (x : ℕ → X) : Prop where
  /-- **Before the tube** (ticks 0 and 1): within `10⁻⁶` of the target (measured `1.22·10⁻⁷`). -/
  early : ∀ t < ts, err (x t) ≤ 1 / 10 ^ 6
  /-- **The start of the tube** (tick 2): the vertical readouts within `ε0VS`, the horizontal
  within `ε0HL`, the target accelerations `≤ 10⁻³` (measured `≤ 7.6·10⁻⁵`), the horizontal velocity
  defect `≤ 10⁻⁶` (measured `1.2·10⁻⁷`). -/
  init : (∀ j, |ξV w₀ x ts j| ≤ ε0VS j) ∧ (∀ a j, |ξH w₀ x ts a j| ≤ ε0HL j) ∧
    (∀ a, |aH w₀ x ts a| ≤ 1 / 1000) ∧ |aZ w₀ x ts| ≤ 1 / 1000 ∧
    ∀ a, |d2H w₀ x ts a| ≤ 1 / 10 ^ 6
  /-- **The tick glue and the reference limits at every tick while the box holds** (`TickBounds3`,
  as `LegRun3.tick` with no horizon). -/
  tick : ∀ t, ts ≤ t → (∀ k, ts ≤ k → k ≤ t → BoxL3 (ξV w₀ x) (ξH w₀ x) k) →
    TickBounds3 (ξV w₀ x) (legWV3 w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) t

/-- **The facts of the 3D safety theorem**: `TrackRun3` for every behavior of the loop from
hover. -/
structure TrackFacts3 (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p₀ : P3)
    (ψ₀ : ℝ) : Prop where
  run : ∀ x ∈ Mloop sense32 senseP w₀ ∩ Reach.Ahover p₀ ψ₀, TrackRun3 w₀ x

section Loop

variable {w₀ : Vehicle.World} {x : ℕ → X}

theorem smodel3_of_run (hx : TrackRun3 w₀ x) :
    SModel3 (ξV w₀ x) (legWV3 w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) ts where
  stepV t _ := by
    simp only [legWV3, VerticalHi.forceOf, aZ, d1Z, d2Z, neg_smul]
    abel
  stepH t _ a := by
    simp only [legWH, Horizontal.forceOf, aH, d1H, d2H, neg_smul]
    abel
  initV := hx.init.1
  initH := hx.init.2.1
  initA := hx.init.2.2.1
  initAZ := hx.init.2.2.2.1
  initD := hx.init.2.2.2.2

/-- **The inductive step on the loop** (3D). -/
theorem sbox3_run (hx : TrackRun3 w₀ x) (τ : ℕ) (hτ : ts ≤ τ)
    (hprev : ∀ k, ts ≤ k → k < τ → SBox3 (ξV w₀ x) (ξH w₀ x) k) :
    SBox3 (ξV w₀ x) (ξH w₀ x) τ := by
  obtain ⟨N, rfl⟩ : ∃ N, τ = ts + N := ⟨τ - ts, by omega⟩
  exact sbox3_step (smodel3_of_run hx) refGains_certified refGains3_certified N fun k hk =>
    hx.tick (ts + k) (by omega) fun k' h1 h2 => (hprev k' h1 (by omega)).1

/-- **The target inclusion** (3D): inside the safety box the tracking error is at most `δ3`. -/
theorem err_le_of_sbox3 (τ : ℕ) (h : SBox3 (ξV w₀ x) (ξH w₀ x) τ) : err (x τ) ≤ δ3 := by
  rw [err_eq (w₀ := w₀) τ]
  exact norm3_le (h.2.1 0) (h.2.1 1) h.2.2 (by norm_num [eHS, eVS3, δ3]) (by norm_num [δ3])

end Loop

/-- **The safety theorem, 3D world** (REACH.md §11): from hover at `p₀`, at every tick of `[0, T]`,
for every `T`, the vehicle is within `δ3 = 0.2668` of the instantaneous position target. By the
invariant rule on histories with the 3D safety box as the family. `hP`, `hW`, `hS`, `hL` are the
context of the fields; the proof does not use them. -/
theorem tracking_safe (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (_hP : LegParams3 w₀)
    (_hW : ReachWorld w₀ w') (_hS : Plant.CopterSense sense32 senseP) (_hL : LibmSpec)
    (hF : TrackFacts3 sense32 senseP w₀ p₀ ψ₀) (T : ℕ) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang_t 0 (.always 0 T (track δ3))⟩ :=
  implements_always_of_prefix (ahover_tick0 p₀ ψ₀) (fun x k => SBox3 (ξV w₀ x) (ξH w₀ x) k) ts
    (fun x => δ3 - dist (pos x) (posTarget x)) T
    (fun x hx τ hτ hprev => sbox3_run (hF.run x hx) τ hτ hprev)
    (fun x hx τ hτ => by
      have := (hF.run x hx).early τ hτ
      have : err (x τ) ≤ δ3 := this.trans (by norm_num [δ3])
      simpa [err] using this)
    (fun x hx τ _ h => by
      have := err_le_of_sbox3 (w₀ := w₀) τ h
      simpa [err] using this)

/-- **The unbounded form** (3D): at every tick. -/
theorem tracking_safe_forever (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (hP : LegParams3 w₀)
    (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : TrackFacts3 sense32 senseP w₀ p₀ ψ₀) :
    Mloop sense32 senseP w₀ ⊨ ⟨Ahover p₀ ψ₀, lang (track δ3)⟩ := by
  intro x hx t
  have := tracking_safe sense32 senseP w₀ p₀ w' ψ₀ hP hW hS hL hF t hx
  exact (sat_always.1 this) t (by omega) (by omega)

end

end Contracts.Track.Reach.Safe
