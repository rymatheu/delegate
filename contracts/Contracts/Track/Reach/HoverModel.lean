import Contracts.Track.Reach.HoverTube

/-!
# The hover model with the measured disturbance class, and its constants (REACH.md §8.7)

The readouts `ξV`, `ξH` of a displaced hold follow `A_v`, `A_h` from `t₀`; at `t₀` they are a
position offset `d` (`|dᵢ| ≤ 2.1` cm) plus deviations within `ε0Vs`, `ε0Hs`; while the box `BoxS`
has held, each row of the per-tick disturbance is within its floor (`εVs`, `εHs`) up to an excess
whose weighted sum `Σ_k exc_k / λ^(k+1)` is at most `κV j · ‖d‖∞`, `κH j · ‖d‖∞`
(`HoverModelS`). The numbers are the hover campaign's (REACH.md §8.7):

| | vertical (`ez, ev, eV, eA, I, f, u, w`) | horizontal (`e, ev, E, D, I, a, c₁, c₂, c₃`) |
|---|---|---|
| floor `ε` | `1.1e-9, 3.5e-8, 2e-7, 5e-6, 2.003e-7, 1e-7, 3.4e-6, 4e-7` | `εHh`: `2.2e-7, 2.5e-5, 3.7e-6, 2.31e-4, 6.2e-7, 0, 1.61e-4, 0, 0` |
| excess `κ` (per meter of `‖d‖∞`) | `8.1e-4, 0.035, 0, 3.32, 8.3e-4, 0, 0.8, 0` | `226 · (h²/2, h, 0, …)` |
| start `ε0` | `0, 1e-6, 1e-5, 2e-5, 1e-4, 1e-4, 1e-4, 1e-4` | `ε0Hh` |
| box | `|ez| ≤ 0.1`, `|ev| ≤ 0.5`, `|I| ≤ 0.5`, `|f|, |u| ≤ 0.12` | `|e| ≤ 0.1`, `|ev| ≤ 0.5`, `|I| ≤ 5`, `|c₁| ≤ 0.5`, `|c₁ − c₂| ≤ 0.075` |

`hover_box_s`: the box at every tick (the region closes: `regionVs`, `regionHs`), and every output
within its free response plus `Σ P ε0 + Σ G ε + Σ P κ ‖d‖∞`. `hover_axes_s`: per axis,
`|eₐ| ≤ 3.47 λᴺ |dₐ| + mH λᴺ ‖d‖∞ + 2.50 mm` and `|e_D| ≤ 1.452 λ_vᴺ |d_D| + mV λᴺ ‖d‖∞ + 0.35 mm`,
with `mH = Σ cH κH`, `mV = Σ cV κV` for any per-coordinate decay constants of the position
responses (`|resp(e, m, j)| ≤ c_j λᵐ`).
-/

namespace Contracts.Track.Reach.Hover

open Matrix Finset Contracts.Track Contracts.Track.Induction Contracts.Track.Induction.Nominal
open Contracts.Track.Reach.Glue

noncomputable section

/-! ## The constants -/

/-- Per-tick floor of the vertical rows: INDUCTION's code part `εV` plus the persistent structured
part (plant and sampled specific force at the quantized tilt, the boost): `1e-9, 1e-8, 0, 1e-6,
3e-10, 0, 2e-7, 0` (measured after the transient: `1.2e-10, 1.9e-9, 0, 3.2e-7, 8.1e-11, 0, 5.0e-8, 0`). -/
def εVs : Fin 8 → ℝ := ![11 / 10 ^ 10, 35 / 10 ^ 9, 2 / 10 ^ 7, 5 / 10 ^ 6, 2003 / 10 ^ 10, 1 / 10 ^ 7,
  34 / 10 ^ 7, 4 / 10 ^ 7]

/-- Per-tick floor of the horizontal rows: `εHh` (the code part `εHβ` plus `εη = 0.01` m/s²
through `eAcc`). -/
def εHs : Fin 9 → ℝ := εHh

/-- Start deviation, vertical (the acceleration error of a settled hold: measured `1.04e-5`). -/
def ε0Vs : Fin 8 → ℝ := ![0, 1 / 10 ^ 6, 1 / 10 ^ 5, 2 / 10 ^ 5, 1 / 10 ^ 4, 1 / 10 ^ 4, 1 / 10 ^ 4,
  1 / 10 ^ 4]

/-- Start deviation, horizontal. -/
def ε0Hs : Fin 9 → ℝ := ε0Hh

/-- The weighted excess of the vertical rows per meter of `‖d‖∞` (measured `7.86e-4, 0.0339, 0,
3.245, 8.10e-4, 0, 0.779, 0`). -/
def κV : Fin 8 → ℝ := ![81 / 10 ^ 5, 35 / 1000, 0, 332 / 100, 83 / 10 ^ 5, 0, 8 / 10, 0]

/-- The weighted excess of the attitude deviation over `εη` per meter of `‖d‖∞` (measured
`220.75`). -/
def κη : ℝ := 226

/-- The weighted excess of the horizontal rows: `κη · eAcc` (`eAcc = (h²/2, h, 0, …)`). -/
def κH : Fin 9 → ℝ := ![226 / 320000, 226 / 400, 0, 0, 0, 0, 0, 0, 0]

theorem κH_eq (j : Fin 9) : κH j = κη * eAcc j := by
  fin_cases j <;> simp [κH, κη, eAcc, Plant.h] <;> norm_num

/-- Vertical box (`bVh`). -/
def bVs : Fin 5 → ℝ := bVh

/-- Horizontal box: `bHh` with the command rate `|c₁ − c₂| ≤ 0.075` (the attitude deviation's
transient adds `1.53 · 0.0119` to the rate's tube). -/
def bHs : Fin 5 → ℝ := ![1 / 10, 1 / 2, 5, 1 / 2, 3 / 40]

/-- `‖d‖∞`. -/
def dinf (d : Fin 3 → ℝ) : ℝ := max |d 0| (max |d 1| |d 2|)

theorem le_dinf (d : Fin 3 → ℝ) (i : Fin 3) : |d i| ≤ dinf d := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem dinf_nonneg (d : Fin 3 → ℝ) : 0 ≤ dinf d := (abs_nonneg _).trans (le_dinf d 0)

theorem dinf_le {d : Fin 3 → ℝ} {r : ℝ} (h : ∀ i, |d i| ≤ r) : dinf d ≤ r :=
  max_le (h 0) (max_le (h 1) (h 2))

theorem εVs_nonneg (j : Fin 8) : 0 ≤ εVs j := by fin_cases j <;> simp [εVs] <;> norm_num
theorem εHs_nonneg (j : Fin 9) : 0 ≤ εHs j := εHh_nonneg j
theorem κV_nonneg (j : Fin 8) : 0 ≤ κV j := by fin_cases j <;> simp [κV] <;> norm_num
theorem κH_nonneg (j : Fin 9) : 0 ≤ κH j := by fin_cases j <;> simp [κH] <;> norm_num

theorem PV_nonneg (o : Fin 5) (j : Fin 8) : 0 ≤ PV o j := (abs_nonneg _).trans (peakV' o j 0)
theorem PH_nonneg (o : Fin 5) (j : Fin 9) : 0 ≤ PH o j := (abs_nonneg _).trans (peakH' o j 0)

/-- **The region closes (vertical)**: offset, start deviation, tube and excess inside the box. -/
theorem regionVs (o : Fin 5) :
    PV o 0 * dMax + (∑ j, PV o j * ε0Vs j + ∑ j, GV o j * εVs j) + ∑ j, PV o j * (κV j * dMax) ≤
      bVs o := by
  fin_cases o <;>
    simp [PV, GV, ε0Vs, εVs, κV, bVs, bVh, dMax, Fin.sum_univ_eight] <;> norm_num

/-- **The region closes (horizontal).** -/
theorem regionHs (o : Fin 5) :
    PH o 0 * dMax + (∑ j, PH o j * ε0Hs j + ∑ j, GH o j * εHs j) + ∑ j, PH o j * (κH j * dMax) ≤
      bHs o := by
  fin_cases o <;>
    simp [PH, GH, ε0Hs, ε0Hh, εHs, εHh, κH, bHs, dMax, Fin.sum_univ_succ] <;> norm_num

/-- The position tube, vertical: `≤ 0.35` mm. -/
theorem tubeVs : ∑ j, PV 0 j * ε0Vs j + ∑ j, GV 0 j * εVs j ≤ 35 / 100000 := by
  simp [PV, GV, ε0Vs, εVs, Fin.sum_univ_eight]; norm_num

/-- The position tube, horizontal: `≤ 2.51` mm (`tubeH0`). -/
theorem tubeHs : ∑ j, PH 0 j * ε0Hs j + ∑ j, GH 0 j * εHs j ≤ 251 / 100000 := tubeH0

/-! ## The model -/

/-- The box at tick `t`. -/
def BoxS (ξV : ℕ → Fin 8 → ℝ) (ξH : ℕ → Fin 2 → Fin 9 → ℝ) (t : ℕ) : Prop :=
  (∀ o, |outV o ⬝ᵥ ξV t| ≤ bVs o) ∧ ∀ a o, |outH o ⬝ᵥ ξH t a| ≤ bHs o

/-- **The hover hypotheses on the error coordinates** from `t₀`, with the measured disturbance
class: per-row floor plus a transient excess of bounded weighted sum. -/
structure HoverModelS (ξV wV : ℕ → Fin 8 → ℝ) (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (t₀ : ℕ)
    (d : Fin 3 → ℝ) : Prop where
  stepV : ∀ t, t₀ ≤ t → ξV (t + 1) = Vertical.AvR *ᵥ ξV t + wV t
  stepH : ∀ t, t₀ ≤ t → ∀ a, ξH (t + 1) a = Horizontal.AhR *ᵥ ξH t a + wH t a
  initV : ∀ j, |ξV t₀ j - (Pi.single 0 (d 2) : Fin 8 → ℝ) j| ≤ ε0Vs j
  initH : ∀ a j, |ξH t₀ a j - (Pi.single 0 (d a.castSucc) : Fin 9 → ℝ) j| ≤ ε0Hs j
  sumV : ∀ N, (∀ k < N, BoxS ξV ξH (t₀ + k)) →
    ∀ j, wsum (fun k => exc (wV (t₀ + k) j) (εVs j)) N ≤ κV j * dinf d
  sumH : ∀ N, (∀ k < N, BoxS ξV ξH (t₀ + k)) →
    ∀ a j, wsum (fun k => exc (wH (t₀ + k) a j) (εHs j)) N ≤ κH j * dinf d

section Model

variable {ξV wV : ℕ → Fin 8 → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ} {t₀ : ℕ} {d : Fin 3 → ℝ}

theorem tubeV_s (hM : HoverModelS ξV wV ξH wH t₀ d) (N : ℕ) (_hB : ∀ k < N, BoxS ξV ξH (t₀ + k))
    (o : Fin 5) :
    |outV o ⬝ᵥ ξV (t₀ + N) - d 2 * resp Vertical.AvR (outV o) N 0| ≤
      ∑ j, PV o j * ε0Vs j + ∑ j, GV o j * εVs j +
        ∑ j, ∑ k ∈ range N, |resp Vertical.AvR (outV o) (N - 1 - k) j| *
          exc (wV (t₀ + k) j) (εVs j) :=
  chan_tube_exc Vertical.AvR ξV wV t₀ N 0 (d 2) hM.stepV (outV o) ε0Vs εVs (PV o) (GV o)
    (fun k j => exc (wV (t₀ + k) j) (εVs j)) εVs_nonneg hM.initV
    (fun _ _ _ => abs_le_exc _ _) (fun j m => peakV' o j m) (fun j N => gainV' o j N)

theorem tubeH_s (hM : HoverModelS ξV wV ξH wH t₀ d) (N : ℕ) (a : Fin 2) (o : Fin 5) :
    |outH o ⬝ᵥ ξH (t₀ + N) a - d a.castSucc * resp Horizontal.AhR (outH o) N 0| ≤
      ∑ j, PH o j * ε0Hs j + ∑ j, GH o j * εHs j +
        ∑ j, ∑ k ∈ range N, |resp Horizontal.AhR (outH o) (N - 1 - k) j| *
          exc (wH (t₀ + k) a j) (εHs j) :=
  chan_tube_exc Horizontal.AhR (fun t => ξH t a) (fun t => wH t a) t₀ N 0 (d a.castSucc)
    (fun t ht => hM.stepH t ht a) (outH o) ε0Hs εHs (PH o) (GH o)
    (fun k j => exc (wH (t₀ + k) a j) (εHs j)) εHs_nonneg (hM.initH a)
    (fun _ _ _ => abs_le_exc _ _) (fun j m => peakH' o j m) (fun j N => gainH' o j N)

/-- The excess part through the peak gains, vertical. -/
theorem excV_peak (hM : HoverModelS ξV wV ξH wH t₀ d) (N : ℕ) (hB : ∀ k < N, BoxS ξV ξH (t₀ + k))
    (o : Fin 5) :
    ∑ j, ∑ k ∈ range N, |resp Vertical.AvR (outV o) (N - 1 - k) j| * exc (wV (t₀ + k) j) (εVs j) ≤
      ∑ j, PV o j * (κV j * dinf d) := by
  refine (exc_peak Vertical.AvR (outV o) (PV o) (fun k j => exc (wV (t₀ + k) j) (εVs j))
    (fun _ _ => exc_nonneg _ _) (fun j m => peakV' o j m) N).trans ?_
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hM.sumV N hB j) (PV_nonneg o j)

theorem excH_peak (hM : HoverModelS ξV wV ξH wH t₀ d) (N : ℕ) (hB : ∀ k < N, BoxS ξV ξH (t₀ + k))
    (a : Fin 2) (o : Fin 5) :
    ∑ j, ∑ k ∈ range N, |resp Horizontal.AhR (outH o) (N - 1 - k) j| *
        exc (wH (t₀ + k) a j) (εHs j) ≤ ∑ j, PH o j * (κH j * dinf d) := by
  refine (exc_peak Horizontal.AhR (outH o) (PH o) (fun k j => exc (wH (t₀ + k) a j) (εHs j))
    (fun _ _ => exc_nonneg _ _) (fun j m => peakH' o j m) N).trans ?_
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hM.sumH N hB a j) (PH_nonneg o j)

/-- **Forward invariance of the box** (strong induction: the box up to `t₀ + N − 1` bounds the
excess sums, the tube then puts the outputs at `t₀ + N` back in the box). -/
theorem hover_box_s (hM : HoverModelS ξV wV ξH wH t₀ d) (hd : ∀ i, |d i| ≤ dMax) (N : ℕ) :
    BoxS ξV ξH (t₀ + N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hB : ∀ k < N, BoxS ξV ξH (t₀ + k) := fun k hk => ih k hk
    have hD : dinf d ≤ dMax := dinf_le hd
    have hD0 := dinf_nonneg d
    refine ⟨fun o => ?_, fun a o => ?_⟩
    · have h1 := tubeV_s hM N hB o
      have h2 := excV_peak hM N hB o
      have h3 : |d 2 * resp Vertical.AvR (outV o) N 0| ≤ PV o 0 * dMax := by
        rw [abs_mul, mul_comm]
        exact mul_le_mul (peakV' o 0 N) (hd 2) (abs_nonneg _) (PV_nonneg o 0)
      have h4 : ∑ j, PV o j * (κV j * dinf d) ≤ ∑ j, PV o j * (κV j * dMax) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD (κV_nonneg j)) (PV_nonneg o j)
      have h5 := regionVs o
      have := abs_sub_abs_le_abs_sub (outV o ⬝ᵥ ξV (t₀ + N)) (d 2 * resp Vertical.AvR (outV o) N 0)
      linarith
    · have h1 := tubeH_s hM N a o
      have h2 := excH_peak hM N hB a o
      have h3 : |d a.castSucc * resp Horizontal.AhR (outH o) N 0| ≤ PH o 0 * dMax := by
        rw [abs_mul, mul_comm]
        exact mul_le_mul (peakH' o 0 N) (hd _) (abs_nonneg _) (PH_nonneg o 0)
      have h4 : ∑ j, PH o j * (κH j * dinf d) ≤ ∑ j, PH o j * (κH j * dMax) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD (κH_nonneg j)) (PH_nonneg o j)
      have h5 := regionHs o
      have := abs_sub_abs_le_abs_sub (outH o ⬝ᵥ ξH (t₀ + N) a)
        (d a.castSucc * resp Horizontal.AhR (outH o) N 0)
      linarith

/-- **The position errors per axis** (horizontal axis `a`, outputs `outH 0`; vertical `outV 0`), for
any per-coordinate decay constants `cH`, `cV` of the position responses. -/
theorem hover_axes_s (hM : HoverModelS ξV wV ξH wH t₀ d) (hd : ∀ i, |d i| ≤ dMax)
    (cH : Fin 9 → ℝ) (cV : Fin 8 → ℝ)
    (hcH : ∀ j m, |resp Horizontal.AhR (outH 0) m j| ≤ cH j * lam ^ m)
    (hcV : ∀ j m, |resp Vertical.AvR (outV 0) m j| ≤ cV j * lam ^ m) (N : ℕ) :
    (∀ a : Fin 2, |outH 0 ⬝ᵥ ξH (t₀ + N) a| ≤ 347 / 100 * lam ^ N * |d a.castSucc| +
      lam ^ N * ((∑ j, cH j * κH j) * dinf d) + 251 / 100000) ∧
    |outV 0 ⬝ᵥ ξV (t₀ + N)| ≤ 1452 / 1000 * (Vertical.lamv : ℝ) ^ N * |d 2| +
      lam ^ N * ((∑ j, cV j * κV j) * dinf d) + 35 / 100000 := by
  have hB : ∀ k < N, BoxS ξV ξH (t₀ + k) := fun k _ => hover_box_s hM hd k
  have hD0 := dinf_nonneg d
  have hl := lam_pos
  have hlN : 0 ≤ lam ^ N := by positivity
  refine ⟨fun a => ?_, ?_⟩
  · have h1 := tubeH_s hM N a 0
    have h2 := exc_decay Horizontal.AhR (outH 0) cH (fun k j => exc (wH (t₀ + k) a j) (εHs j))
      (fun _ _ => exc_nonneg _ _) hcH N
    have h3 : ∑ j, cH j * wsum (fun k => exc (wH (t₀ + k) a j) (εHs j)) N ≤
        (∑ j, cH j * κH j) * dinf d := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      have hc : 0 ≤ cH j := by
        have := hcH j 0; simp only [pow_zero, mul_one] at this; exact (abs_nonneg _).trans this
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hM.sumH N hB a j) hc
    have h4 := respH_decay N
    rw [lamh_eq] at h4
    have h5 : |d a.castSucc * resp Horizontal.AhR (outH 0) N 0| ≤ 347 / 100 * lam ^ N * |d a.castSucc| := by
      rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    have h6 := tubeHs
    have h7 := mul_le_mul_of_nonneg_left h3 hlN
    have := abs_sub_abs_le_abs_sub (outH 0 ⬝ᵥ ξH (t₀ + N) a) (d a.castSucc * resp Horizontal.AhR (outH 0) N 0)
    linarith
  · have h1 := tubeV_s hM N hB 0
    have h2 := exc_decay Vertical.AvR (outV 0) cV (fun k j => exc (wV (t₀ + k) j) (εVs j))
      (fun _ _ => exc_nonneg _ _) hcV N
    have h3 : ∑ j, cV j * wsum (fun k => exc (wV (t₀ + k) j) (εVs j)) N ≤
        (∑ j, cV j * κV j) * dinf d := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j _ => ?_
      have hc : 0 ≤ cV j := by
        have := hcV j 0; simp only [pow_zero, mul_one] at this; exact (abs_nonneg _).trans this
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hM.sumV N hB j) hc
    have h4 := respV_decay N
    have h5 : |d 2 * resp Vertical.AvR (outV 0) N 0| ≤ 1452 / 1000 * (Vertical.lamv : ℝ) ^ N * |d 2| := by
      rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    have h6 := tubeVs
    have h7 := mul_le_mul_of_nonneg_left h3 hlN
    have := abs_sub_abs_le_abs_sub (outV 0 ⬝ᵥ ξV (t₀ + N)) (d 2 * resp Vertical.AvR (outV 0) N 0)
    linarith

end Model

end

end Contracts.Track.Reach.Hover
