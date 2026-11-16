import Contracts.Track.Reach.Leg3GainV
import Contracts.Track.Reach.LegTube

/-!
# The 3D leg theorem, part (2): the tube at `PSC_D_ACC_P = 0.25` (REACH.md §10)

LegTube.lean with the vertical channel `VerticalHi` (`PSC_D_ACC_P = 0.25`) and a vertical reference
that moves (the S-curve of a leg with any elevation): per tick `|asp_z| ≤ 1.001`, its change
`≤ 0.013`, the defects `≤ 1.3·10⁻⁴`, `8·10⁻⁴`. The horizontal channel is LegTube's (same model,
same bounds, same certificates), restated on the 3D model `LegModel3` with the horizon
`hzn3 = 7200` (`◇_[0,6000] □_[0,1200]`).

**The box** (`BoxL3`): horizontally `bHL` (LegTube); vertically `bV3`: `|ez| ≤ 0.2` (INDUCTION's
`0.1` widened: the vertical defects alone give `0.12`; the vertical controller's region asks
`E ≤ 1`, and the code rows `βcode` at `E = 0.21` are within `εVL3`), `|ev| ≤ 0.5`, `|I| ≤ 0.5`,
`|f|, |u| ≤ 0.12`. The throttle `u` closes in the shifted coordinates `ζ = ξ − asp_z • vAccV`
(`VerticalHi.Av_vAccV`): the plain envelope gives `0.34` (the feed-forward `kpAcc · αA` of a target
acceleration), the shifted one `|asp_z|/amax + 0.054 = 0.0995 ≤ 0.12`.

**The rows** `εVL3`: LegTube's `εVL` with the `u` row `4·10⁻⁶` (the code's `β` of the throttle,
`kpAcc · W3c + W4c + N + b`, is `3.11·10⁻⁶` at `kpAcc = 0.05` and `3.89·10⁻⁶` at `0.25`, at the
region's magnitudes and `E = 0.21`); the other rows are unchanged (they do not contain `kpAcc`;
the structured tilt coupling depends on the horizontal acceleration, which is LegTube's).
-/

namespace Contracts.Track.Reach.Leg3

open Matrix Finset Contracts.Track.Induction Contracts.Track.Reach.Glue Contracts.Track.Reach.Leg

noncomputable section

/-! ## Constants -/

/-- The horizon of the 3D statement: `6000 + 1200` ticks. -/
def hzn3 : ℕ := 7200

/-- The decay time of the completion argument in 3D. -/
def Mc3 : ℕ := 704

/-- The decay time of the hold window in 3D. -/
def Mt3 : ℕ := 2624

/-- The vertical box at the leg: `|ez| ≤ 0.2`, `|ev| ≤ 0.5`, `|I| ≤ 0.5`, `|f|, |u| ≤ 0.12`. -/
def bV3 : Fin 5 → ℝ := ![2 / 10, 1 / 2, 1 / 2, 3 / 25, 3 / 25]

/-- Per-tick disturbance of the vertical channel at `PSC_D_ACC_P = 0.25` (`εVL` with the `u` row
`4·10⁻⁶`). -/
def εVL3 : Fin 8 → ℝ := ![11 / 10 ^ 8, 76 / 10 ^ 6, 2 / 10 ^ 7, 42 / 10 ^ 7, 2 / 10 ^ 7, 1 / 10 ^ 7,
  40 / 10 ^ 7, 4 / 10 ^ 7]

/-- ℓ1 gains of the vertical outputs `ez, ev, I, f, u` in the direction `B_v` (certified
`0.04342, 0.06424, 0.04533, 0.05647, 0.3407`, Leg3GainsData.lean). -/
def GBV3 : Fin 5 → ℝ := ![4343 / 100000, 6425 / 100000, 4533 / 100000, 5647 / 100000, 3408 / 10000]

/-- ℓ1 gain of the throttle `u` in the direction `vAccV` (certified `2.1105`). -/
def GC1V : ℝ := 2111 / 1000

/-- `|vAccV|` bounded above (`1/amax = 0.04532`). -/
def vAVa : Fin 8 → ℝ := ![0, 0, 0, 0, 454 / 10000, 454 / 10000, 454 / 10000, 454 / 10000]

/-- Vertical tails past `Mc3`: ℓ1 in the directions `B_v`, `e₀`, the peak in `e₁`. -/
def TBVc : ℝ := 2234 / 100000
def TV0c : ℝ := 7055 / 100
def PV1c : ℝ := 502 / 10000

/-- Vertical tails past `Mt3`. -/
def TBVt : ℝ := 4256 / 1000000
def TV0t : ℝ := 110 / 100
def PV1t : ℝ := 2179 / 1000000

/-! ## The acceleration shift of the vertical channel -/

theorem outV4_vAccV : outV 4 ⬝ᵥ VerticalHi.vAccV = -1 / (Vertical.amax : ℝ) := by
  rw [show outV 4 = Pi.single 6 1 from rfl, single_dotProduct, one_mul]
  simp [VerticalHi.vAccV]

theorem vAccV_abs (j : Fin 8) : |VerticalHi.vAccV j| ≤ vAVa j := by
  have h : 1 / (Vertical.amax : ℝ) ≤ 454 / 10000 := by
    norm_num [Vertical.amax, Vertical.tw, Vertical.grav]
  have h0 : 0 ≤ 1 / (Vertical.amax : ℝ) := by
    norm_num [Vertical.amax, Vertical.tw, Vertical.grav]
  fin_cases j <;> simp [VerticalHi.vAccV, vAVa, neg_div, abs_neg] <;>
    rw [abs_of_nonneg (by norm_num [Vertical.amax, Vertical.tw, Vertical.grav])] <;>
    norm_num [Vertical.amax, Vertical.tw, Vertical.grav]

theorem vAVa_nonneg (j : Fin 8) : 0 ≤ vAVa j := by
  fin_cases j <;> simp [vAVa] <;> norm_num

theorem inv_amax_le : 1 / (Vertical.amax : ℝ) ≤ 454 / 10000 := by
  norm_num [Vertical.amax, Vertical.tw, Vertical.grav]

/-- **The vertical shifted coordinates** `ζ = ξ − asp_z • vAccV` are driven by the vertical jerk. -/
theorem zetaV_step (ξ w : ℕ → Fin 8 → ℝ) (a d₁ d₂ : ℕ → ℝ) (t : ℕ)
    (h : ξ (t + 1) = VerticalHi.AvR *ᵥ ξ t + (a t • VerticalHi.BvR + (-d₁ t) • Vertical.e0 +
      (-d₂ t) • Vertical.e1 + w t)) :
    ξ (t + 1) - a (t + 1) • VerticalHi.vAccV = VerticalHi.AvR *ᵥ (ξ t - a t • VerticalHi.vAccV) +
      ((-(a (t + 1) - a t)) • VerticalHi.vAccV + (-d₁ t) • Vertical.e0 + (-d₂ t) • Vertical.e1 +
        w t) := by
  have hv := VerticalHi.Av_vAccV
  have e : VerticalHi.AvR *ᵥ (a t • VerticalHi.vAccV) =
      a t • VerticalHi.vAccV - a t • VerticalHi.BvR := by
    rw [mulVec_smul, show VerticalHi.AvR *ᵥ VerticalHi.vAccV = VerticalHi.vAccV - VerticalHi.BvR
      from eq_sub_of_add_eq hv, smul_sub]
  rw [h, mulVec_sub, e]
  module

/-! ## The box and the model -/

/-- **The 3D leg box** at tick `t`. -/
def BoxL3 (ξV : ℕ → Fin 8 → ℝ) (ξH : ℕ → Fin 2 → Fin 9 → ℝ) (t : ℕ) : Prop :=
  (∀ o, |outV o ⬝ᵥ ξV t| ≤ bV3 o) ∧ ∀ a o, |outH o ⬝ᵥ ξH t a| ≤ bHL o

/-- The per-tick bounds of the 3D reference and the disturbance: horizontally LegTube's; vertically
the target acceleration `≤ 1.001`, its change `≤ 0.013`, the defects `≤ 1.3·10⁻⁴`, `8·10⁻⁴`. -/
structure TickBounds3 (ξV wV : ℕ → Fin 8 → ℝ) (aZ d1Z d2Z : ℕ → ℝ)
    (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (aH d1H d2H : ℕ → Fin 2 → ℝ) (t : ℕ) : Prop where
  bwV : ∀ j, |wV t j| ≤ εVL3 j
  bwH : ∀ a j, |wH t a j| ≤ εHL j
  baZ : |aZ t| ≤ 1001 / 1000
  bjZ : |aZ (t + 1) - aZ t| ≤ 13 / 1000
  bd1Z : |d1Z t| ≤ 13 / 10 ^ 5
  bd2Z : |d2Z t| ≤ 8 / 10 ^ 4
  baH : ∀ a, |aH t a| ≤ 1501 / 1000
  bjH : ∀ a, |aH (t + 1) a - aH t a| ≤ 13 / 1000
  bd1H : ∀ a, |d1H t a| ≤ 13 / 10 ^ 5
  bd2H : ∀ a, |d2H t a| ≤ 8 / 10 ^ 4
  bdd2H : ∀ a, |d2H (t + 1) a - d2H t a| ≤ 11 / 10 ^ 6

/-- **The model of the 3D leg** from `t₀`. -/
structure LegModel3 (ξV wV : ℕ → Fin 8 → ℝ) (aZ d1Z d2Z : ℕ → ℝ)
    (ξH wH : ℕ → Fin 2 → Fin 9 → ℝ) (aH d1H d2H : ℕ → Fin 2 → ℝ) (t₀ : ℕ) : Prop where
  stepV : ∀ t, t₀ ≤ t → ξV (t + 1) = VerticalHi.AvR *ᵥ ξV t +
    (aZ t • VerticalHi.BvR + (-d1Z t) • Vertical.e0 + (-d2Z t) • Vertical.e1 + wV t)
  stepH : ∀ t, t₀ ≤ t → ∀ a, ξH (t + 1) a = Horizontal.AhR *ᵥ ξH t a +
    (aH t a • Horizontal.BhR + (-d1H t a) • Horizontal.e0 + (-d2H t a) • Horizontal.e1 + wH t a)
  initV : ∀ j, |ξV t₀ j| ≤ ε0VL j
  initH : ∀ a j, |ξH t₀ a j| ≤ ε0HL j
  initA : ∀ a, |aH t₀ a| ≤ 1 / 1000
  initAZ : |aZ t₀| ≤ 1 / 1000
  initD : ∀ a, |d2H t₀ a| ≤ 1 / 10 ^ 6
  tick : ∀ t, t₀ ≤ t → t < hzn3 → (∀ k, t₀ ≤ k → k ≤ t → BoxL3 ξV ξH k) →
    TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t

/-- The certified numbers of the vertical reference directions at `PSC_D_ACC_P = 0.25`
(`refGains3_certified`, Leg3Gains.lean). -/
structure RefGains3 : Prop where
  gainBV : ∀ o N, ∑ m ∈ range N, |rsp VerticalHi.AvR (outV o) VerticalHi.BvR m| ≤ GBV3 o
  gainU : ∀ N, ∑ m ∈ range N, |rsp VerticalHi.AvR (outV 4) VerticalHi.vAccV m| ≤ GC1V
  tailBVc : ∀ N, ∑ m ∈ range N, |rsp VerticalHi.AvR (outV 0) VerticalHi.BvR (Mc3 + m)| ≤ TBVc
  tail0Vc : ∀ N, ∑ m ∈ range N, |rsp VerticalHi.AvR (outV 0) Vertical.e0 (Mc3 + m)| ≤ TV0c
  peak1Vc : ∀ m, |rsp VerticalHi.AvR (outV 0) Vertical.e1 (Mc3 + m)| ≤ PV1c
  tailBVt : ∀ N, ∑ m ∈ range N, |rsp VerticalHi.AvR (outV 0) VerticalHi.BvR (Mt3 + m)| ≤ TBVt
  tail0Vt : ∀ N, ∑ m ∈ range N, |rsp VerticalHi.AvR (outV 0) Vertical.e0 (Mt3 + m)| ≤ TV0t
  peak1Vt : ∀ m, |rsp VerticalHi.AvR (outV 0) Vertical.e1 (Mt3 + m)| ≤ PV1t

theorem gVH0 (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp VerticalHi.AvR (outV o) Vertical.e0 m| ≤ GVH o 0 :=
  gainVH' o 0 N

theorem gVH1 (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp VerticalHi.AvR (outV o) Vertical.e1 m| ≤ GVH o 1 :=
  gainVH' o 1 N

theorem εVL3_nonneg (j : Fin 8) : 0 ≤ εVL3 j := by fin_cases j <;> simp [εVL3] <;> norm_num

/-! ## The box closes -/

theorem boxV3_close (o : Fin 5) (ho : o.val < 4) :
    ∑ j, PVH o j * ε0VL j + 1001 / 1000 * GBV3 o + 13 / 10 ^ 5 * GVH o 0 + 8 / 10 ^ 4 * GVH o 1 +
      ∑ j, GVH o j * εVL3 j ≤ bV3 o := by
  fin_cases o <;> simp_all [PVH, GVH, PVHq, GVHq, ε0VL, εVL3, GBV3, bV3, Fin.sum_univ_eight] <;>
    norm_num

theorem boxU3_close :
    (1001 / 1000 + 13 / 1000) * (454 / 10000) + (∑ j, PVH 4 j * (ε0VL j + 1 / 1000 * vAVa j) +
      13 / 1000 * GC1V + 13 / 10 ^ 5 * GVH 4 0 + 8 / 10 ^ 4 * GVH 4 1 + ∑ j, GVH 4 j * εVL3 j) ≤
      bV3 4 := by
  simp [PVH, GVH, PVHq, GVHq, ε0VL, εVL3, GC1V, vAVa, bV3, Fin.sum_univ_eight]; norm_num

/-! ## Forward invariance of the box -/

section Box

variable {ξV wV : ℕ → Fin 8 → ℝ} {aZ d1Z d2Z : ℕ → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ}
  {aH d1H d2H : ℕ → Fin 2 → ℝ} {t₀ : ℕ}

/-- The horizontal half of the 3D model is LegTube's model of the horizontal channel: its outputs
are bounded by the same lemmas. -/
theorem outH_bound3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (a : Fin 2) (o : Fin 5)
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

/-- The vertical output `o` at `t₀ + N` (the model at `PSC_D_ACC_P = 0.25`). -/
theorem outV_bound3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (o : Fin 5)
    (N : ℕ) (hw : ∀ k < N, ∀ j, |wV (t₀ + k) j| ≤ εVL3 j) {BA B1 B2 : ℝ}
    (hA : |∑ k ∈ range N, aZ (t₀ + k) * rsp VerticalHi.AvR (outV o) VerticalHi.BvR (N - 1 - k)| ≤
      BA)
    (h1 : |∑ k ∈ range N, (fun t => -d1Z t) (t₀ + k) *
      rsp VerticalHi.AvR (outV o) Vertical.e0 (N - 1 - k)| ≤ B1)
    (h2 : |∑ k ∈ range N, (fun t => -d2Z t) (t₀ + k) *
      rsp VerticalHi.AvR (outV o) Vertical.e1 (N - 1 - k)| ≤ B2) :
    |outV o ⬝ᵥ ξV (t₀ + N)| ≤ ∑ j, PVH o j * ε0VL j + BA + B1 + B2 + ∑ j, GVH o j * εVL3 j :=
  out_le VerticalHi.AvR ξV wV aZ (fun t => -d1Z t) (fun t => -d2Z t) VerticalHi.BvR Vertical.e0
    Vertical.e1 t₀ hM.stepV (outV o) N ε0VL (PVH o) (GVH o) εVL3 hM.initV
    (fun j m => peakVH' o j m) (fun j N => gainVH' o j N) εVL3_nonneg hw hA h1 h2

/-- **The throttle `u` at `t₀ + N`**, in the shifted coordinates `ζ = ξ − asp_z • vAccV`. -/
theorem u_bound (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains3)
    (N : ℕ) (hT : ∀ k < N, TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k)) :
    |outV 4 ⬝ᵥ ξV (t₀ + N)| ≤ bV3 4 := by
  set ζ : ℕ → Fin 8 → ℝ := fun t => ξV t - aZ t • VerticalHi.vAccV with hζ
  have hstep : ∀ t, t₀ ≤ t → ζ (t + 1) = VerticalHi.AvR *ᵥ ζ t +
      ((fun t => -(aZ (t + 1) - aZ t)) t • VerticalHi.vAccV + (fun t => -d1Z t) t • Vertical.e0 +
        (fun t => -d2Z t) t • Vertical.e1 + wV t) := fun t ht =>
    zetaV_step ξV wV aZ d1Z d2Z t (hM.stepV t ht)
  have hx : ∀ j, |ζ t₀ j| ≤ ε0VL j + 1 / 1000 * vAVa j := by
    intro j
    have h1 := hM.initV j
    have h2 := hM.initAZ
    have hv := vAccV_abs j
    have hv0 := vAVa_nonneg j
    simp only [hζ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    nlinarith [abs_nonneg (aZ t₀), abs_nonneg (VerticalHi.vAccV j)]
  have e : outV 4 ⬝ᵥ ξV (t₀ + N) = outV 4 ⬝ᵥ ζ (t₀ + N) + aZ (t₀ + N) * (-1 / (Vertical.amax : ℝ)) := by
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
    (fun j => ε0VL j + 1 / 1000 * vAVa j) (PVH 4) (GVH 4) εVL3 hx (fun j m => peakVH' 4 j m)
    (fun j N => gainVH' 4 j N) εVL3_nonneg (fun k hk j => (hT k hk).bwV j)
    (env_const_neg _ (fun t => aZ (t + 1) - aZ t) t₀ N (by norm_num)
      (fun k hk => (hT k hk).bjZ) (hg.gainU N))
    (env_const_neg _ d1Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd1Z) (gVH0 4 N))
    (env_const_neg _ d2Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd2Z) (gVH1 4 N))
  have C := boxU3_close
  have hI := inv_amax_le
  have hI0 : 0 ≤ 1 / (Vertical.amax : ℝ) := by norm_num [Vertical.amax, Vertical.tw, Vertical.grav]
  have h3 : |aZ (t₀ + N) * (-1 / (Vertical.amax : ℝ))| ≤ (1001 / 1000 + 13 / 1000) * (454 / 10000) := by
    rw [abs_mul, neg_div, abs_neg, abs_of_nonneg hI0]
    exact mul_le_mul hA hI hI0 (by norm_num)
  have := abs_add_le (outV 4 ⬝ᵥ ζ (t₀ + N)) (aZ (t₀ + N) * (-1 / (Vertical.amax : ℝ)))
  linarith

/-- The command of axis `a` (LegTube's `c1_bound` on the 3D model). -/
theorem c1_bound3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains) (a : Fin 2)
    (N : ℕ) (hT : ∀ k < N, TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k)) :
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

/-- The command rate of axis `a` (LegTube's `rate_bound` on the 3D model). -/
theorem rate_bound3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains)
    (a : Fin 2) (N : ℕ) (hT : ∀ k < N, TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k)) :
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

/-- **The 3D box holds at every tick up to the horizon** (strong induction). -/
theorem leg_box3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains)
    (hg3 : RefGains3) : ∀ N, t₀ + N ≤ hzn3 → BoxL3 ξV ξH (t₀ + N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    have hT : ∀ k < N, TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H (t₀ + k) := fun k hk =>
      hM.tick (t₀ + k) (by omega) (by omega) (fun k' h1 h2 => by
        obtain ⟨m, rfl⟩ : ∃ m, k' = t₀ + m := ⟨k' - t₀, by omega⟩
        exact ih m (by omega) (by omega))
    refine ⟨fun o => ?_, fun a o => ?_⟩
    · by_cases h4 : o = 4
      · subst h4; exact u_bound hM hg3 N hT
      have ho : o.val < 4 := by
        have := o.isLt
        have h4' : o.val ≠ 4 := fun h => h4 (Fin.ext h)
        omega
      have B := outV_bound3 hM o N (fun k hk j => (hT k hk).bwV j)
        (env_const _ aZ t₀ N (by norm_num) (fun k hk => (hT k hk).baZ) (hg3.gainBV o N))
        (env_const_neg _ d1Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd1Z) (gVH0 o N))
        (env_const_neg _ d2Z t₀ N (by norm_num) (fun k hk => (hT k hk).bd2Z) (gVH1 o N))
      have C := boxV3_close o ho
      linarith
    · by_cases h4 : o = 4
      · subst h4; exact rate_bound3 hM hg a N hT
      by_cases h3 : o = 3
      · subst h3; exact c1_bound3 hM hg a N hT
      have ho : o.val < 3 := by
        have := o.isLt
        have h4' : o.val ≠ 4 := fun h => h4 (Fin.ext h)
        have h3' : o.val ≠ 3 := fun h => h3 (Fin.ext h)
        omega
      have B := outH_bound3 hM a o N (fun k hk j => (hT k hk).bwH a j)
        (env_const _ (fun t => aH t a) t₀ N (by norm_num) (fun k hk => (hT k hk).baH a)
          (hg.gainB o N))
        (env_const_neg _ (fun t => d1H t a) t₀ N (by norm_num) (fun k hk => (hT k hk).bd1H a)
          (gH0 o N))
        (env_const_neg _ (fun t => d2H t a) t₀ N (by norm_num) (fun k hk => (hT k hk).bd2H a)
          (gH1 o N))
      have C := boxH_close o ho
      linarith

theorem leg_ticks3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains)
    (hg3 : RefGains3) :
    ∀ t, t₀ ≤ t → t < hzn3 → TickBounds3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t := fun t h1 h2 =>
  hM.tick t h1 h2 fun k hk1 hk2 => by
    obtain ⟨m, rfl⟩ : ∃ m, k = t₀ + m := ⟨k - t₀, by omega⟩
    exact leg_box3 hM hg hg3 m (by omega)

end Box

/-! ## The completion check and the hold in 3D -/

/-- The disturbance and start part of the vertical position error at `PSC_D_ACC_P = 0.25`. -/
def τz3 : ℝ := ∑ j, PVH 0 j * ε0VL j + ∑ j, GVH 0 j * εVL3 j

/-- The vertical position error `Mc3` ticks after the leg's S-curve has finished. -/
def vC3 : ℝ := 1001 / 1000 * TBVc + 1 / 10 ^ 6 * GBV3 0 +
  (13 / 10 ^ 5 * TV0c + 1 / 10 ^ 8 * GVH 0 0) + (1 / 4 * PV1c + 3 / 10 ^ 6 * GVH 0 1) + τz3

/-- The vertical position error once the reference has stopped for `Mt3` ticks. -/
def vT3 : ℝ := 1001 / 1000 * TBVt + 1 / 10 ^ 6 * GBV3 0 +
  (13 / 10 ^ 5 * TV0t + 3 / 10 ^ 9 * GVH 0 0) + (1 / 4 * PV1t + 3 / 10 ^ 6 * GVH 0 1) + τz3

theorem vC3_le : vC3 ≤ 514 / 10000 := by
  simp [vC3, τz3, TBVc, TV0c, PV1c, GBV3, PVH, GVH, PVHq, GVHq, ε0VL, εVL3, Fin.sum_univ_eight]
  norm_num
theorem vT3_le : vT3 ≤ 1222 / 100000 := by
  simp [vT3, τz3, TBVt, TV0t, PV1t, GBV3, PVH, GVH, PVHq, GVHq, ε0VL, εVL3, Fin.sum_univ_eight]
  norm_num

section Tube

variable {ξV wV : ℕ → Fin 8 → ℝ} {aZ d1Z d2Z : ℕ → ℝ} {ξH wH : ℕ → Fin 2 → Fin 9 → ℝ}
  {aH d1H d2H : ℕ → Fin 2 → ℝ} {t₀ : ℕ}

/-- **The horizontal error at the completion check** (LegTube's `tail_e_c` on the 3D model:
the tails past `Mc ≤ Mc3`). -/
theorem tail_e_c3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains)
    (hg3 : RefGains3) (L : ℕ) (a : Fin 2) (N : ℕ)
    (hz : ∀ t, L ≤ t → t < t₀ + N →
      |aH t a| ≤ 1 / 10 ^ 6 ∧ |d1H t a| ≤ 1 / 10 ^ 8 ∧ |d2H t a| ≤ 3 / 10 ^ 6)
    (hS : ∑ k ∈ range N, |d2H (t₀ + k) a| ≤ 1 / 4)
    (hNL : L + Mc ≤ t₀ + N) (hNz : t₀ + N ≤ hzn3) :
    |ξH (t₀ + N) a 0| ≤ hC := by
  have hT' := leg_ticks3 hM hg hg3
  have B := outH_bound3 hM a 0 N (fun k hk j => (hT' (t₀ + k) (by omega) (by omega)).bwH a j)
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

/-- **The vertical error at the completion check**: `Mc3` ticks after the vertical reference has come
to rest, at most `vC3 ≤ 0.0514`. -/
theorem tail_z_c3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains)
    (hg3 : RefGains3) (L : ℕ) (N : ℕ)
    (hz : ∀ t, L ≤ t → t < t₀ + N →
      |aZ t| ≤ 1 / 10 ^ 6 ∧ |d1Z t| ≤ 1 / 10 ^ 8 ∧ |d2Z t| ≤ 3 / 10 ^ 6)
    (hS : ∑ k ∈ range N, |d2Z (t₀ + k)| ≤ 1 / 4)
    (hNL : L + Mc3 ≤ t₀ + N) (hNz : t₀ + N ≤ hzn3) :
    |ξV (t₀ + N) 0| ≤ vC3 := by
  have hT' := leg_ticks3 hM hg hg3
  have B := outV_bound3 hM 0 N (fun k hk j => (hT' (t₀ + k) (by omega) (by omega)).bwV j)
    (env_tail2 _ aZ t₀ N L Mc3 (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).baZ)
      (fun t ht ht' => (hz t ht ht').1) hNL hg3.tailBVc (hg3.gainBV 0 N))
    (env_tail2_neg _ d1Z t₀ N L Mc3 (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).bd1Z)
      (fun t ht ht' => (hz t ht ht').2.1) hNL hg3.tail0Vc (gVH0 0 N))
    (env_tail_l1_neg _ d2Z t₀ N L Mc3 (by norm_num [PV1c]) (by norm_num) hS
      (fun t ht ht' => (hz t ht ht').2.2) hNL hg3.peak1Vc (gVH1 0 N))
  rw [outV0_dot] at B
  have e : vC3 = ∑ j, PVH 0 j * ε0VL j + (1001 / 1000 * TBVc + 1 / 10 ^ 6 * GBV3 0) +
      (13 / 10 ^ 5 * TV0c + 1 / 10 ^ 8 * GVH 0 0) + (1 / 4 * PV1c + 3 / 10 ^ 6 * GVH 0 1) +
      ∑ j, GVH 0 j * εVL3 j := by
    simp only [vC3, τz3]; ring
  rw [e]; exact B

/-- **The horizontal error after the reference stops** (the tails past `Mt ≤ Mt3`). -/
theorem tail_e3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains)
    (hg3 : RefGains3) (L : ℕ) (a : Fin 2)
    (hz : ∀ t, L ≤ t → |aH t a| ≤ 1 / 10 ^ 6 ∧ |d1H t a| ≤ 3 / 10 ^ 9 ∧ |d2H t a| ≤ 3 / 10 ^ 6)
    (N : ℕ) (hS : ∑ k ∈ range N, |d2H (t₀ + k) a| ≤ 1 / 4)
    (hNL : L + Mt ≤ t₀ + N) (hNz : t₀ + N ≤ hzn3) :
    |ξH (t₀ + N) a 0| ≤ hT := by
  have hT' := leg_ticks3 hM hg hg3
  have B := outH_bound3 hM a 0 N (fun k hk j => (hT' (t₀ + k) (by omega) (by omega)).bwH a j)
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

/-- **The vertical error after the reference stops**: at most `vT3 ≤ 0.01222`. -/
theorem tail_z3 (hM : LegModel3 ξV wV aZ d1Z d2Z ξH wH aH d1H d2H t₀) (hg : RefGains)
    (hg3 : RefGains3) (L : ℕ)
    (hz : ∀ t, L ≤ t → |aZ t| ≤ 1 / 10 ^ 6 ∧ |d1Z t| ≤ 3 / 10 ^ 9 ∧ |d2Z t| ≤ 3 / 10 ^ 6) (N : ℕ)
    (hS : ∑ k ∈ range N, |d2Z (t₀ + k)| ≤ 1 / 4)
    (hNL : L + Mt3 ≤ t₀ + N) (hNz : t₀ + N ≤ hzn3) :
    |ξV (t₀ + N) 0| ≤ vT3 := by
  have hT' := leg_ticks3 hM hg hg3
  have B := outV_bound3 hM 0 N (fun k hk j => (hT' (t₀ + k) (by omega) (by omega)).bwV j)
    (env_tail2 _ aZ t₀ N L Mt3 (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).baZ) (fun t ht _ => (hz t ht).1) hNL
      hg3.tailBVt (hg3.gainBV 0 N))
    (env_tail2_neg _ d1Z t₀ N L Mt3 (by norm_num) (by norm_num)
      (fun k hk => (hT' (t₀ + k) (by omega) (by omega)).bd1Z) (fun t ht _ => (hz t ht).2.1) hNL
      hg3.tail0Vt (gVH0 0 N))
    (env_tail_l1_neg _ d2Z t₀ N L Mt3 (by norm_num [PV1t]) (by norm_num) hS
      (fun t ht _ => (hz t ht).2.2) hNL hg3.peak1Vt (gVH1 0 N))
  rw [outV0_dot] at B
  have e : vT3 = ∑ j, PVH 0 j * ε0VL j + (1001 / 1000 * TBVt + 1 / 10 ^ 6 * GBV3 0) +
      (13 / 10 ^ 5 * TV0t + 3 / 10 ^ 9 * GVH 0 0) + (1 / 4 * PV1t + 3 / 10 ^ 6 * GVH 0 1) +
      ∑ j, GVH 0 j * εVL3 j := by
    simp only [vT3, τz3]; ring
  rw [e]; exact B

end Tube

/-- **The 3D error at the completion check is below 9.21 cm.** -/
theorem complete3_3d {e₀ e₁ ez : ℝ} (h₀ : |e₀| ≤ hC) (h₁ : |e₁| ≤ hC) (hz : |ez| ≤ vC3) :
    e₀ ^ 2 + e₁ ^ 2 + ez ^ 2 ≤ (921 / 10000) ^ 2 := by
  have a0 : e₀ ^ 2 ≤ (54 / 1000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₀.trans hC_le) 2
  have a1 : e₁ ^ 2 ≤ (54 / 1000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₁.trans hC_le) 2
  have az : ez ^ 2 ≤ (514 / 10000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hz.trans vC3_le) 2
  nlinarith

/-- **The 3D error in the hold window is below 1.84 cm.** -/
theorem hold3_3d {e₀ e₁ ez : ℝ} (h₀ : |e₀| ≤ hT) (h₁ : |e₁| ≤ hT) (hz : |ez| ≤ vT3) :
    e₀ ^ 2 + e₁ ^ 2 + ez ^ 2 ≤ (184 / 10000) ^ 2 := by
  have a0 : e₀ ^ 2 ≤ (971 / 100000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₀.trans hT_le) 2
  have a1 : e₁ ^ 2 ≤ (971 / 100000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h₁.trans hT_le) 2
  have az : ez ^ 2 ≤ (1222 / 100000) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hz.trans vT3_le) 2
  nlinarith

end

end Contracts.Track.Reach.Leg3
