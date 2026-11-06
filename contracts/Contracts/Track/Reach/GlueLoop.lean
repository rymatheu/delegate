import Contracts.Track.Reach.GlueTube
import Contracts.Track.Reach.GlueFalse
import Contracts.Track.Reach.GlueMix
import Contracts.Track.Reach.GlueNE

/-!
# The corrected hover glue on `Mloop`, and the hover theorem with its constants

REACH.md §"Glue" (2)–(4). `HoverGlue` is false as stated (`not_hoverGlue`). The corrected glue,
`HoverGlueT S … wp t₀`, asks of every behavior of `Mloop` in a scenario `S` (the hover world: the
single waypoint completed and the target held, or the vehicle resting at the target) that starts the
hold at tick `t₀` inside the region (`HoverStart`: position offset `|dᵢ| ≤ 2.1` cm, the other
readouts within `ε0`), the two facts `HoverTubeGlue`:

* `target`: the position controller's target stays at `wp` from `t₀` on;
* `dist`: while the box `BoxT` has held at every tick since `t₀`, the readouts `ξV`, `ξH` of `Induction/Run.lean` follow `A_v`, `A_h`
  up to `εVh`, `εHh` per coordinate (the per-tick code facts of the C-series joins, the plant rows,
  the attitude deviation from the lag law).

From it, `hover_practically_exponentially_stable_tube`:
`‖p_t − wp‖ ≤ 3.47 · 0.9997^(t − t₀) · ‖p_{t₀} − wp‖ + 0.0039` for all `t ≥ t₀`, and the box
(`|ez|, |e| ≤ 0.1`, `|ev| ≤ 0.5`, commands `|c₁| ≤ 0.5`, `|c₁ − c₂| ≤ 0.05`, …) at every tick
(`hover_tube_axes`). From any start in the weighted-ℓ1 region (`HoverStartG`, `HoverGlueG`):
`hover_practically_exponentially_stable_gen`,
`‖p_t − wp‖ ≤ 0.9997^(t − t₀) · startSize + 0.0039`; `hover_hold` is it for the hold of the
single-waypoint world (`HoldScenario`).
-/

namespace Contracts.Track.Reach.Glue

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction

noncomputable section

/-! ## (2) The readouts with the target held -/

/-- With the target at `wp`, the vertical readout's position coordinate is `pos − wp` (down). -/
theorem ξV_pos (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) (wp : P3) (h : posTarget (x t) = wp) :
    ξV w₀ x t 0 = (pos (x t) - wp) 2 := by
  rw [ξV_zero, h]; simp [pos, ph]

/-- With the target at `wp`, the horizontal readouts' position coordinates are `pos − wp`. -/
theorem ξH_pos (w₀ : Vehicle.World) (x : ℕ → X) (t : ℕ) (wp : P3) (h : posTarget (x t) = wp)
    (a : Fin 2) : ξH w₀ x t a 0 = (pos (x t) - wp) a.castSucc := by
  rw [ξH_zero, h]
  fin_cases a <;> simp [pos, ph, pIx]

/-! ## The corrected glue -/

/-- **The hover glue at one behavior** (from tick `t₀`): the target held at `wp`, and, while the box
has held since `t₀`, the per-tick disturbances of the readouts within `εVh`, `εHh`. -/
structure HoverTubeGlue (w₀ : Vehicle.World) (wp : P3) (t₀ : ℕ) (x : ℕ → X) : Prop where
  target : ∀ t, t₀ ≤ t → posTarget (x t) = wp
  dist : ∀ t, t₀ ≤ t → (∀ k, t₀ ≤ k → k ≤ t → BoxT (ξV w₀ x) (ξH w₀ x) k) →
    (∀ j, |(ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t) j| ≤ εVh j) ∧
      ∀ a j, |(ξH w₀ x (t + 1) a - Horizontal.AhR *ᵥ ξH w₀ x t a) j| ≤ εHh j

/-- **The region at the start of the hold**: offset `≤ 2.1` cm per axis, the other readouts within
`ε0Vh`, `ε0Hh` (at rest, the controller relaxed, the trims). -/
def HoverStart (w₀ : Vehicle.World) (wp : P3) (t₀ : ℕ) (x : ℕ → X) : Prop :=
  (∀ i, |(pos (x t₀) - wp) i| ≤ dMax) ∧ (∀ j, j ≠ 0 → |ξV w₀ x t₀ j| ≤ ε0Vh j) ∧
    ∀ a j, j ≠ 0 → |ξH w₀ x t₀ a j| ≤ ε0Hh j

/-- **The corrected `HoverGlue`** (open): every behavior of the loop in the scenario `S` that starts
the hold at `t₀` in the region satisfies `HoverTubeGlue`. -/
def HoverGlueT (S : Set (ℕ → X)) (sense32 : ℝ → Float32) (senseP : ℝ → Float)
    (w₀ : Vehicle.World) (wp : P3) (t₀ : ℕ) : Prop :=
  ∀ x ∈ Mloop sense32 senseP w₀ ∩ S, HoverStart w₀ wp t₀ x → HoverTubeGlue w₀ wp t₀ x

/-! ## From the glue to the model -/

/-- The glue and the start give `HoverModel` of the readouts, with the offset `pos (x t₀) − wp`. -/
theorem hoverModel_of_glue {w₀ : Vehicle.World} {wp : P3} {t₀ : ℕ} {x : ℕ → X}
    (hS : HoverStart w₀ wp t₀ x) (hG : HoverTubeGlue w₀ wp t₀ x) :
    HoverModel (ξV w₀ x) (fun t => ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t) (ξH w₀ x)
      (fun t a => ξH w₀ x (t + 1) a - Horizontal.AhR *ᵥ ξH w₀ x t a) t₀
      (fun i => (pos (x t₀) - wp) i) where
  stepV t _ := by abel
  stepH t _ a := by abel
  initV j := by
    by_cases hj : j = 0
    · subst hj
      rw [ξV_pos w₀ x t₀ wp (hG.target t₀ le_rfl)]
      simp [ε0Vh]
    · rw [Pi.single_eq_of_ne hj, sub_zero]; exact hS.2.1 j hj
  initH a j := by
    by_cases hj : j = 0
    · subst hj
      rw [ξH_pos w₀ x t₀ wp (hG.target t₀ le_rfl) a]
      simp [ε0Hh]
    · rw [Pi.single_eq_of_ne hj, sub_zero]; exact hS.2.2 a j hj
  dist t ht hB := hG.dist t ht hB

/-! ## Three axes into one distance -/

/-- `‖e‖ ≤ k ‖d‖ + √(β₀² + β₁² + β₂²)` from `|eᵢ| ≤ k |dᵢ| + βᵢ`. -/
theorem norm_le_axes {e d : EuclideanSpace ℝ (Fin 3)} {k : ℝ} (β : Fin 3 → ℝ) (hk : 0 ≤ k)
    (hβ : ∀ i, 0 ≤ β i) (h : ∀ i, |e i| ≤ k * |d i| + β i) :
    ‖e‖ ≤ k * ‖d‖ + Real.sqrt (β 0 ^ 2 + β 1 ^ 2 + β 2 ^ 2) := by
  set a : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun i => k * |d i|)
  set b : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 β
  have h1 : ‖e‖ ≤ ‖a + b‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    refine Finset.sum_le_sum fun i _ => ?_
    have hi := h i
    have h0 : 0 ≤ k * |d i| + β i := by have := hβ i; positivity
    simp only [Real.norm_eq_abs, sq_abs, a, b, PiLp.add_apply]
    nlinarith [abs_nonneg (e i), sq_abs (e i)]
  have h2 : ‖a‖ = k * ‖d‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, a, abs_mul, abs_abs, abs_of_nonneg hk, mul_pow,
      ← Finset.mul_sum]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hk]
  have h3 : ‖b‖ = Real.sqrt (β 0 ^ 2 + β 1 ^ 2 + β 2 ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [b, Fin.sum_univ_three, sq_abs]
  calc ‖e‖ ≤ ‖a + b‖ := h1
    _ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    _ = _ := by rw [h2, h3]

/-! ## (3)–(4) The hover theorem on the loop -/

/-- **Per axis** (the box and the three position errors): for `t = t₀ + N`, the box holds, the
horizontal errors are within `3.47 λ_hᴺ |dₐ| + 2.51` mm, the vertical within
`1.452 λ_vᴺ |d_D| + 1.08` mm (`λ_h = 0.9997`, `λ_v = 0.998`). -/
theorem hover_tube_axes {w₀ : Vehicle.World} {wp : P3} {t₀ : ℕ} {x : ℕ → X}
    (hS : HoverStart w₀ wp t₀ x) (hG : HoverTubeGlue w₀ wp t₀ x) (N : ℕ) :
    BoxT (ξV w₀ x) (ξH w₀ x) (t₀ + N) ∧
      (∀ a : Fin 2, |(pos (x (t₀ + N)) - wp) a.castSucc| ≤
        347 / 100 * (Horizontal.lamh : ℝ) ^ N * |(pos (x t₀) - wp) a.castSucc| + 251 / 100000) ∧
      |(pos (x (t₀ + N)) - wp) 2| ≤
        1452 / 1000 * (Vertical.lamv : ℝ) ^ N * |(pos (x t₀) - wp) 2| + 108 / 100000 := by
  obtain ⟨hB, hV, hH⟩ := hover_box (hoverModel_of_glue hS hG) hS.1 N
  refine ⟨hB, fun a => ?_, ?_⟩
  · have h := hH a 0
    have e0 : outH 0 ⬝ᵥ ξH w₀ x (t₀ + N) a = (pos (x (t₀ + N)) - wp) a.castSucc := by
      rw [← ξH_pos w₀ x (t₀ + N) wp (hG.target _ (by omega)) a]
      simp [outH, dotProduct, Pi.single_apply]
    rw [e0] at h
    have hd := respH_decay N
    have h2 := abs_sub_abs_le_abs_sub ((pos (x (t₀ + N)) - wp) a.castSucc)
      ((pos (x t₀) - wp) a.castSucc * resp Horizontal.AhR (outH 0) N 0)
    have h3 : |(pos (x t₀) - wp) a.castSucc * resp Horizontal.AhR (outH 0) N 0| ≤
        347 / 100 * (Horizontal.lamh : ℝ) ^ N * |(pos (x t₀) - wp) a.castSucc| := by
      rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
    have := tubeH0
    linarith
  · have h := hV 0
    have e0 : outV 0 ⬝ᵥ ξV w₀ x (t₀ + N) = (pos (x (t₀ + N)) - wp) 2 := by
      rw [← ξV_pos w₀ x (t₀ + N) wp (hG.target _ (by omega))]
      simp [outV, dotProduct, Pi.single_apply]
    rw [e0] at h
    have hd := respV_decay N
    have h2 := abs_sub_abs_le_abs_sub ((pos (x (t₀ + N)) - wp) 2)
      ((pos (x t₀) - wp) 2 * resp Vertical.AvR (outV 0) N 0)
    have h3 : |(pos (x t₀) - wp) 2 * resp Vertical.AvR (outV 0) N 0| ≤
        1452 / 1000 * (Vertical.lamv : ℝ) ^ N * |(pos (x t₀) - wp) 2| := by
      rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
    have := tubeV0
    linarith

/-- **Hover is practically exponentially stable on the loop, from the corrected glue**: in the
scenario `S`, from a hold started at `t₀` in the region (offset `≤ 2.1` cm per axis),
`‖p_t − wp‖ ≤ 3.47 · 0.9997^(t − t₀) · ‖p_{t₀} − wp‖ + 0.0039` for every `t ≥ t₀`. -/
theorem hover_practically_exponentially_stable_tube (S : Set (ℕ → X)) (sense32 : ℝ → Float32)
    (senseP : ℝ → Float) (w₀ : Vehicle.World) (wp : P3) (t₀ : ℕ)
    (hG : HoverGlueT S sense32 senseP w₀ wp t₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨S ∩ {x | HoverStart w₀ wp t₀ x},
       {x | ∀ t, t₀ ≤ t → dist (pos (x t)) wp ≤
          347 / 100 * (9997 / 10000 : ℝ) ^ (t - t₀) * dist (pos (x t₀)) wp + 39 / 10000}⟩ := by
  rintro x ⟨hx, hS, hst⟩
  have hg := hG x ⟨hx, hS⟩ hst
  intro t ht
  obtain ⟨N, rfl⟩ : ∃ N, t = t₀ + N := ⟨t - t₀, by omega⟩
  obtain ⟨-, hH, hV⟩ := hover_tube_axes hst hg N
  rw [Nat.add_sub_cancel_left, dist_eq_norm, dist_eq_norm]
  have hl : (Horizontal.lamh : ℝ) = 9997 / 10000 := by norm_num [Horizontal.lamh]
  have hlv : (Vertical.lamv : ℝ) ^ N ≤ (9997 / 10000 : ℝ) ^ N :=
    pow_le_pow_left₀ (by norm_num [Vertical.lamv]) (by norm_num [Vertical.lamv]) N
  have hk : (0 : ℝ) ≤ 347 / 100 * (9997 / 10000 : ℝ) ^ N := by positivity
  have key := norm_le_axes (e := pos (x (t₀ + N)) - wp) (d := pos (x t₀) - wp)
    ![251 / 100000, 251 / 100000, 108 / 100000] hk
    (fun i => by fin_cases i <;> simp <;> norm_num)
    (fun i => by
      fin_cases i
      · have := hH 0; rw [hl] at this; simpa using this
      · have := hH 1; rw [hl] at this; simpa using this
      · have h0 : (0 : ℝ) ≤ |(pos (x t₀) - wp) 2| := abs_nonneg _
        have : 1452 / 1000 * (Vertical.lamv : ℝ) ^ N * |(pos (x t₀) - wp) 2| ≤
            347 / 100 * (9997 / 10000 : ℝ) ^ N * |(pos (x t₀) - wp) 2| := by
          apply mul_le_mul_of_nonneg_right _ h0
          have : (0 : ℝ) ≤ (Vertical.lamv : ℝ) ^ N := pow_nonneg (by norm_num [Vertical.lamv]) N
          nlinarith
        simp only [Fin.reduceFinMk, Matrix.cons_val]
        linarith)
  refine key.trans ?_
  have hs : Real.sqrt ((251 / 100000 : ℝ) ^ 2 + (251 / 100000) ^ 2 + (108 / 100000) ^ 2) ≤
      39 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at *
  linarith

/-! ## A general start (the hold after a flight): practical exponential stability in the
`P`-norms -/

/-- **The region of a general start** at `t₀`: the readouts in `RegionG` (peak-weighted ℓ1 size plus
tube inside the box, every output). -/
def HoverStartG (w₀ : Vehicle.World) (t₀ : ℕ) (x : ℕ → X) : Prop := RegionG (ξV w₀ x t₀) (ξH w₀ x t₀)

/-- **The corrected `HoverGlue`, general start** (open). -/
def HoverGlueG (S : Set (ℕ → X)) (sense32 : ℝ → Float32) (senseP : ℝ → Float)
    (w₀ : Vehicle.World) (wp : P3) (t₀ : ℕ) : Prop :=
  ∀ x ∈ Mloop sense32 senseP w₀ ∩ S, HoverStartG w₀ t₀ x → HoverTubeGlue w₀ wp t₀ x

/-- The `P`-size of the start: `√(γ_h V_h(ξ_N) + γ_h V_h(ξ_E) + γ_v V_v(ξ_D))`. -/
def startSize (w₀ : Vehicle.World) (x : ℕ → X) (t₀ : ℕ) : ℝ :=
  Real.sqrt ((Horizontal.gamh : ℝ) * Horizontal.V (ξH w₀ x t₀ 0) +
    (Horizontal.gamh : ℝ) * Horizontal.V (ξH w₀ x t₀ 1) + (Vertical.gamv : ℝ) * Vertical.V (ξV w₀ x t₀))

/-- **Hover is practically exponentially stable on the loop from any start in the region**, from
the corrected glue: `‖p_t − wp‖ ≤ 0.9997^(t − t₀) · startSize + 0.0039` and the box at every tick
`t ≥ t₀`. -/
theorem hover_practically_exponentially_stable_gen (S : Set (ℕ → X)) (sense32 : ℝ → Float32)
    (senseP : ℝ → Float) (w₀ : Vehicle.World) (wp : P3) (t₀ : ℕ)
    (hG : HoverGlueG S sense32 senseP w₀ wp t₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨S ∩ {x | HoverStartG w₀ t₀ x},
       {x | ∀ t, t₀ ≤ t → BoxT (ξV w₀ x) (ξH w₀ x) t ∧ dist (pos (x t)) wp ≤
          (9997 / 10000 : ℝ) ^ (t - t₀) * startSize w₀ x t₀ + 39 / 10000}⟩ := by
  rintro x ⟨hx, hS, hst⟩
  have hg := hG x ⟨hx, hS⟩ hst
  intro t ht
  obtain ⟨N, rfl⟩ : ∃ N, t = t₀ + N := ⟨t - t₀, by omega⟩
  have hM : HoverModelG (ξV w₀ x) (fun t => ξV w₀ x (t + 1) - Vertical.AvR *ᵥ ξV w₀ x t) (ξH w₀ x)
      (fun t a => ξH w₀ x (t + 1) a - Horizontal.AhR *ᵥ ξH w₀ x t a) t₀ :=
    ⟨fun t _ => by abel, fun t _ a => by abel, fun t ht hB => hg.dist t ht hB⟩
  obtain ⟨hB, hV, hH⟩ := hover_box_gen hM hst N
  refine ⟨hB, ?_⟩
  rw [Nat.add_sub_cancel_left, dist_eq_norm]
  have hl : (Horizontal.lamh : ℝ) = 9997 / 10000 := by norm_num [Horizontal.lamh]
  have hlv : (Vertical.lamv : ℝ) ^ N ≤ (9997 / 10000 : ℝ) ^ N :=
    pow_le_pow_left₀ (by norm_num [Vertical.lamv]) (by norm_num [Vertical.lamv]) N
  have hgh : (0 : ℝ) ≤ (Horizontal.gamh : ℝ) := by norm_num [Horizontal.gamh]
  have hgv : (0 : ℝ) ≤ (Vertical.gamv : ℝ) := by norm_num [Vertical.gamv]
  -- the axes
  have axH : ∀ a : Fin 2, |(pos (x (t₀ + N)) - wp) a.castSucc| ≤
      (9997 / 10000 : ℝ) ^ N * Real.sqrt ((Horizontal.gamh : ℝ) * Horizontal.V (ξH w₀ x t₀ a)) +
        251 / 100000 := by
    intro a
    have h := hH a 0
    have e0 : outH 0 ⬝ᵥ ξH w₀ x (t₀ + N) a = (pos (x (t₀ + N)) - wp) a.castSucc := by
      rw [← ξH_pos w₀ x (t₀ + N) wp (hg.target _ (by omega)) a]
      simp [outH, dotProduct, Pi.single_apply]
    have e1 : outH 0 ⬝ᵥ ((Horizontal.AhR ^ N) *ᵥ ξH w₀ x t₀ a) =
        ((Horizontal.AhR ^ N) *ᵥ ξH w₀ x t₀ a) 0 := by
      simp [outH, dotProduct, Pi.single_apply]
    rw [e0, e1] at h
    have hd := freeH_decay N (ξH w₀ x t₀ a)
    rw [hl] at hd
    have := tubeH0g
    have h2 := abs_sub_abs_le_abs_sub ((pos (x (t₀ + N)) - wp) a.castSucc)
      (((Horizontal.AhR ^ N) *ᵥ ξH w₀ x t₀ a) 0)
    nlinarith
  have axV : |(pos (x (t₀ + N)) - wp) 2| ≤
      (9997 / 10000 : ℝ) ^ N * Real.sqrt ((Vertical.gamv : ℝ) * Vertical.V (ξV w₀ x t₀)) +
        93 / 100000 := by
    have h := hV 0
    have e0 : outV 0 ⬝ᵥ ξV w₀ x (t₀ + N) = (pos (x (t₀ + N)) - wp) 2 := by
      rw [← ξV_pos w₀ x (t₀ + N) wp (hg.target _ (by omega))]
      simp [outV, dotProduct, Pi.single_apply]
    have e1 : outV 0 ⬝ᵥ ((Vertical.AvR ^ N) *ᵥ ξV w₀ x t₀) = ((Vertical.AvR ^ N) *ᵥ ξV w₀ x t₀) 0 := by
      simp [outV, dotProduct, Pi.single_apply]
    rw [e0, e1] at h
    have hd := freeV_decay N (ξV w₀ x t₀)
    have hs := Real.sqrt_nonneg ((Vertical.gamv : ℝ) * Vertical.V (ξV w₀ x t₀))
    have hd' : Real.sqrt ((Vertical.gamv : ℝ) * Vertical.V (ξV w₀ x t₀)) * (Vertical.lamv : ℝ) ^ N ≤
        (9997 / 10000 : ℝ) ^ N * Real.sqrt ((Vertical.gamv : ℝ) * Vertical.V (ξV w₀ x t₀)) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_right hlv hs
    have := tubeV0g
    have h2 := abs_sub_abs_le_abs_sub ((pos (x (t₀ + N)) - wp) 2)
      (((Vertical.AvR ^ N) *ᵥ ξV w₀ x t₀) 0)
    linarith
  -- three axes
  set dN := Real.sqrt ((Horizontal.gamh : ℝ) * Horizontal.V (ξH w₀ x t₀ 0))
  set dE := Real.sqrt ((Horizontal.gamh : ℝ) * Horizontal.V (ξH w₀ x t₀ 1))
  set dD := Real.sqrt ((Vertical.gamv : ℝ) * Vertical.V (ξV w₀ x t₀))
  have hk : (0 : ℝ) ≤ (9997 / 10000 : ℝ) ^ N := by positivity
  have key := norm_le_axes (e := pos (x (t₀ + N)) - wp) (d := !₂[dN, dE, dD])
    ![251 / 100000, 251 / 100000, 93 / 100000] hk
    (fun i => by fin_cases i <;> simp <;> norm_num)
    (fun i => by
      fin_cases i
      · have := axH 0
        simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
        simpa [abs_of_nonneg (Real.sqrt_nonneg _), dN] using this
      · have := axH 1
        simpa [abs_of_nonneg (Real.sqrt_nonneg _), dE] using this
      · simpa [abs_of_nonneg (Real.sqrt_nonneg _), dD] using axV)
  have hn : ‖(!₂[dN, dE, dD] : EuclideanSpace ℝ (Fin 3))‖ = startSize w₀ x t₀ := by
    rw [EuclideanSpace.norm_eq, startSize]
    congr 1
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    simp [dN, dE, dD, Real.sq_sqrt (mul_nonneg hgh (Horizontal.V_nonneg _)),
      Real.sq_sqrt (mul_nonneg hgv (Vertical.V_nonneg _))]
  rw [hn] at key
  refine key.trans ?_
  have hs : Real.sqrt ((251 / 100000 : ℝ) ^ 2 + (251 / 100000) ^ 2 + (93 / 100000) ^ 2) ≤
      39 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at *
  linarith

/-! ## The hold scenario of the single-waypoint world -/

/-- **The hold scenario** (REACH.md §4, §"Glue"): the single-waypoint world to `w'`; at tick `t₀`
the vehicle is in Auto mode past the mission's start, the mission is `COMPLETE` (the loiter at the
stopping point has been set, `loiter_start`), the loiter S-curve has finished, and the position
target is `wp`. The single waypoint does not hold the target at `w'`: before completion the target
runs the S-curve from the stopping point at the start to `w'`, and at completion it moves to the
stopping point of that moment (within `d + |v| + 10⁻⁵` of `w'`, `loiter_dest_bound`). -/
def HoldScenario (w₀ : Vehicle.World) (w' : AC_WPNav_lib.Vector3p.State) (wp : P3) (t₀ : ℕ) :
    Set (ℕ → X) :=
  {x | Reach.ReachWorld w₀ w' ∧ (run w₀ x t₀).in_auto = true ∧
    (run w₀ x t₀).au.waiting_to_start = false ∧ (run w₀ x t₀).au.state = .COMPLETE ∧
    AC_WPNav_lib.SCurve.finished (run w₀ x t₀).wps._scurve_this_leg = true ∧ posTarget (x t₀) = wp}

/-- **Hover in the hold of the single-waypoint world** (`hover_practically_exponentially_stable_gen`
with `S = HoldScenario`): from the corrected glue of the hold, every hold that starts in the region
stays in the box and `‖p_t − wp‖ ≤ 0.9997^(t − t₀) · startSize + 0.0039`. -/
theorem hover_hold (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (w' : AC_WPNav_lib.Vector3p.State) (wp : P3) (t₀ : ℕ)
    (hG : HoverGlueG (HoldScenario w₀ w' wp t₀) sense32 senseP w₀ wp t₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨HoldScenario w₀ w' wp t₀ ∩ {x | HoverStartG w₀ t₀ x},
       {x | ∀ t, t₀ ≤ t → BoxT (ξV w₀ x) (ξH w₀ x) t ∧ dist (pos (x t)) wp ≤
          (9997 / 10000 : ℝ) ^ (t - t₀) * startSize w₀ x t₀ + 39 / 10000}⟩ :=
  hover_practically_exponentially_stable_gen _ sense32 senseP w₀ wp t₀ hG

end

end Contracts.Track.Reach.Glue
