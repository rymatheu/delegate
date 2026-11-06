import Contracts.Track.Induction.Inv

/-!
# M9, certified nominal: the generic theory of the gain certificates

Part of `Nominal.lean` (NOMINAL.md). The adjoint integer recurrence `adjZ` and its rounding
(`round_err`), the forced recurrence (`round_err_fwd`), the kernel loop with checkpoints (`runG`,
`chkAt`, `chain`), the coordinates from the `L D Lᵀ` certificates (`coord_of_ldl`), the entrywise
decay of the powers (`pow_entry_le`), the exact powers by squaring (`sqZ`, `powK_bound`), the
block tails with Neumann certificates (`neumann`, `head_tail`) and the assembly of one output
(`gain_assemble`); the rational tables `GVq`, `PVq`, `GHq`, `PHq` of Inv.lean's `GV`, `PV`, `GH`,
`PH`.
-/

namespace Contracts.Track.Induction.Nominal

open Matrix Finset

noncomputable section

/-! ## Generic theory: adjoint integer trajectories, rounding, block tails -/

section Generic

variable {n : ℕ}

/-- One step of the floor-rounded adjoint recurrence `y ↦ ⌊y Â / D⌋`. -/
def adjZ (Ahat : Matrix (Fin n) (Fin n) ℤ) (D : ℤ) (y : Fin n → ℤ) : Fin n → ℤ :=
  fun j => (∑ i, y i * Ahat i j) / D

/-- The cast of an integer vector. -/
def castZ (y : Fin n → ℤ) : Fin n → ℝ := fun i => (y i : ℝ)

theorem adjZ_round (Ahat : Matrix (Fin n) (Fin n) ℤ) (D : ℤ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : 0 < D) (hA : ∀ i j, (Ahat i j : ℝ) = (D : ℝ) * A i j) (y : Fin n → ℤ) (j : Fin n) :
    0 ≤ (castZ y ᵥ* A) j - castZ (adjZ Ahat D y) j ∧
      (castZ y ᵥ* A) j - castZ (adjZ Ahat D y) j < 1 := by
  set X : ℤ := ∑ i, y i * Ahat i j with hX
  have hXr : (X : ℝ) = (D : ℝ) * (castZ y ᵥ* A) j := by
    simp only [hX, vecMul, dotProduct, castZ, Int.cast_sum, Int.cast_mul, hA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  have h1 : X / D * D ≤ X := Int.ediv_mul_le X hD.ne'
  have h2 : X < (X / D + 1) * D := Int.lt_ediv_add_one_mul_self X hD
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h1r : ((X / D : ℤ) : ℝ) * D ≤ X := by exact_mod_cast h1
  have h2r : (X : ℝ) < (((X / D : ℤ) : ℝ) + 1) * D := by exact_mod_cast h2
  have hq : castZ (adjZ Ahat D y) j = ((X / D : ℤ) : ℝ) := rfl
  rw [hq]
  rw [hXr] at h1r h2r
  constructor
  · nlinarith
  · nlinarith

/-- The real rounding error of the adjoint recurrence, in closed form. -/
theorem err_closed (A : Matrix (Fin n) (Fin n) ℝ) (e δ : ℕ → Fin n → ℝ) (he0 : e 0 = 0)
    (he : ∀ m, e (m + 1) = e m ᵥ* A + δ m) (m : ℕ) :
    e m = ∑ k ∈ range m, δ k ᵥ* (A ^ (m - 1 - k)) := by
  induction m with
  | zero => simp [he0]
  | succ m ih =>
    rw [he, ih, sum_range_succ, Matrix.sum_vecMul]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk := mem_range.mp hk
      rw [vecMul_vecMul, ← pow_succ]
      congr 2
      omega
    · simp

theorem abs_vecMul_le (v : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    |(v ᵥ* X) j| ≤ ∑ i, |v i| * |X i j| := by
  simp only [vecMul, dotProduct]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  simp [abs_mul]

/-- **Rounding**: the stored adjoint trajectory, divided by the scale, is within
`n R / ((1 - λ) S)` of the true response `o Aᵐ`, when `|(Aᵖ)ᵢⱼ| ≤ R λᵖ`. -/
theorem round_err (Ahat : Matrix (Fin n) (Fin n) ℤ) (D : ℤ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : 0 < D) (hA : ∀ i j, (Ahat i j : ℝ) = (D : ℝ) * A i j) (o : Fin n → ℝ) (y0 : Fin n → ℤ)
    {S R lam : ℝ} (hS : 0 < S) (hy0 : ∀ i, (y0 i : ℝ) = S * o i) (hR : 0 ≤ R) (hl0 : 0 ≤ lam)
    (hl1 : lam < 1) (hpow : ∀ p i j, |(A ^ p) i j| ≤ R * lam ^ p) (m : ℕ) (j : Fin n) :
    |(o ᵥ* A ^ m) j - ((adjZ Ahat D)^[m] y0 j : ℝ) / S| ≤ n * R / ((1 - lam) * S) := by
  set Y : ℕ → Fin n → ℤ := fun m => (adjZ Ahat D)^[m] y0 with hYdef
  have hYs : ∀ m, Y (m + 1) = adjZ Ahat D (Y m) := fun m => by
    simp only [hYdef, Function.iterate_succ_apply']
  set e : ℕ → Fin n → ℝ := fun m => S • (o ᵥ* A ^ m) - castZ (Y m) with he_def
  set δ : ℕ → Fin n → ℝ := fun m => castZ (Y m) ᵥ* A - castZ (Y (m + 1)) with hδ_def
  have he0 : e 0 = 0 := by
    ext i; simp [he_def, hYdef, castZ, hy0]
  have he : ∀ m, e (m + 1) = e m ᵥ* A + δ m := by
    intro m
    simp only [he_def, hδ_def, pow_succ, ← vecMul_vecMul, sub_vecMul, smul_vecMul]
    abel
  have hδ : ∀ k i, |δ k i| ≤ 1 := by
    intro k i
    have := adjZ_round Ahat D A hD hA (Y k) i
    rw [← hYs] at this
    simp only [hδ_def, Pi.sub_apply]
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hcl := err_closed A e δ he0 he m
  have hbound : |e m j| ≤ n * R / (1 - lam) := by
    rw [hcl, Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ range m, |(δ k ᵥ* A ^ (m - 1 - k)) j| ≤ n * R * lam ^ (m - 1 - k) := by
      intro k _
      refine (abs_vecMul_le _ _ _).trans ?_
      calc ∑ i, |δ k i| * |(A ^ (m - 1 - k)) i j| ≤ ∑ _i : Fin n, 1 * (R * lam ^ (m - 1 - k)) :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul (hδ k i) (hpow _ _ _) (abs_nonneg _) zero_le_one
        _ = n * R * lam ^ (m - 1 - k) := by simp; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_range_reflect (fun p => lam ^ p) m]
    have hg : (∑ p ∈ range m, lam ^ p) * (1 - lam) ≤ 1 := by
      have := mul_neg_geom_sum lam m
      nlinarith [pow_nonneg hl0 m]
    have h1l : 0 < 1 - lam := by linarith
    rw [le_div_iff₀ h1l, mul_assoc]
    have hnR : 0 ≤ (n : ℝ) * R := by positivity
    nlinarith
  have hS' : S ≠ 0 := hS.ne'
  have key : (o ᵥ* A ^ m) j - ((Y m j : ℤ) : ℝ) / S = e m j / S := by
    simp only [he_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, castZ]
    field_simp
  show |(o ᵥ* A ^ m) j - ((Y m j : ℤ) : ℝ) / S| ≤ _
  rw [key, abs_div, abs_of_pos hS, div_le_div_iff₀ hS (mul_pos (by linarith) hS)]
  have h1l : 0 < 1 - lam := by linarith
  have := hbound
  rw [le_div_iff₀ h1l] at this
  nlinarith [abs_nonneg (e m j)]

/-! ### Entrywise bounds of matrix powers -/

theorem pow_abs_le (X Mb : Matrix (Fin n) (Fin n) ℝ) (hMb : ∀ i j, 0 ≤ Mb i j)
    (hX : ∀ i j, |X i j| ≤ Mb i j) (q : ℕ) :
    (∀ i j, |(X ^ q) i j| ≤ (Mb ^ q) i j) ∧ ∀ i j, 0 ≤ (Mb ^ q) i j := by
  induction q with
  | zero =>
    refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
      · by_cases h : i = j <;> simp [h]
  | succ q ih =>
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul (ih.1 i k) (hX k j) (abs_nonneg _) (ih.2 i k)
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (ih.2 i k) (hMb k j)

theorem vecMul_mono (v w : Fin n → ℝ) (Mb : Matrix (Fin n) (Fin n) ℝ) (hMb : ∀ i j, 0 ≤ Mb i j)
    (h : ∀ i, v i ≤ w i) (j : Fin n) : (v ᵥ* Mb) j ≤ (w ᵥ* Mb) j := by
  simp only [vecMul, dotProduct]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (hMb i j)

/-- The Neumann certificate: `σ Mb + z Mb ≤ z` bounds every partial sum `Σ_{q<Q} σ Mb^(q+1)`. -/
theorem neumann (σ z : Fin n → ℝ) (Mb : Matrix (Fin n) (Fin n) ℝ) (hMb : ∀ i j, 0 ≤ Mb i j)
    (hz0 : ∀ j, 0 ≤ z j) (hz : ∀ j, (σ ᵥ* Mb) j + (z ᵥ* Mb) j ≤ z j) (Q : ℕ) (j : Fin n) :
    ∑ q ∈ range Q, (σ ᵥ* Mb ^ (q + 1)) j ≤ z j := by
  induction Q generalizing j with
  | zero => simpa using hz0 j
  | succ Q ih =>
    rw [sum_range_succ']
    have e : ∑ q ∈ range Q, (σ ᵥ* Mb ^ (q + 1 + 1)) j =
        ((∑ q ∈ range Q, σ ᵥ* Mb ^ (q + 1)) ᵥ* Mb) j := by
      rw [Matrix.sum_vecMul, Finset.sum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [pow_succ _ (q + 1), ← vecMul_vecMul]
    rw [e]
    have ih' : ∀ i, (∑ q ∈ range Q, σ ᵥ* Mb ^ (q + 1)) i ≤ z i := fun i => by
      rw [Finset.sum_apply]; exact ih i
    have := vecMul_mono _ _ Mb hMb ih' j
    simp only [zero_add, pow_one]
    linarith [hz j]

/-- **Head and tail.** For `u m = o Aᵐ` approximated within `ρ` by `Yr m`, with the head sums and
maxima of `Yr` over `m < N`, the sums and maxima of the last block `[N - K, N)`, an entrywise
bound `Mb` of `|A^K|`, and Neumann certificates `z` (sums) and `zP` (peaks), every partial ℓ1 sum
of `u · j` is at most `SH j + N ρ + z j` and every value at most `max (MH j + ρ) (zP j)`. -/
theorem head_tail (A : Matrix (Fin n) (Fin n) ℝ) (o : Fin n → ℝ) (Yr : ℕ → Fin n → ℝ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hY : ∀ m j, |(o ᵥ* A ^ m) j - Yr m j| ≤ ρ) {N K : ℕ} (hK : K ≤ N) (hK0 : 0 < K)
    (SH MH SL ML z zP : Fin n → ℝ) (Mb : Matrix (Fin n) (Fin n) ℝ)
    (hSH : ∀ j, ∑ m ∈ range N, |Yr m j| ≤ SH j) (hMH : ∀ m < N, ∀ j, |Yr m j| ≤ MH j)
    (hSL : ∀ j, ∑ r ∈ range K, |Yr (N - K + r) j| ≤ SL j)
    (hML : ∀ r < K, ∀ j, |Yr (N - K + r) j| ≤ ML j)
    (hMb0 : ∀ i j, 0 ≤ Mb i j) (hMb : ∀ i j, |(A ^ K) i j| ≤ Mb i j)
    (hz0 : ∀ j, 0 ≤ z j) (hz : ∀ j, ((fun i => SL i + K * ρ) ᵥ* Mb) j + (z ᵥ* Mb) j ≤ z j)
    (hzP0 : ∀ j, 0 ≤ zP j) (hzP : ∀ j, ((fun i => ML i + ρ) ᵥ* Mb) j + (zP ᵥ* Mb) j ≤ zP j) :
    (∀ N' j, ∑ m ∈ range N', |(o ᵥ* A ^ m) j| ≤ SH j + N * ρ + z j) ∧
      ∀ m j, |(o ᵥ* A ^ m) j| ≤ max (MH j + ρ) (zP j) := by
  set u : ℕ → Fin n → ℝ := fun m => o ᵥ* A ^ m with hu
  have hu1 : ∀ m j, |u m j| ≤ |Yr m j| + ρ := fun m j => by
    have := hY m j
    have := abs_sub_abs_le_abs_sub (u m j) (Yr m j)
    simp only [hu] at *; linarith
  -- the block shift
  have hshift : ∀ q r, u (N + q * K + r) = u (N - K + r) ᵥ* (A ^ K) ^ (q + 1) := by
    intro q r
    simp only [hu, vecMul_vecMul, ← pow_mul, ← pow_add]
    congr 2
    have : N - K + K = N := Nat.sub_add_cancel hK
    nlinarith [this]
  have hpow := fun q => pow_abs_le (A ^ K) Mb hMb0 hMb q
  -- one tail entry against a row vector `w` that bounds the last block entrywise
  have hblock : ∀ q r j, |u (N + q * K + r) j| ≤ ∑ i, |u (N - K + r) i| * (Mb ^ (q + 1)) i j := by
    intro q r j
    rw [hshift]
    refine (abs_vecMul_le _ _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_left ((hpow (q + 1)).1 i j) (abs_nonneg _)
  -- the head part of the sums
  have hhead : ∀ j, ∑ m ∈ range N, |u m j| ≤ SH j + N * ρ := by
    intro j
    calc ∑ m ∈ range N, |u m j| ≤ ∑ m ∈ range N, (|Yr m j| + ρ) :=
          Finset.sum_le_sum fun m _ => hu1 m j
      _ = ∑ m ∈ range N, |Yr m j| + N * ρ := by rw [Finset.sum_add_distrib]; simp
      _ ≤ SH j + N * ρ := by linarith [hSH j]
  have hσ : ∀ i, ∑ r ∈ range K, |u (N - K + r) i| ≤ SL i + K * ρ := by
    intro i
    calc ∑ r ∈ range K, |u (N - K + r) i| ≤ ∑ r ∈ range K, (|Yr (N - K + r) i| + ρ) :=
          Finset.sum_le_sum fun r _ => hu1 _ i
      _ = ∑ r ∈ range K, |Yr (N - K + r) i| + K * ρ := by rw [Finset.sum_add_distrib]; simp
      _ ≤ SL i + K * ρ := by linarith [hSL i]
  have hsumQ : ∀ Q j, ∑ m ∈ range (N + Q * K), |u m j| ≤ SH j + N * ρ + z j := by
    intro Q j
    have hsplit : ∀ Q, ∑ m ∈ range (N + Q * K), |u m j| =
        ∑ m ∈ range N, |u m j| + ∑ q ∈ range Q, ∑ r ∈ range K, |u (N + q * K + r) j| := by
      intro Q
      induction Q with
      | zero => simp
      | succ Q ih =>
        rw [show N + (Q + 1) * K = (N + Q * K) + K by ring, Finset.sum_range_add, ih,
          sum_range_succ, add_assoc]
    rw [hsplit]
    have htail : ∑ q ∈ range Q, ∑ r ∈ range K, |u (N + q * K + r) j| ≤ z j := by
      calc ∑ q ∈ range Q, ∑ r ∈ range K, |u (N + q * K + r) j|
          ≤ ∑ q ∈ range Q, ∑ r ∈ range K, ∑ i, |u (N - K + r) i| * (Mb ^ (q + 1)) i j :=
            Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun r _ => hblock q r j
        _ = ∑ q ∈ range Q, ∑ i, (∑ r ∈ range K, |u (N - K + r) i|) * (Mb ^ (q + 1)) i j := by
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.sum_comm]
            simp only [Finset.sum_mul]
        _ ≤ ∑ q ∈ range Q, ((fun i => SL i + K * ρ) ᵥ* Mb ^ (q + 1)) j :=
            Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_right (hσ i) ((hpow (q + 1)).2 i j)
        _ ≤ z j := neumann _ z Mb hMb0 hz0 hz Q j
    linarith [hhead j]
  refine ⟨fun N' j => ?_, fun m j => ?_⟩
  · refine le_trans ?_ (hsumQ N' j)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => abs_nonneg _
    intro m hm
    simp only [mem_range] at hm ⊢
    nlinarith
  · by_cases hm : m < N
    · exact le_max_of_le_left (by linarith [hu1 m j, hMH m hm j])
    · refine le_max_of_le_right ?_
      have hm' : m = N + (m - N) / K * K + (m - N) % K := by
        have := Nat.div_add_mod (m - N) K
        rw [mul_comm] at this
        omega
      have hr : (m - N) % K < K := Nat.mod_lt _ hK0
      show |u m j| ≤ zP j
      rw [hm']
      refine (hblock _ _ j).trans ?_
      have h1 : ∑ i, |u (N - K + (m - N) % K) i| * (Mb ^ ((m - N) / K + 1)) i j ≤
          ((fun i => ML i + ρ) ᵥ* Mb ^ ((m - N) / K + 1)) j :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
          ((hu1 _ i).trans (by linarith [hML _ hr i])) ((hpow _).2 i j)
      refine h1.trans ?_
      have h2 := neumann _ zP Mb hMb0 hzP0 hzP ((m - N) / K + 1) j
      refine le_trans ?_ h2
      have hnn : ∀ q ∈ range ((m - N) / K + 1), 0 ≤ ((fun i => ML i + ρ) ᵥ* Mb ^ (q + 1)) j := by
        intro q _
        simp only [vecMul, dotProduct]
        refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ ((hpow (q + 1)).2 i j)
        have := (abs_nonneg _).trans (hML 0 hK0 i)
        linarith
      exact Finset.single_le_sum hnn (mem_range.mpr (Nat.lt_succ_self _))


/-! ### The kernel loop and its checkpoints -/

section Run

variable {T U : Type}

/-- `k` steps of the stored recurrence, accumulating the sums and the maxima of the entries. -/
def runG (st : T → T) (ad mx : U → T → U) : ℕ → T → U → U → T × U × U
  | 0, y, s, m => (y, s, m)
  | k + 1, y, s, m => runG st ad mx k (st y) (ad s y) (mx m y)

/-- `f c, f (c+1), …, f (c+k-1)` all hold. -/
def allOK (f : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, c => f c && allOK f k (c + 1)

theorem allOK_spec (f : ℕ → Bool) : ∀ k c, allOK f k c = true → ∀ i < k, f (c + i) = true
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, c, h, i, hi => by
    simp only [allOK, Bool.and_eq_true] at h
    rcases i with _ | i
    · simpa using h.1
    · have := allOK_spec f k (c + 1) h.2 i (by omega)
      rwa [show c + 1 + i = c + (i + 1) by omega] at this

/-- The check of chunk `c`: `L` steps from checkpoint `c` (with the maxima reset at chunk `cB`)
give checkpoint `c + 1`. -/
def chkAt (st : T → T) (ad mx : U → T → U) (z0 : U) (eqT : T → T → Bool) (eqU : U → U → Bool)
    (L cB : ℕ) (cp : ℕ → T × U × U) (c : ℕ) : Bool :=
  match runG st ad mx L (cp c).1 (cp c).2.1 (if c = cB then z0 else (cp c).2.2) with
  | (a, b, d) => eqT a (cp (c + 1)).1 && eqU b (cp (c + 1)).2.1 && eqU d (cp (c + 1)).2.2

variable {n : ℕ} (F : (Fin n → ℤ) → (Fin n → ℤ)) (vec : T → Fin n → ℤ) (nat : U → Fin n → ℕ)
  (st : T → T) (ad mx : U → T → U)
  (hst : ∀ y, vec (st y) = F (vec y))
  (had : ∀ s y j, nat (ad s y) j = nat s j + (vec y j).natAbs)
  (hmx : ∀ m y j, nat (mx m y) j = max (nat m j) (vec y j).natAbs)

include hst had hmx in
theorem runG_spec : ∀ k y s m, vec (runG st ad mx k y s m).1 = F^[k] (vec y) ∧
    (∀ j, nat (runG st ad mx k y s m).2.1 j = nat s j + ∑ i ∈ range k, (F^[i] (vec y) j).natAbs) ∧
    (∀ j, nat m j ≤ nat (runG st ad mx k y s m).2.2 j) ∧
    ∀ i < k, ∀ j, (F^[i] (vec y) j).natAbs ≤ nat (runG st ad mx k y s m).2.2 j
  | 0, y, s, m => by simp [runG]
  | k + 1, y, s, m => by
    obtain ⟨h1, h2, h3, h4⟩ := runG_spec k (st y) (ad s y) (mx m y)
    simp only [runG]
    refine ⟨?_, fun j => ?_, fun j => ?_, fun i hi j => ?_⟩
    · rw [h1, hst, Function.iterate_succ_apply]
    · rw [h2, had, Finset.sum_range_succ', hst]
      simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
      ring
    · exact (le_max_left _ _).trans ((hmx m y j).symm.le.trans (h3 j))
    · rcases i with _ | i
      · exact (le_max_right _ _).trans ((hmx m y j).symm.le.trans (h3 j))
      · have := h4 i (by omega) j
        rwa [hst, ← Function.iterate_succ_apply] at this

variable (z0 : U) (eqT : T → T → Bool) (eqU : U → U → Bool)
  (hz0 : ∀ j, nat z0 j = 0) (heqT : ∀ a b, eqT a b = true → a = b)
  (heqU : ∀ a b, eqU a b = true → a = b)

include hst had hmx heqT heqU in
/-- **The checkpoint chain.** -/
theorem chain (L cB C : ℕ) (cp : ℕ → T × U × U)
    (hchk : ∀ c < C, chkAt st ad mx z0 eqT eqU L cB cp c = true) :
    ∀ c ≤ C, vec (cp c).1 = F^[L * c] (vec (cp 0).1) ∧
      (∀ j, nat (cp c).2.1 j = nat (cp 0).2.1 j +
        ∑ i ∈ range (L * c), (F^[i] (vec (cp 0).1) j).natAbs) ∧
      (c ≤ cB → ∀ i < L * c, ∀ j, (F^[i] (vec (cp 0).1) j).natAbs ≤ nat (cp c).2.2 j) ∧
      (cB < c → ∀ i, L * cB ≤ i → i < L * c → ∀ j,
        (F^[i] (vec (cp 0).1) j).natAbs ≤ nat (cp c).2.2 j) := by
  intro c hc
  induction c with
  | zero => simp
  | succ c ih =>
    obtain ⟨i1, i2, i3, i4⟩ := ih (by omega)
    have hk := hchk c (by omega)
    simp only [chkAt] at hk
    set r := runG st ad mx L (cp c).1 (cp c).2.1 (if c = cB then z0 else (cp c).2.2) with hr
    obtain ⟨a, b, d⟩ := r
    simp only [Bool.and_eq_true] at hk
    have ea := heqT _ _ hk.1.1
    have eb := heqU _ _ hk.1.2
    have ed := heqU _ _ hk.2
    obtain ⟨r1, r2, r3, r4⟩ := runG_spec F vec nat st ad mx hst had hmx L (cp c).1 (cp c).2.1
      (if c = cB then z0 else (cp c).2.2)
    rw [← hr] at r1 r2 r3 r4
    simp only at r1 r2 r3 r4
    rw [ea] at r1; rw [eb] at r2; rw [ed] at r3 r4
    have hit : ∀ i, F^[i] (vec (cp c).1) = F^[i + L * c] (vec (cp 0).1) := fun i => by
      rw [i1, ← Function.iterate_add_apply]
    refine ⟨?_, fun j => ?_, fun hcB i hi j => ?_, fun hcB i hi1 hi2 j => ?_⟩
    · rw [r1, hit, show L + L * c = L * (c + 1) by ring]
    · rw [r2 j, i2 j, show L * (c + 1) = L * c + L by ring, Finset.sum_range_add, add_assoc]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hit, add_comm i]
    · -- before the reset chunk
      have hne : c ≠ cB := by omega
      by_cases hi' : i < L * c
      · have := i3 (by omega) i hi' j
        refine this.trans ((le_of_eq ?_).trans (r3 j))
        simp [hne]
      · have := r4 (i - L * c) (by rw [show L * (c + 1) = L * c + L by ring] at hi; omega) j
        rwa [hit, Nat.sub_add_cancel (by omega)] at this
    · by_cases hcc : c = cB
      · subst hcc
        have := r4 (i - L * c) (by rw [show L * (c + 1) = L * c + L by ring] at hi2; omega) j
        rwa [hit, Nat.sub_add_cancel (by omega)] at this
      · by_cases hi' : i < L * c
        · have := i4 (by omega) i hi1 hi' j
          refine this.trans ((le_of_eq ?_).trans (r3 j))
          simp [hcc]
        · have := r4 (i - L * c) (by rw [show L * (c + 1) = L * c + L by ring] at hi2; omega) j
          rwa [hit, Nat.sub_add_cancel (by omega)] at this

end Run

/-! ### Coordinates from the Lyapunov certificate, powers, squaring -/

/-- A coordinate of `x` from the `L D Lᵀ` factorization of `P` and an inverse of `L`:
`xᵢ² ≤ (Σₖ Linvₖᵢ² / dₖ) · xᵀ P x`. -/
theorem coord_of_ldl (P L Linv : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hd : ∀ k, 0 < d k)
    (hP : P = L * diagonal d * Lᵀ) (hinv : L * Linv = 1) (x : Fin n → ℝ) (i : Fin n) :
    x i ^ 2 ≤ (∑ k, Linv k i ^ 2 / d k) * Vertical.qf P x := by
  set z := Lᵀ *ᵥ x with hz
  have hq : Vertical.qf P x = ∑ k, d k * z k ^ 2 := by
    rw [Vertical.qf, hP, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
      ← hz]
    simp only [dotProduct, mulVec_diagonal]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hx : x = Linvᵀ *ᵥ z := by
    rw [hz, mulVec_mulVec, ← transpose_mul, hinv, transpose_one, one_mulVec]
  have hxi : x i = ∑ k, (Linv k i / Real.sqrt (d k)) * (Real.sqrt (d k) * z k) := by
    conv_lhs => rw [hx]
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : Real.sqrt (d k) ≠ 0 := (Real.sqrt_pos.2 (hd k)).ne'
    field_simp
  rw [hxi, hq]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_pow, Real.sq_sqrt (hd k).le]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, Real.sq_sqrt (hd k).le]

/-- Entrywise decay of the powers from a quadratic Lyapunov function. -/
theorem pow_entry_le (A : Matrix (Fin n) (Fin n) ℝ) (V : (Fin n → ℝ) → ℝ) {lam C Pm R : ℝ}
    (hVA : ∀ x, V (A *ᵥ x) ≤ lam ^ 2 * V x) (hC : ∀ x i, x i ^ 2 ≤ C * V x)
    (hC0 : 0 ≤ C) (hPm : ∀ j, V (Pi.single j 1) ≤ Pm) (hR : 0 ≤ R) (hRC : C * Pm ≤ R ^ 2)
    (hl : 0 ≤ lam) (p : ℕ) (i j : Fin n) : |(A ^ p) i j| ≤ R * lam ^ p := by
  have hVp : ∀ p, V (A ^ p *ᵥ Pi.single j 1) ≤ (lam ^ p) ^ 2 * V (Pi.single j 1) := by
    intro p
    induction p with
    | zero => rw [pow_zero, one_mulVec, pow_zero, one_pow, one_mul]
    | succ p ih =>
      rw [pow_succ', ← mulVec_mulVec]
      refine (hVA _).trans ?_
      have := mul_le_mul_of_nonneg_left ih (sq_nonneg lam)
      calc lam ^ 2 * V (A ^ p *ᵥ Pi.single j 1) ≤ lam ^ 2 * ((lam ^ p) ^ 2 * V (Pi.single j 1)) := this
        _ = (lam ^ (p + 1)) ^ 2 * V (Pi.single j 1) := by ring
  have he : (A ^ p) i j = (A ^ p *ᵥ Pi.single j 1) i := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [he]
  have h1 := hC (A ^ p *ᵥ Pi.single j 1) i
  have h2 : C * V (A ^ p *ᵥ Pi.single j 1) ≤ (R * lam ^ p) ^ 2 := by
    calc C * V (A ^ p *ᵥ Pi.single j 1) ≤ C * ((lam ^ p) ^ 2 * Pm) :=
          mul_le_mul_of_nonneg_left ((hVp p).trans
            (mul_le_mul_of_nonneg_left (hPm j) (sq_nonneg _))) hC0
      _ = (lam ^ p) ^ 2 * (C * Pm) := by ring
      _ ≤ (lam ^ p) ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left hRC (sq_nonneg _)
      _ = (R * lam ^ p) ^ 2 := by ring
  exact abs_le.2 (abs_le_of_sq_le_sq' (h1.trans h2) (mul_nonneg hR (pow_nonneg hl p)))

/-- Repeated squaring. -/
def sqZ (M : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ := M * M

theorem sqZ_iter (p : ℕ) : ∀ M : Matrix (Fin n) (Fin n) ℤ, sqZ^[p] M = M ^ (2 ^ p) := by
  induction p with
  | zero => intro M; simp
  | succ p ih =>
    intro M
    rw [Function.iterate_succ_apply, ih, sqZ, ← sq, ← pow_mul, pow_succ, mul_comm]

/-- The entrywise bound of `A^(2^p)` from the integer powers: `|Âᵏ| 2^s ≤ Mn Dᵏ`. -/
theorem powK_bound (Ahat : Matrix (Fin n) (Fin n) ℤ) (D : ℤ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : 0 < D) (hA : ∀ i j, (Ahat i j : ℝ) = (D : ℝ) * A i j) (p s : ℕ) (Mn : Matrix (Fin n) (Fin n) ℕ)
    (h : ∀ i j, ((sqZ^[p] Ahat) i j).natAbs * 2 ^ s ≤ Mn i j * D.natAbs ^ (2 ^ p)) (i j : Fin n) :
    |(A ^ (2 ^ p)) i j| ≤ (Mn i j : ℝ) / 2 ^ s := by
  have hcast : Ahat.map (Int.cast : ℤ → ℝ) = (D : ℝ) • A := by
    ext a b; simp [hA]
  have hpow : ((sqZ^[p] Ahat).map (Int.cast : ℤ → ℝ)) = (D : ℝ) ^ (2 ^ p) • A ^ (2 ^ p) := by
    rw [sqZ_iter, ← smul_pow, ← hcast]
    exact (Matrix.map_pow Ahat (Int.castRingHom ℝ) (2 ^ p))
  have hij := congrFun (congrFun hpow i) j
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hij
  have hb : (|((sqZ^[p] Ahat) i j : ℝ)|) * 2 ^ s ≤ (Mn i j : ℝ) * (D : ℝ) ^ (2 ^ p) := by
    have h1 : ((((sqZ^[p] Ahat) i j).natAbs * 2 ^ s : ℕ) : ℝ) ≤ ((Mn i j * D.natAbs ^ (2 ^ p) : ℕ) : ℝ) := by
      exact_mod_cast h i j
    push_cast [Nat.cast_natAbs] at h1
    rwa [abs_of_pos (show (0 : ℝ) < D by exact_mod_cast hD)] at h1
  rw [hij, abs_mul, abs_of_pos (pow_pos (by exact_mod_cast hD) _)] at hb
  have hDp : (0 : ℝ) < (D : ℝ) ^ (2 ^ p) := pow_pos (by exact_mod_cast hD) _
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-! ### Assembly: from the kernel checks to the gains of one output -/

theorem resp_eq_vecMul (A : Matrix (Fin n) (Fin n) ℝ) (o : Fin n → ℝ) (m : ℕ) (j : Fin n) :
    resp A o m j = (o ᵥ* A ^ m) j := by
  rw [resp, dotProduct_mulVec, dotProduct_single, mul_one]

theorem cast_vecMul (v : Fin n → ℚ) (M : Matrix (Fin n) (Fin n) ℚ) (j : Fin n) :
    (((v ᵥ* M) j : ℚ) : ℝ) = ((fun i => (v i : ℝ)) ᵥ* M.map (Rat.cast : ℚ → ℝ)) j := by
  have := RingHom.map_vecMul (Rat.castHom ℝ) M v j
  simpa [Function.comp_def] using this

variable {T U : Type}

/-- **The gains of one output.** All numbers are rationals checked by the kernel. -/
theorem gain_assemble (Ahat : Matrix (Fin n) (Fin n) ℤ) (D : ℤ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : 0 < D) (hA : ∀ i j, (Ahat i j : ℝ) = (D : ℝ) * A i j) {R lam : ℚ} (hR : 0 ≤ R)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hpow : ∀ p i j, |(A ^ p) i j| ≤ (R : ℝ) * (lam : ℝ) ^ p)
    (o : Fin n → ℝ) (vec : T → Fin n → ℤ) (nat : U → Fin n → ℕ) (st : T → T) (ad mx : U → T → U)
    (hst : ∀ y, vec (st y) = adjZ Ahat D (vec y))
    (had : ∀ s y j, nat (ad s y) j = nat s j + (vec y j).natAbs)
    (hmx : ∀ m y j, nat (mx m y) j = max (nat m j) (vec y j).natAbs)
    (z0 : U) (eqT : T → T → Bool) (eqU : U → U → Bool) (heqT : ∀ a b, eqT a b = true → a = b)
    (heqU : ∀ a b, eqU a b = true → a = b) (L cB C : ℕ) (cp : ℕ → T × U × U)
    (hchk : ∀ c < C, chkAt st ad mx z0 eqT eqU L cB cp c = true)
    (hcB : cB < C) (hL : 0 < L)
    {S : ℚ} (hS : 0 < S) (hy0 : ∀ i, (vec (cp 0).1 i : ℝ) = (S : ℝ) * o i)
    (hs0 : ∀ j, nat (cp 0).2.1 j = 0)
    {ρ : ℚ} (hρ : n * R / ((1 - lam) * S) ≤ ρ)
    (p s : ℕ) (Mn : Matrix (Fin n) (Fin n) ℕ) (hKp : L * (C - cB) = 2 ^ p)
    (hMn : ∀ i j, ((sqZ^[p] Ahat) i j).natAbs * 2 ^ s ≤ Mn i j * D.natAbs ^ (2 ^ p))
    (z zP Gb Pb : Fin n → ℚ)
    (hz0 : ∀ j, 0 ≤ z j)
    (hz : ∀ j, ((fun i => ((nat (cp C).2.1 i : ℚ) - nat (cp cB).2.1 i) / S + (L * (C - cB) : ℕ) * ρ)
        ᵥ* Mn.map (fun k => (k : ℚ) / 2 ^ s)) j + (z ᵥ* Mn.map (fun k => (k : ℚ) / 2 ^ s)) j ≤ z j)
    (hzP0 : ∀ j, 0 ≤ zP j)
    (hzP : ∀ j, ((fun i => (nat (cp C).2.2 i : ℚ) / S + ρ)
        ᵥ* Mn.map (fun k => (k : ℚ) / 2 ^ s)) j + (zP ᵥ* Mn.map (fun k => (k : ℚ) / 2 ^ s)) j ≤ zP j)
    (hG : ∀ j, (nat (cp C).2.1 j : ℚ) / S + (L * C : ℕ) * ρ + z j ≤ Gb j)
    (hP1 : ∀ j, (max (nat (cp cB).2.2 j) (nat (cp C).2.2 j) : ℚ) / S + ρ ≤ Pb j)
    (hP2 : ∀ j, zP j ≤ Pb j) :
    (∀ j N', ∑ m ∈ range N', |resp A o m j| ≤ (Gb j : ℝ)) ∧
      ∀ j m, |resp A o m j| ≤ (Pb j : ℝ) := by
  set F := adjZ Ahat D
  set y0 := vec (cp 0).1
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hρ0 : (0 : ℝ) ≤ ρ := by
    have : (0 : ℚ) ≤ n * R / ((1 - lam) * S) := by
      apply div_nonneg (mul_nonneg (by positivity) hR) (mul_nonneg (by linarith) hS.le)
    exact_mod_cast this.trans hρ
  have hY : ∀ m j, |(o ᵥ* A ^ m) j - ((F^[m] y0 j : ℤ) : ℝ) / S| ≤ ρ := by
    intro m j
    have h := round_err Ahat D A hD hA o y0 hSr hy0 (by exact_mod_cast hR) (by exact_mod_cast hl0)
      (by exact_mod_cast hl1) hpow m j
    refine h.trans ?_
    have : ((n * R / ((1 - lam) * S) : ℚ) : ℝ) ≤ ρ := by exact_mod_cast hρ
    push_cast at this
    exact this
  have hch := chain F vec nat st ad mx hst had hmx z0 eqT eqU heqT heqU L cB C cp hchk
  obtain ⟨_, hC2, _, hC4⟩ := hch C le_rfl
  obtain ⟨_, hB2, hB3, _⟩ := hch cB hcB.le
  set N := L * C
  set K := L * (C - cB)
  have hNK : N - K = L * cB := by
    simp only [N, K, Nat.mul_sub]; have : L * cB ≤ L * C := Nat.mul_le_mul_left _ hcB.le; omega
  have hKN : K ≤ N := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hK0 : 0 < K := Nat.mul_pos hL (by omega)
  set Yr : ℕ → Fin n → ℝ := fun m j => ((F^[m] y0 j : ℤ) : ℝ) / S
  have habsY : ∀ m j, |Yr m j| = ((F^[m] y0 j).natAbs : ℝ) / S := by
    intro m j
    simp only [Yr, abs_div, abs_of_pos hSr, Nat.cast_natAbs, Int.cast_abs]
  set Mb : Matrix (Fin n) (Fin n) ℝ := (Mn.map (fun k => (k : ℚ) / 2 ^ s)).map (Rat.cast : ℚ → ℝ)
  have hMb0 : ∀ i j, 0 ≤ Mb i j := fun i j => by simp [Mb]; positivity
  have hMb : ∀ i j, |(A ^ K) i j| ≤ Mb i j := fun i j => by
    rw [hKp]
    refine (powK_bound Ahat D A hD hA p s Mn hMn i j).trans (le_of_eq ?_)
    simp [Mb]
  -- the head and tail theorem
  have hT := head_tail A o Yr hρ0 hY hKN hK0
    (fun j => ((nat (cp C).2.1 j : ℚ) / S : ℚ))
    (fun j => ((max (nat (cp cB).2.2 j) (nat (cp C).2.2 j) : ℚ) / S : ℚ))
    (fun j => (((nat (cp C).2.1 j : ℚ) - nat (cp cB).2.1 j) / S : ℚ))
    (fun j => ((nat (cp C).2.2 j : ℚ) / S : ℚ))
    (fun j => (z j : ℝ)) (fun j => (zP j : ℝ)) Mb
    (fun j => by
      simp only [habsY, ← Finset.sum_div]
      rw [hC2 j, hs0 j, zero_add]
      push_cast; exact le_rfl)
    (fun m hm j => by
      rw [habsY]
      by_cases hmB : m < L * cB
      · have := hB3 le_rfl m hmB j
        have h' : (((F^[m] y0 j).natAbs : ℕ) : ℝ) ≤ (max (nat (cp cB).2.2 j) (nat (cp C).2.2 j) : ℕ) :=
          by exact_mod_cast this.trans (le_max_left _ _)
        push_cast at h' ⊢
        exact div_le_div_of_nonneg_right h' hSr.le
      · have := hC4 hcB m (by omega) hm j
        have h' : (((F^[m] y0 j).natAbs : ℕ) : ℝ) ≤ (max (nat (cp cB).2.2 j) (nat (cp C).2.2 j) : ℕ) :=
          by exact_mod_cast this.trans (le_max_right _ _)
        push_cast at h' ⊢
        exact div_le_div_of_nonneg_right h' hSr.le)
    (fun j => by
      simp only [habsY, ← Finset.sum_div]
      have e1 := hC2 j
      have e2 := hB2 j
      rw [hs0 j, zero_add] at e1 e2
      have hsplit : N = L * cB + K := by omega
      rw [hsplit, Finset.sum_range_add] at e1
      rw [hNK]
      have : ((∑ x ∈ range K, (F^[L * cB + x] y0 j).natAbs : ℕ) : ℝ) =
          (nat (cp C).2.1 j : ℝ) - nat (cp cB).2.1 j := by
        rw [e1, e2]; push_cast; ring
      push_cast at this ⊢
      rw [this])
    (fun r hr j => by
      rw [habsY, hNK]
      have := hC4 hcB (L * cB + r) (by omega) (by omega) j
      have h' : (((F^[L * cB + r] y0 j).natAbs : ℕ) : ℝ) ≤ (nat (cp C).2.2 j : ℕ) := by
        exact_mod_cast this
      push_cast at h' ⊢
      exact div_le_div_of_nonneg_right h' hSr.le)
    hMb0 hMb (fun j => by exact_mod_cast hz0 j)
    (fun j => by
      have h := hz j
      have h' : ((((fun i => ((nat (cp C).2.1 i : ℚ) - nat (cp cB).2.1 i) / S + (K : ℕ) * ρ)
          ᵥ* Mn.map (fun k => (k : ℚ) / 2 ^ s)) j + (z ᵥ* Mn.map (fun k => (k : ℚ) / 2 ^ s)) j : ℚ) : ℝ)
          ≤ (z j : ℝ) := by exact_mod_cast h
      rw [Rat.cast_add, cast_vecMul, cast_vecMul] at h'
      convert h' using 3
      ext i; push_cast; ring)
    (fun j => by exact_mod_cast hzP0 j)
    (fun j => by
      have h := hzP j
      have h' : ((((fun i => (nat (cp C).2.2 i : ℚ) / S + ρ)
          ᵥ* Mn.map (fun k => (k : ℚ) / 2 ^ s)) j + (zP ᵥ* Mn.map (fun k => (k : ℚ) / 2 ^ s)) j : ℚ) : ℝ)
          ≤ (zP j : ℝ) := by exact_mod_cast h
      rw [Rat.cast_add, cast_vecMul, cast_vecMul] at h'
      convert h' using 3
      ext i; push_cast; ring)
  refine ⟨fun j N' => ?_, fun j m => ?_⟩
  · simp only [resp_eq_vecMul]
    refine (hT.1 N' j).trans ?_
    have := hG j
    have h' : (((nat (cp C).2.1 j : ℚ) / S + (N : ℕ) * ρ + z j : ℚ) : ℝ) ≤ (Gb j : ℝ) := by
      exact_mod_cast this
    push_cast at h' ⊢
    exact h'
  · rw [resp_eq_vecMul]
    refine (hT.2 m j).trans (max_le ?_ ?_)
    · have h' : (((max (nat (cp cB).2.2 j) (nat (cp C).2.2 j) : ℚ) / S + ρ : ℚ) : ℝ) ≤ (Pb j : ℝ) := by
        exact_mod_cast hP1 j
      push_cast at h' ⊢
      exact h'
    · exact_mod_cast hP2 j

/-- **Rounding of a forced recurrence**: `X (i+1) = ⌊(Â X i + U i) / D⌋` with `U i = S D f i` stays
within `n R / ((1 - λ) S)` of `S` times the trajectory of `x' = A x + f` from rest. -/
theorem round_err_fwd (Ahat : Matrix (Fin n) (Fin n) ℤ) (D : ℤ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : 0 < D) (hA : ∀ i j, (Ahat i j : ℝ) = (D : ℝ) * A i j) (X U : ℕ → Fin n → ℤ)
    (f : ℕ → Fin n → ℝ) {S R lam : ℝ} (hS : 0 < S) (hR : 0 ≤ R) (hl0 : 0 ≤ lam) (hl1 : lam < 1)
    (hpow : ∀ p i j, |(A ^ p) i j| ≤ R * lam ^ p) (hX0 : X 0 = 0)
    (hX : ∀ i r, X (i + 1) r = (∑ j, Ahat r j * X i j + U i r) / D)
    (hU : ∀ i r, (U i r : ℝ) = S * D * f i r) (i : ℕ) (r : Fin n) :
    |Vertical.traj A 0 f i r - (X i r : ℝ) / S| ≤ n * R / ((1 - lam) * S) := by
  set e : ℕ → Fin n → ℝ := fun i => S • Vertical.traj A 0 f i - castZ (X i) with he_def
  set δ : ℕ → Fin n → ℝ := fun i => A *ᵥ castZ (X i) + S • f i - castZ (X (i + 1)) with hδ_def
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hδ : ∀ i r, 0 ≤ δ i r ∧ δ i r < 1 := by
    intro i r
    set Y : ℤ := ∑ j, Ahat r j * X i j + U i r with hY
    have hYr : (Y : ℝ) = (D : ℝ) * ((A *ᵥ castZ (X i)) r + S * f i r) := by
      simp only [hY, Int.cast_add, Int.cast_sum, Int.cast_mul, hA, hU, mulVec, dotProduct, castZ,
        mul_add, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => by ring
      · ring
    have h1 : Y / D * D ≤ Y := Int.ediv_mul_le Y hD.ne'
    have h2 : Y < (Y / D + 1) * D := Int.lt_ediv_add_one_mul_self Y hD
    have h1r : ((Y / D : ℤ) : ℝ) * D ≤ Y := by exact_mod_cast h1
    have h2r : (Y : ℝ) < (((Y / D : ℤ) : ℝ) + 1) * D := by exact_mod_cast h2
    have hq : castZ (X (i + 1)) r = ((Y / D : ℤ) : ℝ) := by simp only [castZ, hX i r, hY]
    simp only [hδ_def, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq]
    rw [hYr] at h1r h2r
    constructor <;> nlinarith
  have he : ∀ i, e i = Vertical.traj A 0 δ i := by
    intro i
    induction i with
    | zero => ext r; simp [he_def, hX0, castZ]
    | succ i ih =>
      rw [Vertical.traj_succ, ← ih]
      ext r
      simp only [he_def, hδ_def, Vertical.traj_succ, mulVec_sub, mulVec_smul, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
  have hb : |e i r| ≤ n * R / (1 - lam) := by
    rw [he, Vertical.traj_eq_sum, Finset.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ range i, |(A ^ (i - 1 - k) *ᵥ δ k) r| ≤ n * R * lam ^ (i - 1 - k) := by
      intro k _
      simp only [mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |(A ^ (i - 1 - k)) r j * δ k j| ≤ ∑ _j : Fin n, (R * lam ^ (i - 1 - k)) * 1 :=
            Finset.sum_le_sum fun j _ => by
              rw [abs_mul]
              exact mul_le_mul (hpow _ _ _) (by rw [abs_le]; constructor <;> linarith [hδ k j])
                (abs_nonneg _) (by have := hpow (i - 1 - k) r j; linarith [abs_nonneg ((A ^ (i - 1 - k)) r j)])
        _ = n * R * lam ^ (i - 1 - k) := by simp; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum, Finset.sum_range_reflect (fun p => lam ^ p) i]
    have hg : (∑ p ∈ range i, lam ^ p) * (1 - lam) ≤ 1 := by
      have := mul_neg_geom_sum lam i
      nlinarith [pow_nonneg hl0 i]
    have h1l : 0 < 1 - lam := by linarith
    rw [le_div_iff₀ h1l, mul_assoc]
    have hnR : 0 ≤ (n : ℝ) * R := by positivity
    nlinarith
  have key : Vertical.traj A 0 f i r - (X i r : ℝ) / S = e i r / S := by
    simp only [he_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, castZ]
    field_simp
  rw [key, abs_div, abs_of_pos hS, div_le_div_iff₀ hS (mul_pos (by linarith) hS)]
  have h1l : 0 < 1 - lam := by linarith
  rw [le_div_iff₀ h1l] at hb
  nlinarith [abs_nonneg (e i r)]

end Generic

def GVq : Fin 5 → Fin 8 → ℚ :=
  ![![408, 971 / 10, 13, 13 / 20, 817, 829 / 10, 261 / 100, 451 / 100],
    ![408, 230, 233 / 10, 117 / 100, 1050, 203, 159 / 25, 807 / 100],
    ![119 / 5, 237 / 10, 189 / 100, 949 / 10000, 215, 361 / 10, 57 / 50, 329 / 500],
    ![331 / 10, 161 / 5, 413 / 100, 107 / 500, 116, 439 / 10, 27 / 20, 37 / 25],
    ![337 / 10, 163 / 5, 267 / 50, 171 / 500, 120, 97 / 2, 51 / 20, 237 / 100]]

def PVq : Fin 5 → Fin 8 → ℚ :=
  ![![51 / 50, 129 / 500, 143 / 5000, 9 / 6250, 131 / 100, 17 / 100, 533 / 100000, 497 / 50000],
    ![449 / 500, 51 / 50, 207 / 2500, 433 / 100000, 213 / 100, 94 / 125, 237 / 10000, 3 / 100],
    ![501 / 10000, 639 / 10000, 961 / 100000, 341 / 500000, 51 / 50, 109 / 1000, 171 / 50000, 473 / 100000],
    ![59 / 500, 33 / 250, 439 / 10000, 91 / 25000, 107 / 250, 51 / 50, 311 / 10000, 63 / 2500],
    ![33 / 200, 173 / 1000, 37 / 250, 391 / 10000, 51 / 50, 409 / 500, 51 / 50, 271 / 1000]]

def GHq : Fin 5 → Fin 9 → ℚ :=
  ![![272, 743 / 10, 59 / 2, 119 / 100, 273, 143 / 20, 93 / 500, 93 / 500, 93 / 500],
    ![408, 129, 186 / 5, 187 / 100, 372 / 5, 57 / 5, 37 / 125, 37 / 125, 37 / 125],
    ![112, 408, 205, 13 / 2, 2450, 393 / 10, 51 / 50, 51 / 50, 51 / 50],
    ![1280, 643, 274, 69 / 5, 129, 282 / 5, 249 / 100, 147 / 100, 147 / 100],
    ![349 / 10, 108 / 5, 201 / 10, 113 / 100, 249 / 100, 59 / 50, 52 / 25, 53 / 50, 61 / 2000]]

def PHq : Fin 5 → Fin 9 → ℚ :=
  ![![51 / 50, 147 / 1000, 199 / 5000, 213 / 100000, 93 / 1000, 13 / 1000, 337 / 1000000, 337 / 1000000, 337 / 1000000],
    ![139 / 100, 51 / 50, 43 / 250, 467 / 50000, 27 / 200, 299 / 5000, 39 / 25000, 39 / 25000, 39 / 25000],
    ![11 / 50, 197 / 1000, 111 / 1250, 303 / 100000, 51 / 50, 23 / 1250, 477 / 1000000, 477 / 1000000, 477 / 1000000],
    ![74 / 5, 103 / 10, 23 / 5, 473 / 1000, 51 / 50, 561 / 1000, 51 / 50, 73 / 5000, 73 / 5000],
    ![23 / 10, 153 / 100, 23 / 5, 473 / 1000, 51 / 50, 1 / 50, 51 / 50, 51 / 50, 259 / 500000]]

theorem GV_eq (o : Fin 5) (j : Fin 8) : GV o j = (GVq o j : ℝ) := by
  fin_cases o <;> fin_cases j <;> norm_num [GV, GVq]

theorem PV_eq (o : Fin 5) (j : Fin 8) : PV o j = (PVq o j : ℝ) := by
  fin_cases o <;> fin_cases j <;> norm_num [PV, PVq]

theorem GH_eq (o : Fin 5) (j : Fin 9) : GH o j = (GHq o j : ℝ) := by
  fin_cases o <;> fin_cases j <;> norm_num [GH, GHq]

theorem PH_eq (o : Fin 5) (j : Fin 9) : PH o j = (PHq o j : ℝ) := by
  fin_cases o <;> fin_cases j <;> norm_num [PH, PHq]

end

end Contracts.Track.Induction.Nominal
