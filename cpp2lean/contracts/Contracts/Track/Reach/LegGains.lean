import Contracts.Track.Reach.LegGainsData

/-!
# The leg theorem: `RefGains` certified (REACH.md §9)

`refGains_certified : RefGains`, from the kernel-checked trajectories of LegGainsData.lean:

* `gainsB` (horizontal and vertical), `gainsA`: `Nominal.gain_assemble` on the transposed models with
  the initial vectors `S · B_h`, `S · vAcc`, `S · B_v`: for every coordinate `j`, `Σₘ |(Aᵐ D)ⱼ| ≤ Gbⱼ`
  (`B_h`: `e 0.0300, ev 0.1654, I 0.0389, c₁ 2.2373`; `vAcc`: `c₁ 60.542`; `B_v`: `0.1161, 0.2902,
  0.0505, 0.0675, 0.0792`);
* the command rate's jerk gain is the `c₁` gain of `B_h` (`rate_shift`);
* the tails past `Mc = 416` and `Mt = 1728`: the certified states `A^{416} D`, `A^{1728} D`
  (`round_err` at the checkpoints 13 and 54, `stateAt`) weighted by the certified per-coordinate
  ℓ1 gains (`tail_of_state`) or, for the velocity defect `e₁`, by the peak gains (`peak_of_state`).
-/

namespace Contracts.Track.Reach.Leg

open Matrix Finset Contracts.Track.Induction Contracts.Track.Induction.Nominal

noncomputable section

/-- The certified state after `M` ticks: `|(o Aᴹ)ⱼ| ≤ |Yⱼ| / S + ρ` for the stored iterate `Y`. -/
theorem state_le {n : ℕ} (Ahat : Matrix (Fin n) (Fin n) ℤ) (D : ℤ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hD : 0 < D) (hA : ∀ i j, (Ahat i j : ℝ) = (D : ℝ) * A i j) (o : Fin n → ℝ) (y0 : Fin n → ℤ)
    {S R lam ρ : ℚ} (hS : 0 < S) (hy0 : ∀ i, (y0 i : ℝ) = (S : ℝ) * o i) (hR : 0 ≤ R)
    (hl0 : 0 ≤ lam) (hl1 : lam < 1) (hpow : ∀ p i j, |(A ^ p) i j| ≤ (R : ℝ) * (lam : ℝ) ^ p)
    (hρ : n * R / ((1 - lam) * S) ≤ ρ) (M : ℕ) (Y : Fin n → ℤ) (hY : (adjZ Ahat D)^[M] y0 = Y)
    (j : Fin n) : |(o ᵥ* A ^ M) j| ≤ (((Y j).natAbs : ℚ) / S + ρ : ℚ) := by
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have h := round_err Ahat D A hD hA o y0 hSr hy0 (by exact_mod_cast hR) (by exact_mod_cast hl0)
    (by exact_mod_cast hl1) hpow M j
  rw [hY] at h
  have hρ' : ((n : ℝ) * R / ((1 - lam) * S)) ≤ (ρ : ℝ) := by exact_mod_cast hρ
  have e : |((Y j : ℤ) : ℝ) / (S : ℝ)| = (((Y j).natAbs : ℚ) / S : ℚ) := by
    push_cast
    rw [abs_div, abs_of_pos hSr, Nat.cast_natAbs, Int.cast_abs]
  have := abs_sub_abs_le_abs_sub ((o ᵥ* A ^ M) j) (((Y j : ℤ) : ℝ) / (S : ℝ))
  push_cast at e ⊢
  linarith

/-- **A peak tail from a state**: `|o A^{M+m} D| ≤ Σⱼ xbⱼ Pⱼ` when `|(A^M D)ⱼ| ≤ xbⱼ` and `Pⱼ` bounds
the peak responses of `o` per coordinate. -/
theorem peak_of_state {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (o D : Fin n → ℝ) (M : ℕ)
    (xb P : Fin n → ℝ) (hx : ∀ j, |(A ^ M *ᵥ D) j| ≤ xb j)
    (hP : ∀ j m, |resp A o m j| ≤ P j) (m : ℕ) :
    |rsp A o D (M + m)| ≤ ∑ j, xb j * P j := by
  rw [rsp, add_comm, pow_add, ← mulVec_mulVec, dot_mulVec_eq]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hx j) (hP j m) (abs_nonneg _) ((abs_nonneg _).trans (hx j))

/-! ## Horizontal -/

namespace CertGainH

theorem gainsB : (∀ j N', ∑ m ∈ range N', |resp Horizontal.AhRᵀ Horizontal.BhR m j| ≤ (GbB j : ℝ)) ∧
    ∀ j m, |resp Horizontal.AhRᵀ Horizontal.BhR m j| ≤ (PbB j : ℝ) := by
  obtain ⟨i1, i2⟩ := initB
  have e1 := GainH.eqT_spec _ _ i1
  have e2 := GainH.eqU_spec _ _ i2
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := numB
  refine gain_assemble Horizontal.Ahatᵀ Horizontal.DAh Horizontal.AhRᵀ (by decide) hAT
    (R := GainH.Rq) (lam := Horizontal.lamh) (by norm_num [GainH.Rq]) (by norm_num [Horizontal.lamh])
    (by norm_num [Horizontal.lamh]) hpowT Horizontal.BhR GainH.vec GainH.nat step GainH.ad GainH.mx
    step_spec GainH.ad_spec GainH.mx_spec GainH.zU GainH.eqT GainH.eqU GainH.eqT_spec
    GainH.eqU_spec 32 64 128 cpB chkB (by norm_num) (by norm_num) (S := SB) (by norm_num [SB]) ?_ ?_
    ρB_check 11 64 GainH.Mnᵀ (by norm_num) MnT_check zSB zPB GbB PbB n1 n3 n2 n4 n5 n6 n7
  · intro i; rw [e1]
    fin_cases i <;> simp [GainH.vec, Horizontal.BhR, Horizontal.Bh, Horizontal.per, SB] <;> norm_num
  · intro j; rw [e2]; fin_cases j <;> rfl

/-- **The acceleration-shift direction `vAcc`**: its per-coordinate gains (the `c₁` coordinate is the
jerk gain of the command). -/
theorem gainsA : (∀ j N', ∑ m ∈ range N', |resp Horizontal.AhRᵀ vAcc m j| ≤ (GbA j : ℝ)) ∧
    ∀ j m, |resp Horizontal.AhRᵀ vAcc m j| ≤ (PbA j : ℝ) := by
  obtain ⟨i1, i2⟩ := initA
  have e1 := GainH.eqT_spec _ _ i1
  have e2 := GainH.eqU_spec _ _ i2
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := numA
  refine gain_assemble Horizontal.Ahatᵀ Horizontal.DAh Horizontal.AhRᵀ (by decide) hAT
    (R := GainH.Rq) (lam := Horizontal.lamh) (by norm_num [GainH.Rq]) (by norm_num [Horizontal.lamh])
    (by norm_num [Horizontal.lamh]) hpowT vAcc GainH.vec GainH.nat step GainH.ad GainH.mx
    step_spec GainH.ad_spec GainH.mx_spec GainH.zU GainH.eqT GainH.eqU GainH.eqT_spec
    GainH.eqU_spec 32 64 128 cpA chkA (by norm_num) (by norm_num) (S := SA) (by norm_num [SA]) ?_ ?_
    ρA_check 11 64 GainH.Mnᵀ (by norm_num) MnT_check zSA zPA GbA PbA n1 n3 n2 n4 n5 n6 n7
  · intro i; rw [e1]
    fin_cases i <;> simp [GainH.vec, vAcc, SA]
  · intro j; rw [e2]; fin_cases j <;> rfl

/-- The certified state `A_h^M D` of a direction at the checkpoint `cc` (`M = 32 cc`). -/
theorem stateAt (D : Fin 9 → ℝ) (cp : ℕ → GainH.Z9 × GainH.N9 × GainH.N9) {S ρ : ℚ} (hS : 0 < S)
    (hy0 : ∀ i, (GainH.vec (cp 0).1 i : ℝ) = (S : ℝ) * D i)
    (hρ : (9 : ℚ) * GainH.Rq / ((1 - Horizontal.lamh) * S) ≤ ρ) (cB C cc M : ℕ) (hC : cc ≤ C)
    (hM : M = 32 * cc)
    (hchk : ∀ c < C, chkAt step GainH.ad GainH.mx GainH.zU GainH.eqT GainH.eqU 32 cB cp c = true)
    (j : Fin 9) :
    |(Horizontal.AhR ^ M *ᵥ D) j| ≤ ((((GainH.vec (cp cc).1 j).natAbs : ℚ) / S + ρ : ℚ) : ℝ) := by
  have hc := (Contracts.Track.Induction.Nominal.chain (adjZ Horizontal.Ahatᵀ Horizontal.DAh) GainH.vec GainH.nat step GainH.ad GainH.mx
    step_spec GainH.ad_spec GainH.mx_spec GainH.zU GainH.eqT GainH.eqU GainH.eqT_spec
    GainH.eqU_spec 32 cB C cp hchk cc hC).1
  have h := state_le Horizontal.Ahatᵀ Horizontal.DAh Horizontal.AhRᵀ (by decide) hAT D
    (GainH.vec (cp 0).1) hS hy0 (by norm_num [GainH.Rq]) (by norm_num [Horizontal.lamh])
    (by norm_num [Horizontal.lamh]) hpowT hρ (32 * cc) _ hc.symm j
  rw [forward_transpose] at h
  rw [hM]; exact h

theorem y0B (i : Fin 9) : (GainH.vec (cpB 0).1 i : ℝ) = (SB : ℝ) * Horizontal.BhR i := by
  rw [GainH.eqT_spec _ _ initB.1]
  fin_cases i <;> simp [GainH.vec, Horizontal.BhR, Horizontal.Bh, Horizontal.per, SB] <;> norm_num

theorem y0E0 (i : Fin 9) : (GainH.vec (cpE0 0).1 i : ℝ) = (SE0 : ℝ) * Horizontal.e0 i := by
  rw [GainH.eqT_spec _ _ initE0.1]
  fin_cases i <;> simp [GainH.vec, Horizontal.e0, SE0]

theorem y0E1 (i : Fin 9) : (GainH.vec (cpE1 0).1 i : ℝ) = (SE1 : ℝ) * Horizontal.e1 i := by
  rw [GainH.eqT_spec _ _ initE1.1]
  fin_cases i <;> simp [GainH.vec, Horizontal.e1, SE1]

theorem tail_Bc (K : ℕ) :
    ∑ m ∈ range K, |rsp Horizontal.AhR (outH 0) Horizontal.BhR (Mc + m)| ≤ TBc := by
  have hx := stateAt Horizontal.BhR cpB (by norm_num [SB]) y0B ρB_check 64 128 13 Mc
    (by norm_num) rfl chkB
  refine (tail_of_state _ _ _ Mc _ _ hx (fun j N => Glue.gainH' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainH.vec (cpB 13).1 j).natAbs : ℚ) / SB + ρB : ℚ) : ℝ) * GH 0 j =
      ((GtailB_13 : ℚ) : ℝ) := by
    rw [← GtailB_13_eq]; push_cast; simp [GH_eq]
  rw [e]; simp only [GtailB_13, TBc]; norm_num

theorem tail_E0c (K : ℕ) :
    ∑ m ∈ range K, |rsp Horizontal.AhR (outH 0) Horizontal.e0 (Mc + m)| ≤ T0c := by
  have hx := stateAt Horizontal.e0 cpE0 (by norm_num [SE0]) y0E0 ρE0_check 64 64 13 Mc
    (by norm_num) rfl chkE0
  refine (tail_of_state _ _ _ Mc _ _ hx (fun j N => Glue.gainH' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainH.vec (cpE0 13).1 j).natAbs : ℚ) / SE0 + ρE0 : ℚ) : ℝ) * GH 0 j =
      ((GtailE0_13 : ℚ) : ℝ) := by
    rw [← GtailE0_13_eq]; push_cast; simp [GH_eq]
  rw [e]; simp only [GtailE0_13, T0c]; norm_num

theorem peak_E1c (m : ℕ) :
    |rsp Horizontal.AhR (outH 0) Horizontal.e1 (Mc + m)| ≤ P1c := by
  have hx := stateAt Horizontal.e1 cpE1 (by norm_num [SE1]) y0E1 ρE1_check 64 64 13 Mc
    (by norm_num) rfl chkE1
  refine (peak_of_state _ _ _ Mc _ _ hx (fun j m => Glue.peakH' 0 j m) m).trans ?_
  have e : ∑ j, ((((GainH.vec (cpE1 13).1 j).natAbs : ℚ) / SE1 + ρE1 : ℚ) : ℝ) * PH 0 j =
      ((PtailE1_13 : ℚ) : ℝ) := by
    rw [← PtailE1_13_eq]; push_cast; simp [PH_eq]
  rw [e]; simp only [PtailE1_13, P1c]; norm_num

theorem tail_B (K : ℕ) :
    ∑ m ∈ range K, |rsp Horizontal.AhR (outH 0) Horizontal.BhR (Mt + m)| ≤ TB := by
  have hx := stateAt Horizontal.BhR cpB (by norm_num [SB]) y0B ρB_check 64 128 54 Mt
    (by norm_num) rfl chkB
  refine (tail_of_state _ _ _ Mt _ _ hx (fun j N => Glue.gainH' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainH.vec (cpB 54).1 j).natAbs : ℚ) / SB + ρB : ℚ) : ℝ) * GH 0 j =
      ((GtailB_54 : ℚ) : ℝ) := by
    rw [← GtailB_54_eq]; push_cast; simp [GH_eq]
  rw [e]; simp only [GtailB_54, TB]; norm_num

theorem tail_E0 (K : ℕ) :
    ∑ m ∈ range K, |rsp Horizontal.AhR (outH 0) Horizontal.e0 (Mt + m)| ≤ T0 := by
  have hx := stateAt Horizontal.e0 cpE0 (by norm_num [SE0]) y0E0 ρE0_check 64 64 54 Mt
    (by norm_num) rfl chkE0
  refine (tail_of_state _ _ _ Mt _ _ hx (fun j N => Glue.gainH' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainH.vec (cpE0 54).1 j).natAbs : ℚ) / SE0 + ρE0 : ℚ) : ℝ) * GH 0 j =
      ((GtailE0_54 : ℚ) : ℝ) := by
    rw [← GtailE0_54_eq]; push_cast; simp [GH_eq]
  rw [e]; simp only [GtailE0_54, T0]; norm_num

theorem peak_E1 (m : ℕ) :
    |rsp Horizontal.AhR (outH 0) Horizontal.e1 (Mt + m)| ≤ P1 := by
  have hx := stateAt Horizontal.e1 cpE1 (by norm_num [SE1]) y0E1 ρE1_check 64 64 54 Mt
    (by norm_num) rfl chkE1
  refine (peak_of_state _ _ _ Mt _ _ hx (fun j m => Glue.peakH' 0 j m) m).trans ?_
  have e : ∑ j, ((((GainH.vec (cpE1 54).1 j).natAbs : ℚ) / SE1 + ρE1 : ℚ) : ℝ) * PH 0 j =
      ((PtailE1_54 : ℚ) : ℝ) := by
    rw [← PtailE1_54_eq]; push_cast; simp [PH_eq]
  rw [e]; simp only [PtailE1_54, P1]; norm_num

end CertGainH

/-! ## Vertical -/

namespace CertGainV

theorem gainsB : (∀ j N', ∑ m ∈ range N', |resp Vertical.AvRᵀ Vertical.BvR m j| ≤ (GbB j : ℝ)) ∧
    ∀ j m, |resp Vertical.AvRᵀ Vertical.BvR m j| ≤ (PbB j : ℝ) := by
  obtain ⟨i1, i2⟩ := initB
  have e1 := GainV.eqT_spec _ _ i1
  have e2 := GainV.eqU_spec _ _ i2
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := numB
  refine gain_assemble Vertical.Ahatᵀ Vertical.DAz Vertical.AvRᵀ (by decide) hAT
    (R := GainV.Rq) (lam := Vertical.lamv) (by norm_num [GainV.Rq]) (by norm_num [Vertical.lamv])
    (by norm_num [Vertical.lamv]) hpowT Vertical.BvR GainV.vec GainV.nat step GainV.ad GainV.mx
    step_spec GainV.ad_spec GainV.mx_spec GainV.zU GainV.eqT GainV.eqU GainV.eqT_spec
    GainV.eqU_spec 32 32 64 cpB chkB (by norm_num) (by norm_num) (S := SB) (by norm_num [SB]) ?_ ?_
    ρB_check 10 64 GainV.Mnᵀ (by norm_num) MnT_check zSB zPB GbB PbB n1 n3 n2 n4 n5 n6 n7
  · intro i; rw [e1]
    fin_cases i <;>
      simp [GainV.vec, Vertical.BvR, Vertical.Bv, Vertical.per, Vertical.αA, Vertical.kiDt,
        Vertical.kpAcc, SB] <;> norm_num
  · intro j; rw [e2]; fin_cases j <;> rfl

/-- The certified state `A_v^M D` of a direction at the checkpoint `cc` (`M = 32 cc`). -/
theorem stateAt (D : Fin 8 → ℝ) (cp : ℕ → GainV.Z8 × GainV.N8 × GainV.N8) {S ρ : ℚ} (hS : 0 < S)
    (hy0 : ∀ i, (GainV.vec (cp 0).1 i : ℝ) = (S : ℝ) * D i)
    (hρ : (8 : ℚ) * GainV.Rq / ((1 - Vertical.lamv) * S) ≤ ρ) (cB C cc M : ℕ) (hC : cc ≤ C)
    (hM : M = 32 * cc)
    (hchk : ∀ c < C, chkAt step GainV.ad GainV.mx GainV.zU GainV.eqT GainV.eqU 32 cB cp c = true)
    (j : Fin 8) :
    |(Vertical.AvR ^ M *ᵥ D) j| ≤ ((((GainV.vec (cp cc).1 j).natAbs : ℚ) / S + ρ : ℚ) : ℝ) := by
  have hc := (Contracts.Track.Induction.Nominal.chain (adjZ Vertical.Ahatᵀ Vertical.DAz) GainV.vec GainV.nat step GainV.ad GainV.mx
    step_spec GainV.ad_spec GainV.mx_spec GainV.zU GainV.eqT GainV.eqU GainV.eqT_spec
    GainV.eqU_spec 32 cB C cp hchk cc hC).1
  have h := state_le Vertical.Ahatᵀ Vertical.DAz Vertical.AvRᵀ (by decide) hAT D
    (GainV.vec (cp 0).1) hS hy0 (by norm_num [GainV.Rq]) (by norm_num [Vertical.lamv])
    (by norm_num [Vertical.lamv]) hpowT hρ (32 * cc) _ hc.symm j
  rw [forward_transpose] at h
  rw [hM]; exact h

theorem tail_B (K : ℕ) :
    ∑ m ∈ range K, |rsp Vertical.AvR (outV 0) Vertical.BvR (Mt + m)| ≤ TBV := by
  have hx := stateAt Vertical.BvR cpB (by norm_num [SB])
    (fun i => by
      rw [GainV.eqT_spec _ _ initB.1]
      fin_cases i <;>
        simp [GainV.vec, Vertical.BvR, Vertical.Bv, Vertical.per, Vertical.αA, Vertical.kiDt,
          Vertical.kpAcc, SB] <;> norm_num) ρB_check 32 64 54 Mt (by norm_num) rfl chkB
  refine (tail_of_state _ _ _ Mt _ _ hx (fun j N => Glue.gainV' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainV.vec (cpB 54).1 j).natAbs : ℚ) / SB + ρB : ℚ) : ℝ) * GV 0 j =
      ((GtailB_54 : ℚ) : ℝ) := by
    rw [← GtailB_54_eq]; push_cast; simp [GV_eq]
  rw [e]; simp only [GtailB_54, TBV]; norm_num

theorem tail_E0 (K : ℕ) :
    ∑ m ∈ range K, |rsp Vertical.AvR (outV 0) Vertical.e0 (Mt + m)| ≤ TV0 := by
  have hx := stateAt Vertical.e0 cpE0 (by norm_num [SE0])
    (fun i => by
      rw [GainV.eqT_spec _ _ initE0.1]
      fin_cases i <;> simp [GainV.vec, Vertical.e0, SE0]) ρE0_check 64 64 54 Mt (by norm_num) rfl
    chkE0
  refine (tail_of_state _ _ _ Mt _ _ hx (fun j N => Glue.gainV' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainV.vec (cpE0 54).1 j).natAbs : ℚ) / SE0 + ρE0 : ℚ) : ℝ) * GV 0 j =
      ((GtailE0_54 : ℚ) : ℝ) := by
    rw [← GtailE0_54_eq]; push_cast; simp [GV_eq]
  rw [e]; simp only [GtailE0_54, TV0]; norm_num

theorem tail_E1 (K : ℕ) :
    ∑ m ∈ range K, |rsp Vertical.AvR (outV 0) Vertical.e1 (Mt + m)| ≤ TV1 := by
  have hx := stateAt Vertical.e1 cpE1 (by norm_num [SE1])
    (fun i => by
      rw [GainV.eqT_spec _ _ initE1.1]
      fin_cases i <;> simp [GainV.vec, Vertical.e1, SE1]) ρE1_check 64 64 54 Mt (by norm_num) rfl
    chkE1
  refine (tail_of_state _ _ _ Mt _ _ hx (fun j N => Glue.gainV' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainV.vec (cpE1 54).1 j).natAbs : ℚ) / SE1 + ρE1 : ℚ) : ℝ) * GV 0 j =
      ((GtailE1_54 : ℚ) : ℝ) := by
    rw [← GtailE1_54_eq]; push_cast; simp [GV_eq]
  rw [e]; simp only [GtailE1_54, TV1]; norm_num

end CertGainV

/-! ## The fields of `RefGains` -/

/-- One coordinate of the `B_h` trajectory. -/
theorem gainBh_coord (j : Fin 9) (N : ℕ) :
    ∑ m ∈ range N, |rsp Horizontal.AhR (Pi.single j 1) Horizontal.BhR m| ≤ (CertGainH.GbB j : ℝ) := by
  have := CertGainH.gainsB.1 j N
  simpa only [resp_transpose] using this

/-- One coordinate of the `B_v` trajectory. -/
theorem gainBv_coord (j : Fin 8) (N : ℕ) :
    ∑ m ∈ range N, |rsp Vertical.AvR (Pi.single j 1) Vertical.BvR m| ≤ (CertGainV.GbB j : ℝ) := by
  have := CertGainV.gainsB.1 j N
  simpa only [resp_transpose] using this

theorem rsp_sub {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a b D : Fin n → ℝ) (m : ℕ) :
    rsp A (a - b) D m = rsp A a D m - rsp A b D m := by
  simp [rsp, sub_dotProduct]

theorem gainB_cert (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp Horizontal.AhR (outH o) Horizontal.BhR m| ≤ GB o := by
  fin_cases o
  · exact (gainBh_coord 0 N).trans (by simp [CertGainH.GbB, GB]; norm_num)
  · exact (gainBh_coord 1 N).trans (by simp [CertGainH.GbB, GB]; norm_num)
  · exact (gainBh_coord 4 N).trans (by simp [CertGainH.GbB, GB]; norm_num)
  · exact (gainBh_coord 6 N).trans (by simp [CertGainH.GbB, GB]; norm_num)
  · show ∑ m ∈ range N, |rsp Horizontal.AhR (Pi.single 6 1 - Pi.single 7 1) Horizontal.BhR m| ≤ GB 4
    simp only [rsp_sub]
    calc ∑ m ∈ range N, |rsp Horizontal.AhR (Pi.single 6 1) Horizontal.BhR m -
          rsp Horizontal.AhR (Pi.single 7 1) Horizontal.BhR m|
        ≤ ∑ m ∈ range N, (|rsp Horizontal.AhR (Pi.single 6 1) Horizontal.BhR m| +
          |rsp Horizontal.AhR (Pi.single 7 1) Horizontal.BhR m|) :=
          Finset.sum_le_sum fun m _ => abs_sub _ _
      _ ≤ (CertGainH.GbB 6 : ℝ) + CertGainH.GbB 7 := by
          rw [Finset.sum_add_distrib]; exact add_le_add (gainBh_coord 6 N) (gainBh_coord 7 N)
      _ ≤ GB 4 := by simp [CertGainH.GbB, GB]; norm_num

/-- **The jerk response of the command rate is the `c₁` response of `B_h`, one tick later.** -/
theorem rate_shift (m : ℕ) :
    rsp Horizontal.AhR (outH 4) vAcc (m + 1) = -rsp Horizontal.AhR (outH 3) Horizontal.BhR m := by
  have e4 : outH 4 = Pi.single 6 1 - Pi.single 7 1 := rfl
  have e3 : outH 3 = Pi.single 6 1 := rfl
  have hv : Horizontal.AhR *ᵥ vAcc = vAcc - Horizontal.BhR := eq_sub_of_add_eq Ah_vAcc
  have h6 : (Horizontal.AhR ^ (m + 1) *ᵥ vAcc) 6 =
      (Horizontal.AhR ^ m *ᵥ vAcc) 6 - (Horizontal.AhR ^ m *ᵥ Horizontal.BhR) 6 := by
    rw [pow_succ, ← mulVec_mulVec, hv, mulVec_sub]; rfl
  have h7 : (Horizontal.AhR ^ (m + 1) *ᵥ vAcc) 7 = (Horizontal.AhR ^ m *ᵥ vAcc) 6 := by
    rw [pow_succ', ← mulVec_mulVec, Ah_row7]
  simp only [rsp, e4, e3, sub_dotProduct, single_dotProduct, one_mul]
  rw [h6, h7]
  ring

theorem gainJ_cert (N : ℕ) : ∑ m ∈ range N, |rsp Horizontal.AhR (outH 4) vAcc m| ≤ GJ := by
  rcases N with _ | N
  · norm_num [GJ]
  · rw [Finset.sum_range_succ']
    have h0 : rsp Horizontal.AhR (outH 4) vAcc 0 = 0 := by
      simp [rsp, outH4_vAcc]
    simp only [rate_shift, abs_neg, h0, abs_zero, add_zero]
    exact (gainB_cert 3 N).trans (by simp [GB, GJ])

/-- The jerk gain of the command: the `c₁` coordinate of the `vAcc` trajectory. -/
theorem gainC1_cert (N : ℕ) : ∑ m ∈ range N, |rsp Horizontal.AhR (outH 3) vAcc m| ≤ GC1 := by
  have := CertGainH.gainsA.1 6 N
  simp only [resp_transpose] at this
  exact this.trans (by simp [CertGainH.GbA, GC1]; norm_num)

theorem gainBV_cert (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp Vertical.AvR (outV o) Vertical.BvR m| ≤ GBV o := by
  fin_cases o
  · exact (gainBv_coord 0 N).trans (by simp [CertGainV.GbB, GBV]; norm_num)
  · exact (gainBv_coord 1 N).trans (by simp [CertGainV.GbB, GBV]; norm_num)
  · exact (gainBv_coord 4 N).trans (by simp [CertGainV.GbB, GBV]; norm_num)
  · exact (gainBv_coord 5 N).trans (by simp [CertGainV.GbB, GBV]; norm_num)
  · exact (gainBv_coord 6 N).trans (by simp [CertGainV.GbB, GBV]; norm_num)

/-- **The certified numbers of the reference directions.** -/
theorem refGains_certified : RefGains where
  gainB := gainB_cert
  gainJ := gainJ_cert
  gainC1 := gainC1_cert
  gainBV := gainBV_cert
  tailBc := CertGainH.tail_Bc
  tail0c := CertGainH.tail_E0c
  peak1c := CertGainH.peak_E1c
  tailB := CertGainH.tail_B
  tail0 := CertGainH.tail_E0
  peak1 := CertGainH.peak_E1
  tailBV := CertGainV.tail_B
  tail0V := CertGainV.tail_E0
  tail1V := CertGainV.tail_E1

end

end Contracts.Track.Reach.Leg
