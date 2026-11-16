import Contracts.Track.Reach.Leg3GainsData
import Contracts.Track.Reach.Leg3Tube
import Contracts.Track.Reach.LegGains

/-!
# The 3D leg theorem: `RefGains3` certified (REACH.md §10)

`refGains3_certified : RefGains3`, from the kernel-checked trajectories of Leg3GainsData.lean
(`VerticalHi.AvR`, transposed): the gains of `B_v` (`ez 0.0434, ev 0.0642, I 0.0453, f 0.0565,
u 0.3407`) and of the acceleration shift `vAccV` (`u 2.1105`), and the tails past `Mc3 = 704`,
`Mt3 = 2624` (checkpoints 22, 82): `TBVc = 0.02234`, `TV0c = 70.55`, `PV1c = 0.0502`;
`TBVt = 0.004256`, `TV0t = 1.10`, `PV1t = 0.002179`.
-/

namespace Contracts.Track.Reach.Leg3

open Matrix Finset Contracts.Track.Induction Contracts.Track.Induction.Nominal Contracts.Track.Reach.Leg

noncomputable section

namespace CertVHi

theorem gainsB : (∀ j N', ∑ m ∈ range N', |resp VerticalHi.AvRᵀ VerticalHi.BvR m j| ≤ (GbB j : ℝ)) ∧
    ∀ j m, |resp VerticalHi.AvRᵀ VerticalHi.BvR m j| ≤ (PbB j : ℝ) := by
  obtain ⟨i1, i2⟩ := initB
  have e1 := GainVHi.eqT_spec _ _ i1
  have e2 := GainVHi.eqU_spec _ _ i2
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := numB
  refine gain_assemble VerticalHi.Ahatᵀ VerticalHi.DAz VerticalHi.AvRᵀ (by decide) hAT
    (R := GainVHi.Rq) (lam := VerticalHi.lamv) (by norm_num [GainVHi.Rq])
    (by norm_num [VerticalHi.lamv]) (by norm_num [VerticalHi.lamv]) hpowT VerticalHi.BvR GainVHi.vec
    GainVHi.nat step GainVHi.ad GainVHi.mx step_spec GainVHi.ad_spec GainVHi.mx_spec GainVHi.zU
    GainVHi.eqT GainVHi.eqU GainVHi.eqT_spec GainVHi.eqU_spec 32 64 128 cpB chkB (by norm_num)
    (by norm_num) (S := SB) (by norm_num [SB]) ?_ ?_ ρB_check 11 64 GainVHi.Mnᵀ (by norm_num)
    MnT_check zSB zPB GbB PbB n1 n3 n2 n4 n5 n6 n7
  · intro i; rw [e1]
    fin_cases i <;>
      simp [GainVHi.vec, VerticalHi.BvR, VerticalHi.Bv, Vertical.per, Vertical.αA, Vertical.kiDt,
        VerticalHi.kpAcc, SB] <;> norm_num
  · intro j; rw [e2]; fin_cases j <;> rfl

theorem gainsA : (∀ j N', ∑ m ∈ range N', |resp VerticalHi.AvRᵀ VerticalHi.vAccV m j| ≤ (GbA j : ℝ)) ∧
    ∀ j m, |resp VerticalHi.AvRᵀ VerticalHi.vAccV m j| ≤ (PbA j : ℝ) := by
  obtain ⟨i1, i2⟩ := initA
  have e1 := GainVHi.eqT_spec _ _ i1
  have e2 := GainVHi.eqU_spec _ _ i2
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := numA
  refine gain_assemble VerticalHi.Ahatᵀ VerticalHi.DAz VerticalHi.AvRᵀ (by decide) hAT
    (R := GainVHi.Rq) (lam := VerticalHi.lamv) (by norm_num [GainVHi.Rq])
    (by norm_num [VerticalHi.lamv]) (by norm_num [VerticalHi.lamv]) hpowT VerticalHi.vAccV
    GainVHi.vec GainVHi.nat step GainVHi.ad GainVHi.mx step_spec GainVHi.ad_spec GainVHi.mx_spec
    GainVHi.zU GainVHi.eqT GainVHi.eqU GainVHi.eqT_spec GainVHi.eqU_spec 32 64 128 cpA chkA
    (by norm_num) (by norm_num) (S := SA) (by norm_num [SA]) ?_ ?_ ρA_check 11 64 GainVHi.Mnᵀ
    (by norm_num) MnT_check zSA zPA GbA PbA n1 n3 n2 n4 n5 n6 n7
  · intro i; rw [e1]
    fin_cases i <;>
      simp [GainVHi.vec, VerticalHi.vAccV, Vertical.amax, Vertical.tw, Vertical.grav, SA] <;>
      norm_num
  · intro j; rw [e2]; fin_cases j <;> rfl

/-- The certified state `A_v^M D` at the checkpoint `cc` (`M = 32 cc`). -/
theorem stateAt (D : Fin 8 → ℝ) (cp : ℕ → GainVHi.Z8 × GainVHi.N8 × GainVHi.N8) {S ρ : ℚ}
    (hS : 0 < S) (hy0 : ∀ i, (GainVHi.vec (cp 0).1 i : ℝ) = (S : ℝ) * D i)
    (hρ : (8 : ℚ) * GainVHi.Rq / ((1 - VerticalHi.lamv) * S) ≤ ρ) (cB C cc M : ℕ) (hC : cc ≤ C)
    (hM : M = 32 * cc)
    (hchk : ∀ c < C, chkAt step GainVHi.ad GainVHi.mx GainVHi.zU GainVHi.eqT GainVHi.eqU 32 cB cp c =
      true)
    (j : Fin 8) :
    |(VerticalHi.AvR ^ M *ᵥ D) j| ≤ ((((GainVHi.vec (cp cc).1 j).natAbs : ℚ) / S + ρ : ℚ) : ℝ) := by
  have hc := (Contracts.Track.Induction.Nominal.chain (adjZ VerticalHi.Ahatᵀ VerticalHi.DAz)
    GainVHi.vec GainVHi.nat step GainVHi.ad GainVHi.mx step_spec GainVHi.ad_spec GainVHi.mx_spec
    GainVHi.zU GainVHi.eqT GainVHi.eqU GainVHi.eqT_spec GainVHi.eqU_spec 32 cB C cp hchk cc hC).1
  have h := state_le VerticalHi.Ahatᵀ VerticalHi.DAz VerticalHi.AvRᵀ (by decide) hAT D
    (GainVHi.vec (cp 0).1) hS hy0 (by norm_num [GainVHi.Rq]) (by norm_num [VerticalHi.lamv])
    (by norm_num [VerticalHi.lamv]) hpowT hρ (32 * cc) _ hc.symm j
  rw [forward_transpose] at h
  rw [hM]; exact h

theorem y0B (i : Fin 8) : (GainVHi.vec (cpB 0).1 i : ℝ) = (SB : ℝ) * VerticalHi.BvR i := by
  rw [GainVHi.eqT_spec _ _ initB.1]
  fin_cases i <;>
    simp [GainVHi.vec, VerticalHi.BvR, VerticalHi.Bv, Vertical.per, Vertical.αA, Vertical.kiDt,
      VerticalHi.kpAcc, SB] <;> norm_num

theorem y0E0 (i : Fin 8) : (GainVHi.vec (cpE0 0).1 i : ℝ) = (SE0 : ℝ) * Vertical.e0 i := by
  rw [GainVHi.eqT_spec _ _ initE0.1]
  fin_cases i <;> simp [GainVHi.vec, Vertical.e0, SE0]

theorem y0E1 (i : Fin 8) : (GainVHi.vec (cpE1 0).1 i : ℝ) = (SE1 : ℝ) * Vertical.e1 i := by
  rw [GainVHi.eqT_spec _ _ initE1.1]
  fin_cases i <;> simp [GainVHi.vec, Vertical.e1, SE1]

theorem GVH0_eq (j : Fin 8) : GVH 0 j = ((GVHq 0 j : ℚ) : ℝ) := rfl
theorem PVH0_eq (j : Fin 8) : PVH 0 j = ((PVHq 0 j : ℚ) : ℝ) := rfl

theorem tail_Bc (K : ℕ) :
    ∑ m ∈ range K, |rsp VerticalHi.AvR (outV 0) VerticalHi.BvR (Mc3 + m)| ≤ TBVc := by
  have hx := stateAt VerticalHi.BvR cpB (by norm_num [SB]) y0B ρB_check 64 128 22 Mc3
    (by norm_num) rfl chkB
  refine (tail_of_state _ _ _ Mc3 _ _ hx (fun j N => gainVH' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainVHi.vec (cpB 22).1 j).natAbs : ℚ) / SB + ρB : ℚ) : ℝ) * GVH 0 j =
      ((GtailB_22 : ℚ) : ℝ) := by
    rw [← GtailB_22_eq]; push_cast; simp [GVH0_eq]
  rw [e]; simp only [GtailB_22, TBVc]; norm_num

theorem tail_E0c (K : ℕ) :
    ∑ m ∈ range K, |rsp VerticalHi.AvR (outV 0) Vertical.e0 (Mc3 + m)| ≤ TV0c := by
  have hx := stateAt Vertical.e0 cpE0 (by norm_num [SE0]) y0E0 ρE0_check 88 88 22 Mc3
    (by norm_num) rfl chkE0
  refine (tail_of_state _ _ _ Mc3 _ _ hx (fun j N => gainVH' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainVHi.vec (cpE0 22).1 j).natAbs : ℚ) / SE0 + ρE0 : ℚ) : ℝ) * GVH 0 j =
      ((GtailE0_22 : ℚ) : ℝ) := by
    rw [← GtailE0_22_eq]; push_cast; simp [GVH0_eq]
  rw [e]; simp only [GtailE0_22, TV0c]; norm_num

theorem peak_E1c (m : ℕ) :
    |rsp VerticalHi.AvR (outV 0) Vertical.e1 (Mc3 + m)| ≤ PV1c := by
  have hx := stateAt Vertical.e1 cpE1 (by norm_num [SE1]) y0E1 ρE1_check 88 88 22 Mc3
    (by norm_num) rfl chkE1
  refine (peak_of_state _ _ _ Mc3 _ _ hx (fun j m => peakVH' 0 j m) m).trans ?_
  have e : ∑ j, ((((GainVHi.vec (cpE1 22).1 j).natAbs : ℚ) / SE1 + ρE1 : ℚ) : ℝ) * PVH 0 j =
      ((PtailE1_22 : ℚ) : ℝ) := by
    rw [← PtailE1_22_eq]; push_cast; simp [PVH0_eq]
  rw [e]; simp only [PtailE1_22, PV1c]; norm_num

theorem tail_Bt (K : ℕ) :
    ∑ m ∈ range K, |rsp VerticalHi.AvR (outV 0) VerticalHi.BvR (Mt3 + m)| ≤ TBVt := by
  have hx := stateAt VerticalHi.BvR cpB (by norm_num [SB]) y0B ρB_check 64 128 82 Mt3
    (by norm_num) rfl chkB
  refine (tail_of_state _ _ _ Mt3 _ _ hx (fun j N => gainVH' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainVHi.vec (cpB 82).1 j).natAbs : ℚ) / SB + ρB : ℚ) : ℝ) * GVH 0 j =
      ((GtailB_82 : ℚ) : ℝ) := by
    rw [← GtailB_82_eq]; push_cast; simp [GVH0_eq]
  rw [e]; simp only [GtailB_82, TBVt]; norm_num

theorem tail_E0t (K : ℕ) :
    ∑ m ∈ range K, |rsp VerticalHi.AvR (outV 0) Vertical.e0 (Mt3 + m)| ≤ TV0t := by
  have hx := stateAt Vertical.e0 cpE0 (by norm_num [SE0]) y0E0 ρE0_check 88 88 82 Mt3
    (by norm_num) rfl chkE0
  refine (tail_of_state _ _ _ Mt3 _ _ hx (fun j N => gainVH' 0 j N) K).trans ?_
  have e : ∑ j, ((((GainVHi.vec (cpE0 82).1 j).natAbs : ℚ) / SE0 + ρE0 : ℚ) : ℝ) * GVH 0 j =
      ((GtailE0_82 : ℚ) : ℝ) := by
    rw [← GtailE0_82_eq]; push_cast; simp [GVH0_eq]
  rw [e]; simp only [GtailE0_82, TV0t]; norm_num

theorem peak_E1t (m : ℕ) :
    |rsp VerticalHi.AvR (outV 0) Vertical.e1 (Mt3 + m)| ≤ PV1t := by
  have hx := stateAt Vertical.e1 cpE1 (by norm_num [SE1]) y0E1 ρE1_check 88 88 82 Mt3
    (by norm_num) rfl chkE1
  refine (peak_of_state _ _ _ Mt3 _ _ hx (fun j m => peakVH' 0 j m) m).trans ?_
  have e : ∑ j, ((((GainVHi.vec (cpE1 82).1 j).natAbs : ℚ) / SE1 + ρE1 : ℚ) : ℝ) * PVH 0 j =
      ((PtailE1_82 : ℚ) : ℝ) := by
    rw [← PtailE1_82_eq]; push_cast; simp [PVH0_eq]
  rw [e]; simp only [PtailE1_82, PV1t]; norm_num

end CertVHi

theorem gainBv3_coord (j : Fin 8) (N : ℕ) :
    ∑ m ∈ range N, |rsp VerticalHi.AvR (Pi.single j 1) VerticalHi.BvR m| ≤ (CertVHi.GbB j : ℝ) := by
  have := CertVHi.gainsB.1 j N
  simpa only [resp_transpose] using this

theorem gainBV3_cert (o : Fin 5) (N : ℕ) :
    ∑ m ∈ range N, |rsp VerticalHi.AvR (outV o) VerticalHi.BvR m| ≤ GBV3 o := by
  fin_cases o
  · exact (gainBv3_coord 0 N).trans (by simp [CertVHi.GbB, GBV3]; norm_num)
  · exact (gainBv3_coord 1 N).trans (by simp [CertVHi.GbB, GBV3]; norm_num)
  · exact (gainBv3_coord 4 N).trans (by simp [CertVHi.GbB, GBV3]; norm_num)
  · exact (gainBv3_coord 5 N).trans (by simp [CertVHi.GbB, GBV3]; norm_num)
  · exact (gainBv3_coord 6 N).trans (by simp [CertVHi.GbB, GBV3]; norm_num)

theorem gainU_cert (N : ℕ) :
    ∑ m ∈ range N, |rsp VerticalHi.AvR (outV 4) VerticalHi.vAccV m| ≤ GC1V := by
  have := CertVHi.gainsA.1 6 N
  simp only [resp_transpose] at this
  exact this.trans (by simp [CertVHi.GbA, GC1V]; norm_num)

/-- **The certified numbers of the vertical reference directions at `PSC_D_ACC_P = 0.25`.** -/
theorem refGains3_certified : RefGains3 where
  gainBV := gainBV3_cert
  gainU := gainU_cert
  tailBVc := CertVHi.tail_Bc
  tail0Vc := CertVHi.tail_E0c
  peak1Vc := CertVHi.peak_E1c
  tailBVt := CertVHi.tail_Bt
  tail0Vt := CertVHi.tail_E0t
  peak1Vt := CertVHi.peak_E1t

end

end Contracts.Track.Reach.Leg3
