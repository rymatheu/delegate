import Contracts.Track.Induction.NominalGainV
import Contracts.Track.Induction.NominalGainH
import Contracts.Track.Induction.NominalCorner

/-!
# M9: the certified nominal

The fields of `Pieces` (Pieces.lean) that the linear channel models certify, and the certified
vertical nominal at the corners. NOMINAL.md documents the method, the numbers and what the
remaining nominal fields need.

* **The gains** `peakV`, `gainV`, `peakH`, `gainH`: `peakV_cert`, `gainV_cert`, `peakH_cert`,
  `gainH_cert`, literally the field types (NominalGainV.lean, NominalGainH.lean, from the generic
  theory of NominalBase.lean).
* **The vertical nominal at `w₁ … w₆`** (`Corner.vz_w1 … vz_w6`, NominalCorner.lean): for the
  ideal course (leg-0 climb `L ∈ [0.5, 0.8]`, any phase, then legs 1–7), on the corner windows,
  `|ez| ≤ 0.02068, 0.00228, 0.00438, 0.00792, 0.00767, 0.00572`; `corner_budget` closes the 3D
  budget at every corner with them.
-/

namespace Contracts.Track.Induction.Nominal

open Matrix Finset

noncomputable section

/-! ## The gain fields of `Pieces` -/

/-- **`peakV`**: the peak gains of the vertical model are within `PV`. -/
theorem peakV_cert : ∀ o j m, |resp Vertical.AvR (outV o) m j| ≤ PV o j := by
  intro o j m
  rw [PV_eq]
  fin_cases o
  · exact GainV.out0.2 j m
  · exact GainV.out1.2 j m
  · exact GainV.out2.2 j m
  · exact GainV.out3.2 j m
  · exact GainV.out4.2 j m

/-- **`gainV`**: the ℓ1 gains of the vertical model are within `GV`. -/
theorem gainV_cert : ∀ o j N, ∑ m ∈ Finset.range N, |resp Vertical.AvR (outV o) m j| ≤ GV o j := by
  intro o j N
  rw [GV_eq]
  fin_cases o
  · exact GainV.out0.1 j N
  · exact GainV.out1.1 j N
  · exact GainV.out2.1 j N
  · exact GainV.out3.1 j N
  · exact GainV.out4.1 j N

/-- **`peakH`**: the peak gains of the horizontal model are within `PH`. -/
theorem peakH_cert : ∀ o j m, |resp Horizontal.AhR (outH o) m j| ≤ PH o j := by
  intro o j m
  rw [PH_eq]
  fin_cases o
  · exact GainH.out0.2 j m
  · exact GainH.out1.2 j m
  · exact GainH.out2.2 j m
  · exact GainH.out3.2 j m
  · exact GainH.out4.2 j m

/-- **`gainH`**: the ℓ1 gains of the horizontal model are within `GH`. -/
theorem gainH_cert : ∀ o j N, ∑ m ∈ Finset.range N, |resp Horizontal.AhR (outH o) m j| ≤ GH o j := by
  intro o j N
  rw [GH_eq]
  fin_cases o
  · exact GainH.out0.1 j N
  · exact GainH.out1.1 j N
  · exact GainH.out2.1 j N
  · exact GainH.out3.1 j N
  · exact GainH.out4.1 j N

/-- The fields, literally as `Pieces` states them. -/
example : (∀ o j m, |resp Vertical.AvR (outV o) m j| ≤ PV o j) ∧
    (∀ o j N, ∑ m ∈ Finset.range N, |resp Vertical.AvR (outV o) m j| ≤ GV o j) ∧
    (∀ o j m, |resp Horizontal.AhR (outH o) m j| ≤ PH o j) ∧
    (∀ o j N, ∑ m ∈ Finset.range N, |resp Horizontal.AhR (outH o) m j| ≤ GH o j) :=
  ⟨peakV_cert, gainV_cert, peakH_cert, gainH_cert⟩

/-! ## Tools for the nominal fields

The nominal of the induction is the model's response to the run's actual target plus the
structured inputs. It splits into the response to the target (`errResp`, which the certificates
bound for the ideal references) and the response to the structured input. The latter, and any
small deviation of the forcing from a certified reference, is bounded through the certified gains
(`forced_outV`, `forced_outH`).
-/

theorem nomV_split (I : Iface) (w₀ : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) :
    nomV I w₀ x t = Vertical.errResp (refV w₀ x) t + Vertical.traj Vertical.AvR 0 (I.wVs x) t := by
  have h := Vertical.traj_add Vertical.AvR 0 0 (Vertical.forceOf (refV w₀ x)) (I.wVs x) t
  rw [add_zero] at h
  simpa [nomV, Vertical.errResp] using h

theorem nomH_split (I : Iface) (w₀ : Vehicle.World) (x : ℕ → Mission.X) (a : Fin 2) (t : ℕ) :
    nomH I w₀ x a t = Horizontal.errResp (refH w₀ x a) t +
      Vertical.traj Horizontal.AhR 0 (fun k => I.etaHat x k a • eAcc) t := by
  have h := Vertical.traj_add Horizontal.AhR 0 0 (Horizontal.forceOf (refH w₀ x a))
    (fun k => I.etaHat x k a • eAcc) t
  rw [add_zero] at h
  simpa [nomH, Horizontal.errResp] using h

/-- **Forced response of the vertical model through the certified gains**: an input bounded by
`ε` per coordinate moves each watched output by at most `Σⱼ GV o j εⱼ`. -/
theorem forced_outV (u : ℕ → Fin 8 → ℝ) (ε : Fin 8 → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (hu : ∀ k j, |u k j| ≤ ε j) (o : Fin 5) (t : ℕ) :
    |outV o ⬝ᵥ Vertical.traj Vertical.AvR 0 u t| ≤ ∑ j, GV o j * ε j := by
  have h := tube_out Vertical.AvR (Vertical.traj Vertical.AvR 0 u) u 0 t
    (fun k _ => Vertical.traj_succ _ _ _ k) (outV o) 0 ε (PV o) (GV o) hε (fun j => by simp)
    (fun k _ j => by simpa using hu k j) (fun j m => peakV_cert o j m) (fun j N => gainV_cert o j N)
  simpa using h

/-- The same for a horizontal axis. -/
theorem forced_outH (u : ℕ → Fin 9 → ℝ) (ε : Fin 9 → ℝ) (hε : ∀ j, 0 ≤ ε j)
    (hu : ∀ k j, |u k j| ≤ ε j) (o : Fin 5) (t : ℕ) :
    |outH o ⬝ᵥ Vertical.traj Horizontal.AhR 0 u t| ≤ ∑ j, GH o j * ε j := by
  have h := tube_out Horizontal.AhR (Vertical.traj Horizontal.AhR 0 u) u 0 t
    (fun k _ => Vertical.traj_succ _ _ _ k) (outH o) 0 ε (PH o) (GH o) hε (fun j => by simp)
    (fun k _ j => by simpa using hu k j) (fun j m => peakH_cert o j m) (fun j N => gainH_cert o j N)
  simpa using h

/-! ## The corner budget with the certified vertical nominal -/

/-- The certified vertical bounds at `w₁ … w₆` (`Corner.vz_w1 … vz_w6`). -/
def vzC : Fin 6 → ℝ := ![517 / 25000, 57 / 25000, 219 / 50000, 99 / 12500, 767 / 100000, 143 / 25000]

/-- **The 3D corner budget** of the coordinator: with the per-corner planar bound of
`Horizontal.corner_vehicle_per_105` (`BB i / 10⁵ + 2·10⁻⁷`), the alignment `0.0025 + 0.007`, the
corner's vertical offset `0.0131` and the certified vertical nominal `vzC i`,
`√((P + 0.0095)² + (0.0131 + vz)²) ≤ 0.0954` at every corner (slack 1.22, 5.10, 4.31, 2.74, 3.91,
4.60 mm). -/
theorem corner_budget (i : Fin 6) :
    ((Horizontal.BB i : ℝ) / 100000 + 2 / 10 ^ 7 + 25 / 10000 + 7 / 1000) ^ 2 + (131 / 10000 + vzC i) ^ 2 ≤
      (954 / 10000) ^ 2 := by
  fin_cases i <;> norm_num [Horizontal.BB, vzC]

end

end Contracts.Track.Induction.Nominal
