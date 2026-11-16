import Contracts.Track.Vertical

/-!
# The vertical channel at `PSC_D_ACC_P = 0.25` (the 3D leg theorem, REACH.md §10)

The vertical model of `Vertical.lean` with the acceleration loop's proportional gain
`PSC_D_ACC_P = 0.25` (the float32 `0.25` is exact) instead of `0.05`; everything else (the state
order `(ez, ev, eV, eA, I, f, u, w)`, the filter coefficients, `PSC_D_POS_P = 1`, `PSC_D_VEL_P = 5`,
`PSC_D_ACC_I · dt`, the plant) is `Vertical.lean`'s, whose constants are reused. Only `rowU` and
the last entry of `B_v` contain `kpAcc`. `tick_eq` and `errOf_absTick` are the same statements as
in `Vertical.lean`; the error coordinates `Vertical.errOf` do not depend on the gain.
-/

namespace Contracts.Track.VerticalHi

open Matrix Finset Contracts.Track.Vertical

/-- `PSC_D_ACC_P = 0.25f` (exact). -/
def kpAcc : ℚ := 1 / 4

/-- New `_throttle_in` deviation `-(kpAcc eA' + I')`. -/
def rowU : Fin 8 → ℚ := fun j => -(kpAcc * rowEA j + rowI j)

/-- `A_v` at `PSC_D_ACC_P = 0.25`: state `(ez, ev, eV, eA, I, f, u, w)`. -/
def Av : Matrix (Fin 8) (Fin 8) ℚ := Matrix.of ![rowEz, rowEv, rowEV, rowEA, rowI, rowAct, rowU, rowAct]

/-- `B_v` at `PSC_D_ACC_P = 0.25`. -/
def Bv : Fin 8 → ℚ :=
  ![-(per ^ 2 / 2), -per, 0, αA, kiDt * αA, 0, -(kpAcc * αA + kiDt * αA), 0]

noncomputable def AvR : Matrix (Fin 8) (Fin 8) ℝ := Av.map (fun q : ℚ => (q : ℝ))
noncomputable def BvR : Fin 8 → ℝ := fun i => (Bv i : ℝ)

/-- One tick of the vertical channel in error coordinates (as `Vertical.tick`, with `kpAcc = 1/4`). -/
noncomputable def tick (x : Fin 8 → ℝ) (a d₁ d₂ : ℝ) : Fin 8 → ℝ :=
  let act : ℝ := x 5 + (αT : ℝ) * (x 6 - x 5)
  let eV' : ℝ := x 2 + (αV : ℝ) * ((-((kpPos : ℝ) * x 0) - x 1) - x 2)
  let eA' : ℝ := x 3 + (αA : ℝ) * (((kpVel : ℝ) * eV' + a) - (-((amax : ℝ) * x 7)) - x 3)
  let I' : ℝ := x 4 + (kiDt : ℝ) * eA'
  let u' : ℝ := -((kpAcc : ℝ) * eA' + I')
  let acc : ℝ := -((amax : ℝ) * act)
  ![x 0 + (per : ℝ) * x 1 + (per : ℝ) ^ 2 / 2 * (acc - a) - d₁,
    x 1 + (per : ℝ) * (acc - a) - d₂, eV', eA', I', act, u', act]

/-- **The tick is the linear system `(A_v, B_v)`.** -/
theorem tick_eq (x : Fin 8 → ℝ) (a d₁ d₂ : ℝ) :
    tick x a d₁ d₂ = AvR *ᵥ x + (a • BvR - d₁ • Vertical.e0 - d₂ • Vertical.e1) := by
  ext i
  fin_cases i <;>
    simp [tick, AvR, BvR, Av, Bv, rowEz, rowEv, rowEV, rowEA, rowI, rowU, rowAct, Vertical.e0,
      Vertical.e1, mulVec, dotProduct, Fin.sum_univ_eight] <;>
    ring

/-- One tick of the code's variables with target `(sp, vsp, asp)` at `PSC_D_ACC_P = 0.25`. -/
noncomputable def absTick (s : VAbs) (sp vsp asp : ℝ) : VAbs :=
  let act : ℝ := s.f + (αT : ℝ) * (s.u - s.f)
  let vt : ℝ := (kpPos : ℝ) * (sp - s.z) + vsp
  let eV' : ℝ := s.eV + (αV : ℝ) * ((vt - s.vz) - s.eV)
  let atgt : ℝ := (kpVel : ℝ) * eV' + asp
  let am : ℝ := -((amax : ℝ) * s.w)
  let eA' : ℝ := s.eA + (αA : ℝ) * ((atgt - am) - s.eA)
  let I' : ℝ := s.I + (kiDt : ℝ) * eA'
  let u' : ℝ := -((kpAcc : ℝ) * eA' + I')
  let acc : ℝ := -((amax : ℝ) * act)
  { z := s.z + (per : ℝ) * s.vz + (per : ℝ) ^ 2 / 2 * acc, vz := s.vz + (per : ℝ) * acc,
    eV := eV', eA := eA', I := I', f := act, u := u', w := act }

/-- **Change of coordinates** (as `Vertical.errOf_absTick`). -/
theorem errOf_absTick (s : VAbs) (sp vsp asp sp' vsp' : ℝ) :
    errOf (absTick s sp vsp asp) sp' vsp' =
      tick (errOf s sp vsp) asp (defect₁ sp sp' vsp asp) (defect₂ vsp vsp' asp) := by
  ext i
  fin_cases i <;>
    simp [errOf, absTick, tick, defect₁, defect₂, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
    ring

/-- The reference forcing of a target sequence `r = (sp, vsp, asp)` at tick `k`. -/
noncomputable def forceOf (r : ℕ → ℝ × ℝ × ℝ) (k : ℕ) : Fin 8 → ℝ :=
  (r k).2.2 • BvR - defect₁ (r k).1 (r (k + 1)).1 (r k).2.1 (r k).2.2 • Vertical.e0 -
    defect₂ (r k).2.1 (r (k + 1)).2.1 (r k).2.2 • Vertical.e1

/-- **The acceleration shift**: `vAccV = (0, 0, 0, 0, 1/amax, -1/amax, -1/amax, -1/amax)` is the
steady state of a constant target acceleration (zero errors, the throttle at `asp/amax`):
`A_v vAccV + B_v = vAccV`. -/
noncomputable def vAccV : Fin 8 → ℝ :=
  ![0, 0, 0, 0, 1 / (amax : ℝ), -1 / (amax : ℝ), -1 / (amax : ℝ), -1 / (amax : ℝ)]

theorem Av_vAccV : AvR *ᵥ vAccV + BvR = vAccV := by
  have ha : (amax : ℝ) ≠ 0 := by norm_num [amax, tw, grav]
  ext i
  fin_cases i <;>
    simp [AvR, BvR, Av, Bv, rowEz, rowEv, rowEV, rowEA, rowI, rowU, rowAct, vAccV, mulVec,
      dotProduct, Fin.sum_univ_eight] <;>
    field_simp <;>
    ring

end Contracts.Track.VerticalHi
