import Contracts.Track.CtrlVerticalWorld

/-!
# `vertical_tick_eq`: one `Vehicle.tick` on the vertical channel is the model's tick plus `w`

The join of the C-lemmas (C1, C5, C6, C7, C12 of `CtrlVertical{PID,IO,D}.lean`) with the real
model of `VERTICAL.md` (`Contracts/Track/Vertical.lean`):

* `vtick_real` (real numbers only): if the code's values of one tick (`VVals`) satisfy the code
  relations with their `β` (`VRel`), then `ξ' - tick ξ asp d₁ d₂` is bounded componentwise by
  `βvec`, where `tick ξ a d₁ d₂ = A_v ξ + a B_v - d₁ e₀ - d₂ e₁` (`tick_eq`);
* `vertical_tick_eq` (the code): for one `Vehicle.tick` of Auto mode, the state vector read off the
  worlds (`vstate`) satisfies the same bound, with `VRel` discharged from the C-lemmas and the
  frames of `CtrlVerticalWorld.lean`.

The hypotheses not discharged here are listed in `CTRL_VERTICAL.md`: the navigator's frame
(`NavV`), the region (`DPar`, `DReg`, `DInp`, `MotReg`, `BoostReg`, ...) and the mixer's identity
(`hmix`, C12 second half).
-/

namespace Contracts.Track.CtrlV

open Contracts.Track.Vertical Contracts.Mission

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

noncomputable section

/-- The values on the vertical channel at one tick, in the order of `Vehicle.tick`: the plant's
position and velocity (`z vz`), the sample the code reads (`zs vzs`), the navigator's target
(`sp vsp asp`), the controller state at the start of the tick (`eV eA I f u`, the mean actuator
`held` of the period that ended), what the tick computes (`vt eV' atg am eA' I' thr u' f'
held'`), the next plant state (`z' vz'`), the next target (`sp' vsp'`), the hover throttle `hov`,
the measured specific force `acc` and the target thrust angle `θ` of the boost. -/
structure VVals where
  z : ℝ
  vz : ℝ
  zs : ℝ
  vzs : ℝ
  sp : ℝ
  vsp : ℝ
  asp : ℝ
  eV : ℝ
  eA : ℝ
  I : ℝ
  f : ℝ
  u : ℝ
  held : ℝ
  hov : ℝ
  acc : ℝ
  θ : ℝ
  vt : ℝ
  eV' : ℝ
  atg : ℝ
  am : ℝ
  eA' : ℝ
  I' : ℝ
  thr : ℝ
  u' : ℝ
  f' : ℝ
  held' : ℝ
  z' : ℝ
  vz' : ℝ
  sp' : ℝ
  vsp' : ℝ

namespace VVals

variable (v : VVals)

/-- The trim of the hover throttle: the integrator's equilibrium is `hover - 1/2.25`. -/
def Itr : ℝ := v.hov - 1 / (9 / 4)

/-- The vertical state of `VERTICAL.md` at the start of the tick. -/
def ξ : Fin 8 → ℝ :=
  ![v.z - v.sp, v.vz - v.vsp, v.eV, v.eA, v.I - v.Itr, v.f - 1 / (9 / 4), v.u - 1 / (9 / 4),
    v.held - 1 / (9 / 4)]

/-- The vertical state after the tick. -/
def ξ' : Fin 8 → ℝ :=
  ![v.z' - v.sp', v.vz' - v.vsp', v.eV', v.eA', v.I' - v.Itr, v.f' - 1 / (9 / 4),
    v.u' - 1 / (9 / 4), v.held' - 1 / (9 / 4)]

/-- The plant residuals: the next sample against the exact vertical double integrator with the
linear thrust `-amax · (held' - 1/2.25)`. -/
def ρz : ℝ := v.z' - (v.z + (per : ℝ) * v.vz + (per : ℝ) ^ 2 / 2 * (-((amax : ℝ) * (v.held' - 1 / (9 / 4)))))
def ρv : ℝ := v.vz' - (v.vz + (per : ℝ) * (-((amax : ℝ) * (v.held' - 1 / (9 / 4)))))
/-- The specific-force residual of the sample: `acc + 9.80665016f + amax (held - 1/2.25)` (zero
for the level, exact plant up to the trim of `g`). -/
def ρam : ℝ := v.acc + gfR + (amax : ℝ) * (v.held - 1 / (9 / 4))
/-- The angle boost's deviation: `u' = -thr / cos θ` against `-thr`. -/
def τ : ℝ := (-v.thr) * (1 / Real.cos v.θ - 1)

end VVals

/-- The error bounds of the code relations (the `β`s of C1-C12). -/
structure VErr where
  smp : ℝ
  vt : ℝ
  V : ℝ
  atg : ℝ
  am : ℝ
  E : ℝ
  I : ℝ
  N : ℝ
  b : ℝ
  f : ℝ
  mix : ℝ

/-- The code relations of one tick (C5, C6, C7, C12 with their `β`). -/
structure VRel (v : VVals) (e : VErr) : Prop where
  smp : |v.z - v.zs| + |v.vz - v.vzs| ≤ e.smp
  vt : |v.vt - ((v.sp - v.zs) + v.vsp)| ≤ e.vt
  V : |v.eV' - (v.eV + (αV : ℝ) * ((v.vt - v.vzs) - v.eV))| ≤ e.V
  atg : |v.atg - (5 * v.eV' + v.asp)| ≤ e.atg
  am : |v.am - (v.acc + gfR)| ≤ e.am
  E : |v.eA' - (v.eA + (αA : ℝ) * ((v.atg - v.am) - v.eA))| ≤ e.E
  I : |v.I' - (v.I + (kiDt : ℝ) * v.eA')| ≤ e.I
  N : |v.thr - ((kpAcc : ℝ) * v.eA' + v.I' - v.hov)| ≤ e.N
  b : |v.u' - (-v.thr) / Real.cos v.θ| ≤ e.b
  f : |v.f' - (v.f + (αT : ℝ) * (v.u - v.f))| ≤ e.f
  mix : |v.held' - v.f'| ≤ e.mix

/-- The componentwise bound of the disturbance: `W2`, `W3`, `W4` are the bounds of the velocity
filter, acceleration filter and integrator rows. -/
def VErr.W2 (e : VErr) : ℝ := (αV : ℝ) * (e.vt + e.smp) + e.V
def VErr.W3 (e : VErr) (ρam : ℝ) : ℝ := (αA : ℝ) * (5 * e.W2 + e.atg + e.am + |ρam|) + e.E
def VErr.W4 (e : VErr) (ρam : ℝ) : ℝ := (kiDt : ℝ) * e.W3 ρam + e.I

/-- The bound vector of `vtick_real`. -/
def βvec (v : VVals) (e : VErr) : Fin 8 → ℝ :=
  ![|v.ρz| + (per : ℝ) ^ 2 / 2 * (amax : ℝ) * (e.f + e.mix),
    |v.ρv| + (per : ℝ) * (amax : ℝ) * (e.f + e.mix),
    e.W2, e.W3 v.ρam, e.W4 v.ρam, e.f,
    (kpAcc : ℝ) * e.W3 v.ρam + e.W4 v.ρam + e.N + |v.τ| + e.b,
    e.f + e.mix]

theorem αV_pos : (0 : ℝ) ≤ (αV : ℝ) := by simp [αV]; norm_num
theorem αA_pos : (0 : ℝ) ≤ (αA : ℝ) := by simp [αA]; norm_num
theorem kiDt_pos : (0 : ℝ) ≤ (kiDt : ℝ) := by simp [kiDt]; norm_num
theorem kpAcc_pos : (0 : ℝ) ≤ (kpAcc : ℝ) := by simp [kpAcc]; norm_num
theorem amax_pos : (0 : ℝ) ≤ (amax : ℝ) := by simp [amax, tw, grav]; norm_num
theorem kpPos_one : (kpPos : ℝ) = 1 := by simp [kpPos]
theorem kpVel_five : (kpVel : ℝ) = 5 := by simp [kpVel]

/-- **The join, in real numbers.** If the code's values of one tick satisfy the code relations
(the C-lemmas with their `β`), then the vertical state moves by the model's tick (`tick`, i.e.
`A_v ξ + asp B_v - d₁ e₀ - d₂ e₁` by `tick_eq`) plus a disturbance bounded componentwise by
`βvec`. -/
theorem vtick_real (v : VVals) (e : VErr) (h : VRel v e) (i : Fin 8) :
    |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp)) i| ≤
      βvec v e i := by
  have aV := αV_pos; have aA := αA_pos; have ki := kiDt_pos; have kp := kpAcc_pos
  have am := amax_pos
  -- the signed errors
  set εvt := v.vt - ((v.sp - v.zs) + v.vsp)
  set εV := v.eV' - (v.eV + (αV : ℝ) * ((v.vt - v.vzs) - v.eV))
  set εat := v.atg - (5 * v.eV' + v.asp)
  set εam := v.am - (v.acc + gfR)
  set εE := v.eA' - (v.eA + (αA : ℝ) * ((v.atg - v.am) - v.eA))
  set εI := v.I' - (v.I + (kiDt : ℝ) * v.eA')
  set εN := v.thr - ((kpAcc : ℝ) * v.eA' + v.I' - v.hov)
  set εb := v.u' - (-v.thr) / Real.cos v.θ
  set εf := v.f' - (v.f + (αT : ℝ) * (v.u - v.f))
  set εm := v.held' - v.f'
  -- the rows
  set w2 := (αV : ℝ) * (εvt + (v.z - v.zs) + (v.vz - v.vzs)) + εV with hw2
  set w3 := (αA : ℝ) * (5 * w2 + εat - εam - v.ρam) + εE with hw3
  set w4 := (kiDt : ℝ) * w3 + εI with hw4
  have b2 : |w2| ≤ e.W2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg aV, VErr.W2]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ aV) h.V
    have hvt : |εvt| ≤ e.vt := h.vt
    have hs := h.smp
    have t1 := abs_add_le (εvt + (v.z - v.zs)) (v.vz - v.vzs)
    have t2 := abs_add_le εvt (v.z - v.zs)
    linarith
  have b3 : |w3| ≤ e.W3 v.ρam := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg aA, VErr.W3]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ aA) h.E
    have hat : |εat| ≤ e.atg := h.atg
    have ham : |εam| ≤ e.am := h.am
    have t1 := abs_add_le (5 * w2 + εat) (-εam - v.ρam)
    have t2 := abs_add_le (5 * w2) εat
    have t3 := abs_sub (-εam) v.ρam
    rw [abs_neg] at t3
    rw [abs_mul, show |(5 : ℝ)| = 5 by norm_num] at t2
    rw [show 5 * w2 + εat - εam - v.ρam = (5 * w2 + εat) + (-εam - v.ρam) by ring]
    linarith
  have b4 : |w4| ≤ e.W4 v.ρam := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg ki, VErr.W4]
    exact add_le_add (mul_le_mul_of_nonneg_left b3 ki) h.I
  have bfm : |εf + εm| ≤ e.f + e.mix := (abs_add_le _ _).trans (add_le_add h.f h.mix)
  fin_cases i
  · -- position error
    have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp)) 0 = v.ρz + (per : ℝ) ^ 2 / 2 * (-(amax : ℝ)) * (εf + εm) := by
      simp [VVals.ξ', VVals.ξ, tick, defect₁, VVals.ρz, εf, εm]; ring
    simp only [Fin.zero_eta, Fin.isValue] at this ⊢
    rw [this, βvec]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg am, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (per : ℝ) ^ 2 / 2)]
    simp only [Matrix.cons_val_zero]
    have := mul_le_mul_of_nonneg_left bfm (by positivity : (0 : ℝ) ≤ (per : ℝ) ^ 2 / 2 * (amax : ℝ))
    linarith
  · -- velocity error
    have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp)) 1 = v.ρv + (per : ℝ) * (-(amax : ℝ)) * (εf + εm) := by
      simp [VVals.ξ', VVals.ξ, tick, defect₂, VVals.ρv, εf, εm]; ring
    simp only [Fin.mk_one, Fin.isValue] at this ⊢
    rw [this, βvec]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg am, abs_of_nonneg (by simp [per] : (0 : ℝ) ≤ (per : ℝ))]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    have := mul_le_mul_of_nonneg_left bfm (by simp [per, amax, tw, grav]; norm_num : (0 : ℝ) ≤ (per : ℝ) * (amax : ℝ))
    linarith
  · -- velocity filter
    have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp)) 2 = w2 := by
      simp [VVals.ξ', VVals.ξ, tick, hw2, εvt, εV, kpPos_one]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp)) 2| ≤ βvec v e 2
    rw [this]; simpa [βvec] using b2
  · -- acceleration filter
    have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp)) 3 = w3 := by
      simp [VVals.ξ', VVals.ξ, tick, hw3, hw2, εvt, εV, εat, εam, εE, VVals.ρam, kpPos_one,
        kpVel_five]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp)) 3| ≤ βvec v e 3
    rw [this]; simpa [βvec] using b3
  · -- integrator
    have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp)) 4 = w4 := by
      simp [VVals.ξ', VVals.ξ, tick, hw4, hw3, hw2, εvt, εV, εat, εam, εE, εI, VVals.ρam,
        VVals.Itr, kpPos_one, kpVel_five]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp)) 4| ≤ βvec v e 4
    rw [this]; simpa [βvec] using b4
  · -- throttle filter
    have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp)) 5 = εf := by
      simp [VVals.ξ', VVals.ξ, tick, εf]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp)) 5| ≤ βvec v e 5
    rw [this]; simpa [βvec] using h.f
  · -- throttle command
    have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp)) 6 = v.τ + εb - εN - (kpAcc : ℝ) * w3 - w4 := by
      simp [VVals.ξ', VVals.ξ, tick, hw4, hw3, hw2, εvt, εV, εat, εam, εE, εI, εN, εb, VVals.τ,
        VVals.ρam, VVals.Itr, kpPos_one, kpVel_five]
      ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp)) 6| ≤ βvec v e 6
    rw [this]
    have hN : |εN| ≤ e.N := h.N
    have hb : |εb| ≤ e.b := h.b
    have t1 := abs_sub (v.τ + εb - εN - (kpAcc : ℝ) * w3) w4
    have t2 := abs_sub (v.τ + εb - εN) ((kpAcc : ℝ) * w3)
    have t3 := abs_sub (v.τ + εb) εN
    have t4 := abs_add_le v.τ εb
    rw [abs_mul, abs_of_nonneg kp] at t2
    have := mul_le_mul_of_nonneg_left b3 kp
    simp only [βvec]
    show _ ≤ (kpAcc : ℝ) * e.W3 v.ρam + e.W4 v.ρam + e.N + |v.τ| + e.b
    linarith
  · -- held actuator
    have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp)) 7 = εf + εm := by
      simp [VVals.ξ', VVals.ξ, tick, εf, εm]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp)) 7| ≤ βvec v e 7
    rw [this]; simpa [βvec] using bfm


/-- **The structured part of the disturbance**: the plant residuals `ρz`, `ρv`, the sample's
specific-force residual `ρam` (tilt coupling, trim of `g`) through the acceleration filter, and the
boost's deviation `τ`, each with its exact coefficient. -/
def wS (v : VVals) : Fin 8 → ℝ :=
  ![v.ρz, v.ρv, 0, -((αA : ℝ) * v.ρam), -((kiDt : ℝ) * ((αA : ℝ) * v.ρam)), 0,
    v.τ + ((kpAcc : ℝ) + (kiDt : ℝ)) * ((αA : ℝ) * v.ρam), 0]

/-- The bounds of the code's part (rounding, `PiF32`-exact coefficients, the mixer, the sample). -/
def VErr.W3c (e : VErr) : ℝ := (αA : ℝ) * (5 * e.W2 + e.atg + e.am) + e.E
def VErr.W4c (e : VErr) : ℝ := (kiDt : ℝ) * e.W3c + e.I

def βcode (e : VErr) : Fin 8 → ℝ :=
  ![(per : ℝ) ^ 2 / 2 * (amax : ℝ) * (e.f + e.mix), (per : ℝ) * (amax : ℝ) * (e.f + e.mix),
    e.W2, e.W3c, e.W4c, e.f, (kpAcc : ℝ) * e.W3c + e.W4c + e.N + e.b, e.f + e.mix]

/-- **The join with the structured part split off**: `ξ' - tick ξ - wS` is bounded by the code's
`β`s alone (`βcode`). This is the form for an induction that carries `wS` in its nominal. -/
theorem vtick_split (v : VVals) (e : VErr) (h : VRel v e) (i : Fin 8) :
    |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) i| ≤
      βcode e i := by
  have aV := αV_pos; have aA := αA_pos; have ki := kiDt_pos; have kp := kpAcc_pos
  have am := amax_pos
  set εvt := v.vt - ((v.sp - v.zs) + v.vsp)
  set εV := v.eV' - (v.eV + (αV : ℝ) * ((v.vt - v.vzs) - v.eV))
  set εat := v.atg - (5 * v.eV' + v.asp)
  set εam := v.am - (v.acc + gfR)
  set εE := v.eA' - (v.eA + (αA : ℝ) * ((v.atg - v.am) - v.eA))
  set εI := v.I' - (v.I + (kiDt : ℝ) * v.eA')
  set εN := v.thr - ((kpAcc : ℝ) * v.eA' + v.I' - v.hov)
  set εb := v.u' - (-v.thr) / Real.cos v.θ
  set εf := v.f' - (v.f + (αT : ℝ) * (v.u - v.f))
  set εm := v.held' - v.f'
  set w2 := (αV : ℝ) * (εvt + (v.z - v.zs) + (v.vz - v.vzs)) + εV with hw2
  set w3 := (αA : ℝ) * (5 * w2 + εat - εam) + εE with hw3
  set w4 := (kiDt : ℝ) * w3 + εI with hw4
  have b2 : |w2| ≤ e.W2 := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg aV, VErr.W2]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ aV) h.V
    have hvt : |εvt| ≤ e.vt := h.vt
    have hs := h.smp
    have t1 := abs_add_le (εvt + (v.z - v.zs)) (v.vz - v.vzs)
    have t2 := abs_add_le εvt (v.z - v.zs)
    linarith
  have b3 : |w3| ≤ e.W3c := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg aA, VErr.W3c]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ aA) h.E
    have hat : |εat| ≤ e.atg := h.atg
    have ham : |εam| ≤ e.am := h.am
    have t1 := abs_sub (5 * w2 + εat) εam
    have t2 := abs_add_le (5 * w2) εat
    rw [abs_mul, show |(5 : ℝ)| = 5 by norm_num] at t2
    linarith
  have b4 : |w4| ≤ e.W4c := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg ki, VErr.W4c]
    exact add_le_add (mul_le_mul_of_nonneg_left b3 ki) h.I
  have bfm : |εf + εm| ≤ e.f + e.mix := (abs_add_le _ _).trans (add_le_add h.f h.mix)
  fin_cases i
  · have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp) - wS v) 0 = (per : ℝ) ^ 2 / 2 * (-(amax : ℝ)) * (εf + εm) := by
      simp [VVals.ξ', VVals.ξ, tick, defect₁, VVals.ρz, εf, εm, wS]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) 0| ≤ βcode e 0
    rw [this, βcode, abs_mul, abs_mul, abs_neg, abs_of_nonneg am,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (per : ℝ) ^ 2 / 2)]
    simp only [Matrix.cons_val_zero]
    have := mul_le_mul_of_nonneg_left bfm (by positivity : (0 : ℝ) ≤ (per : ℝ) ^ 2 / 2 * (amax : ℝ))
    linarith
  · have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp) - wS v) 1 = (per : ℝ) * (-(amax : ℝ)) * (εf + εm) := by
      simp [VVals.ξ', VVals.ξ, tick, defect₂, VVals.ρv, εf, εm, wS]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) 1| ≤ βcode e 1
    rw [this, βcode, abs_mul, abs_mul, abs_neg, abs_of_nonneg am,
      abs_of_nonneg (by simp [per] : (0 : ℝ) ≤ (per : ℝ))]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    have := mul_le_mul_of_nonneg_left bfm (by simp [per, amax, tw, grav]; norm_num : (0 : ℝ) ≤ (per : ℝ) * (amax : ℝ))
    linarith
  · have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp) - wS v) 2 = w2 := by
      simp [VVals.ξ', VVals.ξ, tick, hw2, εvt, εV, kpPos_one, wS]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) 2| ≤ βcode e 2
    rw [this]; simpa [βcode] using b2
  · have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp) - wS v) 3 = w3 := by
      simp [VVals.ξ', VVals.ξ, tick, hw3, hw2, εvt, εV, εat, εam, εE, VVals.ρam, kpPos_one,
        kpVel_five, wS]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) 3| ≤ βcode e 3
    rw [this]; simpa [βcode] using b3
  · have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp) - wS v) 4 = w4 := by
      simp [VVals.ξ', VVals.ξ, tick, hw4, hw3, hw2, εvt, εV, εat, εam, εE, εI, VVals.ρam,
        VVals.Itr, kpPos_one, kpVel_five, wS]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) 4| ≤ βcode e 4
    rw [this]; simpa [βcode] using b4
  · have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp) - wS v) 5 = εf := by
      simp [VVals.ξ', VVals.ξ, tick, εf, wS]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) 5| ≤ βcode e 5
    rw [this]; simpa [βcode] using h.f
  · have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp) - wS v) 6 = εb - εN - (kpAcc : ℝ) * w3 - w4 := by
      simp [VVals.ξ', VVals.ξ, tick, hw4, hw3, hw2, εvt, εV, εat, εam, εE, εI, εN, εb, VVals.τ,
        VVals.ρam, VVals.Itr, kpPos_one, kpVel_five, wS]
      ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) 6| ≤ βcode e 6
    rw [this]
    have hN : |εN| ≤ e.N := h.N
    have hb : |εb| ≤ e.b := h.b
    have t1 := abs_sub (εb - εN - (kpAcc : ℝ) * w3) w4
    have t2 := abs_sub (εb - εN) ((kpAcc : ℝ) * w3)
    have t3 := abs_sub εb εN
    rw [abs_mul, abs_of_nonneg kp] at t2
    have := mul_le_mul_of_nonneg_left b3 kp
    simp only [βcode]
    show _ ≤ (kpAcc : ℝ) * e.W3c + e.W4c + e.N + e.b
    linarith
  · have : (v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp)
        (defect₂ v.vsp v.vsp' v.asp) - wS v) 7 = εf + εm := by
      simp [VVals.ξ', VVals.ξ, tick, εf, εm, wS]; ring
    show |(v.ξ' - tick v.ξ v.asp (defect₁ v.sp v.sp' v.vsp v.asp) (defect₂ v.vsp v.vsp' v.asp) - wS v) 7| ≤ βcode e 7
    rw [this]; simpa [βcode] using bfm

/-! ## The world-level tick -/

open Vehicle

/-- The hover throttle the position controller reads. -/
def hovF (mp : AP_Motors_lib.AP_MotorsMatrix.Params) : Float32 :=
  AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover mp

/-- **The vertical state of `VERTICAL.md` §1, read off the code** at a tick boundary: the
sampled position and velocity against the navigator's target, the velocity and acceleration
error filters, the acceleration integrator against its trim `hover - 1/2.25`, the throttle filter
and `_throttle_in` of the motors, and the mean actuator `held` of the period that ended. -/
def vstate (w : World) (z vz held sp vsp : ℝ) : Fin 8 → ℝ :=
  ![z - sp, vz - vsp, w.ps._pid_vel_d_m._error.toReal, w.ps._pid_accel_d_m._error.toReal,
    w.ps._pid_accel_d_m._integrator.toReal - ((hovF w.mp).toReal - 1 / (9 / 4)),
    w.ms._throttle_filter.output.toReal - 1 / (9 / 4), w.ms._throttle_in.toReal - 1 / (9 / 4),
    held - 1 / (9 / 4)]

/-- The mean of the four actuators a tick returns. -/
def meanAct (a : Array Float32) : ℝ :=
  (a[0]!.toReal + a[1]!.toReal + a[2]!.toReal + a[3]!.toReal) / 4

/-- The navigator's world inside `wp_run` (after `update_wpnav` and its calls into the position
controller), on a tick of Auto mode. -/
def navOf (w : World) (smp : Sample) : World :=
  navW (mission_update (preAuto (postMot (preMot w smp)) smp))


/-! ### The stages' frames -/

theorem withMotors_au (w : World) f : (withMotors w f).au = w.au := by
  unfold withMotors; rcases f (attOutputs w.ms) with ⟨a, o⟩; rfl
theorem withMotors_mp (w : World) f : (withMotors w f).mp = w.mp := by
  unfold withMotors; rcases f (attOutputs w.ms) with ⟨a, o⟩; rfl

/-- The period of a tick after the first, `2500 µs · 1e-6f = 0.0025f`. -/
theorem dt_tick (smp : Sample) (hdt : smp.dt_us = 2500) :
    (smp.dt_us.toFloat32 * (1.0e-6 : Float32)).IsFinite ∧
      (smp.dt_us.toFloat32 * (1.0e-6 : Float32)).toReal = dtR := by
  rw [hdt]
  have h : ((2500 : UInt64).toFloat32 * (1.0e-6 : Float32)).toModel.unpack =
      .finite .positive 10737418 (-32) (by decide) := by f32_unpack
  refine ⟨Float32.isFinite_of_unpack h, ?_⟩
  rw [Float32.toReal_of_unpack h, dtR]; simp [Float.Model.UnpackedFloat.Sign.apply]; norm_num

/-- The period `preMot` sets. -/
def tPer (w : World) (smp : Sample) : Float32 :=
  if (w.ticks32 == 0) = true then (1.0 : Float32) / (400.0 : Float32) else smp.dt_us.toFloat32 * (1.0e-6 : Float32)

theorem tPer_eq (w : World) (smp : Sample) (ht0 : w.ticks32 ≠ 0) :
    tPer w smp = smp.dt_us.toFloat32 * (1.0e-6 : Float32) := by
  have : (w.ticks32 == 0) = false := by simpa using ht0
  simp [tPer, this]

theorem preMot_ps (w : World) (smp : Sample) :
    (preMot w smp).ps = AC_PosControl_lib.AC_PosControl.set_dt_s w.ps (tPer w smp) := by
  unfold preMot; dsimp only; rw [withMotors_ps]; rfl
theorem preMot_mp (w : World) (smp : Sample) : (preMot w smp).mp = w.mp := by
  unfold preMot; dsimp only; rw [withMotors_mp]
theorem preMot_au (w : World) (smp : Sample) : (preMot w smp).au = w.au := by
  unfold preMot; dsimp only; rw [withMotors_au]
theorem preMot_ms (w : World) (smp : Sample) : ∃ o : AC_Attitude_lib.AC_AttitudeControl_Multi.Outputs,
    (preMot w smp).ms = applyAtt (AP_Motors_lib.AP_MotorsMatrix.set_dt_s w.ms (tPer w smp)) o ∧
    o.set_throttle = w.ms._throttle_in ∧ o.set_throttle_filter_cutoff = w.ms._throttle_filter.cutoff_freq := by
  unfold preMot; dsimp only; rw [withMotors_ms]
  exact ⟨_, rfl, rate_thr _ _ _ _⟩

theorem postMot_ps (w : World) : (postMot w).ps = w.ps := rfl
theorem postMot_au (w : World) : (postMot w).au = w.au := rfl
theorem postMot_ms (w : World) :
    (postMot w).ms = (AP_Motors_lib.AP_MotorsMatrix.output w.mp w.ms #[] (motorsInputs w)).2.1 := rfl
theorem postMot_mp (w : World) :
    (postMot w).mp = (AP_Motors_lib.AP_MotorsMatrix.output w.mp w.ms #[] (motorsInputs w)).1 := rfl

theorem preAuto_ms (w : World) (smp : Sample) : (preAuto w smp).ms = w.ms := rfl
theorem preAuto_mp (w : World) (smp : Sample) : (preAuto w smp).mp = w.mp := rfl
theorem preAuto_au (w : World) (smp : Sample) : (preAuto w smp).au = w.au := rfl
theorem preAuto_sample (w : World) (smp : Sample) :
    (preAuto w smp).sample = { smp with gyro := w.sample.gyro } := rfl
theorem preAuto_ps (w : World) (smp : Sample) :
    (preAuto w smp).ps = AC_PosControl_lib.AC_PosControl.set_reset_handling_method
      (AC_PosControl_lib.AC_PosControl.update_estimates w.ps
        (posInputs (viewUpdate { w with sample := { smp with gyro := w.sample.gyro } })) false) .MoveVehicle := rfl

section HovFrame
open AP_Motors_lib AP_MotorsMatrix
set_option maxHeartbeats 4000000 in
theorem hov_output_logic (p : Params) (s : State) :
    (output_logic p s).1._throttle_hover = p._throttle_hover := by
  frame_gen Params (fun q : Params => q._throttle_hover = p._throttle_hover) (output_logic p s)
    using first | rfl

theorem hov_output (p : Params) (s : State) o inp :
    (output p s o inp).1._throttle_hover = p._throttle_hover := by
  simp only [output, Id.run]
  exact hov_output_logic p _
end HovFrame



/-! ### The hypotheses of `vertical_tick_eq` -/

/-- **The navigator's frame** on the vertical controller: from `w9` (after the estimates) to `w12`
(after `update_wpnav` and its calls into the position controller), the vertical PIDs, the
estimates, the period, the motors' throttle filter, the motors' parameters and the sample are
unchanged. (On a normal leg the navigator only writes the targets; the calls that reset the
vertical controller, `D_init_controller_stopping_point`, happen at mission start.) -/
structure NavV (w9 w12 : World) : Prop where
  pidV : w12.ps._pid_vel_d_m = w9.ps._pid_vel_d_m
  pidA : w12.ps._pid_accel_d_m = w9.ps._pid_accel_d_m
  posE : w12.ps._pos_estimate_ned_m = w9.ps._pos_estimate_ned_m
  velE : w12.ps._vel_estimate_ned_ms = w9.ps._vel_estimate_ned_ms
  dt : w12.ps._dt_s = w9.ps._dt_s
  filt : w12.ms._throttle_filter = w9.ms._throttle_filter
  mp : w12.mp = w9.mp
  sample : w12.sample = w9.sample

/-- The motors at the start of the tick (D8): armed, the throttle filter initialised with the
`2` Hz cutoff of the last `set_throttle_out`, the filter and `_throttle_in` in `[1/4, 3/4]`. -/
structure MotReg (ms : AP_Motors_lib.AP_MotorsMatrix.State) : Prop where
  armed : ms._armed = true
  init : ms._throttle_filter.initialised = true
  cut : ms._throttle_filter.cutoff_freq = 2.0
  f : ms._throttle_filter.output.IsFinite
  f0 : 1 / 4 ≤ ms._throttle_filter.output.toReal
  f1 : ms._throttle_filter.output.toReal ≤ 3 / 4
  u : ms._throttle_in.IsFinite
  u0 : 1 / 4 ≤ ms._throttle_in.toReal
  u1 : ms._throttle_in.toReal ≤ 3 / 4

/-- The angle boost's region (D2, D16): the boost enabled, the vehicle's `cos_pitch cos_roll ≥ 0.11`,
the attitude controller's target thrust angle with `cos θ ≥ c0 ≥ 1/2`. -/
structure BoostReg (w : World) (c0 : ℝ) : Prop where
  en : w.ap._angle_boost_enabled ≠ 0
  cp : w.vs.trig.cos_pitch.IsFinite
  cr : w.vs.trig.cos_roll.IsFinite
  cpb : |w.vs.trig.cos_pitch.toReal| ≤ 1
  crb : |w.vs.trig.cos_roll.toReal| ≤ 1
  ct : 11 / 100 ≤ w.vs.trig.cos_pitch.toReal * w.vs.trig.cos_roll.toReal
  θ : w.as._thrust_angle_rad.IsFinite
  c0h : 1 / 2 ≤ c0
  cθ : c0 ≤ Real.cos w.as._thrust_angle_rad.toReal

/-- The code's values of one tick (`VVals`), read off the worlds. -/
def vvOf (w : World) (smp : Sample) (held z vz z' vz' sp' vsp' : ℝ) : VVals :=
  let w12 := navOf w smp
  let inp := posInputs w12
  let sD := preD w12.ps inp
  let r := Vehicle.tick w smp
  { z := z, vz := vz, zs := smp.pos.z.toReal, vzs := smp.vel.z.toReal,
    sp := w12.ps._pos_desired_ned_m.z.toReal, vsp := w12.ps._vel_desired_ned_ms.z.toReal,
    asp := w12.ps._accel_desired_ned_mss.z.toReal,
    eV := w.ps._pid_vel_d_m._error.toReal, eA := w.ps._pid_accel_d_m._error.toReal,
    I := w.ps._pid_accel_d_m._integrator.toReal, f := w.ms._throttle_filter.output.toReal,
    u := w.ms._throttle_in.toReal, held := held, hov := (hovF w.mp).toReal, acc := smp.acc.z.toReal,
    θ := w12.as._thrust_angle_rad.toReal,
    vt := (velT w12.pp sD inp).toReal, eV' := r.1.ps._pid_vel_d_m._error.toReal,
    atg := (accT w12.pp sD inp).toReal,
    am := (AC_PosControl_lib.AC_PosControl.get_estimated_accel_D_mss inp).toReal,
    eA' := r.1.ps._pid_accel_d_m._error.toReal, I' := r.1.ps._pid_accel_d_m._integrator.toReal,
    thr := (thrN w12.pp sD inp).toReal, u' := r.1.ms._throttle_in.toReal,
    f' := r.1.ms._throttle_filter.output.toReal, held' := meanAct r.2,
    z' := z', vz' := vz', sp' := sp', vsp' := vsp' }

/-- The `β`s of the C-lemmas, with the region's magnitudes (`DReg2`), the integrator `I`, its
limit `K`, the thrust command `thr`, the tilt bound `c0`, the mixer's `εmix` and the sample's
deviation from the plant `εsmp`. -/
def veOf (E Ev Vv Aa Aam Ma MeA K I thr c0 εmix εsmp : ℝ) : VErr :=
  { smp := εsmp, vt := u32 * (4 * E + Vv) + 4 * η32,
    V := αVr * (u32 * MeV E Ev + η32) + (102 / 100 + 411 / 100 * αVr) * u32 * MeV E Ev + 2 * η32,
    atg := u32 * (21 * MeV E Ev + Aa) + 3 * η32, am := u32 * (Aa + Aam) + η32,
    E := αAr * (514 / 100 * u32 * Ma + u32 * MeA + 4 * η32) + (102 / 100 + 411 / 100 * αAr) * u32 * MeA +
      2 * η32,
    I := u32 * |I| + u32 * MeA / 2 ^ 7 + 4 * η32, N := u32 * (MeA + 2 * K + 2) + 6 * η32,
    b := (1 / 2 ^ 22 / ((c0 - 1 / 2 ^ 22) * c0) + 3 * u32 / (c0 - 1 / 2 ^ 22) + η32) * |thr| + η32,
    f := (102 / 100 + 411 / 100 * αTr) * u32 * (3 / 4) + 2 * η32, mix := εmix }

theorem hovF_congr {p q : AP_Motors_lib.AP_MotorsMatrix.Params} (h : p._throttle_hover = q._throttle_hover) :
    hovF p = hovF q := by
  simp only [hovF, AP_Motors_lib.AP_MotorsMatrix.get_throttle_hover, h]

set_option maxHeartbeats 4000000 in
theorem applyPos_ps (w : World) (evs : AC_PosControl_lib.Outputs) : (applyPos w evs).ps = w.ps := by
  frame_gen World (fun w' : World => w'.ps = w.ps) (applyPos w evs)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [withMotors_ps] <;> with_reducible assumption)

set_option maxHeartbeats 4000000 in
theorem applyPos_mp (w : World) (evs : AC_PosControl_lib.Outputs) : (applyPos w evs).mp = w.mp := by
  frame_gen World (fun w' : World => w'.mp = w.mp) (applyPos w evs)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [withMotors_mp] <;> with_reducible assumption)

theorem postD_ps (w : World) :
    (postD w).ps = (AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w)).2.1 := by
  unfold postD
  rcases AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w) with ⟨pp, ps, evs⟩
  rw [applyPos_ps]

theorem postD_mp (w : World) : (postD w).mp = w.mp := by
  unfold postD
  rcases AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w) with ⟨pp, ps, evs⟩
  rw [applyPos_mp]

theorem finW_mp (w : World) : (finW w).mp = w.mp := by
  simp only [finW, auto_yaw_get_heading, auto_yaw_yaw_rad, auto_yaw_rate_rads]

/-- `postD`'s motors, when `D_update_controller` emits its one `set_throttle_out`. -/
theorem postD_ms (w : World) (thr : Float32)
    (hD : (AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w)).2.2 =
      (#[] : AC_PosControl_lib.Outputs).push (AC_PosControl_lib.Output.set_throttle_out thr true 2.0)) :
    (postD w).ms = applyAtt w.ms (AC_Attitude_lib.AC_AttitudeControl_Multi.set_throttle_out w.ap w.as
      (attOutputs w.ms) (attInputs w) thr true 2.0).2 := by
  unfold postD
  rcases h : AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w) with ⟨pp, ps, evs⟩
  rw [h] at hD
  simp only at hD
  subst hD
  dsimp only
  rw [applyPos_single, withMotors_ms]
  rfl


section UEFrame
open AC_PosControl_lib AC_PosControl

theorem ue_frame (s : State) (inp : Inputs) (hv : Bool) :
    (update_estimates s inp hv)._pid_vel_d_m = s._pid_vel_d_m ∧
    (update_estimates s inp hv)._pid_accel_d_m = s._pid_accel_d_m ∧
    (update_estimates s inp hv)._dt_s = s._dt_s := by
  frame_gen State (fun st : State => st._pid_vel_d_m = s._pid_vel_d_m ∧
      st._pid_accel_d_m = s._pid_accel_d_m ∧ st._dt_s = s._dt_s) (update_estimates s inp hv)
    using first | exact ⟨rfl, rfl, rfl⟩ | with_reducible assumption | assumption

end UEFrame

/-- The vertical controller's state the tick's `D_update_controller` reads, back to the start of
the tick: the navigator's frame, the estimates and the period leave it. -/
theorem pid_back (w : World) (smp : Sample)
    (hnav : NavV (preAuto (postMot (preMot w smp)) smp) (navOf w smp)) :
    (navOf w smp).ps._pid_vel_d_m = w.ps._pid_vel_d_m ∧
    (navOf w smp).ps._pid_accel_d_m = w.ps._pid_accel_d_m ∧
    (navOf w smp).ps._dt_s = tPer w smp := by
  obtain ⟨h1, h2, h3⟩ := ue_frame (postMot (preMot w smp)).ps
    (posInputs (viewUpdate { postMot (preMot w smp) with sample := { smp with gyro := (postMot (preMot w smp)).sample.gyro } })) false
  refine ⟨?_, ?_, ?_⟩
  · rw [hnav.pidV, preAuto_ps]; exact h1.trans (by rw [postMot_ps, preMot_ps]; rfl)
  · rw [hnav.pidA, preAuto_ps]; exact h2.trans (by rw [postMot_ps, preMot_ps]; rfl)
  · rw [hnav.dt, preAuto_ps]; exact h3.trans (by rw [postMot_ps, preMot_ps]; rfl)

/-- The estimates the tick's `D_update_controller` reads are the sample (C1 and the frames). -/
theorem est_back (w : World) (smp : Sample)
    (hnav : NavV (preAuto (postMot (preMot w smp)) smp) (navOf w smp)) :
    (navOf w smp).ps._pos_estimate_ned_m = smp.pos ∧ (navOf w smp).ps._vel_estimate_ned_ms = smp.vel := by
  obtain ⟨h1, h2⟩ := estimates (viewUpdate { postMot (preMot w smp) with sample := { smp with gyro := (postMot (preMot w smp)).sample.gyro } })
    (postMot (preMot w smp)).ps
  exact ⟨by rw [hnav.posE, preAuto_ps]; exact h1, by rw [hnav.velE, preAuto_ps]; exact h2⟩

/-- **The hypotheses of `vertical_tick_eq`** on one tick `w`, `smp`: the schedule (Auto mode
after the first tick, period `2500 µs`), the navigator's frame `NavV` (not discharged here), the
region of the position controller (`DPar2`, `DReg2`, the controller active, no EKF reset, no
vibration compensation, hover below `IMAX`), of the motors (`MotReg`) and of the boost
(`BoostReg`), and the mixer's identity (C12, second half): the mean of the four actuators is the
throttle filter's output within `εmix`. -/
structure VTickHyp (w : World) (smp : Sample) (E Ev Vv Aa Aam Ma MeA c0 εmix : ℝ) : Prop where
  hin : w.in_auto = true
  hwait : w.au.waiting_to_start = false
  ht0 : w.ticks32 ≠ 0
  hdt : smp.dt_us = 2500
  hnav : NavV (preAuto (postMot (preMot w smp)) smp) (navOf w smp)
  hp : DPar2 (navOf w smp).pp
  hs : DReg2 (navOf w smp).pp (preD (navOf w smp).ps (posInputs (navOf w smp)))
      (posInputs (navOf w smp)) E Ev Vv Aa Aam Ma MeA
  hact : AC_PosControl_lib.AC_PosControl.D_is_active (navOf w smp).ps (posInputs (navOf w smp)) = true
  hrc : (posInputs (navOf w smp)).get_position_D_reset_count =
      (navOf w smp).ps._ahrs_position_D_reset_count
  hvib : (navOf w smp).ps._vibe_comp_enabled = false
  hhov : (hovF w.mp).toReal ≤ (navOf w smp).pp._pid_accel_d_m._kimax.toReal
  hm : MotReg w.ms
  hb : BoostReg (navOf w smp) c0
  hmix : |meanAct (Vehicle.tick w smp).2 - (Vehicle.tick w smp).1.ms._throttle_filter.output.toReal| ≤ εmix

/-- The `β`s of one tick, from the hypotheses' magnitudes. -/
def veTick (w : World) (smp : Sample) (z vz E Ev Vv Aa Aam Ma MeA c0 εmix : ℝ) (thr : ℝ) : VErr :=
  veOf E Ev Vv Aa Aam Ma MeA (navOf w smp).pp._pid_accel_d_m._kimax.toReal
    w.ps._pid_accel_d_m._integrator.toReal thr c0 εmix
    (|z - smp.pos.z.toReal| + |vz - smp.vel.z.toReal|)

set_option maxHeartbeats 8000000 in
/-- **The code relations of one tick.** Under `VTickHyp`, the code's values of the tick
(`vvOf`) satisfy the C-lemmas' relations (`VRel`) with the `β`s `veTick`, and the vertical state
vectors before and after the tick are `vstate` of the worlds. -/
theorem vertical_tick_rel (hL : LibmSpec) (hpi : PiF32) (w : World) (smp : Sample)
    (held z vz z' vz' sp' vsp' : ℝ) {E Ev Vv Aa Aam Ma MeA c0 εmix : ℝ}
    (h : VTickHyp w smp E Ev Vv Aa Aam Ma MeA c0 εmix) :
    let v := vvOf w smp held z vz z' vz' sp' vsp'
    VRel v (veTick w smp z vz E Ev Vv Aa Aam Ma MeA c0 εmix v.thr) ∧
      v.ξ = vstate w z vz held v.sp v.vsp ∧
      v.ξ' = vstate (Vehicle.tick w smp).1 z' vz' (meanAct (Vehicle.tick w smp).2) sp' vsp' := by
  obtain ⟨hin, hwait, ht0, hdt, hnav, hp, hs, hact, hrc, hvib, hhov, hm, hb, hmix⟩ := h
  intro v
  set e := veTick w smp z vz E Ev Vv Aa Aam Ma MeA c0 εmix v.thr with he
  -- the stages of the tick
  have hau : (preAuto (postMot (preMot w smp)) smp).au.waiting_to_start = false := by
    rw [preAuto_au, postMot_au, preMot_au]; exact hwait
  have hsplit : Vehicle.tick w smp = (finW (postD (navOf w smp)), actOf (postMot (preMot w smp))) := by
    rw [tick_split w smp hin, auto_run_eq _ hau, wp_run_split]; rfl
  -- the controller's state as `D_update_controller` reads it
  set w12 := navOf w smp with hw12
  set inp := posInputs w12 with hinp
  set sD := preD w12.ps inp with hsD
  have hhovF : hovF w12.mp = hovF w.mp := by
    apply hovF_congr
    rw [hw12, hnav.mp, preAuto_mp, postMot_mp, hov_output, preMot_mp]
  have hh : ¬ (inp.get_throttle_hover > AC_PosControl_lib.AC_PID.imax w12.pp._pid_accel_d_m) := by
    have e1 : inp.get_throttle_hover = hovF w12.mp := rfl
    rw [gt_iff_lt, e1, hhovF]
    show ¬ (w12.pp._pid_accel_d_m._kimax < hovF w.mp)
    have hf : (hovF w.mp).IsFinite := by rw [← hhovF]; exact hs.hov
    rw [Float32.lt_iff_toReal_lt hp.aimx hf, not_lt]
    exact hhov
  have hvib' : sD._vibe_comp_enabled = false := by rw [hsD, preD_vibe]; exact hvib
  have eV := dupd_vel w12.pp w12.ps #[] inp hrc hact hvib' hh
  have eA := dupd_acc w12.pp w12.ps #[] inp hrc hact hvib' hh
  have eO := dupd_out w12.pp w12.ps #[] inp hrc hact hvib' hh
  have hps : (Vehicle.tick w smp).1.ps =
      (AC_PosControl_lib.AC_PosControl.D_update_controller w12.pp w12.ps #[] inp).2.1 := by
    rw [hsplit, finW_ps, postD_ps]
  have hms : (Vehicle.tick w smp).1.ms = applyAtt w12.ms
      (AC_Attitude_lib.AC_AttitudeControl_Multi.set_throttle_out w12.ap w12.as (attOutputs w12.ms)
        (attInputs w12) (-thrN w12.pp sD inp) true 2.0).2 := by
    rw [hsplit, finW_ms, postD_ms _ _ eO]
  -- back to the start of the tick
  obtain ⟨bV, bA, bdt⟩ := pid_back w smp hnav
  obtain ⟨bpos, bvel⟩ := est_back w smp hnav
  have sV : sD._pid_vel_d_m = w.ps._pid_vel_d_m := by rw [hsD, preD_pidV]; exact bV
  have sA : sD._pid_accel_d_m = w.ps._pid_accel_d_m := by rw [hsD, preD_pidA]; exact bA
  have sz : sD._pos_estimate_ned_m.z = smp.pos.z := by rw [hsD, preD_posE, bpos]
  have svz : sD._vel_estimate_ned_ms.z = smp.vel.z := by rw [hsD, preD_velE, bvel]
  have ssp : sD._pos_desired_ned_m = w12.ps._pos_desired_ned_m := by rw [hsD, preD_posD]
  have svsp : sD._vel_desired_ned_ms = w12.ps._vel_desired_ned_ms := by rw [hsD, preD_velD]
  have sasp : sD._accel_desired_ned_mss = w12.ps._accel_desired_ned_mss := by rw [hsD, preD_accD]
  have sacc : inp.get_accel_ef = smp.acc := by
    show w12.sample.acc = smp.acc
    rw [hw12, hnav.sample, preAuto_sample]
  -- the vertical controller (C5, C6)
  have cvt := dctrl2_vt hL w12.pp sD inp hp hs
  obtain ⟨cV, -, -, -, -, -, -⟩ := dctrl2_vel hL hpi w12.pp sD inp hp hs
  have cat := dctrl2_at hL hpi w12.pp sD inp hp hs
  have cam := dctrl2_am w12.pp sD inp hs
  obtain ⟨cE, cI, -, -, -, -, -, -, -, -⟩ := dctrl2_acc hL hpi w12.pp sD inp hp hs
  have cN := dctrl2_thr hL hpi w12.pp sD inp hp hs
  -- the new controller state is the controllers' outputs
  have nV : (Vehicle.tick w smp).1.ps._pid_vel_d_m = (velB w12.pp sD inp).1 := by rw [hps, eV]
  have nA : (Vehicle.tick w smp).1.ps._pid_accel_d_m = (accA w12.pp sD inp).1 := by rw [hps, eA]
  -- the motors' throttle filter (C12)
  obtain ⟨o, hms3, ho1, ho2⟩ := preMot_ms w smp
  have harm : (preMot w smp).ms._armed = true := by rw [hms3]; exact hm.armed
  have hin3 : (preMot w smp).ms._throttle_filter.initialised = true := by rw [hms3]; exact hm.init
  have hdt3 : (preMot w smp).ms._dt_s = tPer w smp := by rw [hms3]; rfl
  have hcut3 : (preMot w smp).ms._throttle_filter.cutoff_freq = w.ms._throttle_filter.cutoff_freq := by
    rw [hms3, applyAtt_cut, ho2]
  have hf3 : (preMot w smp).ms._throttle_filter.output = w.ms._throttle_filter.output := by
    rw [hms3, applyAtt_filt]; rfl
  have hu3 : (preMot w smp).ms._throttle_in = w.ms._throttle_in := by
    rw [hms3, applyAtt_thr_in, ho1]
  have hd0 : tPer w smp = d0 := by rw [tPer_eq w smp ht0, hdt]
  have cf := throttle_filter2 hL hpi (preMot w smp).ms (motorsInputs (preMot w smp)) harm hin3
    (by rw [hdt3, hd0]) (by rw [hcut3]; exact hm.cut) (by rw [hf3]; exact hm.f) (by rw [hu3]; exact hm.u)
    (by rw [hf3]; exact hm.f0) (by rw [hf3]; exact hm.f1) (by rw [hu3]; exact hm.u0)
    (by rw [hu3]; exact hm.u1)
  rw [hf3, hu3] at cf
  have nf : (Vehicle.tick w smp).1.ms._throttle_filter.output =
      (AP_Motors_lib.AP_MotorsMatrix.update_throttle_filter (preMot w smp).ms
        (motorsInputs (preMot w smp)))._throttle_filter.output := by
    rw [hms, applyAtt_filt, hw12, hnav.filt, preAuto_ms, postMot_ms, filt_output]
  -- the boost (C7)
  have nu : (Vehicle.tick w smp).1.ms._throttle_in =
      -thrN w12.pp sD inp * AC_Attitude_lib.constrain_value_line_float ((10.0 : Float32) *
          (w12.vs.trig.cos_pitch * w12.vs.trig.cos_roll)) 0.0 1.0 (Int32.toUInt32 398) *
        ((1.0 : Float32) / AC_Attitude_lib.constrain_value_line_float (Float32.cos w12.as._thrust_angle_rad)
          (0.100000001 : Float32) 1.0 (Int32.toUInt32 400)) := by
    rw [hms, applyAtt_thr_in, (set_throttle_out_eq _ _ _ _ _ _ hb.en).1]
    rfl
  have hthr : |(-thrN w12.pp sD inp).toReal| ≤ 2 ^ 20 := by
    rw [Float32.toReal_neg, abs_neg]
    have h1 := cN.abs_le
    have := hs.MeA2; have := hp.aimx'; have := hs.hov0; have := hs.hov1
    obtain ⟨-, -, -, -, -, -, -, -, hEb, -⟩ := dctrl2_acc hL hpi w12.pp sD inp hp hs
    have hIa := cI.abs_le
    have hIb : |sD._pid_accel_d_m._integrator.toReal| ≤ 2 ^ 10 := by
      have := hs.aIb; have := abs_nonneg sD._pid_accel_d_m._integrator.toReal
      have : 0 ≤ MeA := by
        have := hs.MeA1; have : 0 ≤ MeV E Ev := by rw [MeV]; have := hs.E0; have := hs.Ev0; linarith
        linarith [(abs_nonneg _).trans hs.accb]
      linarith
    have hkd : |kiA * dtR * (accA w12.pp sD inp).1._error.toReal| ≤ 3 * 2 ^ 10 := by
      rw [abs_mul, abs_mul, kiA, dtR]; norm_num; nlinarith [abs_nonneg (accA w12.pp sD inp).1._error.toReal]
    have hkp : |kpA * (accA w12.pp sD inp).1._error.toReal| ≤ 3 * 2 ^ 10 := by
      rw [abs_mul, kpA]; norm_num; nlinarith [abs_nonneg (accA w12.pp sD inp).1._error.toReal]
    have t1 := abs_add_le sD._pid_accel_d_m._integrator.toReal (kiA * dtR * (accA w12.pp sD inp).1._error.toReal)
    have t2 := abs_sub (kpA * (accA w12.pp sD inp).1._error.toReal + (accA w12.pp sD inp).1._integrator.toReal)
      inp.get_throttle_hover.toReal
    have t3 := abs_add_le (kpA * (accA w12.pp sD inp).1._error.toReal) (accA w12.pp sD inp).1._integrator.toReal
    rw [abs_of_nonneg hs.hov0] at t2
    have hη1 := η32_small
    rw [u32_eq] at h1 hIa
    nlinarith [abs_nonneg sD._pid_accel_d_m._integrator.toReal]
  have cb := boost_c hL ((Float32.isFinite_neg _).2 cN.1) hthr hb.cp hb.cr hb.cpb hb.crb hb.ct hb.θ hb.c0h hb.cθ
  -- the constants of the model
  have kV : ((αV : ℚ) : ℝ) = αVr := by rw [αV, αVr]; push_cast; ring
  have kA : ((αA : ℚ) : ℝ) = αAr := by rw [αA, αAr]; push_cast; ring
  have kT : ((αT : ℚ) : ℝ) = αTr := by rw [αT, αTr]; push_cast; ring
  have kI : ((kiDt : ℚ) : ℝ) = kiA * dtR := kiA_dtR.symm
  have kP : ((kpAcc : ℚ) : ℝ) = kpA := kpA_eq.symm
  -- the code relations
  have hR : VRel v e := by
    refine ⟨le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show |(velT w12.pp sD inp).toReal - ((w12.ps._pos_desired_ned_m.z.toReal - smp.pos.z.toReal) +
        w12.ps._vel_desired_ned_ms.z.toReal)| ≤ u32 * (4 * E + Vv) + 4 * η32
      have h := cvt.2
      rw [ssp, sz, svsp] at h
      exact h
    · show |(Vehicle.tick w smp).1.ps._pid_vel_d_m._error.toReal - (w.ps._pid_vel_d_m._error.toReal +
        ((αV : ℚ) : ℝ) * (((velT w12.pp sD inp).toReal - smp.vel.z.toReal) - w.ps._pid_vel_d_m._error.toReal))| ≤
        αVr * (u32 * MeV E Ev + η32) + (102 / 100 + 411 / 100 * αVr) * u32 * MeV E Ev + 2 * η32
      have h := cV.2
      rw [sV, svz] at h
      rw [nV, kV]
      exact h
    · have h := cat.2
      rw [sasp, ← nV] at h
      exact h
    · show |(AC_PosControl_lib.AC_PosControl.get_estimated_accel_D_mss inp).toReal -
        (smp.acc.z.toReal + gfR)| ≤ u32 * (Aa + Aam) + η32
      have h := cam.2
      rw [sacc] at h
      exact h
    · show |(Vehicle.tick w smp).1.ps._pid_accel_d_m._error.toReal - (w.ps._pid_accel_d_m._error.toReal +
        ((αA : ℚ) : ℝ) * (((accT w12.pp sD inp).toReal -
          (AC_PosControl_lib.AC_PosControl.get_estimated_accel_D_mss inp).toReal) -
          w.ps._pid_accel_d_m._error.toReal))| ≤
        αAr * (514 / 100 * u32 * Ma + u32 * MeA + 4 * η32) + (102 / 100 + 411 / 100 * αAr) * u32 * MeA +
          2 * η32
      have h := cE.2
      rw [sA] at h
      rw [nA, kA]
      exact h
    · show |(Vehicle.tick w smp).1.ps._pid_accel_d_m._integrator.toReal -
        (w.ps._pid_accel_d_m._integrator.toReal + ((kiDt : ℚ) : ℝ) *
          (Vehicle.tick w smp).1.ps._pid_accel_d_m._error.toReal)| ≤
        u32 * |w.ps._pid_accel_d_m._integrator.toReal| + u32 * MeA / 2 ^ 7 + 4 * η32
      have h := cI.2
      rw [sA] at h
      rw [nA, kI]
      exact h
    · show |(thrN w12.pp sD inp).toReal - (((kpAcc : ℚ) : ℝ) *
        (Vehicle.tick w smp).1.ps._pid_accel_d_m._error.toReal +
        (Vehicle.tick w smp).1.ps._pid_accel_d_m._integrator.toReal - (hovF w.mp).toReal)| ≤
        u32 * (MeA + 2 * w12.pp._pid_accel_d_m._kimax.toReal + 2) + 6 * η32
      have h := cN.2
      rw [nA, kP, ← hhovF]
      exact h
    · show |(Vehicle.tick w smp).1.ms._throttle_in.toReal - (-(thrN w12.pp sD inp).toReal) /
        Real.cos w12.as._thrust_angle_rad.toReal| ≤
        (1 / 2 ^ 22 / ((c0 - 1 / 2 ^ 22) * c0) + 3 * u32 / (c0 - 1 / 2 ^ 22) + η32) *
          |(thrN w12.pp sD inp).toReal| + η32
      have h := cb.2
      rw [Float32.toReal_neg, abs_neg] at h
      rw [nu]
      exact h
    · show |(Vehicle.tick w smp).1.ms._throttle_filter.output.toReal - (w.ms._throttle_filter.output.toReal +
        ((αT : ℚ) : ℝ) * (w.ms._throttle_in.toReal - w.ms._throttle_filter.output.toReal))| ≤
        (102 / 100 + 411 / 100 * αTr) * u32 * (3 / 4) + 2 * η32
      rw [nf, kT]
      exact cf.2
    · exact hmix
  -- the state vectors
  have hξ : v.ξ = vstate w z vz held v.sp v.vsp := by
    funext j; fin_cases j <;> rfl
  have hξ' : v.ξ' = vstate (Vehicle.tick w smp).1 z' vz' (meanAct (Vehicle.tick w smp).2) sp' vsp' := by
    have hmp : hovF (Vehicle.tick w smp).1.mp = hovF w.mp := by
      rw [← hhovF]; congr 1
      rw [hsplit]; exact (finW_mp _).trans (postD_mp _)
    funext j; fin_cases j
    all_goals simp only [VVals.ξ', vstate, VVals.Itr, hmp]
    all_goals rfl
  exact ⟨hR, hξ, hξ'⟩

/-- **`vertical_tick_eq`.** One `Vehicle.tick` of Auto mode maps the vertical state of
`VERTICAL.md` (`vstate`, read off the worlds before and after the tick, with the plant's `z vz`
before and `z' vz'` after, the navigator's target `(sp, vsp, asp)` of the tick and the next target
`sp', vsp'`) as the model's `tick` (`= A_v ξ + asp B_v - d₁ e₀ - d₂ e₁`, `tick_eq`) plus a
disturbance bounded componentwise by `βvec`. -/
theorem vertical_tick_eq (hL : LibmSpec) (hpi : PiF32) (w : World) (smp : Sample)
    (held z vz z' vz' sp' vsp' : ℝ) {E Ev Vv Aa Aam Ma MeA c0 εmix : ℝ}
    (h : VTickHyp w smp E Ev Vv Aa Aam Ma MeA c0 εmix) :
    let v := vvOf w smp held z vz z' vz' sp' vsp'
    ∀ i, |(vstate (Vehicle.tick w smp).1 z' vz' (meanAct (Vehicle.tick w smp).2) sp' vsp' -
      tick (vstate w z vz held v.sp v.vsp) v.asp
        (defect₁ v.sp sp' v.vsp v.asp) (defect₂ v.vsp vsp' v.asp)) i| ≤
      βvec v (veTick w smp z vz E Ev Vv Aa Aam Ma MeA c0 εmix v.thr) i := by
  intro v i
  obtain ⟨hR, hξ, hξ'⟩ := vertical_tick_rel hL hpi w smp held z vz z' vz' sp' vsp' h
  have := vtick_real v _ hR i
  rw [hξ, hξ'] at this
  exact this

/-- **`vertical_tick_eq`, split form**: the disturbance minus its structured part `wS` (plant
residuals, the sample's tilt coupling through the acceleration filter, the boost's deviation) is
bounded componentwise by the code's `β`s alone (`βcode`). -/
theorem vertical_tick_split (hL : LibmSpec) (hpi : PiF32) (w : World) (smp : Sample)
    (held z vz z' vz' sp' vsp' : ℝ) {E Ev Vv Aa Aam Ma MeA c0 εmix : ℝ}
    (h : VTickHyp w smp E Ev Vv Aa Aam Ma MeA c0 εmix) :
    let v := vvOf w smp held z vz z' vz' sp' vsp'
    ∀ i, |(vstate (Vehicle.tick w smp).1 z' vz' (meanAct (Vehicle.tick w smp).2) sp' vsp' -
      tick (vstate w z vz held v.sp v.vsp) v.asp
        (defect₁ v.sp sp' v.vsp v.asp) (defect₂ v.vsp vsp' v.asp) - wS v) i| ≤
      βcode (veTick w smp z vz E Ev Vv Aa Aam Ma MeA c0 εmix v.thr) i := by
  intro v i
  obtain ⟨hR, hξ, hξ'⟩ := vertical_tick_rel hL hpi w smp held z vz z' vz' sp' vsp' h
  have := vtick_split v _ hR i
  rw [hξ, hξ'] at this
  exact this

end

end Contracts.Track.CtrlV
