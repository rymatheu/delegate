import Contracts.Basic
import Contracts.Lift
import Contracts.FloatReal
import Flight.FloatInstance

/-!
# A closed loop with a `Float` controller

Two modules over one universe:

* the **controller** `ctrlF : Float → Float → Float`, a proportional-derivative altitude law written
  over the scalar interface `Flight.Arith` like the flight stack's modules and executed at its
  `Float` instance: it reads the measured altitude and vertical velocity and writes a commanded
  acceleration, all three `Float`s;
* the **plant**, whose ports are `Float` and whose dynamics are real: it reads the command, takes
  its exact value `Float.toReal`, saturates it to `[-100, 100]` in `ℝ`, integrates the double
  integrator `(z, v) ↦ (z + h v, v + h a)` with `h = 1/50`, and writes the measurements
  `sense z`, `sense v`, where `sense : ℝ → Float` is only known to round within `δ` on `|r| ≤ 100`.

The loop is verified by delegation (`Contracts.chain`): the controller contract is discharged
against the `Float` code under the rounding hypotheses `FloatArith`, and the plant contract against
the real dynamics, assuming the controller's guarantee. With exact arithmetic the error coordinates
`e = z - 5`, `w = v + 2 e` evolve by `e' = 0.96 e + w/50`, `w' = 0.96 w`; the float error `d` of the
applied acceleration enters only as `w' = 0.96 w + d/50`. The box `|w| ≤ 8, |e| ≤ 4` is then
invariant whenever `|d| ≤ 16`, which gives the ceiling for every horizon, and `max |w| |e|`
contracts by `49/50` per tick up to `|d|`, which gives reach-and-hold.
-/

namespace Contracts.FloatLoop

open Contracts.FloatReal Contracts.Lift

/-! ## The two modules -/

/-- The altitude law `u = 4 (5 - z) - 4 v` over any scalar type of the flight stack. -/
-- <<altCtrl>>
def altCtrl {α : Type} [Flight.Arith α] (zf vf : α) : α := 4.0 * (5.0 - zf) - 4.0 * vf
-- <</altCtrl>>

/-- The verified controller: the altitude law at `Float`. -/
-- <<ctrlF>>
def ctrlF : Float → Float → Float := altCtrl
-- <</ctrlF>>

/-- Saturation of the applied acceleration to `[-100, 100]`. -/
-- <<sat>>
noncomputable def sat (a : ℝ) : ℝ := max (-100) (min 100 a)
-- <</sat>>

/-- The plant: real state `(z, v)`, `Float` command in, `Float` measurements out. -/
-- <<plant>>
noncomputable def plant (sense : ℝ → Float) (s : ℝ × ℝ) (uf : Float) :
    (ℝ × ℝ) × (Float × Float) :=
  ((s.1 + (1/50) * s.2, s.2 + (1/50) * sat uf.toReal), (sense s.1, sense s.2))
-- <</plant>>

/-! ## Universe, components and contract -/

/-- One tick of a behaviour: real altitude and velocity, their `Float` measurements, the `Float`
command. -/
-- <<X>>
structure X where
  z : ℝ
  v : ℝ
  zf : Float
  vf : Float
  uf : Float
-- <</X>>

/-- The real state of a tick. -/
def phys (x : X) : ℝ × ℝ := (x.z, x.v)

/-- The plant component. -/
-- <<Mplant>>
noncomputable def Mplant (sense : ℝ → Float) : Set (ℕ → X) :=
  liftStep phys (·.uf) (fun x => (x.zf, x.vf)) (plant sense)
-- <</Mplant>>

/-- The controller component. -/
-- <<Mctrl>>
def Mctrl : Set (ℕ → X) := liftStatic (fun x => (x.zf, x.vf)) (·.uf) (fun m => ctrlF m.1 m.2)
-- <</Mctrl>>

/-- The closed loop. -/
-- <<M>>
noncomputable def M (sense : ℝ → Float) : Set (ℕ → X) := Mplant sense ∩ Mctrl
-- <</M>>

/-- Assumption: the loop starts at rest within `4` of the reference altitude `5`. -/
-- <<A>>
def A : Set (ℕ → X) := {x | |(x 0).z - 5| ≤ 4 ∧ (x 0).v = 0}
-- <</A>>

/-- Ceiling: the altitude stays at or below `10` over `[0, T]`. -/
-- <<ceiling>>
def ceiling (T : ℕ) : STL.Formula (ℝ × ℝ) := .always 0 T (.atom fun s => 10 - s.1)
-- <</ceiling>>

/-- Reach-and-hold: within `T₁` ticks the altitude is within `tol` of `5` and stays there for `T₂`. -/
-- <<reachHold>>
def reachHold (T₁ T₂ : ℕ) (tol : ℝ) : STL.Formula (ℝ × ℝ) :=
  .eventually 0 T₁ (.always 0 T₂ (.atom fun s => tol - |s.1 - 5|))
-- <</reachHold>>

/-- All the hypotheses on `Float`: the rounding of subtraction and multiplication, and the sensor. -/
-- <<LoopHyp>>
structure LoopHyp (ε η Ω δ : ℝ) (sense : ℝ → Float) : Prop
    extends FloatArith ε η Ω, SenseSpec δ sense
-- <</LoopHyp>>

/-- The numeric side conditions on the error parameters. -/
-- <<Small>>
structure Small (ε η Ω δ : ℝ) : Prop where
  ε_nonneg : 0 ≤ ε
  ε_le : ε ≤ 1/100
  η_nonneg : 0 ≤ η
  η_le : η ≤ 1
  δ_nonneg : 0 ≤ δ
  δ_le : δ ≤ 1/2
  Ω_ge : 100 ≤ Ω
-- <</Small>>

/-- The bound on the error of the applied acceleration. -/
-- <<D>>
def D (ε η δ : ℝ) : ℝ := 8 * δ + 200 * ε + 2 * η
-- <</D>>

/-! ## The controller contract, discharged against the `Float` code -/

/-- Controller guarantee: on finite measurements in range, the command is finite and within
`200 ε + 2 η` of the real law evaluated at the measurements' exact values. -/
-- <<Gctrl>>
def Gctrl (ε η : ℝ) : Set (ℕ → X) :=
  {x | ∀ t, (x t).zf.isFinite → (x t).vf.isFinite → |(x t).zf.toReal - 5| ≤ 9/2 →
    |(x t).vf.toReal| ≤ 33/2 → (x t).uf.isFinite ∧
      |(x t).uf.toReal - (4 * (5 - (x t).zf.toReal) - 4 * (x t).vf.toReal)| ≤ 200 * ε + 2 * η}
-- <</Gctrl>>

/-- The rounding error of one evaluation of `ctrlF`. -/
-- <<ctrlF_err>>
theorem ctrlF_err {ε η Ω : ℝ} (H : FloatArith ε η Ω) (hε0 : 0 ≤ ε) (hε : ε ≤ 1/100)
    (hη : η ≤ 1) (hΩ : 100 ≤ Ω) {zf vf : Float} (hzf : zf.isFinite)
    (hvf : vf.isFinite) (hz : |zf.toReal - 5| ≤ 9/2) (hv : |vf.toReal| ≤ 33/2) :
    (ctrlF zf vf).isFinite ∧
      |(ctrlF zf vf).toReal - (4 * (5 - zf.toReal) - 4 * vf.toReal)| ≤ 200 * ε + 2 * η := by
  change ((4.0 : Float) * ((5.0 : Float) - zf) - (4.0 : Float) * vf).isFinite ∧
    |((4.0 : Float) * ((5.0 : Float) - zf) - (4.0 : Float) * vf).toReal -
      (4 * (5 - zf.toReal) - 4 * vf.toReal)| ≤ 200 * ε + 2 * η
  set a := zf.toReal with ha
  set b := vf.toReal with hb
  -- `p₁ = 5 - zf`
  have h1a : |(5.0 : Float).toReal - a| ≤ 9/2 := by
    rw [toReal_five, abs_sub_comm]; exact hz
  obtain ⟨f1, e1⟩ := H.sub_err _ _ isFinite_five hzf (by linarith)
  set p1 := (5.0 : Float) - zf
  rw [toReal_five] at e1 h1a
  have e1' : |p1.toReal - (5 - a)| ≤ ε * (9/2) :=
    e1.trans (mul_le_mul_of_nonneg_left h1a hε0)
  have hp1 : |p1.toReal| ≤ 9/2 + ε * (9/2) := by
    have := abs_sub_abs_le_abs_sub p1.toReal (5 - a); linarith
  -- `p₂ = 4 * p₁`
  have h2a : |(4.0 : Float).toReal * p1.toReal| ≤ 4 * (9/2 + ε * (9/2)) := by
    rw [toReal_four, abs_mul]; norm_num; linarith
  obtain ⟨f2, e2⟩ := H.mul_err _ _ isFinite_four f1 (by nlinarith)
  set p2 := (4.0 : Float) * p1
  rw [toReal_four] at e2 h2a
  have e2' : |p2.toReal - 4 * p1.toReal| ≤ ε * (4 * (9/2 + ε * (9/2))) + η := by
    have := mul_le_mul_of_nonneg_left h2a hε0; linarith
  -- `p₃ = 4 * vf`
  have h3a : |(4.0 : Float).toReal * b| ≤ 66 := by
    rw [toReal_four, abs_mul]; norm_num; linarith
  obtain ⟨f3, e3⟩ := H.mul_err _ _ isFinite_four hvf (by linarith)
  set p3 := (4.0 : Float) * vf
  rw [toReal_four] at e3 h3a
  have e3' : |p3.toReal - 4 * b| ≤ ε * 66 + η := by
    have := mul_le_mul_of_nonneg_left h3a hε0; linarith
  -- `p₄ = p₂ - p₃`
  have hεε : ε * ε ≤ ε / 100 := by nlinarith
  have hp2 : |p2.toReal| ≤ 18 + 37 * ε + η := by
    have := abs_sub_abs_le_abs_sub p2.toReal (4 * p1.toReal)
    rw [abs_mul] at this; norm_num at this; nlinarith
  have hp3 : |p3.toReal| ≤ 66 + 66 * ε + η := by
    have := abs_sub_abs_le_abs_sub p3.toReal (4 * b)
    rw [abs_mul] at this; norm_num at this; linarith
  have h4a : |p2.toReal - p3.toReal| ≤ 84 + 103 * ε + 2 * η := by
    have := abs_sub p2.toReal p3.toReal; linarith
  obtain ⟨f4, e4⟩ := H.sub_err _ _ f2 f3 (by nlinarith)
  refine ⟨f4, ?_⟩
  have e4' : |(p2 - p3).toReal - (p2.toReal - p3.toReal)| ≤ ε * (84 + 103 * ε + 2 * η) :=
    e4.trans (mul_le_mul_of_nonneg_left h4a hε0)
  have hεη : ε * η ≤ ε := by nlinarith
  rw [abs_le] at e1' e2' e3' e4' ⊢
  constructor <;> nlinarith
-- <</ctrlF_err>>

/-- The controller implements its contract under any assumption. -/
-- <<Mctrl_impl>>
theorem Mctrl_impl {ε η Ω : ℝ} (H : FloatArith ε η Ω) (hε0 : 0 ≤ ε) (hε : ε ≤ 1/100)
    (hη : η ≤ 1) (hΩ : 100 ≤ Ω) (Asm : Set (ℕ → X)) :
    Mctrl ⊨ ⟨Asm, Gctrl ε η⟩ := by
  rintro x ⟨hx, -⟩ t hzf hvf hz hv
  rw [show (x t).uf = ctrlF (x t).zf (x t).vf from hx t]
  exact ctrlF_err H hε0 hε hη hΩ hzf hvf hz hv
-- <</Mctrl_impl>>

/-! ## The plant contract, discharged against the real dynamics -/

/-- Saturation is the identity on `[-100, 100]`. -/
theorem sat_of_abs_le {a : ℝ} (h : |a| ≤ 100) : sat a = a := by
  rw [abs_le] at h
  rw [sat, min_eq_right h.2, max_eq_right h.1]

/-- On the plant, assuming the initial box and the controller guarantee, the error coordinates
`e = z - 5` and `w = v + 2 e` stay in the box `|w| ≤ 8`, `|e| ≤ 4`, and `max |w| |e|` decays
by `49/50` per tick down to the error bound `D`. -/
-- <<plant_inv>>
theorem plant_inv {ε η Ω δ : ℝ} {sense : ℝ → Float} (HS : SenseSpec δ sense)
    (hs : Small ε η Ω δ) {x : ℕ → X} (hp : x ∈ Mplant sense) (hA : x ∈ A)
    (hc : x ∈ Gctrl ε η) (t : ℕ) :
    |(x t).v + 2 * ((x t).z - 5)| ≤ 8 ∧ |(x t).z - 5| ≤ 4 ∧
      |(x t).v + 2 * ((x t).z - 5)| ≤ 8 * (49/50) ^ t + D ε η δ ∧
      |(x t).z - 5| ≤ 8 * (49/50) ^ t + D ε η δ := by
  obtain ⟨hε0, hε, hη0, hη, hδ0, hδ, -⟩ := hs
  have hD0 : 0 ≤ D ε η δ := by unfold D; positivity
  have hD : D ε η δ ≤ 8 := by unfold D; linarith
  induction t with
  | zero =>
    obtain ⟨h0, hv0⟩ := hA
    rw [hv0, pow_zero]
    rw [abs_le] at h0 ⊢
    refine ⟨?_, abs_le.2 h0, ?_, ?_⟩ <;> (try rw [abs_le]) <;> constructor <;> linarith
  | succ t ih =>
    obtain ⟨iw, ie, dw, de⟩ := ih
    have hstep := hp t
    simp only [plant, phys, Prod.mk.injEq] at hstep
    obtain ⟨⟨hz', hv'⟩, hzf, hvf⟩ := hstep
    have hz100 : |(x t).z| ≤ 100 := by rw [abs_le] at ie ⊢; constructor <;> linarith
    have hv100 : |(x t).v| ≤ 100 := by rw [abs_le] at iw ie ⊢; constructor <;> linarith
    obtain ⟨fz, ez⟩ := HS.sense_err (x t).z hz100
    obtain ⟨fv, ev⟩ := HS.sense_err (x t).v hv100
    rw [← hzf] at fz ez
    rw [← hvf] at fv ev
    rw [abs_le] at iw ie ez ev
    have hzr : |(x t).zf.toReal - 5| ≤ 9/2 := abs_le.2 ⟨by linarith, by linarith⟩
    have hvr : |(x t).vf.toReal| ≤ 33/2 := abs_le.2 ⟨by linarith, by linarith⟩
    obtain ⟨-, eu⟩ := hc t fz fv hzr hvr
    rw [abs_le] at eu
    -- the error `d` of the applied acceleration against the exact law
    have hd : |(x t).uf.toReal - (4 * (5 - (x t).z) - 4 * (x t).v)| ≤ D ε η δ := by
      unfold D; rw [abs_le]; constructor <;> linarith
    have hu : |(x t).uf.toReal| ≤ 100 := by
      rw [abs_le] at hd ⊢; unfold D at hd; constructor <;> linarith
    rw [sat_of_abs_le hu] at hv'
    rw [hz', hv', pow_succ]
    rw [abs_le] at hd dw de
    have hρ : 0 ≤ (8 : ℝ) * (49/50) ^ t := by positivity
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> nlinarith
-- <</plant_inv>>

/-- The plant keeps the altitude under the ceiling for every horizon. -/
-- <<Mplant_ceiling>>
theorem Mplant_ceiling {ε η Ω δ : ℝ} {sense : ℝ → Float} (HS : SenseSpec δ sense)
    (hs : Small ε η Ω δ) (T : ℕ) :
    Mplant sense ⊨ ⟨A ∩ Gctrl ε η, initOn phys (ceiling T)⟩ := by
  rintro x ⟨hp, hA, hc⟩ τ - -
  have := (plant_inv HS hs hp hA hc τ).2.1
  rw [abs_le] at this
  show 0 ≤ 10 - (x τ).z
  linarith
-- <</Mplant_ceiling>>

/-- The plant reaches and holds the band of width `tol` once `8 (49/50)^T₁ + D ≤ tol`. -/
-- <<Mplant_reachHold>>
theorem Mplant_reachHold {ε η Ω δ tol : ℝ} {sense : ℝ → Float} (HS : SenseSpec δ sense)
    (hs : Small ε η Ω δ) (T₁ T₂ : ℕ) (hT : 8 * (49/50) ^ T₁ + D ε η δ ≤ tol) :
    Mplant sense ⊨ ⟨A ∩ Gctrl ε η, initOn phys (reachHold T₁ T₂ tol)⟩ := by
  rintro x ⟨hp, hA, hc⟩
  refine ⟨T₁, by omega, le_refl _, fun σ hσ _ => ?_⟩
  have h := (plant_inv HS hs hp hA hc σ).2.2.2
  have hpow : ((49 : ℝ)/50) ^ σ ≤ (49/50) ^ T₁ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  show 0 ≤ tol - |(x σ).z - 5|
  linarith
-- <</Mplant_reachHold>>

/-! ## The closed loop, by delegation -/

theorem M_eq (sense : ℝ → Float) : M sense = Mctrl ∩ Mplant sense := Set.inter_comm _ _

/-- **The `Float` closed loop meets the ceiling.** For every horizon `T`, from rest within `4` of
the reference `5`, the real altitude stays at or below `10`, provided the rounding hypotheses and the
sensor bound hold with `ε ≤ 1/100`, `η ≤ 1`, `δ ≤ 1/2`, `Ω ≥ 100`. -/
-- <<loop_ceiling>>
theorem loop_ceiling {ε η Ω δ : ℝ} {sense : ℝ → Float} (H : LoopHyp ε η Ω δ sense)
    (hs : Small ε η Ω δ) (T : ℕ) :
    M sense ⊨ ⟨A, initOn phys (ceiling T)⟩ := by
  rw [M_eq]
  exact chain (Mctrl_impl H.toFloatArith hs.ε_nonneg hs.ε_le hs.η_le hs.Ω_ge A)
    (Mplant_ceiling H.toSenseSpec hs T)
-- <</loop_ceiling>>

/-- **The `Float` closed loop reaches and holds.** Under the same hypotheses, the real altitude is
within `tol` of `5` from tick `T₁` for `T₂` ticks whenever `8 (49/50)^T₁ + 8δ + 200ε + 2η ≤ tol`. -/
-- <<loop_reachHold>>
theorem loop_reachHold {ε η Ω δ tol : ℝ} {sense : ℝ → Float} (H : LoopHyp ε η Ω δ sense)
    (hs : Small ε η Ω δ) (T₁ T₂ : ℕ) (hT : 8 * (49/50) ^ T₁ + D ε η δ ≤ tol) :
    M sense ⊨ ⟨A, initOn phys (reachHold T₁ T₂ tol)⟩ := by
  rw [M_eq]
  exact chain (Mctrl_impl H.toFloatArith hs.ε_nonneg hs.ε_le hs.η_le hs.Ω_ge A)
    (Mplant_reachHold H.toSenseSpec hs T₁ T₂ hT)
-- <</loop_reachHold>>

/-- **Both properties at once**, as one STL formula: the ceiling over `[0, T]` and reach-and-hold. -/
-- <<loop_spec>>
theorem loop_spec {ε η Ω δ tol : ℝ} {sense : ℝ → Float} (H : LoopHyp ε η Ω δ sense)
    (hs : Small ε η Ω δ) (T T₁ T₂ : ℕ) (hT : 8 * (49/50) ^ T₁ + D ε η δ ≤ tol) :
    M sense ⊨ ⟨A, initOn phys ((ceiling T).and (reachHold T₁ T₂ tol))⟩ :=
  fun _ hx => ⟨loop_ceiling H hs T hx, loop_reachHold H hs T₁ T₂ hT hx⟩
-- <</loop_spec>>

/-- A concrete instance: with `ε, η ≤ 10⁻³` and `δ ≤ 10⁻²`, the altitude stays under `10` over any
horizon and is within `1/2` of `5` from tick `200` (four seconds at `h = 1/50`) on. -/
-- <<loop_spec_concrete>>
theorem loop_spec_concrete {ε η Ω δ : ℝ} {sense : ℝ → Float} (H : LoopHyp ε η Ω δ sense)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1/1000) (hη0 : 0 ≤ η) (hη : η ≤ 1/1000) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1/100) (hΩ : 100 ≤ Ω) (T T₂ : ℕ) :
    M sense ⊨ ⟨A, initOn phys ((ceiling T).and (reachHold 200 T₂ (1/2)))⟩ := by
  refine loop_spec H ⟨hε0, by linarith, hη0, by linarith, hδ0, by linarith, hΩ⟩ T 200 T₂ ?_
  unfold D
  have : (8 : ℝ) * (49/50) ^ 200 ≤ 1/5 := by norm_num
  linarith
-- <</loop_spec_concrete>>

end Contracts.FloatLoop
