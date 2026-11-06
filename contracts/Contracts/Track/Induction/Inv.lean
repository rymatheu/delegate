import Contracts.Track.Induction.Run

/-!
# M9, part 2: the invariant of the closed loop

`Inv I w₀ x t` is the invariant of TRACK_PLAN.md §3.6 for one behavior `x` of the closed loop, at
every tick up to `t`. Its parts, per tick (`Inv1`, `Region`, `TubeOK`):

* **the world** (`WorldOK`): the stored actuators in `[0, 1]` (M1), the integrators within their
  limits (M2), and from tick 1 on the mission state machine in order (`MInv`, Q5);
* **the region `D°`** (TRACK_PLAN.md §3.2):
  * the channel boxes (`BoxV`, `BoxH`): position errors at most `0.1` m (D6), velocity errors at
    most `0.5` m/s, the integrators strictly inside their limits (D13), the throttle filter and
    `_throttle_in` within `0.12` of hover, that is in `[0.32, 0.57] ⊂ [0.30, 0.62]` (D8), the
    horizontal command at most `4` m/s² (D7) changing by at most `0.05` m/s² per tick;
  * the attitude invariant `AttInv` of M4 (tilt, rates, actuators in `[0.30, 0.62]`, no saturation
    flag: D2–D4, D8–D12), the heading invariant `YawInv` (3.8, Y1–Y5), the code invariant `CtrlInv`
    of the C-series (finite floats, reset flags off, branch conditions: D15–D17);
* **the navigator's phase**: its invariant `NavInv` (target geometry, leg index, S-curve state).
  The pacing itself is not part of the per-tick invariant: it is a statement about the whole run,
  proved by M8's `Pacing.pacing_course` from the code facts of the scaler along the run and the
  tubes (`Main.lean`);
* **the tubes** (`TubeOK`): the deviation `η = ξ - ξ̂` of each channel's error coordinates from the
  certified nominal `ξ̂` (the model's response to the actual target sequence and to the structured
  disturbances `wVs`, `etaHat`), read through the outputs `outV`, `outH`, is within `τV`, `τH`.

The abstract parts (`AttInv`, `YawInv`, `NavInv`, `CtrlInv`, `sc`, `r`, `q`, `ar`, `τv`, the
structured inputs, the vertical trim) are the interfaces of the other milestones, bundled in
`Iface`; `Pieces` (Pieces.lean) states what each must satisfy.

**The numbers** (INDUCTION.md §2): `εV`, `εH` are the per-tick disturbance bounds the C-series
lemmas must deliver (per coordinate, after the structured part), `ε0V`, `ε0H` the deviation after
the first two ticks, `GV`, `PV`, `GH`, `PH` the ℓ1 and peak gains of the channel models (Python,
`2 %` margin, to be certified), and `τV`, `τH`, `τ3`, `τ3v` the tube radii they give
(`τV_spec`, `τH_spec`, `τ3_spec`, `τ3v_spec`).
-/

namespace Contracts.Track.Induction

open Contracts Contracts.STL Contracts.Mission Matrix Finset

noncomputable section

/-! ## The interfaces of the other milestones -/

/-- **The data the other milestones define.** Each is constrained only through the fields of
`Pieces`. -/
structure Iface where
  /-- The structured vertical disturbance (tilt coupling and angle boost, TRACK_PLAN.md §3.3),
  whose response is part of the certified vertical nominal (M5). -/
  wVs : (ℕ → Mission.X) → ℕ → Fin 8 → ℝ
  /-- The structured part of the attitude deviation `η` (the heading coupling, HORIZONTAL.md §7,
  option 1 or 2), whose response is part of the certified horizontal nominal (M4/M6). -/
  etaHat : (ℕ → Mission.X) → ℕ → Fin 2 → ℝ
  /-- The attitude invariant of M4 (TRACK_PLAN.md §8.2). -/
  AttInv : (ℕ → Mission.X) → ℕ → Prop
  /-- The heading-subsystem invariant (TRACK_PLAN.md §3.8). -/
  YawInv : (ℕ → Mission.X) → ℕ → Prop
  /-- The navigator's invariant (MISSION.md, `nav_contract` (d)). -/
  NavInv : (ℕ → Mission.X) → ℕ → Prop
  /-- The code invariant of the C-series lemmas (finite floats, flags, branches). -/
  CtrlInv : (ℕ → Mission.X) → ℕ → Prop
  /-- The filtered track scaler `_track_dt_scalar` after tick `t` (PACING.md `s`). -/
  sc : (ℕ → Mission.X) → ℕ → ℝ
  /-- The raw track scaler of tick `t` (PACING.md `r`). -/
  r : (ℕ → Mission.X) → ℕ → ℝ
  /-- The S-curve time after tick `t`, in ticks (PACING.md `q`). -/
  q : (ℕ → Mission.X) → ℕ → ℝ
  /-- The arrival windows of the S-curve time (PACING.md `a i`, M7). -/
  ar : (ℕ → Mission.X) → Fin 8 → ℝ
  /-- The S-curve time from which the climb's speed stays above `v_min` (PACING.md `τ_v`). -/
  τv : (ℕ → Mission.X) → ℝ

variable (I : Iface) (w₀ : Vehicle.World)

/-! ## Constants -/

/-- The outputs of the vertical channel watched by the region: `ez`, `ev`, `I`, `f`, `u`. -/
def outV : Fin 5 → Fin 8 → ℝ :=
  ![Pi.single 0 1, Pi.single 1 1, Pi.single 4 1, Pi.single 5 1, Pi.single 6 1]

/-- The outputs of a horizontal axis watched by the region: `e`, `ev`, `I`, `c₁`, `c₁ - c₂`. -/
def outH : Fin 5 → Fin 9 → ℝ :=
  ![Pi.single 0 1, Pi.single 1 1, Pi.single 4 1, Pi.single 6 1, Pi.single 6 1 - Pi.single 7 1]

/-- Box of the vertical outputs (D6, velocity, D13, D8). -/
def bV : Fin 5 → ℝ := ![1 / 10, 1 / 2, 1 / 2, 3 / 25, 3 / 25]

/-- Box of the horizontal outputs (D6, velocity, D13, D7, command rate). -/
def bH : Fin 5 → ℝ := ![1 / 10, 1 / 2, 5, 4, 1 / 20]

/-- Per-tick disturbance bound of the vertical channel, per coordinate, after the structured part
`wVs` (which carries the plant residuals, the tilt coupling of the sampled specific force and the
angle boost's deviation: `CtrlV.wS`): the code's `βcode` of `CtrlV.vertical_tick_split` at the
region's magnitudes (`Vert.lean`, `βcode_le`). -/
def εV : Fin 8 → ℝ := ![1e-10, 2.5e-8, 2e-7, 4e-6, 2e-7, 1e-7, 3.2e-6, 4e-7]

/-- Bound of the vertical deviation after the first two ticks. -/
def ε0V : Fin 8 → ℝ := ![1e-6, 1e-6, 1e-5, 1e-5, 1e-4, 1e-4, 1e-4, 1e-4]

/-- Per-tick bound of the horizontal controller and plant rows (`β`, plant remainder). Rows 2, 3, 4,
6 are the bounds `ne_spec` of `CtrlHorizontalTick.lean` proves (`E` 3.6e-6, `D` 2.3e-4, `I` 6.1e-7,
command 1.6e-4) plus the sensing difference through `A_h` (`wHβ_bound`, Horiz.lean); rows 5, 7, 8
are exact by definition (`aLag`, `cmdAgo`); row 1 is exact since `aReal` is the realized mean
acceleration; row 0 is the plant's position row (`prow_le`, PlantRow.lean). -/
def εHβ : Fin 9 → ℝ := ![1.8e-7, 0, 3.7e-6, 2.31e-4, 6.2e-7, 0, 1.61e-4, 0, 0]

/-- Bound of the unstructured attitude deviation `η - η̂`, m/s². -/
def εη : ℝ := 1e-2

/-- Per-tick disturbance bound of a horizontal axis: `εHβ` plus `η - η̂` through `eAcc`. -/
def εH : Fin 9 → ℝ := ![2.2e-7, 2.5e-5, 3.7e-6, 2.31e-4, 6.2e-7, 0, 1.61e-4, 0, 0]

/-- Bound of the horizontal deviation after the first two ticks. -/
def ε0H : Fin 9 → ℝ := ![1e-6, 1e-6, 1e-5, 1e-4, 1e-5, 1e-5, 1e-4, 1e-4, 1e-4]

/-- ℓ1 gains of the vertical outputs per input coordinate. -/
def GV : Fin 5 → Fin 8 → ℝ :=
  ![![408, 97.1, 13, 0.65, 817, 82.9, 2.61, 4.51],
    ![408, 230, 23.3, 1.17, 1050, 203, 6.36, 8.07],
    ![23.8, 23.7, 1.89, 0.0949, 215, 36.1, 1.14, 0.658],
    ![33.1, 32.2, 4.13, 0.214, 116, 43.9, 1.35, 1.48],
    ![33.7, 32.6, 5.34, 0.342, 120, 48.5, 2.55, 2.37]]

/-- Peak gains of the vertical outputs per initial coordinate. -/
def PV : Fin 5 → Fin 8 → ℝ :=
  ![![1.02, 0.258, 0.0286, 0.00144, 1.31, 0.17, 0.00533, 0.00994],
    ![0.898, 1.02, 0.0828, 0.00433, 2.13, 0.752, 0.0237, 0.03],
    ![0.0501, 0.0639, 0.00961, 0.000682, 1.02, 0.109, 0.00342, 0.00473],
    ![0.118, 0.132, 0.0439, 0.00364, 0.428, 1.02, 0.0311, 0.0252],
    ![0.165, 0.173, 0.148, 0.0391, 1.02, 0.818, 1.02, 0.271]]

/-- ℓ1 gains of the horizontal outputs per input coordinate. -/
def GH : Fin 5 → Fin 9 → ℝ :=
  ![![272, 74.3, 29.5, 1.19, 273, 7.15, 0.186, 0.186, 0.186],
    ![408, 129, 37.2, 1.87, 74.4, 11.4, 0.296, 0.296, 0.296],
    ![112, 408, 205, 6.5, 2450, 39.3, 1.02, 1.02, 1.02],
    ![1280, 643, 274, 13.8, 129, 56.4, 2.49, 1.47, 1.47],
    ![34.9, 21.6, 20.1, 1.13, 2.49, 1.18, 2.08, 1.06, 0.0305]]

/-- Peak gains of the horizontal outputs per initial coordinate. -/
def PH : Fin 5 → Fin 9 → ℝ :=
  ![![1.02, 0.147, 0.0398, 0.00213, 0.093, 0.013, 0.000337, 0.000337, 0.000337],
    ![1.39, 1.02, 0.172, 0.00934, 0.135, 0.0598, 0.00156, 0.00156, 0.00156],
    ![0.22, 0.197, 0.0888, 0.00303, 1.02, 0.0184, 0.000477, 0.000477, 0.000477],
    ![14.8, 10.3, 4.6, 0.473, 1.02, 0.561, 1.02, 0.0146, 0.0146],
    ![2.3, 1.53, 4.6, 0.473, 1.02, 0.02, 1.02, 1.02, 0.000518]]

/-- Tube radii of the vertical outputs. -/
def τV : Fin 5 → ℝ := ![0.0028, 0.0063, 0.00075, 0.001, 0.0012]

/-- Tube radii of the horizontal outputs. -/
def τH : Fin 5 → ℝ := ![0.0026, 0.004, 0.015, 0.022, 0.0016]

/-- Tube radius of the 3D position error. -/
def τ3 : ℝ := 0.0047

/-- Tube radius of the 3D velocity error. -/
def τ3v : ℝ := 0.0085

/-! ## Nominal, deviation and tube -/

/-- The vertical error coordinates (`ξV`; the `Iface` argument is kept for uniform call sites). -/
abbrev ξv (_I : Iface) (w : Vehicle.World) (x : ℕ → Mission.X) (t : ℕ) : Fin 8 → ℝ := ξV w x t

/-- **The certified vertical nominal**: the model's response, from zero, to the actual target
sequence and to the structured disturbance. -/
def nomV (x : ℕ → Mission.X) : ℕ → Fin 8 → ℝ :=
  Vertical.traj Vertical.AvR 0 (fun k => Vertical.forceOf (refV w₀ x) k + I.wVs x k)

/-- The vertical disturbance of tick `t`: what the code's tick adds to the model. -/
def wV (x : ℕ → Mission.X) (t : ℕ) : Fin 8 → ℝ :=
  ξv I w₀ x (t + 1) - (Vertical.AvR *ᵥ ξv I w₀ x t + Vertical.forceOf (refV w₀ x) t + I.wVs x t)

/-- The vertical tube coordinate. -/
def ηV (x : ℕ → Mission.X) (t : ℕ) : Fin 8 → ℝ := ξv I w₀ x t - nomV I w₀ x t

/-- **The certified horizontal nominal** of axis `a`. -/
def nomH (x : ℕ → Mission.X) (a : Fin 2) : ℕ → Fin 9 → ℝ :=
  Vertical.traj Horizontal.AhR 0
    (fun k => Horizontal.forceOf (refH w₀ x a) k + I.etaHat x k a • eAcc)

/-- The controller and plant part of the horizontal disturbance of tick `t` (HORIZONTAL.md §7:
the `β`s and the plant remainder), with the attitude deviation `etaA` taken out. -/
def wHβ (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) : Fin 9 → ℝ :=
  ξH w₀ x (t + 1) a -
    (Horizontal.AhR *ᵥ ξH w₀ x t a + Horizontal.forceOf (refH w₀ x a) t + etaA w₀ x t a • eAcc)

/-- The horizontal disturbance of tick `t`: `wHβ` plus the unstructured attitude deviation. -/
def wH (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) : Fin 9 → ℝ :=
  wHβ w₀ x t a + (etaA w₀ x t a - I.etaHat x t a) • eAcc

/-- The horizontal tube coordinate. -/
def ηH (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) : Fin 9 → ℝ := ξH w₀ x t a - nomH I w₀ x a t

theorem ηV_succ (x : ℕ → Mission.X) (t : ℕ) :
    ηV I w₀ x (t + 1) = Vertical.AvR *ᵥ ηV I w₀ x t + wV I w₀ x t := by
  simp only [ηV, wV, nomV, Vertical.traj_succ, mulVec_sub]
  abel

theorem ηH_succ (x : ℕ → Mission.X) (t : ℕ) (a : Fin 2) :
    ηH I w₀ x (t + 1) a = Horizontal.AhR *ᵥ ηH I w₀ x t a + wH I w₀ x t a := by
  simp only [ηH, wH, wHβ, nomH, Vertical.traj_succ, mulVec_sub, sub_smul]
  abel

/-- The 3D position error: vehicle minus target (north, east, down). -/
def E3 (x : ℕ → Mission.X) (t : ℕ) : P3 :=
  !₂[ξH w₀ x t 0 0, ξH w₀ x t 1 0, ξv I w₀ x t 0]

/-- The nominal 3D position error. -/
def nomE3 (x : ℕ → Mission.X) (t : ℕ) : P3 :=
  !₂[nomH I w₀ x 0 t 0, nomH I w₀ x 1 t 0, nomV I w₀ x t 0]

/-- The 3D velocity error: vehicle minus velocity target. -/
def V3 (x : ℕ → Mission.X) (t : ℕ) : P3 :=
  !₂[ξH w₀ x t 0 1, ξH w₀ x t 1 1, ξv I w₀ x t 1]

/-- The nominal 3D velocity error. -/
def nomV3 (x : ℕ → Mission.X) (t : ℕ) : P3 :=
  !₂[nomH I w₀ x 0 t 1, nomH I w₀ x 1 t 1, nomV I w₀ x t 1]

/-! ## The phase -/

/-- The mission is complete after tick `t`. -/
def complete (x : ℕ → Mission.X) (t : ℕ) : Prop := (run w₀ x (t + 1)).au.state = .COMPLETE

/-! ## The invariant -/

/-- The world facts that need no region (M1, M2, Q5). -/
structure WorldOK (x : ℕ → Mission.X) (t : ℕ) : Prop where
  act : ActOK (run w₀ x t).ms._actuator
  int : IntOK (run w₀ x t)
  order : 1 ≤ t → Quick.MInv w₀.mission (run w₀ x t)

/-- The vertical box. -/
def BoxV (x : ℕ → Mission.X) (t : ℕ) : Prop := ∀ o, |outV o ⬝ᵥ ξv I w₀ x t| ≤ bV o

/-- The horizontal boxes. -/
def BoxH (x : ℕ → Mission.X) (t : ℕ) : Prop := ∀ a o, |outH o ⬝ᵥ ξH w₀ x t a| ≤ bH o

/-- **The region `D°`** at tick `t`. -/
structure Region (x : ℕ → Mission.X) (t : ℕ) : Prop where
  /-- The invariant is kept over the horizon (12000 ticks, the span of `ψtrack`). -/
  hz : t ≤ horizonTicks
  world : WorldOK w₀ x t
  boxV : BoxV I w₀ x t
  boxH : BoxH w₀ x t
  att : I.AttInv x t
  yaw : I.YawInv x t
  nav : I.NavInv x t
  ctrl : I.CtrlInv x t

/-- **The tubes** at tick `t`. -/
structure TubeOK (x : ℕ → Mission.X) (t : ℕ) : Prop where
  v : ∀ o, |outV o ⬝ᵥ ηV I w₀ x t| ≤ τV o
  h : ∀ a o, |outH o ⬝ᵥ ηH I w₀ x t a| ≤ τH o

/-- The invariant at one tick. -/
structure Inv1 (x : ℕ → Mission.X) (t : ℕ) : Prop where
  region : Region I w₀ x t
  tube : TubeOK I w₀ x t

/-- **The invariant** `Inv t`: `Inv1` at every tick up to `t`. -/
def Inv (x : ℕ → Mission.X) (t : ℕ) : Prop := ∀ k ≤ t, Inv1 I w₀ x k

/-- What the certified nominal may assume at tick `t`: the invariant before `t`, the navigator's
phase at `t`. -/
def Pre (x : ℕ → Mission.X) (t : ℕ) : Prop :=
  (∀ k < t, Inv1 I w₀ x k) ∧ I.NavInv x t

/-- The commands of tick `t` are in the class of the attitude contract (M4): at most `4` m/s²,
changing by at most `0.05` m/s² per tick. -/
def CmdOK (x : ℕ → Mission.X) (t : ℕ) : Prop :=
  ∀ a, |cmd w₀ x t a| ≤ 4 ∧ |cmd w₀ x t a - cmdAgo w₀ x t 1 a| ≤ 1 / 20

/-! ## The numbers -/

theorem τV_spec (o : Fin 5) :
    ∑ j, PV o j * ε0V j + ∑ j, GV o j * εV j ≤ τV o := by
  fin_cases o <;> simp [PV, GV, ε0V, εV, τV, Fin.sum_univ_eight] <;> norm_num

theorem τH_spec (o : Fin 5) :
    ∑ j, PH o j * ε0H j + ∑ j, GH o j * εH j ≤ τH o := by
  fin_cases o <;> simp [PH, GH, ε0H, εH, τH, Fin.sum_univ_succ] <;> norm_num

/-- `εH` covers `εHβ` plus the unstructured attitude deviation through `eAcc`. -/
theorem εH_spec (j : Fin 9) : εHβ j + |eAcc j| * εη ≤ εH j := by
  fin_cases j <;> simp [εHβ, eAcc, εη, εH, Plant.h] <;> norm_num

theorem εV_nonneg (j : Fin 8) : 0 ≤ εV j := by fin_cases j <;> simp [εV] <;> norm_num

theorem εH_nonneg (j : Fin 9) : 0 ≤ εH j := by fin_cases j <;> simp [εH] <;> norm_num

/-- The 3D position tube: `√(2 τH₀² + τV₀²) ≤ τ3`. -/
theorem τ3_spec : 2 * τH 0 ^ 2 + τV 0 ^ 2 ≤ τ3 ^ 2 := by norm_num [τH, τV, τ3]

/-- The 3D velocity tube: `√(2 τH₁² + τV₁²) ≤ τ3v`. -/
theorem τ3v_spec : 2 * τH 1 ^ 2 + τV 1 ^ 2 ≤ τ3v ^ 2 := by norm_num [τH, τV, τ3v]

end

end Contracts.Track.Induction
