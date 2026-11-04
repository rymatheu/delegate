import Contracts.CopterHoverTick0
import Contracts.CopterHoverTick1

/-!
# Hover invariance of the ArduCopter port closed with the Crazyflie plant

The closed loop `McopterH runParams ∩ MplantH sense32 senseP` (the Lean port of ArduCopter in
Auto at 400 Hz, as the `copter` executable runs it, with the run parameters `runParams` of
`sim/params/copter-cf2x.txt` and the one-waypoint mission of `sim/params/copter-hover.txt`, and
the CF2X rigid body with `Float32`/binary64 ports), started at the waypoint, level, facing north,
at rest (`Ahover`), stays for all time exactly on the vertical through the waypoint, level, not
rotating, within `5 mm` of the waypoint altitude and `1 cm/s` of vertical rest (`hover_invariant`).

The proof is an induction over ticks with three phases:

* **tick 0** (`tick_zero`, Contracts/CopterHoverTick0*.lean): the harness's `takeover`, the switch
  into Auto (`ModeAuto::init`, the position controller's initialization at the stopping point),
  the mission start on an empty first leg (the vehicle is at the waypoint), the first vertical tick
  with both vertical PIDs in reset (`vert_tick0`); the waypoint is reached on this tick. Result:
  `InvP1`;
* **tick 1** (`tick_one`, Contracts/CopterHoverTick1.lean): the mission completes and the vehicle
  enters loiter at the stopping point, whose leg from the waypoint is empty (a few micrometers,
  below `AC_WPNav`'s `FLT_EPSILON` threshold), so the navigator keeps the waypoint as its target.
  Result: `InvSteady`;
* **ticks ≥ 2** (`tick_steady`, Contracts/CopterHoverInv.lean): `InvSteady` is preserved. The
  horizontal and rotational channels stay exactly at zero (Contracts/CopterZero*.lean and the
  frame lemmas of Contracts/CopterHover{Att,Motors,NE,Nav,Dctl}.lean), the four actuators are
  equal so the plant moves on the vertical only, and the vertical floats follow the perturbed
  linear recurrence `CopterVert.stepN` (`vert_tick`) whose Lyapunov sublevel set `V ≤ 1/10` lies in
  the box (`CopterVert.lyap_stepN`, `box_of_V`).

**Hypotheses.** Each is about an opaque `extern` constant of core Lean (the C library or a C
conversion), which cannot be evaluated in the kernel, or about the sensor ports:
* `LibmZero32`: `acosf`, `sinf`, `cosf`, `atan2f`, `asinf` at zero (C99 Annex F);
* `LibmCos32`: `cosf` of a finite argument is finite (the motor matrix's roll and pitch factors
  at boot);
* `ConvZero`: `float ↔ double` conversions map `±0` to `±0`;
* `NarrowSpec 2`: `(float)x` rounds to nearest on `|x| ≤ 2` (IEEE 754);
* `WidenSpec`: `(double)x` is exact (IEEE 754; the stopping points widen nonzero positions);
* `CopterSense`: the binary32 and binary64 sensor ports round to nearest on their ranges and map
  `0` to `+0` and `1` to `1`.

**Non-vacuity**: the closed loop meets the assumption for every pair of sensors
(`hover_nonvacuous`, Contracts/CopterHoverUniverse.lean).
-/

namespace Contracts.CopterHover

open Contracts.Lift Contracts.CopterLift Contracts.CopterPlant

/-- The phase invariant of tick `t`: the boot state, the state after tick 0, the steady state. -/
def Phase (P : Copter.Parameters) : ℕ → Harness → CState → Prop
  | 0, h, x => h = Harness.init P ∧ x = phys0
  | 1, h, x => h.started = true ∧ InvP1 h.st x ∧ 1 / 100 ≤ h.st.pos_control._accel_max_d_mss.toReal
  | _ + 2, h, x => h.started = true ∧ InvSteady h.st x

/-- Every phase puts the plant state in the box. -/
theorem Phase.box {t : ℕ} {h : Harness} {x : CState} (hp : Phase runParams t h x) :
    ∃ z w f : ℝ, x = vstate z w f ∧ |z + 1| ≤ 1 / 200 ∧ |w| ≤ 1 / 100 := by
  match t, hp with
  | 0, ⟨_, hx⟩ => exact ⟨-1, 0, _, hx, by norm_num, by norm_num⟩
  | 1, ⟨_, hi, _⟩ => exact hi.1.box
  | _ + 2, ⟨_, hi⟩ => exact hi.1.box

/-- One closed-loop tick moves each phase to the next. -/
theorem Phase.step (L : CopterZero.LibmZero32) (LC : LibmCos32) (C : CopterZero.ConvZero)
    (N : CopterVertNear.NarrowSpec 2) (W : WidenSpec) {sense32 : ℝ → Float32} {senseP : ℝ → Float}
    (S : CopterSense sense32 senseP) {t : ℕ} {h : Harness} {x : CState}
    (hp : Phase runParams t h x) :
    Phase runParams (t + 1) (tick runParams h (sample sense32 senseP x)).1
      (dyn x (tick runParams h (sample sense32 senseP x)).2) := by
  match t, hp with
  | 0, ⟨hh, hx⟩ =>
    subst hh hx
    exact tick_zero L LC C N W S
  | 1, ⟨hs, hi, hA⟩ =>
    obtain ⟨st, b⟩ := h
    simp only at hs
    subst hs
    exact tick_one L C N W S st x hi hA
  | _ + 2, ⟨hs, hi⟩ =>
    obtain ⟨st, b⟩ := h
    simp only at hs
    subst hs
    exact tick_steady L C N S st x hi

/-- **Hover invariance.** Started at the waypoint, level and at rest, the closed loop of the
ArduCopter port (run parameters `runParams`, hover mission) and the Crazyflie plant stays on the
vertical through the waypoint, level, facing north and not rotating, within `5 mm` of the waypoint
altitude and `1 cm/s` of vertical rest, over every horizon `T`. -/
-- <<copter_hover_invariant>>
theorem hover_invariant (L : CopterZero.LibmZero32) (LC : LibmCos32) (C : CopterZero.ConvZero)
    (N : CopterVertNear.NarrowSpec 2) (W : WidenSpec) {sense32 : ℝ → Float32} {senseP : ℝ → Float}
    (S : CopterSense sense32 senseP) (T : ℕ) :
    McopterH runParams ∩ MplantH sense32 senseP ⊨
      ⟨Ahover, initOn (·.phys) (.always 0 T hoverBox)⟩ := by
  rintro x ⟨⟨hM, hP⟩, hA⟩
  obtain ⟨s, hs0, hs⟩ := mem_McopterH.1 hM
  have hP' := mem_MplantH.1 hP
  have inv : ∀ t, Phase runParams t (s t) (x t).phys := by
    intro t
    induction t with
    | zero => exact ⟨hs0, hA⟩
    | succ t ih =>
      have e := hs t
      rw [(hP' t).2] at e
      have h1 : s (t + 1) = (tick runParams (s t) (sample sense32 senseP (x t).phys)).1 :=
        congrArg Prod.fst e
      have h2 : (x t).act = (tick runParams (s t) (sample sense32 senseP (x t).phys)).2 :=
        congrArg Prod.snd e
      rw [h1, (hP' t).1, h2]
      exact Phase.step L LC C N W S ih
  rw [mem_initOn]
  intro τ _ _
  obtain ⟨z, w, f, hx, hz, hw⟩ := (inv τ).box
  exact sat_hoverBox (x := fun t => (x t).phys) hx hz hw
-- <</copter_hover_invariant>>

/-- **Non-vacuity** of the hover theorem: the closed loop meets the assumption. -/
theorem hover_invariant_nonvacuous (sense32 : ℝ → Float32) (senseP : ℝ → Float) :
    (McopterH runParams ∩ MplantH sense32 senseP ∩ Ahover).Nonempty :=
  hover_nonvacuous sense32 senseP

end Contracts.CopterHover
