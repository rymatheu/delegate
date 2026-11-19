import Contracts.Mission.SubSpec
import Contracts.Mission.NavStop
import Contracts.Track.Induction.Instance

/-!
# The three sub-contracts

The mission contract is assembled (`Theorem.lean`) from

* `nav_contract`, a contract of the controller `Mctrl w₀` alone: under assumptions on the samples
  it reads (well-formed, starting in the box at rest, tracking the target), the position target
  stays within `ρ` of the polyline or in the takeoff column above the box;
* `track_contract`, a contract of the closed loop `Mloop` from `Atakeoff`: the tracking error is at
  most `δ` (at most `δ₀` while the target is still in the column outside the `ρ`-corridor), the
  rigid-body state stays in an envelope, near each waypoint the vehicle is within `r` whenever the
  target is within `rPass`, and the target reaches the waypoints in order within the allowances and
  holds near `w7`;
* `arrive_lemma`: reaching transfers from the target to the vehicle through any tick-wise
  transfer property, with no time shift. It is proved; `transfer_of_err` is the transfer from an
  error bound `δ` with `rT + δ ≤ r`.

`nav_contract` and `track_contract` are open (`sorry`).

**Why the split is not "target reaches, error small, so vehicle reaches".** In the nominal run
(`sim/out/lean-course-1ms`) the target never comes within `r = 0.1` m of `w0 … w6`: ArduPilot's
S-curves blend the corners and cut them by the waypoint radius (closest approach `0.1000`–`0.1006` m),
and after the mission completes the loiter target sits `0.028` m from `w7`. The vehicle reaches every
waypoint within `0.1` m only because it lags the target into the corner (closest `0.070`–`0.073` m).
An isotropic error bound cannot carry that, so the transfer near the waypoints is a closed-loop
statement (`proxAllF`, in `track_contract`); while the target is within `rPass = 0.105` m of a
waypoint the vehicle was within `0.1` m in the nominal run, with 12 to 37 ticks to spare on each side.

**Why the target's timing is in `track_contract`.** The navigator advances its S-curve time at the
rate `track_scaler_dt = clamp(0.05 + (v·d − kP e·d)/|v_T|, 0, 1)` (`AC_WPNav::advance_wp_target_along_track`),
which depends on the sampled velocity and position error. In the nominal run it is `0` at every leg
start (418 ticks below `0.8`); samples that keep a small constant lag with zero velocity freeze the
target while satisfying any tick-wise tracking tolerance. So no assumption on the samples tick by tick
makes the target's timing true for the controller alone; it is a property of the loop.
-/

namespace Contracts.Mission

open Contracts Contracts.STL

noncomputable section

/-! ## The sub-contracts -/

/-- **Navigation** (open). The translated controller alone keeps its position target within `ρ` of
the planned polyline, or in the takeoff column while it climbs out of the box, on every sample stream
that starts at rest in the box, keeps the 2500 µs period, stays finite and in the envelope, tracks
the target within `δs`, and keeps the sampled velocity within `δv` of the velocity target while the
target rests at `w7` (`restF`). The proof is about the translated `AC_WPNav` (straight S-curve legs
from the stopping point, corner blending within `WP_RADIUS_M`, the loiter at the end) and
`AC_PosControl` (the target is not pulled toward the vehicle within the leash).

The first statement (column bottom at `0.001`, no `restF`) was refuted by evaluation
(`MissionData/NavCex.lean`, `MISSION.md`); this is the corrected one. Proved parts:
`NavStop.lean` (the loiter destination, milestone (a)), `NavLeg.lean` and `NavBlend.lean` (the
geometry of a straight leg and of the corner blend, milestones (b) and (c)). -/
theorem nav_contract (w₀ : Vehicle.World) (hM : MissionWorld w₀) (hL : LibmSpec) :
    Mctrl w₀ ⊨ ⟨lang_t 0 ψnavA, lang_t 0 ψnavG⟩ := by
  sorry

/-- **Tracking and pacing** (open). In the closed loop from the takeoff assumption: the vehicle
tracks the target within `δ` (within `δ₀` during the climb out of the box), stays in the envelope,
is within `r` of each waypoint whenever the target is within `rPass` of it, keeps the sampled velocity
within `δv` of the velocity target while the target rests at `w7`, and the target reaches the
waypoints in order within the allowances and holds near `w7`. The escape of the climb
(`ClimbEscape`, validated, not proved) is a hypothesis. -/
theorem track_contract (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (hM : MissionWorld w₀) (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hE : ClimbEscape sense32 senseP w₀) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψtrack⟩ :=
  Contracts.Track.Induction.track_contract_proof sense32 senseP w₀ hM hS hL hE

/-- **Arrival** (proved). If at every tick up to `N` the formula `F w` implies `G w` for each point
`w` of the list, then reaching the points in order through `F` implies reaching them in order
through `G`, with the same allowances, from any `t` with `t + span L ≤ N`. -/
theorem arrive_lemma {F G : P3 → Formula X} {L' : List (P3 × ℕ)} (x : ℕ → X) (N : ℕ)
    (hFG : ∀ τ ≤ N, ∀ w, ∀ T, (w, T) ∈ L' → sat x τ (F w) → sat x τ (G w)) :
    ∀ (L : List (P3 × ℕ)) (t : ℕ), (∀ p ∈ L, p ∈ L') → t + span L ≤ N →
      sat x t (reachSeqF F L) → sat x t (reachSeqF G L)
  | [], t, _, _, h => h
  | (w, T) :: rest, t, hL, hN, h => by
    simp only [reachSeqF, sat_eventually, sat_and] at h ⊢
    obtain ⟨τ, h0, h1, hw, hr⟩ := h
    have hspan : span ((w, T) :: rest) = T + span rest := by simp [span]
    refine ⟨τ, h0, h1, hFG τ (by omega) w T (hL _ (by simp)) hw, ?_⟩
    exact arrive_lemma x N hFG rest τ (fun p hp => hL p (by simp [hp])) (by omega) hr

/-- The transfer from an error bound: if the tracking error is at most `δ'` and the target is
within `rT` of `w`, the vehicle is within `rT + δ'` of `w`. -/
theorem transfer_of_err {x : ℕ → X} {τ : ℕ} {w : P3} {rT δ' r : ℝ} (hr : rT + δ' ≤ r)
    (he : sat x τ (errLE δ')) (hT : sat x τ (nearT w rT)) : sat x τ (near w r) := by
  simp only [sat_errLE, sat_nearT, sat_near, err] at *
  linarith [dist_triangle (pos (x τ)) (posTarget (x τ)) w]

/-- **Arrival from an error bound**: with `rT + δ' ≤ r`, if the error is at most `δ'` up to `N`,
the vehicle reaches in order within `r` whatever the target reaches in order within `rT`. (For this
mission `rT + δ ≤ r` would need the target within `0.005` m of each waypoint, which the corner
cutting of the S-curves rules out; the mission uses `proxAllF` instead.) -/
theorem arrive_of_err (x : ℕ → X) (N : ℕ) {rT δ' r : ℝ} (hr : rT + δ' ≤ r)
    (he : ∀ τ ≤ N, sat x τ (errLE δ')) (L : List (P3 × ℕ)) (t : ℕ) (hN : t + span L ≤ N)
    (h : sat x t (reachSeqT rT L)) : sat x t (reachSeq r L) :=
  arrive_lemma (L' := L) x N (fun τ hτ _ _ _ hw => transfer_of_err hr (he τ hτ) hw) L t
    (fun _ hp => hp) hN h

end

end Contracts.Mission
