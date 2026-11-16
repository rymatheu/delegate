import Contracts.Track.Reach.LegNav

/-!
# The leg theorem, parts (4)–(5): the hold window and the assembly (REACH.md §9)

* `forcing_small_H`, `forcing_small_V`, `target_held`: once the loiter S-curve has finished (`Tl`),
  the target is held at the loiter point with velocity and acceleration targets below `10⁻⁶`, so the
  reference forcing of both channels is below `10⁻⁶`, `3·10⁻⁹`, `3·10⁻⁶`.
* `err_hold`: **the hold**: from `Mt = 1728` ticks after `Tl` to the horizon, the vehicle is within
  `0.0166` of the loiter point (the tails of the responses to the leg's and the loiter's reference
  past `Mt`, the velocity defect through its sum over the run and the peak of the tail, the full
  gains on the residual forcing of the hold, `tail_e`/`tail_z`, and the tube).
* `waypoint_reach_h`: **the leg theorem**. The window starts at `Tl + 1728 ≤ 2617 + 450 + 1728 =
  4795 ≤ 4800`; on it `‖p − w'‖ ≤ 0.0166 + 0.081 = 0.0976 ≤ 0.1`.

The hold is carried by the leg's own tube (one ℓ1 tube from tick 2 to the horizon, with the
reference forcing vanishing from `Tl`), not by `Glue.hover_hold`: `hover_hold`'s start region
`RegionG` weighs all nine readouts by their peak gains (the tube bounds only the five watched
outputs; `E`, `D` and the lag state `a` are not watched) and its decay is in the `P`-norm
(`startSize`), and its vertical table `εVh` is the hover one, smaller than the leg's `εVL`.
-/

namespace Contracts.Track.Reach.Leg

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue

noncomputable section

variable {w₀ : Vehicle.World} {w' : P3} {x : ℕ → X}

/-- After the loiter, the position target is the loiter point. -/
theorem target_held {Tc Tl : ℕ} (hP : LegPhase w₀ w' x Tc Tl) (t : ℕ)
    (ht : Tl ≤ t) : posTarget (x t) = posTarget (x Tl) := (hP.hold t ht).1

theorem per_le : (Horizontal.per : ℝ) = 1 / 400 := by norm_num [Horizontal.per]
theorem perV_le : (Vertical.per : ℝ) = 1 / 400 := by norm_num [Vertical.per]

/-- After the loiter, the horizontal reference forcing is below `10⁻⁶`, `3·10⁻⁹`, `3·10⁻⁶`. -/
theorem forcing_small_H {Tc Tl : ℕ} (hP : LegPhase w₀ w' x Tc Tl) (a : Fin 2)
    (t : ℕ) (ht : Tl ≤ t) :
    |aH w₀ x t a| ≤ 1 / 10 ^ 6 ∧ |d1H w₀ x t a| ≤ 3 / 10 ^ 9 ∧ |d2H w₀ x t a| ≤ 3 / 10 ^ 6 := by
  obtain ⟨p0, h0⟩ := hP.hold t ht
  obtain ⟨p1, h1⟩ := hP.hold (t + 1) (by omega)
  have v0 := (h0 a.castSucc).1
  have a0 := (h0 a.castSucc).2
  have v1 := (h1 a.castSucc).1
  have hp : posTarget (x (t + 1)) a.castSucc = posTarget (x t) a.castSucc := by rw [p1, p0]
  refine ⟨?_, ?_, ?_⟩
  · simpa [aH, refH, refAx] using a0
  · simp only [d1H, refH, refAx, Horizontal.defect₁, hp, per_le]
    rw [abs_le] at v0 a0 ⊢
    constructor <;> nlinarith [v0.1, v0.2, a0.1, a0.2]
  · simp only [d2H, refH, refAx, Horizontal.defect₂, per_le]
    rw [abs_le] at v0 v1 a0 ⊢
    constructor <;> nlinarith [v0.1, v0.2, v1.1, v1.2, a0.1, a0.2]

/-- After the loiter, the vertical reference forcing is below `10⁻⁶`, `3·10⁻⁹`, `3·10⁻⁶`. -/
theorem forcing_small_V {Tc Tl : ℕ} (hP : LegPhase w₀ w' x Tc Tl) (t : ℕ)
    (ht : Tl ≤ t) :
    |aZ w₀ x t| ≤ 1 / 10 ^ 6 ∧ |d1Z w₀ x t| ≤ 3 / 10 ^ 9 ∧ |d2Z w₀ x t| ≤ 3 / 10 ^ 6 := by
  obtain ⟨p0, h0⟩ := hP.hold t ht
  obtain ⟨p1, h1⟩ := hP.hold (t + 1) (by omega)
  have v0 := (h0 2).1
  have a0 := (h0 2).2
  have v1 := (h1 2).1
  have hp : posTarget (x (t + 1)) 2 = posTarget (x t) 2 := by rw [p1, p0]
  refine ⟨?_, ?_, ?_⟩
  · simpa [aZ, refV, refAx] using a0
  · simp only [d1Z, refV, refAx, Vertical.defect₁, hp, perV_le]
    rw [abs_le] at v0 a0 ⊢
    constructor <;> nlinarith [v0.1, v0.2, a0.1, a0.2]
  · simp only [d2Z, refV, refAx, Vertical.defect₂, perV_le]
    rw [abs_le] at v0 v1 a0 ⊢
    constructor <;> nlinarith [v0.1, v0.2, v1.1, v1.2, a0.1, a0.2]

/-- **The hold**: from `Tl + Mt` to the horizon the vehicle is within `0.0166` of the target. -/
theorem err_hold (hx : LegRun w₀ w' x) (hg : RefGains) {Tc Tl : ℕ}
    (hP : LegPhase w₀ w' x Tc Tl) (t : ℕ) (h1 : Tl + Mt ≤ t) (h2 : t ≤ hzn) :
    err (x t) ≤ 166 / 10000 := by
  have hM := legModel_of_run hx
  have hts : ts ≤ Tl := hP.order.1.trans hP.order.2.1
  obtain ⟨N, rfl⟩ : ∃ N, t = ts + N := ⟨t - ts, by omega⟩
  have e0 := tail_e hM hg Tl 0 (forcing_small_H hP 0) N (d2sum_run hx hg N h2 0) h1 h2
  have e1 := tail_e hM hg Tl 1 (forcing_small_H hP 1) N (d2sum_run hx hg N h2 1) h1 h2
  have ez := tail_z hM hg Tl (forcing_small_V hP) N h1 h2
  rw [err_eq, Real.sqrt_le_left (by norm_num)]
  exact hold_3d e0 e1 ez

/-- **The leg theorem**: horizontal waypoint reachability from hover on the closed loop, bounded
time. From a hover at `p₀` (any heading `ψ₀`), one waypoint `w'` at the same altitude within
3.6 m: within 4800 ticks the vehicle is within `0.1` of `w'` for 1200 consecutive ticks. -/
theorem waypoint_reach_h (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (hP : LegParams w₀)
    (hmin : 1 / 100 ≤ dist p₀ (wpt w'))
    (hR : dist p₀ (wpt w') ≤ 36 / 10) (hZ : wpt w' 2 = p₀ 2) (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP)
    (hL : LibmSpec) (hF : LegFacts sense32 senseP w₀ p₀ w' ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, lang_t 0 (.eventually 0 4800 (.always 0 1200 (near (wpt w') (1 / 10))))⟩ := by
  rintro x ⟨hx, hA⟩
  have hrun := hF.run x ⟨hx, hA⟩
  obtain ⟨Tc, Tl, hP⟩ := hrun.phase
  have hTc := Tc_le hrun refGains_certified hP
  have hTl := hP.order.2.2
  have hL' := loiter_near hP
  have eM : Mt = 1728 := rfl
  have eMc : Mc = 416 := rfl
  have eH : hzn = 6000 := rfl
  simp only [mem_lang_t, sat_eventually, sat_always, sat_near]
  refine ⟨Tl + Mt, by omega, by omega, fun τ h1 h2 => ?_⟩
  have hE := err_hold hrun refGains_certified hP τ (by omega) (by omega)
  have hT := target_held hP τ (by omega)
  have := dist_triangle (pos (x τ)) (posTarget (x τ)) (wpt w')
  rw [hT] at this
  have : err (x τ) = dist (pos (x τ)) (posTarget (x τ)) := rfl
  rw [hT] at this
  linarith

/-- The leg theorem as the statement `WaypointReachH` of Leg.lean. -/
theorem waypointReachH_holds (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) :
    WaypointReachH sense32 senseP w₀ p₀ w' ψ₀ :=
  fun hP hmin hR hZ hW hS hL hF => waypoint_reach_h sense32 senseP w₀ p₀ w' ψ₀ hP hmin hR hZ hW hS hL hF

end

end Contracts.Track.Reach.Leg
