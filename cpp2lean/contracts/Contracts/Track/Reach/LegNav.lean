import Contracts.Track.Reach.Leg

/-!
# The leg theorem, parts (2)–(3) on the loop: the tube of a behavior, the end of the S-curve, the
completion and the loiter target (REACH.md §9)

* `legModel_of_run`: the facts `LegRun` of a behavior give the abstract model `LegModel` of
  LegTube.lean for its readouts `ξV`, `ξH` (the steps are the definitions of the disturbances
  `legWV`, `legWH`), so `leg_box` holds on the loop.
* `err_eq`: the tracking error `err` is the Euclidean norm of the three position readouts.
* `Tc_le`: **the mission completes by tick 2617** (the leg's S-curve has finished by tick 2200 with
  the target at rest at `w'`; `Mc = 416` ticks later the vehicle is within `0.077` of the target
  (`tail_e_c`: the leg's reference counts through the tails past `Mc`), so within `0.078` of `w'`,
  and the completion test fires on the next tick). An ℓ1 tube along the leg would be `0.145`, too
  wide for the completion radius `0.099` (the velocity defect contributes `0.059`).
* `loiter_near`: **the loiter target is within `0.081` of `w'`**.
-/

namespace Contracts.Track.Reach.Leg

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue

noncomputable section

variable {w₀ : Vehicle.World} {w' : P3} {x : ℕ → X}

/-- **The model of a behavior**: its readouts follow `LegModel` from tick 2. -/
theorem legModel_of_run (hx : LegRun w₀ w' x) :
    LegModel (ξV w₀ x) (legWV w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) ts where
  stepV t _ := by
    simp only [legWV, Vertical.forceOf, aZ, d1Z, d2Z, neg_smul]
    abel
  stepH t _ a := by
    simp only [legWH, Horizontal.forceOf, aH, d1H, d2H, neg_smul]
    abel
  initV := hx.init.1
  initH := hx.init.2.1
  initA := hx.init.2.2.1
  initD := hx.init.2.2.2
  tick := hx.tick

/-- The tracking error is the norm of the position readouts. -/
theorem err_eq (t : ℕ) :
    err (x t) = Real.sqrt (ξH w₀ x t 0 0 ^ 2 + ξH w₀ x t 1 0 ^ 2 + ξV w₀ x t 0 ^ 2) := by
  rw [err, dist_eq3, ξH_zero, ξH_zero, ξV_zero]
  simp [pos, ph, pIx]

/-- The box at every tick up to the horizon, for a behavior with the facts. -/
theorem box_run (hx : LegRun w₀ w' x) (hg : RefGains) (t : ℕ) (h1 : ts ≤ t) (h2 : t ≤ hzn) :
    BoxL (ξV w₀ x) (ξH w₀ x) t := by
  obtain ⟨N, rfl⟩ : ∃ N, t = ts + N := ⟨t - ts, by omega⟩
  exact leg_box (legModel_of_run hx) hg N h2

/-- **The velocity defect summed over the run**, from the field `d2sum` and the box. -/
theorem d2sum_run (hx : LegRun w₀ w' x) (hg : RefGains) (N : ℕ) (hN : ts + N ≤ hzn) (a : Fin 2) :
    ∑ k ∈ Finset.range N, |d2H w₀ x (ts + k) a| ≤ 1 / 4 :=
  hx.d2sum N hN (fun k hk1 hk2 => box_run hx hg k hk1 (by omega)) a

/-- **The completion by tick 2617**: the leg's S-curve has finished by tick 2200 (`arrive`); if the
mission has not completed `Mc = 416` ticks later, the vehicle is then within `0.077` of the target
(the decay of the leg's reference, `tail_e_c`), which is at `w'`, so the completion test fires on
the next tick. -/
theorem Tc_le (hx : LegRun w₀ w' x) (hg : RefGains) {Tc Tl : ℕ}
    (hP : LegPhase w₀ w' x Tc Tl) : Tc ≤ 2200 + Mc + 1 := by
  have hM := legModel_of_run hx
  obtain ⟨Te, h1, h2, h3, h4⟩ := hP.arrive
  by_contra hlt
  push Not at hlt
  have eMc : Mc = 416 := rfl
  have eH : hzn = 6000 := rfl
  have hTe : Te + Mc < Tc := by omega
  obtain ⟨N, hN⟩ : ∃ N, Te + Mc = ts + N := ⟨Te + Mc - ts, by simp [ts] at h1 ⊢; omega⟩
  have hNz : ts + N ≤ hzn := by rw [← hN]; omega
  have hz : ∀ a, ∀ t, Te ≤ t → t < ts + N →
      |aH w₀ x t a| ≤ 1 / 10 ^ 6 ∧ |d1H w₀ x t a| ≤ 1 / 10 ^ 8 ∧ |d2H w₀ x t a| ≤ 3 / 10 ^ 6 :=
    fun a t ht1 ht2 => (h3 t ht1 (by omega)).2 a
  have e0 := tail_e_c hM hg Te 0 N (hz 0) (d2sum_run hx hg N hNz 0) (by omega) hNz
  have e1 := tail_e_c hM hg Te 1 N (hz 1) (d2sum_run hx hg N hNz 1) (by omega) hNz
  have ez := leg_z hM hg Tc (fun t ht1 ht2 => hP.legV t ht1 ht2) N (by omega) hNz
  have q := complete_3d e0 e1 ez
  have he : err (x (ts + N)) ≤ 77 / 1000 := by
    rw [err_eq, Real.sqrt_le_left (by norm_num)]
    exact q
  have ht := (h3 (ts + N) (by omega) (by omega)).1
  have hd : dist (pos (x (ts + N))) w' ≤ 99 / 1000 := by
    have := dist_triangle (pos (x (ts + N))) (posTarget (x (ts + N))) w'
    have e : err (x (ts + N)) = dist (pos (x (ts + N))) (posTarget (x (ts + N))) := rfl
    linarith
  have := h4 (ts + N) (by omega) (by omega) hd
  omega

/-- **The loiter target is within `0.081` of `w'`** (the state at completion, `loiter_dest_bound`
at its estimates). -/
theorem loiter_near {Tc Tl : ℕ} (hP : LegPhase w₀ w' x Tc Tl) :
    dist (posTarget (x Tl)) w' ≤ 8 / 100 + 1 / 1000 := by
  have h1 := hP.loiter
  have h2 := hP.atComplete
  linarith

end

end Contracts.Track.Reach.Leg
