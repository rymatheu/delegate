import Contracts.Track.Reach.Leg3

/-!
# The 3D leg theorem on the loop: the model of a behavior, the completion, the loiter (REACH.md §10)

* `legModel3_of_run`: the facts `LegRun3` give the abstract model `LegModel3` of Leg3Tube.lean.
* `Tc_le3`: **the mission completes by tick 2905**: the leg's S-curve has finished by tick 2200 with
  the target at rest at `w'`; `Mc3 = 704` ticks later the vehicle is within `0.0921` of the target
  (horizontal tails past `Mc = 416`, vertical tails past `Mc3`), so within `0.0931` of `w'`, and the
  completion test fires on the next tick.
* `loiter_near3`: the loiter target is within `0.081` of `w'`.
-/

namespace Contracts.Track.Reach.Leg3

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue Contracts.Track.Reach.Leg

noncomputable section

variable {w₀ : Vehicle.World} {w' : P3} {x : ℕ → X}

/-- **The model of a 3D behavior**: its readouts follow `LegModel3` from tick 2. -/
theorem legModel3_of_run (hx : LegRun3 w₀ w' x) :
    LegModel3 (ξV w₀ x) (legWV3 w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) ts where
  stepV t _ := by
    simp only [legWV3, VerticalHi.forceOf, aZ, d1Z, d2Z, neg_smul]
    abel
  stepH t _ a := by
    simp only [legWH, Horizontal.forceOf, aH, d1H, d2H, neg_smul]
    abel
  initV := hx.init.1
  initH := hx.init.2.1
  initA := hx.init.2.2.1
  initAZ := hx.init.2.2.2.1
  initD := hx.init.2.2.2.2
  tick := hx.tick

/-- The 3D box at every tick up to the horizon. -/
theorem box_run3 (hx : LegRun3 w₀ w' x) (t : ℕ) (h1 : ts ≤ t) (h2 : t ≤ hzn3) :
    BoxL3 (ξV w₀ x) (ξH w₀ x) t := by
  obtain ⟨N, rfl⟩ : ∃ N, t = ts + N := ⟨t - ts, by omega⟩
  exact leg_box3 (legModel3_of_run hx) refGains_certified refGains3_certified N h2

/-- The velocity defects summed over the run. -/
theorem d2sum_run3 (hx : LegRun3 w₀ w' x) (N : ℕ) (hN : ts + N ≤ hzn3) :
    (∀ a, ∑ k ∈ Finset.range N, |d2H w₀ x (ts + k) a| ≤ 1 / 4) ∧
      ∑ k ∈ Finset.range N, |d2Z w₀ x (ts + k)| ≤ 1 / 4 :=
  hx.d2sum N hN (fun k hk1 hk2 => box_run3 hx k hk1 (by omega))

/-- **The completion by tick 2905.** -/
theorem Tc_le3 (hx : LegRun3 w₀ w' x) {Tc Tl : ℕ} (hP : LegPhase3 w₀ w' x Tc Tl) :
    Tc ≤ 2200 + Mc3 + 1 := by
  have hM := legModel3_of_run hx
  obtain ⟨Te, h1, h2, h3, h4⟩ := hP.arrive
  by_contra hlt
  push Not at hlt
  have eMc : Mc3 = 704 := rfl
  have eMc' : Mc = 416 := rfl
  have eH : hzn3 = 7200 := rfl
  obtain ⟨N, hN⟩ : ∃ N, Te + Mc3 = ts + N := ⟨Te + Mc3 - ts, by simp [ts] at h1 ⊢; omega⟩
  have hNz : ts + N ≤ hzn3 := by rw [← hN]; omega
  have hS := d2sum_run3 hx N hNz
  have hz : ∀ a, ∀ t, Te ≤ t → t < ts + N →
      |aH w₀ x t a| ≤ 1 / 10 ^ 6 ∧ |d1H w₀ x t a| ≤ 1 / 10 ^ 8 ∧ |d2H w₀ x t a| ≤ 3 / 10 ^ 6 :=
    fun a t ht1 ht2 => (h3 t ht1 (by omega)).2.1 a
  have hzV : ∀ t, Te ≤ t → t < ts + N →
      |aZ w₀ x t| ≤ 1 / 10 ^ 6 ∧ |d1Z w₀ x t| ≤ 1 / 10 ^ 8 ∧ |d2Z w₀ x t| ≤ 3 / 10 ^ 6 :=
    fun t ht1 ht2 => (h3 t ht1 (by omega)).2.2
  have e0 := tail_e_c3 hM refGains_certified refGains3_certified Te 0 N (hz 0) (hS.1 0)
    (by omega) hNz
  have e1 := tail_e_c3 hM refGains_certified refGains3_certified Te 1 N (hz 1) (hS.1 1)
    (by omega) hNz
  have ez := tail_z_c3 hM refGains_certified refGains3_certified Te N hzV hS.2 (by omega) hNz
  have q := complete3_3d e0 e1 ez
  have he : err (x (ts + N)) ≤ 921 / 10000 := by
    rw [Leg.err_eq, Real.sqrt_le_left (by norm_num)]
    exact q
  have ht := (h3 (ts + N) (by omega) (by omega)).1
  have hd : dist (pos (x (ts + N))) w' ≤ 99 / 1000 := by
    have := dist_triangle (pos (x (ts + N))) (posTarget (x (ts + N))) w'
    have e : err (x (ts + N)) = dist (pos (x (ts + N))) (posTarget (x (ts + N))) := rfl
    linarith
  have := h4 (ts + N) (by omega) (by omega) hd
  omega

/-- **The loiter target is within `0.081` of `w'`.** -/
theorem loiter_near3 {Tc Tl : ℕ} (hP : LegPhase3 w₀ w' x Tc Tl) :
    dist (posTarget (x Tl)) w' ≤ 8 / 100 + 1 / 1000 := by
  have h1 := hP.loiter
  have h2 := hP.atComplete
  linarith

end

end Contracts.Track.Reach.Leg3
