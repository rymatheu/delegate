import Contracts.Mission.Spec

/-!
# The definitions of the sub-contracts

The constants of the decomposition and the formulas of `track_contract` and `nav_contract`
(`Sub.lean` states the sub-contracts; `MISSION.md` explains the decomposition).
-/

namespace Contracts.Mission

open Contracts Contracts.STL

noncomputable section

/-! ## The constants of the decomposition -/

/-- How far the position target may be from the polyline (outside the takeoff column), m. The
nominal run's maximum is `0.071` m. -/
def ρ : ℝ := 0.155

/-- Tracking error bound, m. The nominal run's maximum is `0.0870` m. -/
def δ : ℝ := 0.095

/-- Tracking error bound during the climb out of the box, while the target is in the column and
outside the `ρ`-corridor, m. The nominal run's maximum up to `0.37` m of climb is `0.012` m. -/
def δ₀ : ℝ := 0.035

/-- The target's arrival radius in the transfer property at `w1 … w6`, m (above the corner cut of
`0.1006` m, so the target enters it at each corner). -/
def rPassMid : ℝ := 0.105

/-- The target's arrival radius in the transfer property at `w0 = w7`, m. No single radius at `w0`
serves both the target's arrival and the transfer: on the climb the target's closest approach to `w0`
is `0.0433`–`0.0995` m over the 256 Monte Carlo starts (`0.0942` m on the nominal run), so an arrival
radius must be at least `0.0995`, while the transfer needs less than `0.091` (with `0.105` it fails on
82 of 256 runs as the vehicle leaves `w0` toward `w1`; `sim/out/montecarlo/CONSTANTS.md`). The reach
chain of `ψtrack` therefore starts with the vehicle itself at `w0`, and `rPassEnd` serves the
transfer at `w0 = w7` and the hold: with `0.085` the vehicle is within `0.0934` m of `w0` whenever the
target is within `0.085` of it (6.6 mm of margin), and the loiter target stays within `0.0282` m
of `w7`. With these, every conjunct of the new reach chain and the hold holds on all 256 runs. -/
def rPassEnd : ℝ := 0.085

/-- The target's arrival radius in the transfer property, per waypoint: `rPassEnd` at the point
`w0 = w7`, `rPassMid` at `w1 … w6`. -/
noncomputable def rPass (w : P3) : ℝ := by classical exact if w = w7 then rPassEnd else rPassMid

/-- The sampled tracking error the navigator may assume, m: `δ` plus the sensing error. -/
def δs : ℝ := 0.096

/-- Half-width of the takeoff column, m: the box's `0.15` plus `0.001` for sensing and rounding. -/
def colNE : ℝ := 0.151

/-- Top of the takeoff column (down coordinate), m: the altitude of `w0`. -/
def colDownLo : ℝ := -0.8

/-- Bottom of the takeoff column (down coordinate), m: the ground plus `0.002`. The first sample is
at most `0.001` below the ground (`smpStart`); the navigator rounds the start's down coordinate to
`float` (`AC_PosControl::get_stopping_point_D_m`), and the other `0.001` keeps that rounding inside
the column (with the face at `0.001`, a start at the largest double `≤ 0.001` puts the target
`4.6·10⁻¹¹` below the column at ticks 0 and 1). -/
def colDownHi : ℝ := 0.002

/-- The rest gate, m and m/s: the target is within `rRest` of `w7` and its velocity target is at
most `rRest`. This holds at the tick the mission completes (the last leg's S-curve has finished at
`w7`, the loiter leg starts at rest), and never before it on this course (the target passes the
point `w0 = w7` with the corner cut of `0.1` m). -/
def rRest : ℝ := 0.001

/-- The sampled velocity error allowed while the target rests at `w7`, m/s. The nominal run's
maximum over its 141 rest ticks is `0.0407` m/s (velocity error and speed alike); `0.055` is `1.35×`
that. It bounds the loiter offset that `loiter_start` takes from the sampled velocity: the stopping
point is within `|v|` of the sampled position (`min(|v_NE|, 1)/1.5` horizontally,
`stopping_distance(v_D, 1, 1) = v_D` vertically for `|v_D| ≤ 1`), so the loiter target stays within
`δs + rRest + δv = 0.152 ≤ ρ` of `w7`. A uniform bound would need `δv ≤ 0.058`, below the nominal
maximum `0.136` m/s (at the `w0` corner). -/
def δv : ℝ := 0.055

theorem hρδ : ρ + δ ≤ corridor := by norm_num [ρ, δ, corridor]
theorem hδ : δ < rWp := by norm_num [δ, rWp]
theorem hδs : δ < δs := by norm_num [δ, δs]
theorem hrPass : rWp < rPassMid := by norm_num [rWp, rPassMid]
theorem hrPassEnd : rPassEnd < rWp := by norm_num [rWp, rPassEnd]

theorem rPass_w7 : rPass w7 = rPassEnd := by simp [rPass]

theorem w0_eq_w7 : wp 0 = w7 := by
  ext i; fin_cases i <;> simp [wp, w7]

theorem rPass_w0 : rPass (wp 0) = rPassEnd := by rw [w0_eq_w7, rPass_w7]

/-- At `w1 … w6` the radius is `rPassMid`. -/
theorem rPass_mid (i : Fin 8) (h1 : i ≠ 0) (h7 : i ≠ 7) : rPass (wp i) = rPassMid := by
  have hne : wp i ≠ w7 := by
    intro h
    have h2 := congrArg (· 2) h
    fin_cases i
    · exact h1 rfl
    all_goals first
      | exact h7 rfl
      | (simp [wp, w7] at h2; norm_num at h2)
  simp [rPass, hne]

/-! ## Formulas of the sub-contracts -/

/-- The position target is within `ρ'` of the polyline. -/
def nearPolyT (ρ' : ℝ) : Formula X := .atom fun x => ρ' - polyDist (posTarget x)

/-- The takeoff column: above the box (enlarged by `0.001` horizontally and `0.002` below), up to the
altitude of `w0`. -/
def inColumn (q : P3) : Prop := |q 0| ≤ colNE ∧ |q 1| ≤ colNE ∧ colDownLo ≤ q 2 ∧ q 2 ≤ colDownHi

/-- The position target is in the takeoff column. -/
def inColumnT : Formula X := propF fun x => inColumn (posTarget x)

/-- The position coordinates are at most `R` in absolute value. -/
def PBd (x : Plant.X) (R : ℝ) : Prop := |x 0| ≤ R ∧ |x 1| ≤ R ∧ |x 2| ≤ R

/-- The envelope of the rigid-body state: within 10 m of the takeoff point in each coordinate,
speeds at most 2 m/s, body rates at most 10 rad/s (nominal maxima: 2.5 m, 1.10 m/s, 1.17 rad/s). -/
def physEnv (x : X) : Prop := PBd x.phys.x 10 ∧ Plant.VBd x.phys.x 2 ∧ Plant.WBd x.phys.x 10

/-- The envelope as a formula. -/
def envF : Formula X := propF physEnv

/-- During the climb out of the box (target in the column, not yet within `ρ` of the polyline) the
tracking error is at most `δ₀`. -/
def takeoffF : Formula X := (inColumnT.and (nearPolyT ρ).not).imp (errLE δ₀)

/-- Near waypoint `w`: whenever the target is within `rPass w` of `w`, the vehicle is within `r`. -/
def proxF (w : P3) : Formula X := (nearT w (rPass w)).imp (near w rWp)

/-- The conjunction of a list of formulas. -/
def allF : List (Formula X) → Formula X
  | [] => trueF
  | φ :: l => .and φ (allF l)

theorem sat_allF {x : ℕ → X} {t : ℕ} : ∀ {l : List (Formula X)},
    sat x t (allF l) ↔ ∀ φ ∈ l, sat x t φ
  | [] => by simp [allF]
  | φ :: l => by simp [allF, sat_allF]

/-- The transfer property at all eight waypoints. -/
def proxAllF : Formula X := allF ((List.ofFn wp).map proxF)

/-- **The rest condition**: while the position target rests at `w7` (within `rRest`, velocity
target at most `rRest`), the sampled velocity is within `δv` of the velocity target. -/
def restF : Formula X :=
  ((nearT w7 rRest).and (.atom fun x => rRest - ‖velTarget x‖)).imp (.atom fun x => δv - smpVelErr x)

/-- **The guarantee of `track_contract`**: over the horizon, tracking within `δ`, the envelope,
the climb-out bound, the transfer near the waypoints, and the rest condition; the vehicle reaches
`w0` within `r` within its allowance and from there the target reaches `w1 … w7` in order within
`rPass`, within the allowances; and the target is within `rPass` of `w7` for the hold time within
the total allowance. (The first link is the vehicle's: see `rPassEnd`.) -/
def ψtrack : Formula X :=
  .and (.always 0 horizonTicks (.and (errLE δ) (.and envF (.and takeoffF (.and proxAllF restF)))))
    (.and (.eventually 0 1200 (.and (near (wp 0) rWp) (reachSeqF (fun w => nearT w (rPass w)) legs.tail)))
      (.eventually 0 totalTicks (.always 0 holdTicks (nearT w7 (rPass w7)))))

/-- A `float` is finite and at most `B` in absolute value. -/
def F32Bd (f : Float32) (B : ℝ) : Prop := f.IsFinite ∧ |f.toReal| ≤ B

/-- A `double` is finite and at most `B` in absolute value. -/
def F64Bd (f : Float) (B : ℝ) : Prop := f.IsFinite ∧ |f.toReal| ≤ B

/-- The samples are finite and in an envelope: position 11 m, velocity 3 m/s, specific force
23 m/s², quaternion components 2, body rates 11 rad/s. -/
def smpEnv (s : Vehicle.Sample) : Prop :=
  (F64Bd s.pos.x 11 ∧ F64Bd s.pos.y 11 ∧ F64Bd s.pos.z 11) ∧
  (F32Bd s.vel.x 3 ∧ F32Bd s.vel.y 3 ∧ F32Bd s.vel.z 3) ∧
  (F32Bd s.acc.x 23 ∧ F32Bd s.acc.y 23 ∧ F32Bd s.acc.z 23) ∧
  (F32Bd s.quat.q1 2 ∧ F32Bd s.quat.q2 2 ∧ F32Bd s.quat.q3 2 ∧ F32Bd s.quat.q4 2) ∧
  (F32Bd s.gyro.x 11 ∧ F32Bd s.gyro.y 11 ∧ F32Bd s.gyro.z 11)

/-- The first sample: position in the box (enlarged by `0.001`), velocity and body rates `+0`,
attitude level with any heading (`q2 = q3 = +0`, `q1² + q4²` within `0.001` of `1`), specific force
`(0, 0, ≈ -g)`. -/
def smpStart (s : Vehicle.Sample) : Prop :=
  |s.pos.x.toReal| ≤ colNE ∧ |s.pos.y.toReal| ≤ colNE ∧
  boxDownLo - 0.001 ≤ s.pos.z.toReal ∧ s.pos.z.toReal ≤ boxDownHi + 0.001 ∧
  s.vel = { x := 0, y := 0, z := 0 } ∧ s.gyro = { x := 0, y := 0, z := 0 } ∧
  s.quat.q2 = 0 ∧ s.quat.q3 = 0 ∧ |s.quat.q1.toReal ^ 2 + s.quat.q4.toReal ^ 2 - 1| ≤ 0.001 ∧
  s.acc.x = 0 ∧ s.acc.y = 0 ∧ |s.acc.z.toReal + Plant.grav| ≤ 0.001

/-- **The assumption of `nav_contract`**, on the samples alone: the first sample is of a vehicle at
rest in the box; over the horizon every period is 2500 µs, every sample is finite and in the
envelope, the sampled position is within `δs` of the target, and while the target rests at `w7` the
sampled velocity is within `δv` of the velocity target (`restF`). -/
def ψnavA : Formula X :=
  .and (propF fun x => smpStart x.smp)
    (.always 0 horizonTicks
      (.and (propF fun x => x.smp.dt_us = 2500)
        (.and (propF fun x => smpEnv x.smp) (.and (.atom fun x => δs - smpErr x) restF))))

/-- **The guarantee of `nav_contract`**, on the position target alone: over the horizon it is within
`ρ` of the polyline or in the takeoff column. -/
def ψnavG : Formula X := .always 0 horizonTicks ((nearPolyT ρ).or inColumnT)

end

end Contracts.Mission
