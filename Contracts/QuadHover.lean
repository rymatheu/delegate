import Contracts.QuadHoverVert
import Contracts.QuadCode
import Contracts.FloatLoopIEEE
import Contracts.QuadDivSqrt

/-!
# Hover invariance of the Crazyflie closed loop

The closed loop `MquadHover sense` (the rigid-body plant of `Contracts.QuadPlant` with the full
`Float` controller at the flown gains and the hover mission `(0, 0, -1)`, yaw `0`), started at the
setpoint, level and at rest, stays for all time exactly on the vertical through the setpoint with
level attitude and zero body rates, within `1 cm` of the setpoint altitude and `1 cm/s` of rest
(`hover_invariant`).

The proof composes per-module facts and closes the loop by induction over ticks:

* level channels (`Contracts.QuadHoverZero`): on a hover sample the horizontal position loop, the
  attitude target, the attitude loop and the rate loop output zeros, and the mixer sends one value
  to all four motors;
* plant (`dyn_vert`): four equal commands produce no torque, so a level vehicle at rest in
  rotation and horizontally stays so, and only `(z, w)` moves;
* vertical channel (`Contracts.QuadHoverVert`): the `Float` loop is, up to explicit bounds, the
  linear loop `ζ' = ζ + w/120`, `w' = w + az/120`, `I' = I + ev/60` with `ev = -1.5 ζ - w`,
  `az = I + (241/60) ev`;
* a quadratic Lyapunov function `V` of that linear loop (`V (A x) ≤ (249/250) V x`) with enough
  margin to absorb the bounded perturbations (`lyap_step`), whose sublevel set `V ≤ 9/5000` lies in
  the box `|ζ|, |w|, |I| ≤ 1/100`.

Hypotheses: the sensor rounds within `δ ≤ 10⁻⁶` on `|r| ≤ 100` and sends `0` to a zero
(`HoverSense`); `DivSqrtSpec` (rounding of `/` and `sqrt`); `LibmZero` (`sin`, `cos`, `atan2` at
zero). `DivSqrtSpec` is proven from the binary64 model (`hover_invariant_ieee`), the sensor
hypothesis is met by the concrete sensor `FloatLoopIEEE.senseNearest` (`hover_invariant_nearest`),
and the loop has a behavior meeting the assumption (`hoverTraj_mem`). `LibmZero` is about the
`opaque` C-library functions and cannot be proven in Lean.

Why the hover mission: with the three-waypoint mission of `cf2x.txt` the navigator starts along
the first leg as soon as the vehicle is within `5 cm` of the first waypoint, so a hover there is
not invariant; `hoverParams` is `cf2x.txt` followed by `hover.txt` (same gains, one waypoint).
With a single waypoint the navigator never leaves its take-off phase: whatever its memory's
progress and speed, at index `0` it outputs the waypoint, zero velocity and acceleration
feed-forward and the waypoint's yaw, and stays at index `0` (`nav_hover`).
-/

namespace Contracts.QuadHover

open Contracts.QuadFloat Contracts.QuadNear Contracts.QuadPlant Contracts.Lift Contracts.FloatReal
open Flight

/-! ## The plant on the vertical -/

/-- A state on the vertical, level, not rotating. -/
def vstate (z w : ℝ) : QState := ⟨⟨0, 0, z⟩, ⟨0, 0, w⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩

/-- Four equal commands `u ∈ [0, 1]` move a vertical state along the vertical. -/
theorem dyn_vert (z w u : ℝ) (m : Motors Float) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h1 : m.m1.toReal = u) (h2 : m.m2.toReal = u) (h3 : m.m3.toReal = u) (h4 : m.m4.toReal = u) :
    dyn (vstate z w) m = vstate (z + h * w) (w + h * (grav - 22.05 * u)) := by
  have hc : ∀ x : Float, x.toReal = u → cmd x = u := by
    intro x hx; rw [cmd, clip01, hx, min_eq_right hu1, max_eq_right hu0]
  have hT : thrust m / mass = 22.05 * u := by
    simp only [thrust, force, hc _ h1, hc _ h2, hc _ h3, hc _ h4]
    rw [kf_maxRPM_sq]
    norm_num [thrust2weight, grav, mass]; ring
  simp only [dyn, vstate, thrustDir, eulerRate, rateAccel, torque, Real.sin_zero, Real.cos_zero,
    hc _ h1, hc _ h2, hc _ h3, hc _ h4, hT]
  congr 2 <;> ring

/-! ## The parameters' side conditions -/

theorem nonneg_of_le {x : Float} (hx : x.IsFinite) (h : (0 : Float) ≤ x) : 0 ≤ x.toReal := by
  have := (Float.le_iff_toReal_le Float.isFinite_zero hx).1 h; simpa using this

theorem posOK : PosOK hoverParams.pos := ⟨by decide, by decide, nonneg_of_le (by decide) (by decide),
  ⟨by decide, by decide, by decide, by decide, nonneg_of_le (by decide) (by decide)⟩, by decide,
  nonneg_of_le (by decide) (by decide)⟩

theorem rateOK : RateOK hoverParams.rate :=
  ⟨⟨by decide, by decide, by decide, by decide, nonneg_of_le (by decide) (by decide)⟩,
   ⟨by decide, by decide, by decide, by decide, nonneg_of_le (by decide) (by decide)⟩,
   ⟨by decide, by decide, by decide, by decide, nonneg_of_le (by decide) (by decide)⟩⟩

theorem attOK : AttOK hoverParams.att := ⟨by decide, by decide, by decide, by decide,
  nonneg_of_le (by decide) (by decide), by decide, nonneg_of_le (by decide) (by decide)⟩

theorem targetOK : TargetOK hoverParams.target :=
  ⟨by decide, by decide, nonneg_of_le (by decide) (by decide)⟩

theorem mixOK : MixOK hoverParams.mixer :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
   ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩

/-- The navigator memory the hover mission keeps: index `0` and the saturated zeros. -/
def navHover : NavState Float := ⟨0, clip 0 1 0, clip 0 hoverParams.nav.wpSpeed 0⟩

theorem nav_hover (s : NavState Float) (hs : s.index = 0) (pos : Vec3 Float) (dt : Float) :
    Navigator.step hoverParams.nav s pos dt = (navHover, ⟨⟨0, 0, -1⟩, Vec3.zero, Vec3.zero, 0⟩) := by
  unfold Navigator.step Navigator.advance Navigator.output
  simp only [hs, hoverParams, cf2xParams, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.getElem?_nil]
  rfl

/-- The navigator's step within one controller tick. -/
abbrev N (P : Controller.Params Float) (s : Controller.State Float) (inp : SimInput Float) :
    NavState Float × NavOutput Float :=
  Navigator.step P.nav s.nav inp.pos inp.dt

/-- The decomposition of one controller tick into its modules. -/
theorem step_eq (P : Controller.Params Float) (s : Controller.State Float) (inp : SimInput Float) :
    Controller.step P s inp =
      (⟨(N P s inp).1,
        (PositionControl.step P.pos s.pos ⟨inp.pos, inp.vel,
          (N P s inp).2.posSp, (N P s inp).2.velSp, (N P s inp).2.accSp, inp.dt⟩).1,
        (RateControl.step P.rate s.rate ⟨inp.rates, AttitudeControl.step P.att ⟨inp.att,
          (AttitudeTarget.step P.target ⟨(PositionControl.step P.pos s.pos ⟨inp.pos, inp.vel,
            (N P s inp).2.posSp, (N P s inp).2.velSp, (N P s inp).2.accSp, inp.dt⟩).2,
            (N P s inp).2.yawSp, inp.att.yaw⟩).attitude⟩, inp.dt⟩).1⟩,
       Mixer.step P.mixer ⟨(AttitudeTarget.step P.target ⟨(PositionControl.step P.pos s.pos
          ⟨inp.pos, inp.vel, (N P s inp).2.posSp, (N P s inp).2.velSp, (N P s inp).2.accSp,
            inp.dt⟩).2,
          (N P s inp).2.yawSp, inp.att.yaw⟩).thrust,
        (RateControl.step P.rate s.rate ⟨inp.rates, AttitudeControl.step P.att ⟨inp.att,
          (AttitudeTarget.step P.target ⟨(PositionControl.step P.pos s.pos ⟨inp.pos, inp.vel,
            (N P s inp).2.posSp, (N P s inp).2.velSp, (N P s inp).2.accSp, inp.dt⟩).2,
            (N P s inp).2.yawSp, inp.att.yaw⟩).attitude⟩, inp.dt⟩).2⟩) :=
  rfl

/-! ## One controller tick at a hover sample -/

/-- The sensor: within `δ` on `|r| ≤ 100`, and a zero at `0`. -/
-- <<HoverSense>>
structure HoverSense (δ : ℝ) (sense : ℝ → Float) : Prop where
  spec : SenseSpec δ sense
  zero : Z (sense 0)
-- <</HoverSense>>

/-- Controller memory along the hover: navigator on the (only) waypoint, horizontal and rate PIDs
at zero, vertical integrator of value `I`, previous vertical velocity error at most `1/20`. -/
def InvC (cs : Controller.State Float) (I : ℝ) : Prop :=
  cs.nav.index = 0 ∧ (ZP cs.pos.vx ∧ ZP cs.pos.vy) ∧
    (Near cs.pos.vz.integral I 0 ∧ cs.pos.vz.prevError.IsFinite ∧
      |cs.pos.vz.prevError.toReal| ≤ 1/20) ∧
    (ZP cs.rate.roll ∧ ZP cs.rate.pitch ∧ ZP cs.rate.yaw)

theorem near_sense {δ : ℝ} {sense : ℝ → Float} (HS : HoverSense δ sense) {r : ℝ} (hr : |r| ≤ 100) :
    Near (sense r) r δ := HS.spec.sense_err r hr

/-- **One tick at a hover sample.** The controller keeps its hover memory, updates the vertical
integrator by `ev / 60` and sends one command `u ≈ (9.8 - az) / 22.05` to all four motors. -/
theorem ctrl_hover_step (H : DivSqrtSpec) (L : LibmZero) {δ : ℝ} {sense : ℝ → Float}
    (HS : HoverSense δ sense) (hδ : δ ≤ 1e-6) {ζ w I : ℝ} (hζ : |ζ| ≤ 1/100) (hw : |w| ≤ 1/100)
    (hI : |I| ≤ 1/100) (cs : Controller.State Float) (hc : InvC cs I) :
    let r := Controller.step hoverParams cs (measure sense (vstate (ζ - 1) w))
    InvC r.1 r.1.pos.vz.integral.toReal ∧
      |r.1.pos.vz.integral.toReal - (I + (-(3/2) * ζ - w) / 60)| ≤ 4.3e-8 ∧
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ r.2.m1.toReal = u ∧ r.2.m2.toReal = u ∧ r.2.m3.toReal = u ∧
        r.2.m4.toReal = u ∧ |u - (9.8 - (I + (241/60) * (-(3/2) * ζ - w))) / 22.05| ≤ 9.5e-7 := by
  intro r
  obtain ⟨hnav, ⟨hvx, hvy⟩, ⟨hint, hpf, hpb⟩, hrs⟩ := hc
  have hζ' := abs_le.1 hζ; have hw' := abs_le.1 hw; have hI' := abs_le.1 hI
  have hS0 := HS.zero
  have hzS : Near (sense (ζ - 1)) (ζ - 1) δ := near_sense HS (bnd (by linarith) (by linarith))
  have hwS : Near (sense w) w δ := near_sense HS (bnd (by linarith) (by linarith))
  have hnav' : N hoverParams cs (measure sense (vstate (ζ - 1) w)) =
      (navHover, ⟨⟨0, 0, -1⟩, Vec3.zero, Vec3.zero, 0⟩) := nav_hover _ hnav _ _
  have hr : r = Controller.step hoverParams cs (measure sense (vstate (ζ - 1) w)) := rfl
  rw [step_eq, hnav'] at hr
  -- position loop
  set pin : PosInput Float := ⟨⟨sense 0, sense 0, sense (ζ - 1)⟩, ⟨sense 0, sense 0, sense w⟩,
    ⟨0, 0, -1⟩, Vec3.zero, Vec3.zero, dtF⟩ with hpin
  have hxy := posXY_Z hoverParams.pos posOK cs.pos ⟨hvx, hvy⟩ pin ⟨hS0, hS0⟩ ⟨hS0, hS0⟩
    ⟨Z_zero, Z_zero⟩ ⟨Z_zero, Z_zero⟩ ⟨Z_zero, Z_zero⟩ nDt.1
  obtain ⟨n1, n2, n3⟩ := posZ_near H cs.pos pin hζ hw hI hδ rfl Z_zero Z_zero hzS hwS hint hpf hpb
    rfl
  set pc := PositionControl.step hoverParams.pos cs.pos pin with hpc
  -- thrust and attitude target
  have hab : |I + (241/60) * (-(3/2) * ζ - w)| ≤ 0.12 := bnd (by linarith) (by linarith)
  obtain ⟨t1, t2, t3, t4⟩ := thrust_near H hxy.2.1 hxy.2.2 n3 hab
  set tin : AttTargetInput Float := ⟨pc.2, 0, sense 0⟩ with htin
  obtain ⟨hatt, hthr⟩ := target_Z H L hoverParams.target targetOK tin hxy.2.1 hxy.2.2 t1 t3 t2
    Z_zero hS0
  set tg := AttitudeTarget.step hoverParams.target tin with htg
  have hthr' : Near tg.thrust ((9.8 - (I + (241/60) * (-(3/2) * ζ - w))) / 22.05) 9.5e-7 := by
    rw [hthr]; exact t4
  -- attitude and rate loops
  have hrsp := att_Z L hoverParams.att attOK ⟨⟨sense 0, sense 0, sense 0⟩, tg.attitude⟩
    ⟨hS0, hS0, hS0⟩ hatt
  have hrc := rate_Z hoverParams.rate rateOK cs.rate hrs
    ⟨⟨sense 0, sense 0, sense 0⟩, AttitudeControl.step hoverParams.att
      ⟨⟨sense 0, sense 0, sense 0⟩, tg.attitude⟩, dtF⟩ ⟨hS0, hS0, hS0⟩ hrsp nDt.1
  -- mixer
  have hb := abs_le.1 hthr'.2
  have hu0 : 0 ≤ tg.thrust.toReal := by
    have : 0.43 ≤ (9.8 - (I + (241/60) * (-(3/2) * ζ - w))) / 22.05 := by
      rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hu1 : tg.thrust.toReal ≤ 1 := by
    have : (9.8 - (I + (241/60) * (-(3/2) * ζ - w))) / 22.05 ≤ 0.46 := by
      rw [div_le_iff₀ (by norm_num)]; linarith
    linarith
  have hmix := mixer_Z hoverParams.mixer mixOK ⟨tg.thrust, _⟩ hrc.2 hthr'.1 hu0 hu1
  rw [hr]
  refine ⟨⟨rfl, hxy.1, ⟨Near.exact n1.1, n2.1, ?_⟩, hrc.1⟩, n1.2, tg.thrust.toReal, hu0, hu1,
    hmix.2.1, hmix.2.2.2.1, hmix.2.2.2.2.2.1, hmix.2.2.2.2.2.2.2, hthr'.2⟩
  have h2 : |-(3/2) * ζ - w| ≤ 0.026 := bnd (by linarith) (by linarith)
  exact n2.bound.trans (by linarith)

/-! ## A Lyapunov function of the vertical loop -/

/-- `V x = xᵀ P x` with `P = [[345/2, 55/2, -34], [55/2, 105/2, -60], [-34, -60, 130]]`, in the
coordinates `(ζ, w, I)`. -/
-- <<Vlyap>>
noncomputable def V (ζ w I : ℝ) : ℝ :=
  345/2 * ζ ^ 2 + 105/2 * w ^ 2 + 130 * I ^ 2 + 55 * ζ * w - 68 * ζ * I - 120 * w * I
-- <</Vlyap>>

theorem V_nonneg (ζ w I : ℝ) : 0 ≤ V ζ w I := by
  unfold V
  nlinarith [sq_nonneg (ζ + 11/69 * w - 68/345 * I), sq_nonneg (w - 1883/1660 * I), sq_nonneg I]

theorem V_ge (ζ w I : ℝ) : 18 * (ζ ^ 2 + w ^ 2 + I ^ 2) ≤ V ζ w I := by
  unfold V
  nlinarith [sq_nonneg (ζ + 55/309 * w - 68/309 * I), sq_nonneg (w - 8335/4574 * I), sq_nonneg I]

/-- The linear vertical loop contracts `V` by `249/250` per tick. -/
theorem V_contr (ζ w I : ℝ) :
    V (ζ + w / 120) (w + (I + (241/60) * (-(3/2) * ζ - w)) / 120) (I + (-(3/2) * ζ - w) / 60) ≤
      249/250 * V ζ w I := by
  unfold V
  nlinarith [sq_nonneg (ζ - 878294/2843019 * w + 472472/947673 * I),
    sq_nonneg (w + 7575874896/20028085805 * I), sq_nonneg I]

/-- A perturbation `n` costs at most `V y / 1000 + 1001 V n`. -/
theorem V_pert (y1 y2 y3 n2 n3 : ℝ) :
    V y1 (y2 + n2) (y3 + n3) ≤ 1001/1000 * V y1 y2 y3 + 1001 * V 0 n2 n3 := by
  have := V_nonneg y1 (y2 - 1000 * n2) (y3 - 1000 * n3)
  unfold V at *
  nlinarith

/-- **The sublevel set `V ≤ 9/5000` is invariant** under the perturbed vertical loop. -/
theorem lyap_step {ζ w I d dI : ℝ} (hV : V ζ w I ≤ 9/5000) (hd : |d| ≤ 2.1e-5)
    (hdI : |dI| ≤ 4.3e-8) :
    V (ζ + w / 120) (w + (I + (241/60) * (-(3/2) * ζ - w) + d) / 120)
      (I + (-(3/2) * ζ - w) / 60 + dI) ≤ 9/5000 := by
  have h1 := V_contr ζ w I
  have h2 := V_pert (ζ + w / 120) (w + (I + (241/60) * (-(3/2) * ζ - w)) / 120)
    (I + (-(3/2) * ζ - w) / 60) (d / 120) dI
  have e : V (ζ + w / 120) (w + (I + (241/60) * (-(3/2) * ζ - w) + d) / 120)
      (I + (-(3/2) * ζ - w) / 60 + dI) =
      V (ζ + w / 120) (w + (I + (241/60) * (-(3/2) * ζ - w)) / 120 + d / 120)
      (I + (-(3/2) * ζ - w) / 60 + dI) := by congr 1; ring
  rw [e]
  have hd' := abs_le.1 hd; have hdI' := abs_le.1 hdI
  have hn : V 0 (d / 120) dI ≤ 1e-11 := by
    unfold V
    nlinarith [sq_nonneg (d / 120 + dI), sq_nonneg (d / 120 - dI)]
  nlinarith

theorem box_of_V {ζ w I : ℝ} (hV : V ζ w I ≤ 9/5000) :
    |ζ| ≤ 1/100 ∧ |w| ≤ 1/100 ∧ |I| ≤ 1/100 := by
  have := V_ge ζ w I
  have h1 : ζ ^ 2 ≤ (1/100) ^ 2 := by nlinarith [sq_nonneg w, sq_nonneg I]
  have h2 : w ^ 2 ≤ (1/100) ^ 2 := by nlinarith [sq_nonneg ζ, sq_nonneg I]
  have h3 : I ^ 2 ≤ (1/100) ^ 2 := by nlinarith [sq_nonneg w, sq_nonneg ζ]
  exact ⟨abs_le_of_sq_le_sq' h1 (by norm_num) |> fun h => abs_le.2 h,
    abs_le_of_sq_le_sq' h2 (by norm_num) |> fun h => abs_le.2 h,
    abs_le_of_sq_le_sq' h3 (by norm_num) |> fun h => abs_le.2 h⟩

/-! ## The closed loop -/

/-- Assumption: the loop starts at the setpoint `(0, 0, -1)`, level, facing north, at rest. -/
-- <<Ahover>>
def Ahover : Set (ℕ → QX) := {x | (x 0).phys = vstate (-1) 0}
-- <</Ahover>>

/-- The hover box: within `1/100` of the setpoint altitude and of rest vertically, and exactly on
the vertical, level and not rotating. -/
-- <<hoverBox>>
noncomputable def hoverBox : STL.Formula QState :=
  ((STL.Formula.atom fun s => 1/100 - |s.p.z + 1|).and (.atom fun s => 1/100 - |s.v.z|)).and
    (.atom fun s => -(|s.p.x| + |s.p.y| + |s.v.x| + |s.v.y| + |s.att.roll| + |s.att.pitch| +
      |s.att.yaw| + |s.ω.x| + |s.ω.y| + |s.ω.z|))
-- <</hoverBox>>

theorem init_invC : InvC (Controller.State.init : Controller.State Float) 0 := by
  have h1 : Z (Controller.State.init : Controller.State Float).pos.vz.integral := Z_zero
  have h2 : Z (Controller.State.init : Controller.State Float).pos.vz.prevError := Z_zero
  exact ⟨rfl, ⟨⟨Z_zero, Z_zero⟩, ⟨Z_zero, Z_zero⟩⟩,
    ⟨⟨h1.1, by rw [h1.2]; simp⟩, h2.1, by rw [h2.2]; norm_num⟩,
    ⟨⟨Z_zero, Z_zero⟩, ⟨Z_zero, Z_zero⟩, ⟨Z_zero, Z_zero⟩⟩⟩

/-- The inductive invariant along every behavior of the hover loop. -/
theorem hover_inv (H : DivSqrtSpec) (L : LibmZero) {δ : ℝ} {sense : ℝ → Float}
    (HS : HoverSense δ sense) (hδ : δ ≤ 1e-6) {x : ℕ → QX} (hx : x ∈ MquadHover sense ∩ Ahover) :
    ∃ s : ℕ → Controller.State Float, ∀ t, ∃ ζ w I : ℝ,
      (x t).phys = vstate (ζ - 1) w ∧ V ζ w I ≤ 9/5000 ∧ InvC (s t) I := by
  obtain ⟨⟨hP, s, hs0, hs⟩, hA⟩ := hx
  refine ⟨s, fun t => ?_⟩
  induction t with
  | zero =>
    refine ⟨0, 0, 0, by rw [hA]; norm_num, by norm_num [V], hs0 ▸ init_invC⟩
  | succ t ih =>
    obtain ⟨ζ, w, I, hph, hV, hc⟩ := ih
    obtain ⟨bζ, bw, bI⟩ := box_of_V hV
    have hPt := hP t
    simp only [plant, Prod.mk.injEq] at hPt
    obtain ⟨hnext, hsim⟩ := hPt
    have hst : (s (t+1), (x t).mot) = Controller.step hoverParams (s t) (x t).sim := hs t
    rw [hsim, hph] at hst
    obtain ⟨hcs, hIn, u, hu0, hu1, h1, h2, h3, h4, hu⟩ :=
      ctrl_hover_step H L HS hδ bζ bw bI (s t) hc
    rw [← hst] at hcs hIn h1 h2 h3 h4
    simp only at hcs hIn h1 h2 h3 h4
    have hdyn := dyn_vert (ζ - 1) w u (x t).mot hu0 hu1 h1 h2 h3 h4
    rw [hph, hdyn] at hnext
    refine ⟨ζ + w / 120, w + h * (grav - 22.05 * u), (s (t+1)).pos.vz.integral.toReal,
      by rw [hnext]; congr 1; rw [h]; ring, ?_, hcs⟩
    have hd : |(grav - 22.05 * u) - (I + (241/60) * (-(3/2) * ζ - w))| ≤ 2.1e-5 := by
      have e : (9.8 - (I + (241/60) * (-(3/2) * ζ - w))) / 22.05 =
          (9.8 - (I + (241/60) * (-(3/2) * ζ - w))) * (20/441) := by norm_num [div_eq_mul_inv]
      rw [e] at hu
      obtain ⟨hu1, hu2⟩ := abs_le.1 hu
      rw [grav]; apply bnd <;> linarith
    have hdI : |(s (t+1)).pos.vz.integral.toReal - (I + (-(3/2) * ζ - w) / 60)| ≤ 4.3e-8 := hIn
    have := lyap_step hV hd hdI
    convert this using 2 <;> (try rw [h]) <;> ring

/-- **Hover invariance.** Started at the setpoint, level and at rest, the Crazyflie under the full
`Float` controller stays on the vertical through the setpoint, level and not rotating, within
`1 cm` of the setpoint altitude and `1 cm/s` of vertical rest, over every horizon `T`. -/
-- <<hover_invariant>>
theorem hover_invariant (H : DivSqrtSpec) (L : LibmZero) {δ : ℝ} {sense : ℝ → Float}
    (HS : HoverSense δ sense) (hδ : δ ≤ 1e-6) (T : ℕ) :
    MquadHover sense ⊨ ⟨Ahover, initOn (·.phys) (.always 0 T hoverBox)⟩ := by
  intro x hx
  obtain ⟨s, hinv⟩ := hover_inv H L HS hδ hx
  rw [mem_initOn]
  intro τ _ _
  obtain ⟨ζ, w, I, hph, hV, -⟩ := hinv τ
  obtain ⟨bζ, bw, -⟩ := box_of_V hV
  simp only [hoverBox, STL.sat_and, STL.sat_atom, hph, vstate]
  refine ⟨⟨by rw [show ζ - 1 + 1 = ζ by ring]; linarith, by linarith⟩, by simp⟩
-- <</hover_invariant>>

/-! ## Non-vacuity -/

/-- The concrete sensor of `Contracts.FloatLoopIEEE` (nearest multiple of `2⁻²⁰`, then binary64)
sends `0` to `+0`. -/
theorem senseNearest_zero : Z (FloatLoopIEEE.senseNearest 0) := by
  have h : ⌊(0 : ℝ) * 2 ^ (20 : ℕ) + 1/2⌋ = 0 := by norm_num [Int.floor_eq_iff]
  have e : (FloatLoopIEEE.senseNearest 0).toModel =
      Float.Model.pack (Float.Model.UnpackedFloat.normalize Float.Model.Format.binary64 0 (-20)
        .positive) := by
    show Float.Model.pack _ = _; rw [h]
  exact QuadFloat.Zero.of_pack_zero e ⟨_, rfl⟩

/-- The concrete sensor meets the hover's sensor hypothesis with `δ = 2⁻²⁰ < 10⁻⁶`. -/
theorem senseNearest_hover : HoverSense ((2 : ℝ) ^ (-20 : ℤ)) FloatLoopIEEE.senseNearest :=
  ⟨FloatLoopIEEE.senseNearest_spec, senseNearest_zero⟩

theorem two_pow_neg20_le : (2 : ℝ) ^ (-20 : ℤ) ≤ 1e-6 := by norm_num

/-- Plant state and controller memory of the run from the hover point. -/
noncomputable def hoverRun (sense : ℝ → Float) : ℕ → QState × Controller.State Float
  | 0 => (vstate (-1) 0, Controller.State.init)
  | t + 1 =>
    let pc := hoverRun sense t
    let r := Controller.step hoverParams pc.2 (measure sense pc.1)
    (dyn pc.1 r.2, r.1)

/-- The behavior of the closed loop from the hover point. -/
noncomputable def hoverTraj (sense : ℝ → Float) (t : ℕ) : QX :=
  ⟨(hoverRun sense t).1, measure sense (hoverRun sense t).1,
    (Controller.step hoverParams (hoverRun sense t).2 (measure sense (hoverRun sense t).1)).2⟩

/-- **Non-vacuity**: the hover loop has a behavior meeting the assumption, for every sensor. -/
theorem hoverTraj_mem (sense : ℝ → Float) : hoverTraj sense ∈ MquadHover sense ∩ Ahover :=
  ⟨⟨fun _ => rfl, ⟨fun t => (hoverRun sense t).2, rfl, fun _ => rfl⟩⟩, rfl⟩

/-! ## With the binary64 model and the concrete sensor -/

/-- **Hover invariance, binary64.** The rounding of `/` and `sqrt` is discharged from Lean's
model of `Float` (`QuadDivSqrt.divSqrtSpec`); what remains is the sensor and `LibmZero`. -/
-- <<hover_invariant_ieee>>
theorem hover_invariant_ieee (L : LibmZero) {δ : ℝ} {sense : ℝ → Float}
    (HS : HoverSense δ sense) (hδ : δ ≤ 1e-6) (T : ℕ) :
    MquadHover sense ⊨ ⟨Ahover, initOn (·.phys) (.always 0 T hoverBox)⟩ :=
  hover_invariant QuadDivSqrt.divSqrtSpec L HS hδ T
-- <</hover_invariant_ieee>>

/-- **Hover invariance with the concrete sensor**, assuming only `LibmZero`. -/
-- <<hover_invariant_nearest>>
theorem hover_invariant_nearest (L : LibmZero) (T : ℕ) :
    MquadHover FloatLoopIEEE.senseNearest ⊨ ⟨Ahover, initOn (·.phys) (.always 0 T hoverBox)⟩ :=
  hover_invariant_ieee L senseNearest_hover two_pow_neg20_le T
-- <</hover_invariant_nearest>>

end Contracts.QuadHover
