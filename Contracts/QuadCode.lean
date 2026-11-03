import Contracts.QuadPlant
import Contracts.QuadFloat

/-!
# Code-only contracts of the `Float` flight controller

Contracts on the controller component `MctrlP P` alone (no plant), proven against the code of
`Flight.Controller.step` at the `Float` instance.

* `motors_in_unit`: every motor command is a finite float in `[0, 1]` at every tick, for every
  input whatsoever (NaN and infinities included) and every parameter record, because the mixer's
  last operation is `clip 0 1` and the `Float` clip is finite and in range on every input
  (`QuadFloat.clip_spec`). The assumption "finite inputs" of the contract is therefore not used.
* `controller_finite`: on inputs whose velocities and body rates are finite and below `2^100` in
  magnitude, every run of the hidden controller state stays finite, for every parameter record
  whose saturation limits are finite, non-negative and below `2^100` (`LimitsOK`, which
  `cf2xParams` meets). Every stored integral is the output of a clip, and every stored previous
  error is a difference of a clipped setpoint and a measured velocity or rate; nothing else is
  stored, apart from the navigator's leg index, progress and path speed, and the last two are
  outputs of clips to `[0, 1]` and `[0, wpSpeed]` (`LimitsOK` also bounds `wpSpeed`). No
  hypothesis on `sin`, `cos`, `atan2`, `sqrt` or division is needed, since their results reach the
  state only through clips.
-/

namespace Contracts.QuadCode

open Contracts.QuadPlant Contracts.QuadFloat Contracts.Lift Flight

/-! ## Predicates on signals -/

/-- A finite vector. -/
def FinVec (v : Vec3 Float) : Prop := v.x.IsFinite ∧ v.y.IsFinite ∧ v.z.IsFinite

/-- A finite vector below `B` in every component. -/
def BndVec (B : ℝ) (v : Vec3 Float) : Prop :=
  FinVec v ∧ |v.x.toReal| ≤ B ∧ |v.y.toReal| ≤ B ∧ |v.z.toReal| ≤ B

/-- Every component of the sample is finite. -/
def InputFinite (i : SimInput Float) : Prop :=
  FinVec i.pos ∧ FinVec i.vel ∧ i.att.roll.IsFinite ∧ i.att.pitch.IsFinite ∧ i.att.yaw.IsFinite ∧
    FinVec i.rates ∧ i.dt.IsFinite

/-- A motor command that is a finite float in `[0, 1]`. -/
def UnitCmd (u : Float) : Prop := u.IsFinite ∧ 0 ≤ u.toReal ∧ u.toReal ≤ 1

/-- All four commands are finite and in `[0, 1]`. -/
def MotorsUnit (m : Motors Float) : Prop := UnitCmd m.m1 ∧ UnitCmd m.m2 ∧ UnitCmd m.m3 ∧ UnitCmd m.m4

/-! ## `motors_in_unit` -/

theorem clip01_unit (x : Float) : UnitCmd (clip 0 1 x) := by
  have := clip_spec zero_isFinite one_isFinite (by simp) x
  simpa [UnitCmd] using this

/-- The mixer's output is in `[0, 1]` on every input. -/
theorem mixer_unit (p : MixerParams Float) (inp : MixerInput Float) :
    MotorsUnit (Mixer.step p inp) :=
  ⟨clip01_unit _, clip01_unit _, clip01_unit _, clip01_unit _⟩

/-- One controller tick: the motors are the mixer's output. -/
theorem step_motors (P : Controller.Params Float) (s : Controller.State Float)
    (inp : SimInput Float) : ∃ mi, (Controller.step P s inp).2 = Mixer.step P.mixer mi :=
  ⟨_, rfl⟩

theorem step_motors_unit (P : Controller.Params Float) (s : Controller.State Float)
    (inp : SimInput Float) : MotorsUnit (Controller.step P s inp).2 := by
  obtain ⟨mi, h⟩ := step_motors P s inp
  rw [h]; exact mixer_unit _ _

/-- Assumption: every sample is finite. -/
-- <<Afin>>
def Afin : Set (ℕ → QX) := {x | ∀ t, InputFinite (x t).sim}
-- <</Afin>>

/-- Guarantee: every motor command is a finite float in `[0, 1]` at every tick. -/
-- <<Gunit>>
def Gunit : Set (ℕ → QX) := {x | ∀ t, MotorsUnit (x t).mot}
-- <</Gunit>>

/-- **Motor range.** The controller with any parameters implements `⟨Afin, Gunit⟩`. -/
-- <<motors_in_unit>>
theorem motors_in_unit (P : Controller.Params Float) : MctrlP P ⊨ ⟨Afin, Gunit⟩ := by
  rintro x ⟨⟨s, -, hs⟩, -⟩ t
  have := congrArg Prod.snd (hs t)
  simp only at this
  rw [this]; exact step_motors_unit P _ _
-- <</motors_in_unit>>

/-- The flown controller meets the motor-range contract. -/
theorem motors_in_unit_cf2x : Mctrl ⊨ ⟨Afin, Gunit⟩ := motors_in_unit cf2xParams

/-! ## `controller_finite` -/

/-- A finite PID memory. -/
def PidFin (s : PidState Float) : Prop := s.integral.IsFinite ∧ s.prevError.IsFinite

/-- A finite navigator memory (besides the leg index, a natural number). -/
def NavFin (s : NavState Float) : Prop := s.frac.IsFinite ∧ s.speed.IsFinite

/-- A finite controller memory. -/
def StateFin (s : Controller.State Float) : Prop :=
  NavFin s.nav ∧ PidFin s.pos.vx ∧ PidFin s.pos.vy ∧ PidFin s.pos.vz ∧
    PidFin s.rate.roll ∧ PidFin s.rate.pitch ∧ PidFin s.rate.yaw

/-- A saturation limit: finite, non-negative, below `2^100`. -/
def Lim (l : Float) : Prop := l.IsFinite ∧ 0 ≤ l.toReal ∧ l.toReal ≤ 2 ^ 100

/-- The saturation limits that guard the stored signals. -/
structure LimitsOK (P : Controller.Params Float) : Prop where
  iXY : Lim P.pos.velXY.iMax
  iZ : Lim P.pos.velZ.iMax
  iR : Lim P.rate.roll.iMax
  iP : Lim P.rate.pitch.iMax
  iY : Lim P.rate.yaw.iMax
  sXY : Lim P.pos.maxSpeedXY
  sZ : Lim P.pos.maxSpeedZ
  rRP : Lim P.att.maxRollPitchRate
  rY : Lim P.att.maxYawRate
  wpS : Lim P.nav.wpSpeed

/-- The difference of two finite floats below `2^100` is finite. -/
theorem sub_fin {a b : Float} (ha : a.IsFinite) (hb : b.IsFinite) (ha' : |a.toReal| ≤ 2 ^ 100)
    (hb' : |b.toReal| ≤ 2 ^ 100) : (a - b).IsFinite := by
  refine (Float.sub_err_all ha hb ?_).1
  have hM : (2 : ℝ) ^ 100 + 2 ^ 100 ≤ Float.Model.UnpackedFloat.maxFinite := by
    unfold Float.Model.UnpackedFloat.maxFinite
    have h : (2 : ℝ) ^ (100 : ℤ) ≤ 2 ^ (971 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
    have h' : (2 : ℝ) ^ (100 : ℤ) = 2 ^ 100 := zpow_natCast 2 100
    rw [h'] at h
    have h2 : (2 : ℝ) * 2 ^ (971 : ℤ) ≤ (2 ^ 53 - 1) * 2 ^ (971 : ℤ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (zpow_pos two_pos _).le
    generalize (2 : ℝ) ^ (971 : ℤ) = X at h h2 ⊢
    generalize (2 : ℝ) ^ 100 = Y at h h2 ⊢
    linarith
  calc |a.toReal - b.toReal| ≤ |a.toReal| + |b.toReal| := abs_sub _ _
    _ ≤ _ := by linarith

theorem pid_fin (g : PidGains Float) (hg : Lim g.iMax) (s : PidState Float) {e : Float}
    (he : e.IsFinite) (dt : Float) : PidFin (Pid.step g s e dt).1 :=
  ⟨(clipSym_spec hg.1 hg.2.1 _).1, he⟩

theorem clipSym_lim {l : Float} (hl : Lim l) (x : Float) :
    (clipSym l x).IsFinite ∧ |(clipSym l x).toReal| ≤ 2 ^ 100 := by
  obtain ⟨h1, h2⟩ := clipSym_spec hl.1 hl.2.1 x
  exact ⟨h1, h2.trans hl.2.2⟩

/-- The rate loop keeps its memory finite on finite rates below `2^100`. -/
theorem rate_fin (P : Controller.Params Float) (hP : LimitsOK P) (s : RateState Float)
    (att : Euler Float) (des : Euler Float) (rates : Vec3 Float) (dt : Float)
    (hr : BndVec (2 ^ 100) rates) :
    let r := (RateControl.step P.rate s ⟨rates, AttitudeControl.step P.att ⟨att, des⟩, dt⟩).1
    PidFin r.roll ∧ PidFin r.pitch ∧ PidFin r.yaw := by
  obtain ⟨⟨fx, fy, fz⟩, bx, by', bz⟩ := hr
  obtain ⟨c1, c1'⟩ := clipSym_lim hP.rRP (P.att.rollGain * (des.roll - att.roll))
  obtain ⟨c2, c2'⟩ := clipSym_lim hP.rRP (P.att.pitchGain * (des.pitch - att.pitch))
  obtain ⟨c3, c3'⟩ := clipSym_lim hP.rY (P.att.yawGain * wrapAngle (des.yaw - att.yaw))
  exact ⟨pid_fin _ hP.iR _ (sub_fin c1 fx c1' bx) _, pid_fin _ hP.iP _ (sub_fin c2 fy c2' by') _,
    pid_fin _ hP.iY _ (sub_fin c3 fz c3' bz) _⟩

/-- The position loop keeps its memory finite on finite velocities below `2^100`. -/
theorem pos_fin (P : Controller.Params Float) (hP : LimitsOK P) (s : PosState Float)
    (pos vel posSp velSp accSp : Vec3 Float) (dt : Float) (hv : BndVec (2 ^ 100) vel) :
    let r := (PositionControl.step P.pos s ⟨pos, vel, posSp, velSp, accSp, dt⟩).1
    PidFin r.vx ∧ PidFin r.vy ∧ PidFin r.vz := by
  obtain ⟨⟨fx, fy, fz⟩, bx, by', bz⟩ := hv
  obtain ⟨c1, c1'⟩ := clipSym_lim hP.sXY (velSp.x + P.pos.posGainXY * (posSp.x - pos.x))
  obtain ⟨c2, c2'⟩ := clipSym_lim hP.sXY (velSp.y + P.pos.posGainXY * (posSp.y - pos.y))
  obtain ⟨c3, c3'⟩ := clipSym_lim hP.sZ (velSp.z + P.pos.posGainZ * (posSp.z - pos.z))
  exact ⟨pid_fin _ hP.iXY _ (sub_fin c1 fx c1' bx) _, pid_fin _ hP.iXY _ (sub_fin c2 fy c2' by') _,
    pid_fin _ hP.iZ _ (sub_fin c3 fz c3' bz) _⟩

/-- The navigator stores a progress and a speed that are outputs of clips, so they are finite on
every input. -/
theorem nav_fin (P : Controller.Params Float) (hP : LimitsOK P) (s : NavState Float)
    (pos : Vec3 Float) (dt : Float) : NavFin (Navigator.step P.nav s pos dt).1 :=
  ⟨(clip_spec zero_isFinite one_isFinite (by simp) _).1,
   (clip_spec zero_isFinite hP.wpS.1 (by simpa using hP.wpS.2.1) _).1⟩

/-- Samples whose velocity and body rates are finite and below `2^100`. -/
def InputOK (i : SimInput Float) : Prop := BndVec (2 ^ 100) i.vel ∧ BndVec (2 ^ 100) i.rates

/-- **One tick keeps the controller finite.** On a sample with finite velocity and rates below
`2^100`, the next memory is finite and the motors are finite in `[0, 1]`; the current memory is
not even needed finite, since everything stored is recomputed from clipped signals and the sample. -/
-- <<step_finite>>
theorem step_finite (P : Controller.Params Float) (hP : LimitsOK P) (s : Controller.State Float)
    (inp : SimInput Float) (hi : InputOK inp) :
    StateFin (Controller.step P s inp).1 ∧ MotorsUnit (Controller.step P s inp).2 := by
  refine ⟨?_, step_motors_unit P s inp⟩
  have n := nav_fin P hP s.nav inp.pos inp.dt
  obtain ⟨p1, p2, p3⟩ := pos_fin P hP s.pos inp.pos inp.vel
    (Navigator.step P.nav s.nav inp.pos inp.dt).2.posSp
    (Navigator.step P.nav s.nav inp.pos inp.dt).2.velSp
    (Navigator.step P.nav s.nav inp.pos inp.dt).2.accSp inp.dt hi.1
  obtain ⟨r1, r2, r3⟩ := rate_fin P hP s.rate inp.att _ inp.rates inp.dt hi.2
  exact ⟨n, p1, p2, p3, r1, r2, r3⟩
-- <</step_finite>>

/-- Assumption: every sample is finite, with velocity and rates below `2^100`. -/
-- <<Aok>>
def Aok : Set (ℕ → QX) := {x | ∀ t, InputFinite (x t).sim ∧ InputOK (x t).sim}
-- <</Aok>>

/-- Guarantee: every run of the hidden memory that produces the behavior is finite after the first
tick, and the motor commands are finite in `[0, 1]`. -/
-- <<Gfin>>
def Gfin (P : Controller.Params Float) : Set (ℕ → QX) :=
  {x | (∀ t, MotorsUnit (x t).mot) ∧
    ∀ s : ℕ → Controller.State Float, s 0 = Controller.State.init →
      (∀ t, (s (t+1), (x t).mot) = Controller.step P (s t) (x t).sim) → ∀ t, StateFin (s t)}
-- <</Gfin>>

theorem init_fin : StateFin (Controller.State.init : Controller.State Float) := by
  refine ⟨⟨zero_isFinite, zero_isFinite⟩, ⟨zero_isFinite, zero_isFinite⟩, ⟨zero_isFinite, zero_isFinite⟩,
    ⟨zero_isFinite, zero_isFinite⟩, ⟨zero_isFinite, zero_isFinite⟩,
    ⟨zero_isFinite, zero_isFinite⟩, ⟨zero_isFinite, zero_isFinite⟩⟩

/-- **Finiteness.** The controller implements `⟨Aok, Gfin P⟩` for every parameter record whose
limits are finite, non-negative and below `2^100`. -/
-- <<controller_finite>>
theorem controller_finite (P : Controller.Params Float) (hP : LimitsOK P) :
    MctrlP P ⊨ ⟨Aok, Gfin P⟩ := by
  rintro x ⟨hM, hA⟩
  refine ⟨(motors_in_unit P) ⟨hM, fun t => (hA t).1⟩, ?_⟩
  intro s h0 hs t
  cases t with
  | zero => rw [h0]; exact init_fin
  | succ t =>
    have := congrArg Prod.fst (hs t)
    simp only at this
    rw [this]; exact (step_finite P hP _ _ (hA t).2).1
-- <</controller_finite>>

/-! ## The flown parameters meet `LimitsOK` -/

theorem lim_of {l : Float} (hf : l.isFinite = true) (h0 : (0 : Float) ≤ l)
    (h1 : l ≤ (1000 : Float)) : Lim l := by
  have h1f : (1000 : Float).IsFinite := by decide
  have h0' := (Float.le_iff_toReal_le zero_isFinite hf).1 h0
  have h1' := (Float.le_iff_toReal_le hf h1f).1 h1
  have h1000 : (1000 : Float).toReal = 1000 := by
    rw [Float.toReal, show (1000 : Float).toModel.unpack =
      .finite .positive 8796093022208000 (-43) (by decide) from rfl]
    simp [Float.Model.UnpackedFloat.toReal, Float.Model.UnpackedFloat.Sign.apply]; norm_num
  rw [Float.toReal_zero] at h0'
  have hb : (1000 : ℝ) ≤ 2 ^ 100 := by norm_num
  exact ⟨hf, h0', by rw [h1000] at h1'; linarith⟩

theorem cf2x_limits : LimitsOK cf2xParams where
  iXY := lim_of (by decide) (by decide) (by decide)
  iZ := lim_of (by decide) (by decide) (by decide)
  iR := lim_of (by decide) (by decide) (by decide)
  iP := lim_of (by decide) (by decide) (by decide)
  iY := lim_of (by decide) (by decide) (by decide)
  sXY := lim_of (by decide) (by decide) (by decide)
  sZ := lim_of (by decide) (by decide) (by decide)
  rRP := lim_of (by decide) (by decide) (by decide)
  rY := lim_of (by decide) (by decide) (by decide)
  wpS := lim_of (by decide) (by decide) (by decide)

/-- The flown controller meets the finiteness contract. -/
theorem controller_finite_cf2x : Mctrl ⊨ ⟨Aok, Gfin cf2xParams⟩ :=
  controller_finite cf2xParams cf2x_limits

theorem course_limits : LimitsOK courseParams where
  iXY := lim_of (by decide) (by decide) (by decide)
  iZ := lim_of (by decide) (by decide) (by decide)
  iR := lim_of (by decide) (by decide) (by decide)
  iP := lim_of (by decide) (by decide) (by decide)
  iY := lim_of (by decide) (by decide) (by decide)
  sXY := lim_of (by decide) (by decide) (by decide)
  sZ := lim_of (by decide) (by decide) (by decide)
  rRP := lim_of (by decide) (by decide) (by decide)
  rY := lim_of (by decide) (by decide) (by decide)
  wpS := lim_of (by decide) (by decide) (by decide)

/-- The controller flying the figure-eight course meets the motor-range contract. -/
theorem motors_in_unit_course : MctrlP courseParams ⊨ ⟨Afin, Gunit⟩ := motors_in_unit courseParams

/-- The controller flying the figure-eight course meets the finiteness contract. -/
theorem controller_finite_course : MctrlP courseParams ⊨ ⟨Aok, Gfin courseParams⟩ :=
  controller_finite courseParams course_limits

end Contracts.QuadCode
