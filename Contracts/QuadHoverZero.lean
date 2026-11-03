import Contracts.QuadPlant
import Contracts.QuadNear

/-!
# The level channels of the hover stay exactly at zero

At a hover sample (horizontal position and velocity, attitude and body rates all `±0`, the
setpoint on the vertical through the vehicle, horizontal feed-forward zero, heading setpoint
`0`), every horizontal and
rotational signal of the `Float` controller is a zero: the module lemmas below follow the zeros
through the position loop, the thrust and attitude target, the attitude loop, the rate loop and
the mixer, using only the exact zero cases of the `Float` model (`QuadFloat.Zero`), the clip, and
the three C-library facts `LibmZero`. The mixer then sends the same value to all four motors.
-/

namespace Contracts.QuadHover

open Contracts.QuadFloat Contracts.QuadFloat.Zero Contracts.QuadNear Flight

/-- A finite float of value zero (`+0` or `-0`). -/
def Z (f : Float) : Prop := f.IsFinite ∧ f.toReal = 0

theorem Z.fin {f : Float} (h : Z f) : f.IsFinite := h.1

theorem Z_zero : Z (0 : Float) := ⟨Float.isFinite_zero, Float.toReal_zero⟩

theorem Z_sub {a b : Float} (ha : Z a) (hb : Z b) : Z (a - b) := by
  have := sub_zero_right ha.1 hb.1 hb.2; exact ⟨this.1, this.2.trans ha.2⟩
theorem Z_add {a b : Float} (ha : Z a) (hb : Z b) : Z (a + b) := by
  have := add_zero_right ha.1 hb.1 hb.2; exact ⟨this.1, this.2.trans ha.2⟩
theorem Z_mul_right {a b : Float} (ha : a.IsFinite) (hb : Z b) : Z (a * b) :=
  mul_zero_right ha hb.1 hb.2
theorem Z_mul_left {a b : Float} (ha : Z a) (hb : b.IsFinite) : Z (a * b) :=
  mul_zero_left ha.1 hb ha.2
theorem Z_neg {a : Float} (ha : Z a) : Z (-a) := neg_zero' ha.1 ha.2

theorem Z_clipSym {lim a : Float} (hl : lim.IsFinite) (h0 : 0 ≤ lim.toReal) (ha : Z a) :
    Z (clipSym lim a) :=
  ⟨(clipSym_spec hl h0 a).1, by rw [clipSym_toReal_of_le hl h0 ha.1 (by rw [ha.2]; simpa)]; exact ha.2⟩

theorem Z_max {a b : Float} (ha : Z a) (hb : Z b) : Z (max a b) := by
  rw [max_eq]; split <;> assumption
theorem Z_min {a b : Float} (ha : Z a) (hb : Z b) : Z (min a b) := by
  rw [min_eq]; split <;> assumption

/-- Zero vector. -/
def ZV (v : Vec3 Float) : Prop := Z v.x ∧ Z v.y ∧ Z v.z

/-! ## PID with zero error -/

/-- Finite gains and a finite non-negative integrator limit. -/
def PidOK (g : PidGains Float) : Prop :=
  g.kp.IsFinite ∧ g.ki.IsFinite ∧ g.kd.IsFinite ∧ g.iMax.IsFinite ∧ 0 ≤ g.iMax.toReal

/-- PID memory at zero. -/
def ZP (s : PidState Float) : Prop := Z s.integral ∧ Z s.prevError

/-- The derivative term is a zero when the error and the previous error are zeros. -/
theorem deriv_Z {e prev dt : Float} (primed : Bool) (he : Z e) (hp : Z prev) (hdt : dt.IsFinite) :
    Z (if primed then (if 0 < dt then (e - prev) / dt else 0) else 0) := by
  split
  · split
    · rename_i h
      have h' := (Float.lt_iff_toReal_lt Float.isFinite_zero hdt).1 h
      rw [Float.toReal_zero] at h'
      exact div_zero_left (Z_sub he hp).1 hdt (Z_sub he hp).2 h'.ne'
    · exact Z_zero
  · exact Z_zero

theorem pid_Z (g : PidGains Float) (hg : PidOK g) (s : PidState Float) (hs : ZP s) {e dt : Float}
    (he : Z e) (hdt : dt.IsFinite) : ZP (Pid.step g s e dt).1 ∧ Z (Pid.step g s e dt).2 := by
  obtain ⟨hkp, hki, hkd, hiM, hiM0⟩ := hg
  have hint : Z (clipSym g.iMax (s.integral + g.ki * e * dt)) :=
    Z_clipSym hiM hiM0 (Z_add hs.1 (Z_mul_left (Z_mul_right hki he) hdt))
  refine ⟨⟨hint, he⟩, ?_⟩
  exact Z_add (Z_add (Z_mul_right hkp he) hint) (Z_mul_right hkd (deriv_Z s.primed he hs.2 hdt))

/-! ## Rate loop -/

def RateOK (p : RateParams Float) : Prop := PidOK p.roll ∧ PidOK p.pitch ∧ PidOK p.yaw

theorem rate_Z (p : RateParams Float) (hp : RateOK p) (s : RateState Float)
    (hs : ZP s.roll ∧ ZP s.pitch ∧ ZP s.yaw) (inp : RateInput Float) (hr : ZV inp.rates)
    (hsp : ZV inp.rateSp) (hdt : inp.dt.IsFinite) :
    (ZP (RateControl.step p s inp).1.roll ∧ ZP (RateControl.step p s inp).1.pitch ∧
      ZP (RateControl.step p s inp).1.yaw) ∧ ZV (RateControl.step p s inp).2 := by
  have h1 := pid_Z p.roll hp.1 s.roll hs.1 (Z_sub hsp.1 hr.1) hdt
  have h2 := pid_Z p.pitch hp.2.1 s.pitch hs.2.1 (Z_sub hsp.2.1 hr.2.1) hdt
  have h3 := pid_Z p.yaw hp.2.2 s.yaw hs.2.2 (Z_sub hsp.2.2 hr.2.2) hdt
  have h1f : (1 : Float).IsFinite := Float.isFinite_one
  have h10 : (0 : ℝ) ≤ (1 : Float).toReal := by simp
  exact ⟨⟨h1.1, h2.1, h3.1⟩, Z_clipSym h1f h10 h1.2, Z_clipSym h1f h10 h2.2, Z_clipSym h1f h10 h3.2⟩

/-! ## Attitude loop -/

def AttOK (p : AttCtlParams Float) : Prop :=
  p.rollGain.IsFinite ∧ p.pitchGain.IsFinite ∧ p.yawGain.IsFinite ∧
    p.maxRollPitchRate.IsFinite ∧ 0 ≤ p.maxRollPitchRate.toReal ∧
    p.maxYawRate.IsFinite ∧ 0 ≤ p.maxYawRate.toReal

/-- Zero attitude. -/
def ZE (a : Euler Float) : Prop := Z a.roll ∧ Z a.pitch ∧ Z a.yaw

theorem wrapAngle_Z (L : LibmZero) {e : Float} (he : Z e) : Z (wrapAngle e) := by
  obtain ⟨hs, hs0⟩ := L.sin_zero e he.1 he.2
  obtain ⟨hc, hc0⟩ := L.cos_zero e he.1 he.2
  exact L.atan2_zero _ _ hs hs0 hc hc0

theorem att_Z (L : LibmZero) (p : AttCtlParams Float) (hp : AttOK p) (inp : AttCtlInput Float)
    (hc : ZE inp.current) (hd : ZE inp.desired) : ZV (AttitudeControl.step p inp) := by
  obtain ⟨g1, g2, g3, l1, l1', l2, l2'⟩ := hp
  exact ⟨Z_clipSym l1 l1' (Z_mul_right g1 (Z_sub hd.1 hc.1)),
    Z_clipSym l1 l1' (Z_mul_right g2 (Z_sub hd.2.1 hc.2.1)),
    Z_clipSym l2 l2' (Z_mul_right g3 (wrapAngle_Z L (Z_sub hd.2.2 hc.2.2)))⟩

/-! ## Horizontal position loop -/

def PosOK (p : PosParams Float) : Prop :=
  p.posGainXY.IsFinite ∧ p.maxSpeedXY.IsFinite ∧ 0 ≤ p.maxSpeedXY.toReal ∧ PidOK p.velXY ∧
    p.maxAccelXY.IsFinite ∧ 0 ≤ p.maxAccelXY.toReal

theorem posXY_Z (p : PosParams Float) (hp : PosOK p) (s : PosState Float)
    (hs : ZP s.vx ∧ ZP s.vy) (inp : PosInput Float) (hpos : Z inp.pos.x ∧ Z inp.pos.y)
    (hvel : Z inp.vel.x ∧ Z inp.vel.y) (hsp : Z inp.posSp.x ∧ Z inp.posSp.y)
    (hvsp : Z inp.velSp.x ∧ Z inp.velSp.y) (hasp : Z inp.accSp.x ∧ Z inp.accSp.y)
    (hdt : inp.dt.IsFinite) :
    (ZP (PositionControl.step p s inp).1.vx ∧ ZP (PositionControl.step p s inp).1.vy) ∧
      Z (PositionControl.step p s inp).2.x ∧ Z (PositionControl.step p s inp).2.y := by
  obtain ⟨g, l, l', pid, a, a'⟩ := hp
  have ex : Z (clipSym p.maxSpeedXY (inp.velSp.x + p.posGainXY * (inp.posSp.x - inp.pos.x)) -
      inp.vel.x) :=
    Z_sub (Z_clipSym l l' (Z_add hvsp.1 (Z_mul_right g (Z_sub hsp.1 hpos.1)))) hvel.1
  have ey : Z (clipSym p.maxSpeedXY (inp.velSp.y + p.posGainXY * (inp.posSp.y - inp.pos.y)) -
      inp.vel.y) :=
    Z_sub (Z_clipSym l l' (Z_add hvsp.2 (Z_mul_right g (Z_sub hsp.2 hpos.2)))) hvel.2
  have h1 := pid_Z p.velXY pid s.vx hs.1 ex hdt
  have h2 := pid_Z p.velXY pid s.vy hs.2 ey hdt
  exact ⟨⟨h1.1, h2.1⟩, Z_clipSym a a' (Z_add hasp.1 h1.2), Z_clipSym a a' (Z_add hasp.2 h2.2)⟩

/-! ## Mixer -/

def MixOK (p : MixerParams Float) : Prop :=
  (p.f1.roll.IsFinite ∧ p.f1.pitch.IsFinite ∧ p.f1.yaw.IsFinite) ∧
  (p.f2.roll.IsFinite ∧ p.f2.pitch.IsFinite ∧ p.f2.yaw.IsFinite) ∧
  (p.f3.roll.IsFinite ∧ p.f3.pitch.IsFinite ∧ p.f3.yaw.IsFinite) ∧
  (p.f4.roll.IsFinite ∧ p.f4.pitch.IsFinite ∧ p.f4.yaw.IsFinite)

theorem apply_Z {f : MotorFactors Float} (hf : f.roll.IsFinite ∧ f.pitch.IsFinite ∧ f.yaw.IsFinite)
    {τ : Vec3 Float} (hτ : ZV τ) : Z (f.apply τ) :=
  Z_add (Z_add (Z_mul_right hf.1 hτ.1) (Z_mul_right hf.2.1 hτ.2.1)) (Z_mul_right hf.2.2 hτ.2.2)

/-- With zero torques, every motor receives the clipped collective thrust. -/
theorem mixer_Z (p : MixerParams Float) (hp : MixOK p) (inp : MixerInput Float)
    (hτ : ZV inp.torque) (ht : inp.thrust.IsFinite) (ht0 : 0 ≤ inp.thrust.toReal)
    (ht1 : inp.thrust.toReal ≤ 1) :
    let m := Mixer.step p inp
    m.m1.IsFinite ∧ m.m1.toReal = inp.thrust.toReal ∧ m.m2.IsFinite ∧ m.m2.toReal = inp.thrust.toReal ∧
      m.m3.IsFinite ∧ m.m3.toReal = inp.thrust.toReal ∧ m.m4.IsFinite ∧ m.m4.toReal = inp.thrust.toReal := by
  intro m
  have h1f : (1 : Float).IsFinite := Float.isFinite_one
  have h10 : (0 : ℝ) ≤ (1 : Float).toReal := by simp
  -- the clipped thrust
  have hthr := clip_toReal zero_isFinite h1f (by simp) ht
  simp only [Float.toReal_zero, Float.toReal_one, min_eq_right ht1, max_eq_right ht0] at hthr
  have hthrF := (clip_spec zero_isFinite h1f (by simp) inp.thrust).1
  set thr := clip 0 1 inp.thrust with hthr_def
  -- the clipped torques and the per-motor contributions
  have hτ' : ZV (inp.torque.map (clipSym 1)) :=
    ⟨Z_clipSym h1f h10 hτ.1, Z_clipSym h1f h10 hτ.2.1, Z_clipSym h1f h10 hτ.2.2⟩
  have r1 := apply_Z hp.1 hτ'
  have r2 := apply_Z hp.2.1 hτ'
  have r3 := apply_Z hp.2.2.1 hτ'
  have r4 := apply_Z hp.2.2.2 hτ'
  have hhi := Z_max (Z_max r1 r2) (Z_max r3 r4)
  have hlo := Z_min (Z_min r1 r2) (Z_min r3 r4)
  set hi := max (max (p.f1.apply (inp.torque.map (clipSym 1))) (p.f2.apply (inp.torque.map (clipSym 1))))
    (max (p.f3.apply (inp.torque.map (clipSym 1))) (p.f4.apply (inp.torque.map (clipSym 1))))
  set lo := min (min (p.f1.apply (inp.torque.map (clipSym 1))) (p.f2.apply (inp.torque.map (clipSym 1))))
    (min (p.f3.apply (inp.torque.map (clipSym 1))) (p.f4.apply (inp.torque.map (clipSym 1))))
  -- the torque scale is one
  have hk : Mixer.torqueScale thr lo hi = 1 := by
    have a1 := add_zero_right hthrF hhi.1 hhi.2
    have a2 := add_zero_right hthrF hlo.1 hlo.2
    have c1 : ¬ ((1 : Float) < thr + hi) := by
      rw [Float.lt_iff_toReal_lt h1f a1.1, a1.2, hthr]; simp; linarith
    have c2 : ¬ (thr + lo < (0 : Float)) := by
      rw [Float.lt_iff_toReal_lt a2.1 zero_isFinite, a2.2, hthr]; simp; linarith
    unfold Mixer.torqueScale
    simp only [c1, c2, if_false]
    rw [min_eq]; split <;> rfl
  -- every motor is the clipped thrust
  have mot : ∀ r : Float, Z r → (clip 0 1 (thr + Mixer.torqueScale thr lo hi * r)).IsFinite ∧
      (clip 0 1 (thr + Mixer.torqueScale thr lo hi * r)).toReal = inp.thrust.toReal := by
    intro r hr
    rw [hk]
    have hm := Z_mul_right h1f hr
    have a := add_zero_right hthrF hm.1 hm.2
    have := near_clip01 (r := inp.thrust.toReal) (e := 0) ⟨a.1, by rw [a.2, hthr]; simp⟩
      (by linarith) (by linarith)
    exact ⟨this.1, by have := this.2; rw [abs_le] at this; linarith [this.1, this.2]⟩
  exact ⟨(mot _ r1).1, (mot _ r1).2, (mot _ r2).1, (mot _ r2).2, (mot _ r3).1, (mot _ r3).2,
    (mot _ r4).1, (mot _ r4).2⟩

/-! ## Thrust and attitude target -/

def TargetOK (p : AttTargetParams Float) : Prop :=
  p.gravity.IsFinite ∧ p.maxLean.IsFinite ∧ 0 ≤ p.maxLean.toReal

/-- The squared norm of `(±0, ±0, tz)` is `tz * tz` in value. -/
theorem normSq_Z {ax ay tz : Float} (hx : Z ax) (hy : Z ay) (hz : (tz * tz).IsFinite) :
    (Vec3.normSq (⟨ax, ay, tz⟩ : Vec3 Float)).IsFinite ∧
      (Vec3.normSq (⟨ax, ay, tz⟩ : Vec3 Float)).toReal = (tz * tz).toReal := by
  have h0 : Z (ax * ax + ay * ay) := Z_add (Z_mul_right hx.1 hx) (Z_mul_right hy.1 hy)
  exact add_zero_left h0.1 hz h0.2

/-- With zero horizontal acceleration and heading, the target attitude is level and north, and the
thrust is the clipped `‖(0, 0, az - g)‖ · hover / g`. -/
theorem target_Z (H : DivSqrtSpec) (L : LibmZero) (p : AttTargetParams Float) (hp : TargetOK p)
    (inp : AttTargetInput Float) (hx : Z inp.accelSp.x) (hy : Z inp.accelSp.y)
    (htz : (inp.accelSp.z - p.gravity).IsFinite) (htz1 : (inp.accelSp.z - p.gravity).toReal ≤ -1)
    (htz2 : -100 ≤ (inp.accelSp.z - p.gravity).toReal) (hys : Z inp.yawSp) (hyw : Z inp.yaw) :
    ZE (AttitudeTarget.step p inp).attitude ∧
      (AttitudeTarget.step p inp).thrust =
        clip 0 1 (Float.sqrt (Vec3.normSq (⟨inp.accelSp.x, inp.accelSp.y,
          inp.accelSp.z - p.gravity⟩ : Vec3 Float)) * p.hoverThrottle / p.gravity) := by
  obtain ⟨hg, hl, hl0⟩ := hp
  refine ⟨?_, rfl⟩
  obtain ⟨hc, -⟩ := L.cos_zero _ hyw.1 hyw.2
  obtain ⟨hs, -⟩ := L.sin_zero _ hyw.1 hyw.2
  set tz := inp.accelSp.z - p.gravity
  have hfwd : Z (-(Float.cos inp.yaw * inp.accelSp.x + Float.sin inp.yaw * inp.accelSp.y)) :=
    Z_neg (Z_add (Z_mul_right hc hx) (Z_mul_right hs hy))
  have hright : Z (-(Float.cos inp.yaw * inp.accelSp.y - Float.sin inp.yaw * inp.accelSp.x)) :=
    Z_neg (Z_sub (Z_mul_right hc hy) (Z_mul_right hs hx))
  have hdown : (-tz).IsFinite := (Float.isFinite_neg _).2 htz
  have hdown1 : 1 ≤ (-tz).toReal := by rw [Float.toReal_neg]; linarith
  have hdown2 : (-tz).toReal ≤ 100 := by rw [Float.toReal_neg]; linarith
  -- pitch
  have hpitch := L.atan2_zero _ _ hfwd.1 hfwd.2 hdown (by linarith)
  -- roll: the square root of a positive number is positive
  have hsq := near_mul (Near.exact hdown) (Near.exact hdown) (le_of_eq (abs_of_pos (by linarith)))
    (le_of_eq (abs_of_pos (by linarith))) (by nlinarith)
  have hsq' : Near (sq (-tz)) ((-tz).toReal * (-tz).toReal)
      (uu * ((-tz).toReal * (-tz).toReal) + ηη) := by
    refine hsq.mono (le_of_eq ?_); ring
  have hu := uu_le; have hη := ηη_le_uu; have hu0 := uu_nonneg
  set fwd := -(Float.cos inp.yaw * inp.accelSp.x + Float.sin inp.yaw * inp.accelSp.y)
  have hF2 : Z (Flight.sq fwd) := Z_mul_right hfwd.1 hfwd
  have hsum := add_zero_left hF2.1 hsq'.1 hF2.2
  have hlo := (abs_le.1 hsq'.2).1
  have hhi := (abs_le.1 hsq'.2).2
  have hval : 1 / 2 ≤ (Flight.sq fwd + Flight.sq (-tz)).toReal := by
    rw [hsum.2]; nlinarith
  have hval2 : (Flight.sq fwd + Flight.sq (-tz)).toReal ≤ 1e6 := by
    rw [hsum.2]; nlinarith
  obtain ⟨hsqrt, hsqrt_err⟩ := H.sqrt_err _ hsum.1 (by linarith) hval2
  have hsqrt_pos : 0 < (Float.sqrt (Flight.sq fwd + Flight.sq (-tz))).toReal := by
    have h1 : (1 : ℝ) / 2 ≤ Real.sqrt (Flight.sq fwd + Flight.sq (-tz)).toReal :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    have := (abs_le.1 hsqrt_err).1
    nlinarith
  have hroll := L.atan2_zero _ _ (Z_neg hright).1 (Z_neg hright).2 hsqrt hsqrt_pos
  exact ⟨Z_clipSym hl hl0 hroll, Z_clipSym hl hl0 hpitch, hys⟩

end Contracts.QuadHover
