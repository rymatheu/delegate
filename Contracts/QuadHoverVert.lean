import Contracts.QuadHoverZero

/-!
# The vertical channel of the hover: forward error bounds

Near the hover point (`|ζ|, |w|, |I| ≤ 1/100` with `ζ = z + 1` the altitude error, `w` the vertical
velocity and `I` the vertical velocity integrator) and with a sensor within `δ ≤ 10⁻⁶`, the
`Float` vertical channel of the controller computes, within explicit bounds,

* the velocity error `ev ≈ -1.5 ζ - w`,
* the new integrator `I' ≈ I + ev / 60`,
* the acceleration setpoint `az ≈ I + (241/60) ev` (`= 4 ev + I'`),
* the collective thrust `u ≈ (9.8 - az) / 22.05`, which makes the plant's vertical acceleration
  `9.8 - 22.05 u` equal to `az` up to `2.1 · 10⁻⁵`.

No saturation is active. The bounds are proven operation by operation with the `Near` calculus of
`Contracts.QuadNear`.
-/

namespace Contracts.QuadHover

open Contracts.QuadFloat Contracts.QuadNear Contracts.QuadPlant Flight
open Float.Model UnpackedFloat

/-- The value of a literal read off its unpacked form. -/
theorem lit {x : Float} (m : ℕ) (e : ℤ) (hm : 0 < m)
    (h : x.toModel.unpack = .finite .positive m e hm) : x.IsFinite ∧ x.toReal = (m : ℝ) * 2 ^ e := by
  refine ⟨?_, ?_⟩
  · rw [QuadFloat.isFinite_iff', h]; rfl
  · rw [Float.toReal, h]; simp [UnpackedFloat.toReal, Sign.apply]

theorem near_lit {x : Float} {m : ℕ} {e : ℤ} {hm : 0 < m}
    (h : x.toModel.unpack = .finite .positive m e hm) {v ε : ℝ}
    (hv : |(m : ℝ) * 2 ^ e - v| ≤ ε) : Near x v ε := by
  obtain ⟨hf, hx⟩ := lit m e hm h
  exact ⟨hf, by rw [hx]; exact hv⟩

/-! ## The literals of the hover parameters -/

theorem nGainZ : Near hoverParams.pos.posGainZ 1.5 0 := near_lit (m := 6755399441055744) (e := -52)
  (hm := by decide) rfl (by norm_num)
theorem nSpeedZ : Near hoverParams.pos.maxSpeedZ 1 0 := near_lit (m := 4503599627370496) (e := -52)
  (hm := by decide) rfl (by norm_num)
theorem nKiZ : Near hoverParams.pos.velZ.ki 2 0 := near_lit (m := 4503599627370496) (e := -51)
  (hm := by decide) rfl (by norm_num)
theorem nKpZ : Near hoverParams.pos.velZ.kp 4 0 := near_lit (m := 4503599627370496) (e := -50)
  (hm := by decide) rfl (by norm_num)
theorem nIMaxZ : Near hoverParams.pos.velZ.iMax 3 0 := near_lit (m := 6755399441055744) (e := -51)
  (hm := by decide) rfl (by norm_num)
theorem nAccZ : Near hoverParams.pos.maxAccelZ 3 0 := near_lit (m := 6755399441055744) (e := -51)
  (hm := by decide) rfl (by norm_num)
theorem zKdZ : Z hoverParams.pos.velZ.kd := by
  have : hoverParams.pos.velZ.kd.toModel.unpack = .zero .positive := rfl
  exact ⟨by rw [QuadFloat.isFinite_iff', this]; rfl, by rw [Float.toReal, this]; rfl⟩
theorem nGrav : Near hoverParams.target.gravity 9.8 1e-15 :=
  near_lit (m := 5516909543528858) (e := -49) (hm := by decide) rfl (by norm_num)
theorem nHov : Near hoverParams.target.hoverThrottle (4 / 9) 1e-16 :=
  near_lit (m := 8006399337547548) (e := -54) (hm := by decide) rfl (by norm_num)
theorem nDt : Near dtF (1 / 120) 1e-18 :=
  near_lit (m := 4803839602528529) (e := -59) (hm := by decide) rfl (by norm_num)
theorem nSpZ : Near (-1 : Float) (-1) 0 := by
  have h : (-1 : Float).toModel.unpack = .finite .negative 4503599627370496 (-52) (by decide) := rfl
  refine ⟨?_, ?_⟩
  · rw [QuadFloat.isFinite_iff', h]; rfl
  · rw [Float.toReal, h]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num

theorem Near.val0 {f : Float} {r : ℝ} (h : Near f r 0) : f.toReal = r := by
  have := h.2; rw [abs_nonpos_iff, sub_eq_zero] at this; exact this

/-! ## The vertical position and velocity loop -/

theorem bnd3 {x a b B : ℝ} (h1 : -(B - a - b) ≤ x) (h2 : x ≤ B - a - b) : |x| + a + b ≤ B := by
  have := abs_le.2 ⟨h1, h2⟩; linarith

theorem bnd {x B : ℝ} (h1 : -B ≤ x) (h2 : x ≤ B) : |x| ≤ B := abs_le.2 ⟨h1, h2⟩

theorem near_of_eq_val {x y : Float} {r e : ℝ} (hf : x.IsFinite) (hv : x.toReal = y.toReal)
    (hy : Near y r e) : Near x r e := ⟨hf, by rw [hv]; exact hy.2⟩

theorem near_clipSym_lit {a lim : Float} {r e L : ℝ} (ha : Near a r e) (hl : Near lim L 0)
    (h1 : -(L - e) ≤ r) (h2 : r ≤ L - e) : Near (clipSym lim a) r e :=
  near_clipSym ha hl.1 (by rw [Near.val0 hl]; have := abs_le.2 ⟨(by linarith : -(L - e) ≤ r), h2⟩; linarith)

/-- Near the hover, the vertical loop's new integrator, velocity error and acceleration setpoint. -/
theorem posZ_near (H : DivSqrtSpec) (s : PosState Float) (inp : PosInput Float)
    {ζ w I δ : ℝ} (hζ : |ζ| ≤ 1/100) (hw : |w| ≤ 1/100) (hI : |I| ≤ 1/100) (hδ : δ ≤ 1e-6)
    (hsp : inp.posSp.z = -1) (hvsp : Z inp.velSp.z) (hasp : Z inp.accSp.z)
    (hz : Near inp.pos.z (ζ - 1) δ) (hv : Near inp.vel.z w δ)
    (hint : Near s.vz.integral I 0) (hprev : s.vz.prevError.IsFinite)
    (hprev' : |s.vz.prevError.toReal| ≤ 1/20) (hdt : inp.dt = dtF) :
    Near (PositionControl.step hoverParams.pos s inp).1.vz.integral (I + (-(3/2) * ζ - w) / 60)
      4.3e-8 ∧
    Near (PositionControl.step hoverParams.pos s inp).1.vz.prevError (-(3/2) * ζ - w) 2.51e-6 ∧
    Near (PositionControl.step hoverParams.pos s inp).2.z (I + (241/60) * (-(3/2) * ζ - w))
      1.01e-5 := by
  have hu := uu_le; have hu0 := uu_nonneg; have hη := ηη_le_uu
  have hδ0 : 0 ≤ δ := hz.nonneg
  have hζ' := abs_le.1 hζ; have hw' := abs_le.1 hw; have hI' := abs_le.1 hI
  -- position error and velocity setpoint
  have e1 : Near (inp.posSp.z - inp.pos.z) (-ζ) 1.001e-6 := by
    have := near_sub (hsp ▸ nSpZ) hz (B := 0.012) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have e2 : Near (hoverParams.pos.posGainZ * (inp.posSp.z - inp.pos.z)) (1.5 * -ζ) 1.502e-6 := by
    have := near_mul nGainZ e1 (Ra := 1.5) (Rb := 0.01) (by norm_num) (bnd (by linarith)
      (by linarith)) (by norm_num)
    exact this.mono (by linarith)
  have e2' : Near (inp.velSp.z + hoverParams.pos.posGainZ * (inp.posSp.z - inp.pos.z)) (1.5 * -ζ)
      1.502e-6 := by
    have := Zero.add_zero_left hvsp.1 e2.1 hvsp.2
    exact near_of_eq_val this.1 this.2 e2
  have e3 : Near (clipSym hoverParams.pos.maxSpeedZ
      (inp.velSp.z + hoverParams.pos.posGainZ * (inp.posSp.z - inp.pos.z))) (1.5 * -ζ) 1.502e-6 :=
    near_clipSym_lit e2' nSpeedZ (by linarith) (by linarith)
  -- velocity error
  have e4 : Near (PositionControl.velocitySetpoint hoverParams.pos inp.pos inp.posSp inp.velSp -
      inp.vel).z
      (-(3/2) * ζ - w) 2.51e-6 := by
    have := near_sub e3 hv (B := 0.026) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  set ev := (PositionControl.velocitySetpoint hoverParams.pos inp.pos inp.posSp inp.velSp -
      inp.vel).z
    with hev
  -- integrator
  have e5 : Near (hoverParams.pos.velZ.ki * ev) (2 * (-(3/2) * ζ - w)) 5.03e-6 := by
    have := near_mul nKiZ e4 (Ra := 2) (Rb := 0.025) (by norm_num) (bnd (by linarith)
      (by linarith)) (by norm_num)
    exact this.mono (by linarith)
  have e6 : Near (hoverParams.pos.velZ.ki * ev * inp.dt) (2 * (-(3/2) * ζ - w) * (1/120)) 4.2e-8 := by
    have := near_mul e5 (hdt ▸ nDt) (Ra := 0.05) (Rb := 1/120) (bnd (by linarith) (by linarith))
      (by norm_num) (by norm_num)
    exact this.mono (by linarith)
  have e7 : Near (s.vz.integral + hoverParams.pos.velZ.ki * ev * inp.dt)
      (I + (-(3/2) * ζ - w) / 60) 4.3e-8 := by
    have := near_add hint e6 (B := 0.011) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have e8 : Near (clipSym hoverParams.pos.velZ.iMax
      (s.vz.integral + hoverParams.pos.velZ.ki * ev * inp.dt)) (I + (-(3/2) * ζ - w) / 60) 4.3e-8 :=
    near_clipSym_lit e7 nIMaxZ (by linarith) (by linarith)
  -- output
  have e9 : Near (hoverParams.pos.velZ.kp * ev) (4 * (-(3/2) * ζ - w)) 1.0045e-5 := by
    have := near_mul nKpZ e4 (Ra := 4) (Rb := 0.025) (by norm_num) (bnd (by linarith)
      (by linarith)) (by norm_num)
    exact this.mono (by linarith)
  have e10 : Near (hoverParams.pos.velZ.kp * ev + clipSym hoverParams.pos.velZ.iMax
      (s.vz.integral + hoverParams.pos.velZ.ki * ev * inp.dt))
      (I + (241/60) * (-(3/2) * ζ - w)) 1.01e-5 := by
    have := near_add e9 e8 (B := 0.12) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  -- the derivative term is finite, so `kd * deriv` is a zero
  have hder : (if s.vz.primed then (if 0 < inp.dt then (ev - s.vz.prevError) / inp.dt else 0)
      else 0 : Float).IsFinite := by
    split
    · split
      · have hp := abs_le.1 hprev'
        have d1 := near_sub e4 (Near.exact hprev) (B := 0.1) (bnd3 (by linarith) (by linarith))
          (by norm_num)
        have d2 := near_div H d1 (hdt ▸ nDt) (Ra := 0.08) (bnd (by linarith) (by linarith))
          (by norm_num) (by rw [div_le_iff₀ (by norm_num)]; linarith)
        exact d2.1
      · exact Float.isFinite_zero
    · exact Float.isFinite_zero
  have hkd := Z_mul_left zKdZ hder
  have e11 := Zero.add_zero_right e10.1 hkd.1 hkd.2
  have e12 := near_of_eq_val e11.1 e11.2 e10
  have e13 := Zero.add_zero_left hasp.1 e12.1 hasp.2
  refine ⟨e8, e4, ?_⟩
  exact near_clipSym_lit (near_of_eq_val e13.1 e13.2 e12) nAccZ (by linarith) (by linarith)

/-! ## Thrust -/

/-- Near the hover, the collective thrust is `(9.8 - az) / 22.05` up to `9.5 · 10⁻⁷`. -/
theorem thrust_near (H : DivSqrtSpec) {ax ay az : Float} {a : ℝ} (hx : Z ax) (hy : Z ay)
    (haz : Near az a 1.01e-5) (ha : |a| ≤ 0.12) :
    (az - hoverParams.target.gravity).IsFinite ∧
    -100 ≤ (az - hoverParams.target.gravity).toReal ∧ (az - hoverParams.target.gravity).toReal ≤ -1 ∧
    Near (clip 0 1 (Float.sqrt (Vec3.normSq (⟨ax, ay, az - hoverParams.target.gravity⟩ : Vec3 Float))
      * hoverParams.target.hoverThrottle / hoverParams.target.gravity)) ((9.8 - a) / 22.05) 9.5e-7 := by
  have hu := uu_le; have hu0 := uu_nonneg; have hη := ηη_le_uu
  have ha' := abs_le.1 ha
  have e14 : Near (az - hoverParams.target.gravity) (a - 9.8) 1.011e-5 := by
    have := near_sub haz nGrav (B := 10) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact this.mono (by linarith)
  have b14 := abs_le.1 e14.2
  refine ⟨e14.1, by linarith, by linarith, ?_⟩
  have e15 := near_mul e14 e14 (Ra := 9.92) (Rb := 9.92) (bnd (by linarith) (by linarith))
    (bnd (by linarith) (by linarith)) (by norm_num)
  have e15' : Near ((az - hoverParams.target.gravity) * (az - hoverParams.target.gravity))
      ((9.8 - a) ^ 2) 2.01e-4 := (e15.congr (by ring)).mono (by linarith)
  have hn := normSq_Z hx hy e15'.1
  have e15'' := near_of_eq_val hn.1 hn.2 e15'
  have hs0 : 9.68 ≤ 9.8 - a := by linarith
  have e16 := near_sqrt H e15'' (s := 9.8 - a) rfl (by linarith) (by nlinarith) (by nlinarith)
  have hq : 2.01e-4 / (9.8 - a) ≤ 2.08e-5 - 2e-15 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hq0 : 0 ≤ 2.01e-4 / (9.8 - a) := div_nonneg (by norm_num) (by linarith)
  have e16' : Near (Float.sqrt (Vec3.normSq (⟨ax, ay, az - hoverParams.target.gravity⟩ : Vec3 Float)))
      (9.8 - a) 2.08e-5 := e16.mono (by nlinarith)
  have e17 := near_mul e16' nHov (Ra := 9.92) (Rb := 4/9) (bnd (by linarith) (by linarith))
    (by norm_num) (by norm_num)
  have e17' := e17.mono (e' := 9.25e-6) (by linarith)
  have e18 := near_div H e17' nGrav (Ra := 4.41) (bnd (by linarith) (by linarith)) (by norm_num)
    (by rw [div_le_iff₀ (by norm_num)]; linarith)
  have e18' : Near (Float.sqrt (Vec3.normSq (⟨ax, ay, az - hoverParams.target.gravity⟩ : Vec3 Float))
      * hoverParams.target.hoverThrottle / hoverParams.target.gravity) ((9.8 - a) / 22.05) 9.5e-7 := by
    refine (e18.congr (by ring)).mono ?_
    have h1 : ((4.41 : ℝ) + 9.25e-6) * 1e-15 / ((9.8 - 1e-15) * 9.8) ≤ 1e-15 := by
      rw [div_le_iff₀ (by norm_num)]; norm_num
    have h2 : (9.25e-6 : ℝ) / 9.8 ≤ 9.44e-7 := by norm_num
    have h3 : uu * ((4.41 + 9.25e-6) / (9.8 - 1e-15)) ≤ uu := by
      have : (4.41 + 9.25e-6 : ℝ) / (9.8 - 1e-15) ≤ 1 := by rw [div_le_iff₀ (by norm_num)]; norm_num
      nlinarith
    linarith
  exact near_clip01 e18' (by rw [le_div_iff₀ (by norm_num)]; nlinarith)
    (by have : (9.8 - a) / 22.05 ≤ 9.92 / 22.05 := by gcongr; linarith
        linarith [show (9.92 : ℝ) / 22.05 ≤ 0.45 by norm_num])
