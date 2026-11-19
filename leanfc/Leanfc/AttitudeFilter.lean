import Leanfc.Quat

/-!
# AttitudeFilter

Explicit complementary filter of Mahony, Hamel and Pflimlin with gyro-bias integral, plus a
40 Hz low-pass of the bias-corrected rate for the rate loop; pyfc `estimator.AttitudeFilter`.
The correction is err = downMeas × downPred (downMeas = −accel/‖accel‖, downPred = q⁻¹ (0,0,1) q)
plus, when a heading fix (hc, hs) is present, (kYaw/kAcc) · q⁻¹ (0, 0, e) q with
e = hs·ĉ − hc·ŝ, the sine of the heading difference ((ĉ, ŝ) = `headingVec q`). pyfc uses the
wrapped angle difference (atan2) instead of its sine and the exponential map instead of the
first-order quaternion update; DESIGN.md replaces both to keep the filter transcendental-free.
The constants kYaw/kAcc, dt/2 and the low-pass coefficient a/(1+a), a = 2π · cutoffHz · dt, are
computed once by `make`.
-/

structure AttFilterParams where
  kAcc : R
  kYaw : R
  kBias : R
  cutoffHz : R
  /-- derived by `make`: kYaw / kAcc -/
  yawScale : R
  /-- derived by `make`: dt / 2 -/
  halfDt : R
  /-- derived by `make`: a / (1 + a) with a = 2π · cutoffHz · dt -/
  rateAlpha : R
  deriving Inhabited, Repr

structure AttFilterState where
  q : Quat
  bias : Vec3
  omega : Vec3
  deriving Inhabited, Repr

namespace AttitudeFilter

def init (q0 : Quat) : AttFilterState := ⟨q0, Vec3.zero, Vec3.zero⟩

/-- 2π rounded to binary32 (pyfc `F(2 * np.pi)`). -/
def twoPi : R := 6.283185307179586

def make (kAcc kYaw kBias cutoffHz dt : R) : AttFilterParams :=
  let a := twoPi * cutoffHz * dt
  ⟨kAcc, kYaw, kBias, cutoffHz, kYaw / kAcc, 0.5 * dt, a / (1 + a)⟩

/-- One tick. Output: attitude estimate and filtered body rate. -/
def step (p : AttFilterParams) (st : AttFilterState) (gyro accel : Vec3)
    (heading : Option (R × R)) (dt : R) : AttFilterState × (Quat × Vec3) :=
  let downMeas := Vec3.div (-accel) (Vec3.norm accel)
  let downPred := Quat.rotate (Quat.conj st.q) ⟨0, 0, 1⟩
  let errAcc := Vec3.cross downMeas downPred
  let err := match heading with
    | none => errAcc
    | some (hc, hs) =>
      let (c, s) := Quat.headingVec st.q
      let e := hs * c - hc * s
      errAcc + Vec3.scale p.yawScale (Quat.rotate (Quat.conj st.q) ⟨0, 0, e⟩)
  let bias := st.bias - Vec3.scale dt (Vec3.scale p.kBias err)
  let rate := gyro - bias
  let q := Quat.integrate st.q (rate + Vec3.scale p.kAcc err) p.halfDt
  let omega := st.omega + Vec3.scale p.rateAlpha (rate - st.omega)
  (⟨q, bias, omega⟩, (q, omega))

end AttitudeFilter
