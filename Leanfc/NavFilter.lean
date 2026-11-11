import Leanfc.Quat

/-!
# NavFilter

Fixed-gain navigation filter per axis; pyfc `estimator.NavFilter`. Prediction with the
attitude-rotated accelerometer plus gravity minus an acceleration-bias state,
a = q accel q⁻¹ + (0, 0, g) − aBias, p += v dt + a dt²/2, v += a dt. A position fix corrects
p by alpha·r and v by (beta/dtFix)·r with r = fix − p; a velocity fix corrects v by kV·rv and
aBias by −(kB/dtFix)·rv with rv = fix − v. beta/dtFix, kB/dtFix and dt²/2 are computed once by
`make`. The gains are tuned for one fix rate; the parameter file sets both.
-/

structure NavFilterParams where
  alpha : R
  beta : R
  kV : R
  kB : R
  /-- derived by `make`: beta / dtFix -/
  betaGain : R
  /-- derived by `make`: kB / dtFix -/
  kBGain : R
  /-- derived by `make`: dt · dt / 2 -/
  halfDt2 : R
  deriving Inhabited, Repr

structure NavFilterState where
  p : Vec3
  v : Vec3
  aBias : Vec3
  deriving Inhabited, Repr

namespace NavFilter

def make (alpha beta kV kB dt dtFix : R) : NavFilterParams :=
  ⟨alpha, beta, kV, kB, beta / dtFix, kB / dtFix, dt * dt / 2⟩

def init (p0 : Vec3) : NavFilterState := ⟨p0, Vec3.zero, Vec3.zero⟩

/-- One tick. Output: position and velocity estimates. -/
def step (k : NavFilterParams) (st : NavFilterState) (q : Quat) (accel : Vec3)
    (posFix velFix : Option Vec3) (dt : R) : NavFilterState × (Vec3 × Vec3) :=
  let a := Quat.rotate q accel + ⟨0, 0, gravity⟩ - st.aBias
  let p := st.p + Vec3.scale dt st.v + Vec3.scale k.halfDt2 a
  let v := st.v + Vec3.scale dt a
  let (p, v) := match posFix with
    | none => (p, v)
    | some fix =>
      let r := fix - p
      (p + Vec3.scale k.alpha r, v + Vec3.scale k.betaGain r)
  let (v, aBias) := match velFix with
    | none => (v, st.aBias)
    | some fix =>
      let rv := fix - v
      (v + Vec3.scale k.kV rv, st.aBias - Vec3.scale k.kBGain rv)
  (⟨p, v, aBias⟩, (p, v))

end NavFilter
