import Leanfc.Vec3

/-!
# PI

The vector PI primitive shared by the velocity loop (Position) and the rate loop (Attitude):
u = kp e + ∫ ki e dt, the integral clamped per axis to ±iMax. pyfc `pid.py` with kd = 0 (both
pyfc loops run with kd = 0, so the derivative branch is dropped). `kiDt` = ki · dt is computed
once when the gains are made (`PI.gains`), not in the tick.
-/

structure PIGains where
  kp : R
  ki : R
  iMax : R
  /-- derived by `PI.gains`: ki · dt -/
  kiDt : R
  deriving Inhabited, Repr

structure PIState where
  integral : Vec3
  deriving Inhabited, Repr

namespace PI

def init : PIState := ⟨Vec3.zero⟩

/-- Gains for a loop running every `dt` seconds. -/
def gains (kp ki iMax dt : R) : PIGains := ⟨kp, ki, iMax, ki * dt⟩

/-- One axis, one tick: integral ← clamp (integral + e (ki dt)), output kp e + integral. -/
def step1 (g : PIGains) (integral e : R) : R × R :=
  let i := R.clamp (-g.iMax) g.iMax (integral + g.kiDt * e)
  (i, g.kp * e + i)

/-- All three axes with the same gains. -/
def step (g : PIGains) (st : PIState) (error : Vec3) : PIState × Vec3 :=
  let (ix, ux) := step1 g st.integral.x error.x
  let (iy, uy) := step1 g st.integral.y error.y
  let (iz, uz) := step1 g st.integral.z error.z
  (⟨⟨ix, iy, iz⟩⟩, ⟨ux, uy, uz⟩)

end PI
