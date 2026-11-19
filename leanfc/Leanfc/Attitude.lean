import Leanfc.Quat
import Leanfc.PI
import Leanfc.Vehicle

/-!
# Attitude

Attitude and rate control; pyfc `attitude.py`. e = 2 · vec(qHat⁻¹ ⊗ qDes) (short way round),
omegaSp = clamp per axis ((kpAtt e.x, kpAtt e.y, kpYaw e.z) + ffBody, ±rateMax), torque =
J · PI(omegaSp − omegaHat), the PI with the gains `rate` on roll and pitch and `rateYaw` on yaw, the
vehicle's diagonal inertia J applied componentwise. The rate PI is in angular-acceleration units,
so the gains carry over between vehicles of different inertia. Yaw has its own gains because a
vehicle's yaw authority (rotor drag torque) can be far below its roll and pitch authority (the
X500's is about 20 times lower, the CF2X's 1.7 times lower); pyfc uses one set for all axes, which
is the CF2X's configuration (kpYaw = kpAtt, rateYaw = rate).

ffBody is the navigator's yaw-rate feedforward r (about NED down) in body axes,
R(qHat)ᵀ (0, 0, r), as ArduPilot's `euler_derivative_to_body` turns the Euler yaw rate into body
rates (ArduPilot rotates with its attitude target; here the estimated attitude is used).
-/

structure AttitudeParams where
  kpAtt : R
  rateMax : R
  rate : PIGains
  kpYaw : R
  rateYaw : PIGains
  deriving Inhabited, Repr

namespace Attitude

/-- One tick, with the yaw-rate feedforward `yawRate` (rad/s about NED down). Output: body
torque (N m). -/
def step (veh : Vehicle) (k : AttitudeParams) (st : PIState) (qDes qHat : Quat) (omegaHat : Vec3)
    (yawRate : R) : PIState × Vec3 :=
  let e := Quat.errorVec qHat qDes
  let ff := Quat.rotate (Quat.conj qHat) ⟨0, 0, yawRate⟩
  let omegaSp :=
    Vec3.clampAxes ⟨k.kpAtt * e.x + ff.x, k.kpAtt * e.y + ff.y, k.kpYaw * e.z + ff.z⟩ k.rateMax
  let r := omegaSp - omegaHat
  let (ix, ux) := PI.step1 k.rate st.integral.x r.x
  let (iy, uy) := PI.step1 k.rate st.integral.y r.y
  let (iz, uz) := PI.step1 k.rateYaw st.integral.z r.z
  (⟨⟨ix, iy, iz⟩⟩, Vec3.hadamard veh.inertia ⟨ux, uy, uz⟩)

end Attitude
