import Leanfc.Vec3

/-!
# Vehicle

The physical constants the controller needs from the airframe, read from the parameter file
(`params/*.params`, sources of each vehicle's numbers there): mass, the diagonal inertia, the motor
offset l per axis, the yaw-torque-to-thrust ratio c = km/kf and the maximum thrust of one motor
T_max. `Position.step` reads the mass, `Attitude.step` the inertia, `Mixer.step` the inverse
allocation rows and T_max.

Motor layout: ArduPilot Quad-X order, which is also PX4's Quad-X order; FRD positions (l, l),
(−l, −l), (l, −l), (−l, l): motor 1 front right CCW, 2 rear left CCW, 3 front left CW, 4 rear
right CW. Motor i contributes (T_i, −y_i T_i, x_i T_i, s_i c T_i) to (thrust, roll, pitch, yaw)
with s = (+1, +1, −1, −1), so the allocation matrix A has the rows (1, 1, 1, 1), (−l, l, l, −l),
(l, −l, l, −l), (c, c, −c, −c), and its inverse the closed form: motor i's thrust is
T/4 ∓ τx/(4l) ± τy/(4l) ± τz/(4c). `make` computes the three entries 1/4, 1/(4l), 1/(4c) once, in
binary32, at load time; a tick only multiplies and adds. `sim/mixer_inverse.py` is the reference
(binary64 numpy inverse and the expected binary32 hover command of `Checks`).
-/

/-- A row of a 4×4 matrix. -/
structure Row4 where
  c1 : R
  c2 : R
  c3 : R
  c4 : R
  deriving Inhabited, Repr

namespace Row4
def dot (r : Row4) (a b c d : R) : R := r.c1 * a + r.c2 * b + r.c3 * c + r.c4 * d
end Row4

structure Vehicle where
  /-- kg -/
  mass : R
  /-- diagonal of the inertia tensor about the body FRD axes, kg m² -/
  inertia : Vec3
  /-- motor offset from the center along each body axis, m (arm / √2) -/
  l : R
  /-- yaw torque per unit thrust of one motor, km/kf, m -/
  kmKf : R
  /-- maximum thrust of one motor, N; a command m ∈ [0, 1] asks for m · tMax -/
  tMax : R
  /-- derived by `make`: rows of A⁻¹, row i maps [T, τx, τy, τz] to the thrust of motor i -/
  inv0 : Row4
  inv1 : Row4
  inv2 : Row4
  inv3 : Row4
  deriving Inhabited, Repr

namespace Vehicle

/-- The vehicle with its inverse allocation rows: q = 1/4, r = 1/(4l), y = 1/(4c). -/
def make (mass : R) (inertia : Vec3) (l kmKf tMax : R) : Vehicle :=
  let q : R := 1 / 4
  let r : R := 1 / (4 * l)
  let y : R := 1 / (4 * kmKf)
  { mass, inertia, l, kmKf, tMax,
    inv0 := ⟨q, -r, r, y⟩, inv1 := ⟨q, r, -r, y⟩, inv2 := ⟨q, r, r, -y⟩, inv3 := ⟨q, -r, -r, -y⟩ }

/-- Rows of the allocation matrix A (thrust, roll, pitch, yaw; columns motors 1..4). Used by the
checks and by `Main --print-params`, never in a tick. -/
def allocRows (v : Vehicle) : Row4 × Row4 × Row4 × Row4 :=
  (⟨1, 1, 1, 1⟩, ⟨-v.l, v.l, v.l, -v.l⟩, ⟨v.l, -v.l, v.l, -v.l⟩,
   ⟨v.kmKf, v.kmKf, -v.kmKf, -v.kmKf⟩)

end Vehicle
