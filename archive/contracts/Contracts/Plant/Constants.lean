module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Constants of the Crazyflie 2.x as flown by `sim/run_copter.py`

Every constant names the file and line it is read from. Paths are relative to
`gym_pybullet_drones/` (the installed simulator package, `sim/.venv/lib/python3.12/site-packages/`)
or to `cpp2lean/sim/` for the driver `run_copter.py`.

The per-motor maximum thrust `fmax = kf · MAX_RPM²` is a quarter of `thrust2weight · m · g`
(`kf_maxRPM_sq`), so all forces and torques are rational multiples of `m g`; hover is the thrust
fraction `1 / thrust2weight` on every motor.
-/

@[expose] public section

namespace Contracts.Plant

noncomputable section

/-- Mass, kg: `<mass value="0.027"/>`, `assets/cf2x.urdf:11`. -/
def mass : ℝ := 0.027

/-- Principal moment of inertia about body x (forward), kg m²: `ixx="1.4e-5"`,
`assets/cf2x.urdf:12`. The URDF is loaded with `URDF_USE_INERTIA_FROM_FILE`
(`envs/BaseAviary.py:488`), and the four propeller links have mass and inertia `0`
(`assets/cf2x.urdf:43-44, 55-56, 67-68, 79-80`), so this is the rigid body's inertia. -/
def Jx : ℝ := 1.4e-5

/-- Principal moment of inertia about body y, kg m²: `iyy="1.4e-5"`, `assets/cf2x.urdf:12`. -/
def Jy : ℝ := 1.4e-5

/-- Principal moment of inertia about body z, kg m²: `izz="2.17e-5"`, `assets/cf2x.urdf:12`.
The products of inertia are `0` (same line), so the inertia tensor is `diag(Jx, Jy, Jz)` in the
body frame, and it is the same in FLU and FRD. -/
def Jz : ℝ := 2.17e-5

/-- Arm length (center to rotor), m: `arm="0.0397"`, `assets/cf2x.urdf:5`. Used by the explicit
model `BaseAviary._dynamics` as the lever `L/√2` (`envs/BaseAviary.py:847-848`); not used by the
`Physics.PYB` model, see `lever`. -/
def armL : ℝ := 0.0397

/-- X-configuration lever arm, m: the motor links sit at `(±0.028, ±0.028, 0)` in the body frame
(`<origin xyz="0.028 -0.028 0"/>` etc., `assets/cf2x.urdf:42, 54, 66, 78`). `Physics.PYB`
applies each motor force at its link (`BaseAviary._physics`, `envs/BaseAviary.py:692-699`,
`LINK_FRAME` at the link's inertial origin), so this is the lever of both roll and pitch torques
in the simulated physics. It differs from `armL / √2 = 0.028072…` of `_dynamics` by 0.26 %. -/
def lever : ℝ := 0.028

/-- Thrust coefficient, N per rpm²: `kf="3.16e-10"`, `assets/cf2x.urdf:5`. -/
def kf : ℝ := 3.16e-10

/-- Drag-torque coefficient, N m per rpm²: `km="7.94e-12"`, `assets/cf2x.urdf:5`. -/
def km : ℝ := 7.94e-12

/-- Thrust-to-weight ratio: `thrust2weight="2.25"`, `assets/cf2x.urdf:5`. -/
def thrust2weight : ℝ := 2.25

/-- Gravity, m/s²: ArduPilot's `GRAVITY_MSS = 9.80665` (`run_copter.py:89`), which the driver
writes over the environment's `self.G = 9.8` (`envs/BaseAviary.py:74`) in `make_env`
(`run_copter.py:268`) before `reset` passes it to `p.setGravity`. -/
def grav : ℝ := 9.80665

/-- Maximum rotor speed, rpm, as the driver recomputes it with `GRAVITY_MSS`:
`MAX_RPM = sqrt(THRUST2WEIGHT_RATIO · G · M / (4 KF))` (`run_copter.py:271`, the formula of
`envs/BaseAviary.py:119`). -/
def maxRPM : ℝ := Real.sqrt (thrust2weight * grav * mass / (4 * kf))

/-- Maximum thrust of one motor, N: `kf · MAX_RPM²` (a quarter of `MAX_THRUST`,
`run_copter.py:272`). -/
def fmax : ℝ := kf * maxRPM ^ 2

/-- The control period, s: `1 / CTRL_HZ` with `CTRL_HZ = 400` (`run_copter.py:86`; the period
sent to the controller, `dt = 1.0 / CTRL_HZ`, `run_copter.py:383`). The simulator steps its
physics `PYB_STEPS_PER_CTRL = 3` times per period (`--pyb-hz` default `1200`,
`run_copter.py:892`; `envs/BaseAviary.py:81, 342`) with the same motor speeds: a zero-order hold
of the actuators over `h`. -/
def h : ℝ := 1 / 400

/-- Maximum vertical acceleration of the thrust, m/s²: `4 fmax / m = thrust2weight · g`. -/
def amax : ℝ := thrust2weight * grav

/-- Ratio of the drag-torque and thrust coefficients, m: the yaw torque of one motor is
`(km / kf) ·` its thrust. -/
def kmkf : ℝ := km / kf

/-- **The maximum thrust identity.** `kf · MAX_RPM² = thrust2weight · m · g / 4`. -/
theorem kf_maxRPM_sq : kf * maxRPM ^ 2 = thrust2weight * grav * mass / 4 := by
  rw [maxRPM, Real.sq_sqrt (by norm_num [thrust2weight, grav, mass, kf])]
  unfold kf; field_simp

/-- The four motors at full speed give `thrust2weight` times the weight:
`4 · kf · MAX_RPM² = thrust2weight · m · g`. -/
theorem four_kf_maxRPM_sq : 4 * kf * maxRPM ^ 2 = thrust2weight * mass * grav := by
  have := kf_maxRPM_sq; linear_combination 4 * this

/-- `fmax = thrust2weight · m · g / 4`. -/
theorem fmax_eq : fmax = thrust2weight * grav * mass / 4 := kf_maxRPM_sq

/-- `km · MAX_RPM² = (km / kf) · fmax`. -/
theorem km_maxRPM_sq : km * maxRPM ^ 2 = kmkf * fmax := by
  unfold kmkf fmax; field_simp [show kf ≠ 0 by norm_num [kf]]

theorem mass_pos : 0 < mass := by norm_num [mass]
theorem Jx_pos : 0 < Jx := by norm_num [Jx]
theorem Jy_pos : 0 < Jy := by norm_num [Jy]
theorem Jz_pos : 0 < Jz := by norm_num [Jz]
theorem h_pos : 0 < h := by norm_num [h]
theorem grav_pos : 0 < grav := by norm_num [grav]
theorem lever_pos : 0 < lever := by norm_num [lever]
theorem kmkf_pos : 0 < kmkf := by norm_num [kmkf, km, kf]
theorem fmax_pos : 0 < fmax := by rw [fmax_eq]; norm_num [thrust2weight, grav, mass]
theorem amax_pos : 0 < amax := by norm_num [amax, thrust2weight, grav]
theorem Jy_eq_Jx : Jy = Jx := by norm_num [Jx, Jy]
theorem Jx_le_Jz : Jx ≤ Jz := by norm_num [Jx, Jz]

/-- `4 fmax / m = amax`. -/
theorem four_fmax_div_mass : 4 * fmax / mass = amax := by
  rw [fmax_eq, amax]; field_simp [mass_pos.ne']

end

end Contracts.Plant
