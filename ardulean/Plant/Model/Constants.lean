module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Constants of the X500 as simulated

The vehicle is the Holybro X500 V2 of the gorge flights: gym-pybullet-drones `Physics.PYB` with the URDF
`sim/world/x500/x500.urdf` (loaded by `sim/world/airframes.py`, `AirframeAviary`, with `URDF_USE_INERTIA_FROM_FILE`,
`sim/world/gorge_aviary.py:53-55`), the first-order motor lag of `sim/world/airframes.py`, and the driver
`sim/fly_gorge.py` with `sim/harness/` (gravity, physics rate, control period, the actuator map). Paths are relative to the repository root;
`gpd/` is the installed simulator package `.venv/lib/python3.12/site-packages/gym_pybullet_drones/`. Line numbers
are those of 2026-11-16. Every number is the decimal of the source, read as an exact rational (a Lean scientific
literal is exact). `tests/plant/check_constants.py` compares the literals here with the sources.

The per-motor maximum thrust `fmax = kf · MAX_RPM²` is a quarter of `thrust2weight · m · g` (`kf_maxRPM_sq`), so all
forces and torques are rational multiples of `m g`; hover is the thrust fraction `1 / thrust2weight` on every motor.

The last theorems record the facts of these numbers that the library uses (`Jy_eq_Jx`, `Jx_le_Jz`,
`kmkf_Jx_le_lever_Jz`, `one_le_thrust2weight`, `tauUp_lt_tauDown`); everything else is proved from them and from
positivity.
-/

@[expose] public section

namespace Plant

noncomputable section

/-- Mass, kg: `<mass value="2.0643076923076924"/>`, `sim/world/x500/x500.urdf:47` (the SDF's base 2.0 kg plus four
rotors of 0.016076923076923075 kg lumped into one rigid body, `x500.urdf:9-10`). -/
def mass : ℝ := 2.0643076923076924

/-- Principal moment of inertia about body x (forward), kg m²: `ixx="0.02166666666666667"`, `x500.urdf:48`. The
URDF is loaded with `URDF_USE_INERTIA_FROM_FILE` (`sim/world/gorge_aviary.py:55`), and the four propeller links have
mass and inertia `0` (`x500.urdf:73-74, 85-86, 97-98, 109-110`), so this is the rigid body's inertia. -/
def Jx : ℝ := 0.02166666666666667

/-- Principal moment of inertia about body y, kg m²: `iyy="0.02166666666666667"`, `x500.urdf:48`. -/
def Jy : ℝ := 0.02166666666666667

/-- Principal moment of inertia about body z, kg m²: `izz="0.04000000000000001"`, `x500.urdf:48`. The products of
inertia are `0` (same line), so the inertia tensor is `diag(Jx, Jy, Jz)` in the body frame, the same in FLU and FRD. -/
def Jz : ℝ := 0.04000000000000001

/-- Arm length (center to rotor), m: `arm="0.24607315985291853"`, `x500.urdf:41` (`0.174 √2`). Used only by the
explicit model `BaseAviary._dynamics` (`gpd/envs/BaseAviary.py:847-848`), not by `Physics.PYB`; see `lever`. -/
def armL : ℝ := 0.24607315985291853

/-- X-configuration lever arm, m: the propeller links' inertial origins are at `(±0.174, ±0.174, 0.06)` in the FLU
body frame (`<origin xyz="0.174 -0.174 0.06"/>` etc., `x500.urdf:72, 84, 96, 108`). `Physics.PYB` applies each
propeller force at its link (`BaseAviary._physics`, `gpd/envs/BaseAviary.py:676-707`, `LINK_FRAME`), so this is the
lever of the roll and pitch torques. The height `0.06` m of the thrust points gives no moment to a force along body
`z`. -/
def lever : ℝ := 0.174

/-- Thrust coefficient, N per rpm²: `kf="9.37456697678494e-08"`, `x500.urdf:41` (PX4's `motorConstant`
8.54858e-06 N/(rad/s)² in rpm, `x500.urdf:16-19`). -/
def kf : ℝ := 9.37456697678494e-08

/-- Drag-torque coefficient, N m per rpm²: `km="1.4999307162855904e-09"`, `x500.urdf:41` (`0.016 kf`, PX4's
`momentConstant`, `x500.urdf:17-19`). -/
def km : ℝ := 1.4999307162855904e-09

/-- Thrust-to-weight ratio: `thrust2weight="1.689113625148385"`, `x500.urdf:41`. -/
def thrust2weight : ℝ := 1.689113625148385

/-- Gravity, m/s²: ArduPilot's `GRAVITY_MSS = 9.80665` (`sim/harness/simulator.py:28`), which the driver writes over the
environment's `self.G = 9.8` (`gpd/envs/BaseAviary.py:74`): `env.G = GRAVITY_MSS` (`sim/harness/simulator.py:136`),
passed to `p.setGravity` by the housekeeping (`sim/world/gorge_aviary.py:49`). -/
def grav : ℝ := 9.80665

/-- Maximum rotor speed, rpm, as the driver recomputes it with `GRAVITY_MSS`:
`MAX_RPM = sqrt(THRUST2WEIGHT_RATIO · G · M / (4 KF))` (`sim/harness/simulator.py:137, 139`, the formula of
`gpd/envs/BaseAviary.py:117-119`); `9549.2966` rpm `= 1000` rad/s (`x500.urdf:20-22`). -/
def maxRPM : ℝ := Real.sqrt (thrust2weight * grav * mass / (4 * kf))

/-- Maximum thrust of one propeller, N: `kf · MAX_RPM²` (a quarter of `MAX_THRUST`, `sim/harness/simulator.py:140`);
`8.54858` N (`x500.urdf:22`). -/
def fmax : ℝ := kf * maxRPM ^ 2

/-- The control period, s: one vehicle line every `STEP_US = 2500` µs (`sim/harness/simulator.py:30`,
`sim/fly_gorge.py:78`), `1 / CTRL_HZ` with `CTRL_HZ = 400` (`sim/harness/simulator.py:29`). The actuator command
(PWM) of a line is held over the period: the environment is stepped `substeps = pyb_hz // 400` times with the same
propeller speeds (`sim/fly_gorge.py:144, 233-234`). -/
def h : ℝ := 1 / 400

/-- The physics substep, s: `1 / pyb_hz` with `--pyb-hz` default `1200` (`sim/fly_gorge.py:101`;
`PYB_TIMESTEP = 1 / PYB_FREQ`, `gpd/envs/BaseAviary.py:83`). PyBullet integrates once per substep, and the motor lag
is applied once per substep (`sim/world/airframes.py:58-68`). -/
def hPhys : ℝ := 1 / 1200

/-- The motor time constant when the commanded thrust is above the current thrust, s: `LAG = (0.0125, 0.025)`,
`sim/world/airframes.py:33` (PX4 gz `timeConstantUp`), chosen by `np.where(cmd > self.lag_thrust, up, down)`
(`airframes.py:65`). -/
def tauUp : ℝ := 0.0125

/-- The motor time constant when the commanded thrust is at or below the current thrust, s: `LAG[1] = 0.025`,
`sim/world/airframes.py:33` (PX4 gz `timeConstantDown`). -/
def tauDown : ℝ := 0.025

/-- Maximum vertical acceleration of the thrust, m/s²: `4 fmax / m = thrust2weight · g`. -/
def amax : ℝ := thrust2weight * grav

/-- Ratio of the drag-torque and thrust coefficients, m: the yaw torque of one propeller is `(km / kf) ·` its
thrust (`BaseAviary._physics`: `torques = rpm² KM`, `forces = rpm² KF`, `gpd/envs/BaseAviary.py:690-691`). -/
def kmkf : ℝ := km / kf

/-- **The maximum thrust identity.** `kf · MAX_RPM² = thrust2weight · m · g / 4`. -/
theorem kf_maxRPM_sq : kf * maxRPM ^ 2 = thrust2weight * grav * mass / 4 := by
  rw [maxRPM, Real.sq_sqrt (by norm_num [thrust2weight, grav, mass, kf])]
  unfold kf; field_simp

/-- The four propellers at full speed give `thrust2weight` times the weight. -/
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
theorem hPhys_pos : 0 < hPhys := by norm_num [hPhys]
theorem grav_pos : 0 < grav := by norm_num [grav]
theorem lever_pos : 0 < lever := by norm_num [lever]
theorem kmkf_pos : 0 < kmkf := by norm_num [kmkf, km, kf]
theorem thrust2weight_pos : 0 < thrust2weight := by norm_num [thrust2weight]
theorem fmax_pos : 0 < fmax := by rw [fmax_eq]; norm_num [thrust2weight, grav, mass]
theorem amax_pos : 0 < amax := by norm_num [amax, thrust2weight, grav]
theorem tauUp_pos : 0 < tauUp := by norm_num [tauUp]
theorem tauDown_pos : 0 < tauDown := by norm_num [tauDown]

/-- The control period is three physics substeps. -/
theorem h_eq_three_hPhys : h = 3 * hPhys := by norm_num [h, hPhys]

/-- The X500 is symmetric in roll and pitch. -/
theorem Jy_eq_Jx : Jy = Jx := by norm_num [Jx, Jy]

/-- Roll (and pitch) has the smallest moment of inertia. -/
theorem Jx_le_Jz : Jx ≤ Jz := by norm_num [Jx, Jz]

/-- Yaw authority per unit inertia is below roll authority: `(km/kf) Jx ≤ lever Jz`. -/
theorem kmkf_Jx_le_lever_Jz : kmkf * Jx ≤ lever * Jz := by norm_num [kmkf, km, kf, Jx, lever, Jz]

/-- The motors can lift the vehicle: the hover thrust fraction `1 / thrust2weight` is at most `1`. -/
theorem one_le_thrust2weight : 1 ≤ thrust2weight := by norm_num [thrust2weight]

/-- The motors spin up faster than they spin down. -/
theorem tauUp_lt_tauDown : tauUp < tauDown := by norm_num [tauUp, tauDown]

theorem tauUp_le_tauDown : tauUp ≤ tauDown := tauUp_lt_tauDown.le

/-- `4 fmax / m = amax`. -/
theorem four_fmax_div_mass : 4 * fmax / mass = amax := by
  rw [fmax_eq, amax]; field_simp [mass_pos.ne']

end

end Plant
