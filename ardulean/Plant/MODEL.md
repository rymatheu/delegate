# The plant model: the X500 as simulated

The definitions are `Plant/Model/Constants.lean` and `Plant/Model/Field.lean` (frozen, `MODEL.sha256`). The vehicle is
the Holybro X500 V2 of the gorge flights: gym-pybullet-drones `Physics.PYB` with `../sim/world/x500/x500.urdf`, the motor
lag of `../sim/world/airframes.py`, driven by `sim/fly_gorge.py` (`../sim/gorgesim/`). No wind, drag, ground effect or contact.

## State and equations

`x ∈ ℝ¹⁷`, world NED, body FRD: position `p` (0–2), velocity `v` (3–5), quaternion `q = (q1, q2, q3, q4)` body to
NED, `q1` scalar (6–9), body rates `ω` (10–12), and the **normalized** propeller thrusts `f` (13–16, thrust / `fmax`,
in motor-slot order: 0 front right CCW, 1 rear left CCW, 2 front left CW, 3 rear right CW). Commands `u ∈ ℝ⁴` are held
over the period `h` and clipped, `cᵢ = clip01 uᵢ`. Normalized thrusts put the physical range at `[0, 1]⁴` and keep
`fmax` out of the motor block.

```
ṗ = v
v̇ = g e_z − (T/m) d(q),            T = fmax Σ clip01 fᵢ,  d(q) = (2(q2q4 + q1q3), 2(q3q4 − q1q2), q1² − q2² − q3² + q4²)
q̇ = ½ q ⊗ (0, ω)
ω̇ = J⁻¹ (τ − ω × J ω),             J = diag(Jx, Jy, Jz),  Fᵢ = fmax clip01 fᵢ,
                                   τx = a(−F0 + F1 + F2 − F3),  τy = a(F0 − F1 + F2 − F3),  τz = (km/kf)(F0 + F1 − F2 − F3)
ḟᵢ = (cᵢ − fᵢ) / τ(cᵢ, fᵢ),        τ = tauUp if cᵢ > fᵢ, else tauDown
```
The clip of `f` in the force map is inactive on `[0, 1]⁴`, which the flow keeps (`traj_thrustRange`); it makes the
force and torque bounds hold on every state. The motor rows are `max((c − f)/tauUp, (c − f)/tauDown)`, continuous and
`1/tauUp`-Lipschitz (`lagRate_eq_max`, `abs_lagRate_sub_le`), and their exact flow for a held command is
`c + (f − c) e^{−t/τ(c, f)}` (`lagSol`, `traj_fI`).

## Constants (decimals of the sources, read as exact rationals)

| constant | value | source |
|---|---|---|
| `mass` | 2.0643076923076924 kg | `x500.urdf:47` |
| `Jx`, `Jy`, `Jz` | 0.02166666666666667, 0.02166666666666667, 0.04000000000000001 kg m² | `x500.urdf:48` |
| `lever` | 0.174 m (propeller links at `(±0.174, ±0.174, 0.06)` FLU) | `x500.urdf:72, 84, 96, 108` |
| `armL` | 0.24607315985291853 m (not used by `Physics.PYB`) | `x500.urdf:41` |
| `kf`, `km` | 9.37456697678494e-08 N/rpm², 1.4999307162855904e-09 N m/rpm² (`km/kf = 0.016` m) | `x500.urdf:41` |
| `thrust2weight` | 1.689113625148385 | `x500.urdf:41` |
| `grav` | 9.80665 m/s² (`GRAVITY_MSS`) | `../sim/gorgesim/simulator.py:28, 136` |
| `maxRPM`, `fmax` | `√(t2w g m / (4 kf))` = 9549.30 rpm, `kf maxRPM²` = 8.54858 N | `../sim/gorgesim/simulator.py:137-140` |
| `h` | 1/400 s | `../sim/gorgesim/simulator.py:29-30` (`CTRL_HZ = 400`, `STEP_US = 2500`) |
| `hPhys` | 1/1200 s (`--pyb-hz` 1200, three substeps per period) | `sim/fly_gorge.py` (`--pyb-hz`), `../sim/gorgesim/plant.py` (`substeps`) |
| `tauUp`, `tauDown` | 0.0125 s, 0.025 s | `../sim/world/airframes.py:33` (`LAG`), `:65` (choice) |
| actuator map | `u = (PWM − 1000)/1000` clipped, rpm `= MAX_RPM √u`, so commanded thrust `fmax u` | `../sim/gorgesim/motors.py:32`, `:19-26` |
| slot map | `SLOT_TO_SIM = [0, 2, 3, 1]`, yaw sum `−t0 + t1 − t2 + t3` over sim props | `../sim/gorgesim/motors.py:16`, `gpd/envs/BaseAviary.py:694` |

Derived: `amax = t2w g = 16.5645` m/s², `alphaMax = 2 lever fmax / Jx = 137.303` rad/s², hover thrust and command
`1/t2w = 0.59203`, `gyro = (Jz − Jx)/Jx = 0.84615`. Facts of the numbers used by proofs: `Jy = Jx ≤ Jz`,
`(km/kf) Jx ≤ lever Jz`, `1 ≤ t2w`, `tauUp < tauDown`, `h = 3 hPhys` (`Constants.lean`).

## What the simulator does that the ODE does not

* **Integration.** PyBullet steps the rigid body once per `hPhys = 1/1200` s (semi-implicit, `p.stepSimulation`) with
  the forces and torques held over each substep; the ODE is continuous. The gap is first order in `hPhys`: it halves
  when the physics rate doubles (`tests/plant/numcheck.py`, part (b)).
* **Thrust held per substep, at its end value.** The simulator updates the lagged thrust at the start of each substep
  to its value at the end of the substep (`airframes.py:64-66`) and applies that thrust over the substep, so it leads
  the continuous thrust by about `hPhys/2`. The thrust itself agrees exactly at every substep boundary
  (`step_fI_sim`, three exact lag steps are the flow over `h`); what differs is the force between boundaries.
* **Lag on the thrust, not on the rotor speed.** The simulator lags the thrust `kf rpm²` and derives the speed from it,
  so the drag torque follows the lagged thrust exactly as in the model (`τz` linear in `f`); Gazebo's motor model,
  the source of the time constants, lags the speed instead (`airframes.py:20-22`).
* **Body attitude representation.** PyBullet integrates its own orientation (no quaternion drift term); the model's
  `‖q‖²` is exactly invariant.
* **Not in the simulation either**, hence not modeled: rotor inertia and gyroscopic rotor torque (propeller links
  have zero mass and inertia), rotor drag, ground effect, downwash (coefficients 0, not called by `Physics.PYB`),
  the thrust-point height 0.06 m (no moment for a force along body z). **In the simulation, outside the plant:**
  contact with the ground and the gorge, and the wind runs' aerodynamic force (`../sim/world/wind.py`).
* **Start of the lag.** The simulator's lag starts at the first command or the hover thrust (`airframes.py:61-63`);
  in the model the thrusts are part of the state and start wherever the state says.

Measured gap (`tests/plant/numcheck.py` (b), simulator − ODE, same start and commands): after one period `|Δv| ≤ 3.7e-5` m/s,
`|Δω| ≤ 1.3e-3` rad/s, attitude `≤ 5.2e-6` rad, `|Δp| ≤ 3.3e-6` m; after 8 periods `≤ 2.6e-4` m/s, `6.3e-3` rad/s,
`1.6e-4` rad, `2.6e-5` m; after 40 periods (0.1 s) `≤ 1.4e-3` m/s, `6.9e-3` rad/s, `1.6e-3` rad, `1.2e-4` m; thrusts
agree to `4e-15`; hover is exact.
