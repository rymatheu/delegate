# 6. ArduCopter

**Status (2026-11-18):** every stage of this partition is built as a module of real ArduPilot C++: rate (`rate_pid`, three as `rate`), mixer, position, attitude, guidance, loiter, estimator and supervisor; the plant exists as a formal harness and as the module `plant_sim`. They compose by port name into `ap_ctl` (the controllers), `ap_flight` (the controllers in the simulator with test fixtures for estimator and supervisor), `ap_full` and `ap_full_ekf` (the whole stack, flown from a scripted ground station; the latter with the real EKF). With noise on `ap_full_ekf`, GUIDED, AUTO, RTL, ALT_HOLD and LOITER flights end in normal disarms with no guarantee violation and no discharge failure (the position stage takes the supervisor's same-tick `set_throttle_out` for `D_init_controller`, which ALT_HOLD's takeoff needs; the estimator takes `set_terrain_hgt_stable`). AC_Loiter is the stage `loiter` (beside guidance, before position): the attitude controller's command model it calls (`command_model_rate_predictor`) and the position controller's `lean_angles_rad_to_accel_NED_mss` are compiled into it from the real AC_AttitudeControl.cpp and AC_PosControl.cpp (the latter under another class name, ardupilot/modules/loiter/pos_real.cpp), because they return a value within the call. Not in any stage: AC_Circle (CIRCLE does not fly; it would be the same pattern, with no value-returning call into another stage).

## Partition

Not by library: ArduPilot's libraries call each other in one large cycle. The partition follows the data flow of the control cascade, where each stage has a narrow numeric interface per tick.

| Module | ArduPilot code | In → out | How cleanly it cuts | Likely evidence |
|---|---|---|---|---|
| Estimator | sensor front ends, EKF3, AHRS | sensor samples → position, velocity, attitude | well: ArduPilot already isolates it behind a data layer built for log replay | tested and monitored |
| Guidance | flight modes, waypoint navigation, trajectory shaping, mission | mission, estimate → position, velocity, acceleration targets | hard: modes drive the controllers through many different calls | tested; shaping limits may be proved |
| Position control | AC_PosControl | targets, estimate → lean angles, thrust | medium: reads of other singletons become ports | tested; parts proved |
| Attitude control | AC_AttitudeControl | desired and estimated attitude → rate targets | medium | tested; parts proved |
| Rate control | AC_PID, filters | rate targets, gyro → torque commands | well | proved |
| Mixer | AP_Motors | torques, thrust → four motor commands | well | proved |
| Supervisor | arming, mode switching, failsafes, scheduler | events → mode, armed state | hardest: the most entangled code | tested and monitored; logic tables proved |
| Plant | none; the simulator, and equations of motion in Lean | motor commands → state, sensor samples | given | Lean theorems |

Ground-station communication, parameter storage and logging sit outside the loop.

## Order of work

Each step is a feasibility test for the next.

1. **Ports.** Write the architecture in Lean. Instrument the monolithic vehicle to record every proposed port, every tick, in flight.
2. **Replay test per module.** Build a module and replay the recorded inputs; outputs must match bit for bit.
3. **Decomposed loop.** Run all modules under the harness in the simulator and compare with the monolithic vehicle tick by tick.
4. **Contracts and monitors.** State contracts, monitor every flight, start the ledgers.
5. **Leaf evidence.** Proofs for the small numeric modules, test campaigns for the rest.
6. **Composition proof** to the system contract.

A sensible first slice is the inner loop: rate control, mixer and plant.

## Known risks

- **Hidden dependencies.** Components reach for global singletons. Step 2 is designed to find them.
- **The guidance interface.** It has to be designed as a small set of command messages; ArduPilot does not have one.
- **The estimator's contract** carries the sensor-noise term of the system property and will rest on tests and monitoring.
- **Proof tools.** Open model checkers for C++ with exact floating point exist (ESBMC, CBMC) but have not been tried on this code. Float-heavy modules with trigonometry are expected to be out of their reach.
- **Semantics.** A model checker reasons about the source under its own floating-point rules; the build flags must match them, and math-library calls need stated bounds.
