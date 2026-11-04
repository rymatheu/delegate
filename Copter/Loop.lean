import Copter.ModeAuto

/-!
# `Copter.loop`: one 400 Hz tick of ArduCopter in Auto, in the order of the fast-task table

Mirrors, at ArduPilot 802db19de1:
- `AP_Scheduler::loop` (`libraries/AP_Scheduler/AP_Scheduler.cpp:348-380`): the loop time
  `_last_loop_time_s`, then `tick()` (`:169-173`), then the tasks;
- the `FAST_TASK` entries of `Copter::scheduler_tasks` (`ArduCopter/Copter.cpp:113-136`), in
  table order:
  1. `AP_InertialSensor::update` (`:115`): publishes the tick's gyro;
  2. `run_rate_controller_main` (`:117`; `Attitude.cpp:10-24`): `set_dt_s` on PosControl and
     AttitudeControl, then (no rate thread, `FSTRATE_ENABLE = 0`) `motors->set_dt_s`,
     `attitude_control->rate_controller_run()`, and `rate_controller_target_reset()`;
  3. `motors_output_main` (`:125`; `motors.cpp:124-129` → `motors_output` `:62-110` →
     `Mode::output_to_motors` `mode.cpp:1017-1020` → `AP_MotorsMulticopter::output`), with
     `air_density_ratio` written first (it is read from `AP::ahrs()` inside `output`);
  4. `read_AHRS` (`:127`; `Copter.cpp:882-886`): the AHRS view of the tick (`Copter.AHRS`);
  5. `read_inertia` (`:132`; `inertia.cpp:4-7`): `pos_control->update_estimates(high_vibes =
     false)`;
  6. `check_ekf_reset` (`:134`; `ekf_check.cpp:248-263`): no yaw or attitude resets occur (the
     reset counts are constant), so it does nothing;
  7. `update_flight_mode` (`:136`; `mode.cpp:502-513`): `landed_gain_reduction(false)` (an exact
     identity in the default configuration, see the header of `AC_AttitudeControl.lean`; not
     called), `set_reset_handling_method` (EKF reset handling is not ported), then
     `flightmode->run()`, i.e. `ModeAuto::run`.
  The remaining fast tasks (`:138-148`: home update, land and crash detectors, rangefinder,
  mount, logging) do not write the cascade's state and are left out, as are the slower tasks
  (`run_nav_updates` at 50 Hz only updates the super-simple bearing; `update_throttle_hover` at
  100 Hz does nothing with `MOT_HOVER_LEARN = 0`).

**The one-tick delay falls out of this order; nothing simulates it.** The rate controller at
tick `t` consumes the body-rate target `_ang_vel_body_rads` that the attitude controller stored at
`t-1`, with the gyro of tick `t`; the motors output at `t` filters the `_throttle_in` that
`D_update_controller` → `set_throttle_out` stored at `t-1`; the navigator, position and attitude
controllers at `t` run on the AHRS of `t` and their outputs act at `t+1`
(`ardupilot-review.md` section 3).

## Harness (not ArduPilot code)

- **Initial condition** (`takeover`, applied by the executable once, with the first sample,
  before the first tick). Every object starts as constructed (`Copter.State.init`); then
  `attitude_control->relax_attitude_controllers()` (`AC_AttitudeControl.cpp:246-271`: attitude
  target = the sample's attitude, rate targets = the last gyro, zero at boot, rate integrators
  zero), as a mode that was holding the current attitude leaves it. With `run.start_hover = 1`
  (the default) the vehicle was also hovering: `attitude_control->set_throttle_out(hover, true,
  POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)` with `hover = motors->get_throttle_hover()` (the call
  every position-controlled mode makes, with the steady-hover value of its argument), and the
  motors' throttle filter output is set to the throttle it stores (the filter's steady state; the
  C++ would get there by filtering, there is no setter). Without this, `D_init_controller`
  initialises the vertical acceleration integrator from the attitude controller's throttle 0
  (`AC_PosControl.cpp:917-919`, a bumpless transfer from the ground) and the copter would start
  at zero throttle.
- **Entering Auto.** On the first tick, before `update_flight_mode`, the harness calls
  `Copter::set_mode(AUTO)` (`mode.cpp:318-486`): `ModeAuto::init` (which fails on an empty
  mission; the harness refuses to start then) and the rate time constants
  `set_roll_pitch_rate_tc(ACRO_RP_RATE_TC)`, `set_yaw_rate_tc(PILOT_Y_RATE_TC)` (`:467-469`).
- **Loop time.** The input gives each tick's period in microseconds; the HAL clock advances by
  it, and `_last_loop_time_s = float(dt_us) * 1.0e-6f` as in `AP_Scheduler.cpp:363`, except on the
  first tick, where the C++ uses `get_loop_period_s() = 1.0f / SCHED_LOOP_RATE` (`:361`) with
  `SCHED_LOOP_RATE = 400` (`AP_Scheduler.cpp:43-44`, Copter default).
-/

namespace Copter

open AP_Math

/-- `SCHED_LOOP_RATE`, Copter default (`AP_Scheduler.cpp:43-44`). -/
def SCHED_LOOP_RATE : ftype := 400.0

/-- `AP_Scheduler::loop` up to the tasks (`AP_Scheduler.cpp:348-377`): loop time and `tick()`. -/
def scheduler_loop (s : State) (dt_us : Nat) : State :=
  let sc := s.scheduler
  let last_loop_time_s : ftype :=
    if sc.ticks32 == 0 then 1.0 / SCHED_LOOP_RATE
    else Float32.ofNat dt_us * 1.0e-6
  { s with scheduler := { ticks32 := sc.ticks32 + 1, micros := sc.micros + dt_us, last_loop_time_s } }

/-- `AP_InertialSensor::update` (`Copter.cpp:115`). -/
def ins_update (s : State) (smp : AHRS.Sample) : State := { s with ins_gyro := smp.gyro }

/-- `Copter::run_rate_controller_main()` (`Attitude.cpp:10-24`). The gyro is
`_ahrs.get_gyro_latest()`, the INS gyro of this tick (read by the AHRS view directly from
`AP::ins()`, `AP_AHRS_View.cpp:79-81`). -/
def run_rate_controller_main (p : Parameters) (s : State) : State :=
  -- set attitude and position controller loop time
  let last_loop_time_s := s.scheduler.last_loop_time_s
  let psc := AC_PosControl.set_dt_s s.pos_control last_loop_time_s
  let att := AC_AttitudeControl_Multi.set_dt_s s.attitude_control last_loop_time_s
  -- not using the rate thread (FSTRATE_ENABLE = 0)
  let motors := AP_MotorsMatrix.set_dt_s s.motors last_loop_time_s
  -- only run the rate controller if we are not using the rate thread
  -- (`_motors.get_throttle_slew_rate()` is 0: not ported, no effect at ATC_THR_G_BOOST = 0)
  let (att, m) := AC_AttitudeControl_Multi.rate_controller_run p.att att motors.toInputs 0.0 s.ins_gyro
  let motors := { motors with toInputs := m }
  -- reset sysid and other temporary inputs
  let att := AC_AttitudeControl_Multi.rate_controller_target_reset att
  { s with pos_control := psc, attitude_control := att, motors := motors }

/-- `Copter::motors_output_main()` (`motors.cpp:124-129`): `motors->output()`. -/
def motors_output_main (p : Parameters) (s : State) : State :=
  let motors := { s.motors with air_density_ratio := p.air_density_ratio }
  let (motors, actuators) := AP_MotorsMatrix.output p.mot motors
  { s with motors, actuators }

/-- `Copter::read_AHRS()` (`Copter.cpp:882-886`). -/
def read_AHRS (s : State) (smp : AHRS.Sample) : State := { s with ahrs := AHRS.update smp }

/-- `Copter::read_inertia()` (`inertia.cpp:4-7`). -/
def read_inertia (s : State) : State :=
  { s with pos_control := AC_PosControl.update_estimates s.pos_control s.ahrs.estimates false }

/-- The harness's initial condition (see the header), from the first sample. -/
def takeover (p : Parameters) (s : State) (smp : AHRS.Sample) : State :=
  let view := AHRS.update smp
  let att := AC_AttitudeControl_Multi.relax_attitude_controllers s.attitude_control view.quat_body_to_ned
  let s := { s with attitude_control := att }
  if !p.start_hover then s
  else
    let hover := AP_Motors.get_throttle_hover s.motors.toInputs
    let (att, m) := AC_AttitudeControl_Multi.set_throttle_out p.att s.attitude_control s.motors.toInputs
      view.cos_pitch view.cos_roll hover true AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ
    let m := { m with _throttle_filter_value := m._throttle_in }
    { s with attitude_control := att, motors := { s.motors with toInputs := m } }

/-- The harness's switch into Auto (see the header); `none` if `ModeAuto::init` fails. -/
def enter_auto (p : Parameters) (s : State) : Option State := do
  let s ← ModeAuto.init p s
  -- set rate shaping time constants (mode.cpp:467-469)
  let att := s.attitude_control
  let att := AC_AttitudeControl_Multi.lift (AC_AttitudeControl.set_roll_pitch_rate_tc · p.ACRO_RP_RATE_TC) att
  let att := AC_AttitudeControl_Multi.set_yaw_rate_tc att p.PILOT_Y_RATE_TC
  pure { s with attitude_control := att, in_auto := true }

/-- `Copter::update_flight_mode()` (`mode.cpp:502-513`) in Auto. -/
def update_flight_mode (p : Parameters) (s : State) : State :=
  ModeAuto.run p s

/-- One tick. Returns the new state; the actuator outputs are `State.actuators`. `none` only if the
switch into Auto fails on the first tick (empty mission). -/
def loop (p : Parameters) (s : State) (smp : AHRS.Sample) : Option State := do
  let s := scheduler_loop s smp.dt_us
  let s := ins_update s smp
  let s := run_rate_controller_main p s
  let s := motors_output_main p s
  let s := read_AHRS s smp
  let s := read_inertia s
  -- check_ekf_reset: no resets (header)
  let s ← if s.in_auto then pure s else enter_auto p s
  pure (update_flight_mode p s)

end Copter
