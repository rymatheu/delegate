import px4.modules.px4_rate.Ports

/-! # px4_rate: PX4's multicopter rate controller

PX4's `mc_rate_control` module (src/modules/mc_rate_control, with src/lib/rate_control), real and
unmodified, PX4 v1.17.0. It is started with its own entry point (`mc_rate_control start`) and run
by its work queue whenever `vehicle_angular_velocity` is published, as on the vehicle. The ports
are generated from PX4's .msg files and parameter definitions (Ports.lean, `px4/ports.py`);
what is outside the module (message bus, parameter store, clock, work queue, logging) is the
generic shim in px4/shim. Built by `px4/build.sh px4_rate`.

Contract, from the code (MulticopterRateControl.cpp:136-246, rate_control.cpp:69-118):
* the published torque is finite: each axis is replaced by 0 when not finite (`:205-207`), and the
  battery scaling, when enabled, multiplies by a positive scale and constrains to [-1, 1];
* the integrator, published in rate_ctrl_status, stays within the configured limit
  MC_xR_INT_LIM: every update is constrained to it (rate_control.cpp:111-113), and a non-finite
  update is dropped;
* the setpoints are stamped with the clock and with the gyro sample they answer.
The torque is not clamped to the normalized range [-1, 1] that vehicle_torque_setpoint.msg
describes unless battery scaling is on (`torque_normalized` in `contractAsFirstStated`). -/

namespace Px4.Modules.Px4Rate

open Harness Harness.Contract.Lang

/-- The inputs the code reads in a way a contract has to assume something about: the battery
scale is finite when a battery message arrives (it multiplies the torque). -/
def assumeInputs : List Clause := [
  ⟨"battery_scale_finite", ¬. "battery_status_updated" ∨. finite "battery_status_scale"⟩]

def guarantee : List Clause := [
  ⟨"torque_finite", finite "vehicle_torque_setpoint_xyz_0" ∧. finite "vehicle_torque_setpoint_xyz_1" ∧.
      finite "vehicle_torque_setpoint_xyz_2"⟩,
  ⟨"integrator_bounded", abs "rate_ctrl_status_rollspeed_integ" ≤. "MC_RR_INT_LIM" ∧.
      abs "rate_ctrl_status_pitchspeed_integ" ≤. "MC_PR_INT_LIM" ∧.
      abs "rate_ctrl_status_yawspeed_integ" ≤. "MC_YR_INT_LIM"⟩,
  ⟨"torque_stamped", ¬. "vehicle_torque_setpoint_updated" ∨.
      ("vehicle_torque_setpoint_timestamp" =. "t_us" ∧.
       "vehicle_torque_setpoint_timestamp_sample" =. "vehicle_angular_velocity_timestamp_sample")⟩,
  ⟨"torque_answers_gyro", ¬. "vehicle_torque_setpoint_updated" ∨. "vehicle_angular_velocity_updated"⟩,
  ⟨"no_px4_error", "px4_rate_errors" =. 0⟩]

/-- The first statement: also the normalized range of vehicle_torque_setpoint.msg. -/
def contractAsFirstStated : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs
  guarantee := guarantee ++ [
    ⟨"torque_normalized", abs "vehicle_torque_setpoint_xyz_0" ≤. 1 ∧.
      abs "vehicle_torque_setpoint_xyz_1" ≤. 1 ∧. abs "vehicle_torque_setpoint_xyz_2" ≤. 1⟩]

def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++ assumeInputs
  guarantee := guarantee

/-- In flight: a gyro message every tick, rate control enabled and armed, a rotary-wing vehicle,
the clock advancing one 400 Hz tick (2500 us) per step from 1 s. -/
def flight : Regime where
  name := "flight"
  doc := "armed, rate control on, a gyro message every 400 Hz tick"
  clauses := [
    ⟨"gyro_every_tick", "vehicle_angular_velocity_updated" =. tt⟩,
    ⟨"rates_enabled", ¬. "vehicle_control_mode_updated" ∨.
      ("vehicle_control_mode_flag_control_rates_enabled" ∧. "vehicle_control_mode_flag_armed")⟩,
    ⟨"rotary_wing", ¬. "vehicle_status_updated" ∨. "vehicle_status_vehicle_type" =. 1⟩]
  hints := [.increasing "t_us" 1000000 2400 2600]

/-- PX4's default parameters, flight inputs within 10 rad/s and 100 rad/s², rate setpoints within
4 rad/s. -/
def stockFlight : Regime where
  name := "stock_flight"
  doc := "PX4 defaults, armed in rate control, moderate rates"
  clauses := Ports.paramDefaults ++ flight.clauses ++ [
    ⟨"modest_rates", abs "vehicle_angular_velocity_xyz_0" ≤. 10 ∧. abs "vehicle_angular_velocity_xyz_1" ≤. 10 ∧.
      abs "vehicle_angular_velocity_xyz_2" ≤. 10⟩,
    ⟨"modest_accel", abs "vehicle_angular_velocity_xyz_derivative_0" ≤. 100 ∧.
      abs "vehicle_angular_velocity_xyz_derivative_1" ≤. 100 ∧.
      abs "vehicle_angular_velocity_xyz_derivative_2" ≤. 100⟩,
    ⟨"modest_setpoints", abs "vehicle_rates_setpoint_roll" ≤. 4 ∧. abs "vehicle_rates_setpoint_pitch" ≤. 4 ∧.
      abs "vehicle_rates_setpoint_yaw" ≤. 4⟩]
  hints := flight.hints

def coverage : List Clause := [
  ⟨"torque_published", "vehicle_torque_setpoint_updated" =. tt⟩,
  ⟨"integrator_nonzero", ¬. ("rate_ctrl_status_rollspeed_integ" =. 0)⟩,
  ⟨"torque_beyond_unit", 1 <. abs "vehicle_torque_setpoint_xyz_0"⟩]

def module : Module where
  name := "px4_rate"
  doc := "PX4 mc_rate_control (v1.17.0), unmodified, behind the generic uORB shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_rate/px4_rate"
  stack := .px4
  regimes := [flight, stockFlight]
  coverage := coverage

end Px4.Modules.Px4Rate
