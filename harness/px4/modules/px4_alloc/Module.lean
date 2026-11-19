import px4.modules.px4_alloc.Ports

/-! # px4_alloc: PX4's control allocator

PX4's `control_allocator` module (src/modules/control_allocator, with
src/lib/control_allocation and the effectiveness classes of every airframe), real and unmodified,
PX4 v1.17.0, run by its work queue whenever `vehicle_torque_setpoint` is published. Same generic
shim and generator as px4_rate; what is specific to this module is px4/modules/px4_alloc/px4.txt (its
sources, include directories, parameter sources and topics) and this file.

Contract, from the code (ControlAllocator.cpp:650-700, ControlAllocation.cpp clipActuatorSetpoint):
every motor value is either NaN (no motor, a stopped motor, or a non-finite setpoint: "NaN maps to
disarmed", ActuatorMotors.msg) or within the documented range [-1, 1] of ActuatorMotors.msg; with
no reversible motor configured (CA_R_REV = 0) a finite motor value is at least 0 (rotor minimum 0,
ActuatorEffectivenessRotors). Motors are published only after a torque setpoint (the trigger)
and stamped with the torque setpoint's sample time. -/

namespace Px4.Modules.Px4Alloc

open Harness Harness.Contract.Lang

private def motor (i : Nat) : String := s!"actuator_motors_control_{i}"

/-- `x` is NaN or within [lo, hi] (NaN is the only value for which `x = x` fails). -/
private def nanOr (x : String) (lo hi : Expr) : Expr := ¬. (Expr.var x =. Expr.var x) ∨. (lo ≤. x ∧. x ≤. hi)

private def allMotors (f : Nat → Expr) : Expr :=
  (List.range 11).foldl (fun e i => e ∧. f (i + 1)) (f 0)

def guarantee : List Clause := [
  ⟨"motors_in_documented_range", allMotors fun i => nanOr (motor i) (-1) 1⟩,
  ⟨"motors_nonnegative_unless_reversible", ¬. ("CA_R_REV" =. 0) ∨. allMotors fun i => nanOr (motor i) 0 1⟩,
  ⟨"motors_answer_torque", ¬. "actuator_motors_updated" ∨. "vehicle_torque_setpoint_updated"⟩,
  ⟨"motors_stamped", ¬. "actuator_motors_updated" ∨.
      ("actuator_motors_timestamp" =. "t_us" ∧.
       "actuator_motors_timestamp_sample" =. "vehicle_torque_setpoint_timestamp_sample")⟩,
  ⟨"no_px4_error", "px4_alloc_errors" =. 0⟩]

/-- The first statement. Its campaigns refuted `no_px4_error` at the first step of every case
drawn with CA_AIRFRAME = 6 (px4_alloc alone, seeds 1 and 2, 200 x 100) or 15 (px4_inner, seed 1):
* 6, "Rover (Differential)": ControlAllocator::update_effectiveness_source leaves the
  effectiveness empty on purpose (ControlAllocator.cpp:236-238: the rover module allocates), and
  then logs "Actuator effectiveness init failed" and publishes nothing;
* 15: module.yaml documents 13 "Rover (Mecanum)", 14 "Spacecraft 2D", 15 "Spacecraft 3D", but the
  enum EffectivenessSource (ControlAllocator.hpp:148-163) has 13 SPACECRAFT_2D, 14 SPACECRAFT_3D and
  no 15, so 15 is "Unknown airframe" and 13 and 14 select the next airframe of the documented one.
A second round (seeds 11-13, and px4_inner seed 4) refuted it with "Too many actuators"
(ControlAllocator.cpp:493-496): the documented ranges allow 12 rotors, 8 control surfaces and 4
tilt servos, more than the allocator's 16 actuators (NUM_ACTUATORS), and the allocator then drops
the excess; a third (seeds 21-23) with "Too many servos": 8 control surfaces and 4 tilts exceed
the 8 servo outputs of actuator_servos (ControlAllocator.cpp:519). Kept for the record. -/
def contractAsFirstStated : Contract where
  assume := Ports.widths ++ Ports.paramRanges
  guarantee := guarantee

/-- The contract: the airframe is one the allocator itself allocates for. -/
def contract : Contract where
  assume := Ports.widths ++ Ports.paramRanges ++
    [⟨"airframe_allocated_here", ¬. ("CA_AIRFRAME" =. 6) ∧. ¬. ("CA_AIRFRAME" =. 15)⟩,
     ⟨"actuators_fit", "CA_ROTOR_COUNT" + "CA_SV_CS_COUNT" + "CA_SV_TL_COUNT" ≤. 16 ∧.
        "CA_SV_CS_COUNT" + "CA_SV_TL_COUNT" ≤. 8⟩]
  guarantee := guarantee

/-- The X500 airframe as PX4 configures it in SITL (ROMFS/px4fmu_common/init.d-posix/airframes/
4001_gz_x500): multirotor, four rotors, rotor 0 front right and 1 rear left turning CCW
(KM 0.05), 2 front left and 3 rear right CW (KM -0.05). -/
def x500Airframe : List Clause := [
  ⟨"x500_frame", "CA_AIRFRAME" =. 0 ∧. "CA_ROTOR_COUNT" =. 4⟩,
  ⟨"x500_rotor0", "CA_ROTOR0_PX" =. 0.13 ∧. "CA_ROTOR0_PY" =. 0.22 ∧. "CA_ROTOR0_KM" =. 0.05⟩,
  ⟨"x500_rotor1", "CA_ROTOR1_PX" =. -0.13 ∧. "CA_ROTOR1_PY" =. -0.20 ∧. "CA_ROTOR1_KM" =. 0.05⟩,
  ⟨"x500_rotor2", "CA_ROTOR2_PX" =. 0.13 ∧. "CA_ROTOR2_PY" =. -0.22 ∧. "CA_ROTOR2_KM" =. -0.05⟩,
  ⟨"x500_rotor3", "CA_ROTOR3_PX" =. -0.13 ∧. "CA_ROTOR3_PY" =. 0.20 ∧. "CA_ROTOR3_KM" =. -0.05⟩]

/-- The parameters the airframe file sets; the others keep PX4's defaults. -/
def x500Names : List String :=
  ["CA_AIRFRAME", "CA_ROTOR_COUNT"] ++ (List.range 4).flatMap fun i =>
    [s!"CA_ROTOR{i}_PX", s!"CA_ROTOR{i}_PY", s!"CA_ROTOR{i}_KM"]

def x500Params : List Clause :=
  (Ports.paramDefaults.filter fun c => !x500Names.any (fun n => c.name == s!"default_{n}")) ++ x500Airframe

/-- Flight: a torque and thrust setpoint every 400 Hz tick, allocation enabled, armed rotary wing. -/
def flight : Regime where
  name := "flight"
  doc := "a torque and thrust setpoint every 400 Hz tick, allocation enabled"
  clauses := [
    ⟨"setpoints_every_tick", "vehicle_torque_setpoint_updated" ∧. "vehicle_thrust_setpoint_updated"⟩,
    ⟨"allocation_enabled", ¬. "vehicle_control_mode_updated" ∨. "vehicle_control_mode_flag_control_allocation_enabled"⟩,
    ⟨"armed_rotary_wing", ¬. "vehicle_status_updated" ∨.
      ("vehicle_status_vehicle_type" =. 1 ∧. "vehicle_status_arming_state" =. 2)⟩]
  hints := [.increasing "t_us" 1000000 2400 2600]

/-- The X500 in flight, with setpoints as the rate controller produces them: torque within
[-1, 1], thrust along -z within [0, 1]. -/
def x500Flight : Regime where
  name := "x500_flight"
  doc := "the X500 airframe, PX4 defaults otherwise, normalized setpoints at 400 Hz"
  clauses := x500Params ++ flight.clauses ++ [
    ⟨"normalized_torque", abs "vehicle_torque_setpoint_xyz_0" ≤. 1 ∧. abs "vehicle_torque_setpoint_xyz_1" ≤. 1 ∧.
      abs "vehicle_torque_setpoint_xyz_2" ≤. 1⟩,
    ⟨"vertical_thrust", "vehicle_thrust_setpoint_xyz_0" =. 0 ∧. "vehicle_thrust_setpoint_xyz_1" =. 0 ∧.
      -1 ≤. "vehicle_thrust_setpoint_xyz_2" ∧. "vehicle_thrust_setpoint_xyz_2" ≤. 0⟩]
  hints := flight.hints

def coverage : List Clause := [
  ⟨"motors_published", "actuator_motors_updated" =. tt⟩,
  ⟨"four_motors_finite", finite (motor 0) ∧. finite (motor 1) ∧. finite (motor 2) ∧. finite (motor 3)⟩,
  ⟨"a_motor_saturated", motor 0 =. 1 ∨. motor 1 =. 1 ∨. motor 2 =. 1 ∨. motor 3 =. 1⟩,
  ⟨"torque_not_achieved", "control_allocator_status_updated" ∧. ¬. "control_allocator_status_torque_setpoint_achieved"⟩]

def module : Module where
  name := "px4_alloc"
  doc := "PX4 control_allocator (v1.17.0), unmodified, behind the generic uORB shim"
  params := Ports.params
  input := Ports.input
  output := Ports.output
  contract := { contract with guarantee := contract.guarantee ++ Ports.outWidths }
  exe := "build/modules/px4_alloc/px4_alloc"
  stack := .px4
  regimes := [flight, x500Flight]
  coverage := coverage

end Px4.Modules.Px4Alloc
