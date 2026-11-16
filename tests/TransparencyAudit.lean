import Vehicle_lib
import Estimator_lib

/-!
The transparency audit of the vehicle translation (README.md "Phase 5: total definitions"). Not a proof and not part of
the translated output: a report of how Lean's environment holds the constants of `Vehicle_lib` and, in a second pass
in the same form, of the estimator World `Estimator_lib` (the value back end's translation the vehicle calls through
`VehicleBridge`).

    cd lean && LEAN_NUM_THREADS=1 lake env lean ../tests/TransparencyAudit.lean     (after `lake build vehicle_replay`)

1. Every constant whose name starts with `Vehicle_lib.`: a definition (`def`, the kernel can unfold it), an opaque
   constant (what `partial def` leaves: the kernel sees no body), an unsafe definition (the implementation of a
   `partial def`), or another kind; the counts, and the opaque ones.
2. For each function of the list `keyFns` (the controller path): its own status, and every opaque constant, unsafe
   definition or axiom its definition reaches through the definitions it uses (theorems are not entered: their values
   are proofs). An empty list means the whole definition unfolds in the kernel down to Lean's own definitions.
3. The same two reports for `Estimator_lib` and the list `estKeyFns` (the EKF3 update, AP_AHRS's update and pre-arm
   check, AP_DAL's frame start, leaf math helpers).
-/

open Lean

namespace TransparencyAudit

/-- The controller path: the per-tick control code, its filters and shared helpers, the mixer, the land detector,
arming, and the scheduler. -/
def keyFns : List String := [
  "AC_AttitudeControl_Multi.rate_controller_run", "AC_AttitudeControl_Multi.rate_controller_run_dt",
  "AC_AttitudeControl_Multi.update_throttle_rpy_mix", "AC_AttitudeControl.attitude_controller_run_quat",
  "AC_AttitudeControl.input_quaternion", "AC_AttitudeControl.input_euler_angle_roll_pitch_euler_rate_yaw_rad",
  "AC_AttitudeControl.input_euler_angle_roll_pitch_yaw_rad", "AC_AttitudeControl.input_thrust_vector_rate_heading_rads",
  "AC_PID.update_all", "AC_PID.update_i", "AC_PID_2D.update_all", "AC_PID_Basic.update_all", "AC_P_1D.update_all",
  "AC_P_2D.update_all", "sqrt_controller", "sqrt_controller'2", "sqrt_controller_accel", "shape_pos_vel_accel",
  "shape_pos_vel_accel_xy", "shape_vel_accel", "shape_vel_accel_xy",
  "AC_PosControl.NE_update_controller", "AC_PosControl.D_update_controller", "AC_PosControl.input_pos_vel_accel_NE_m",
  "AC_PosControl.input_pos_vel_accel_D_m", "AC_PosControl.D_set_pos_target_from_climb_rate_ms",
  "AC_PosControl.update_estimates", "AC_WPNav.update_wpnav", "AC_WPNav.advance_wp_target_along_track",
  "SplineCurve.advance_target_along_track", "SCurve.advance_target_along_track", "AC_Loiter.update",
  "AC_Loiter.calc_desired_velocity", "ModeLoiter.run", "ModeAuto.wp_run", "AP_MotorsMatrix.output_armed_stabilizing",
  "AP_MotorsMatrix.output_to_motors", "AP_MotorsMulticopter.output", "AC_CommandModel.get_rate",
  "AC_CommandModel.get_expo", "LowPassFilter'float.apply", "LowPassFilter'Vector3_float.apply",
  "DerivativeFilter'float_7.update", "SlewLimiter.modifier", "safe_sqrt'float", "constrain_value'short",
  "Copter.update_land_detector", "AP_Arming_Copter.arm", "AP_Scheduler.run", "AP_Scheduler.loop",
  "Copter.run_rate_controller_main", "Copter.motors_output", "AP_Vehicle.loop", "ModeAuto.run",
  -- the flight modes and the mission, mode changes, disarming and the land flag (formerly in recursive components)
  "Copter.update_flight_mode", "ModeLand.run", "ModeRTL.run", "ModeGuided.run", "AP_Mission.update", "Copter.set_mode",
  "Copter.set_mode'rec", "AP_Arming.disarm", "AP_Arming_Copter.disarm", "Copter.set_land_complete",
  -- what the replay driver calls (lean/VehicleReplay.lean): once per main-loop step `AP_Vehicle.loop` (above), then the
  -- IO processes through the `void (void *)` dispatcher; the delay callback, the timer failsafe, the World's drain
  "fnptr'0", "AP_Vehicle.scheduler_delay_callback", "failsafe_check_static", "worldOutputs'drain", "worldOutputs'ctext",
  -- the pure versions (`f.pure'` in `Id`) of shared math helpers
  "safe_sqrt'float.pure'", "sqrt_controller_accel.pure'", "inv_sqrt_controller.pure'", "constrain_value'short.pure'",
  "constrain_value_line'float.pure'", "is_zero.pure'", "wrap_PI'float.pure'", "input_expo.pure'", "stopping_distance.pure'"]

/-- The estimator's path each step and at arming: what the bridge calls (`AP_AHRS.update`, which runs
`NavEKF3.UpdateFilter` and each core's `NavEKF3_core.UpdateFilter`; `AP_AHRS.pre_arm_check`), AP_DAL's frame start, the
EKF's prediction steps, and leaf math helpers. -/
def estKeyFns : List String := [
  "AP_AHRS.update", "AP_AHRS.pre_arm_check", "AP_DAL.start_frame", "NavEKF3.UpdateFilter", "NavEKF3_core.UpdateFilter",
  "NavEKF3_core.UpdateStrapdownEquationsNED", "NavEKF3_core.CovariancePrediction", "AP_Baro.arming_checks",
  "wrap_PI_float", "safe_sqrt_float", "safe_asin_float", "Vector3f.length", "Matrix3f.from_euler",
  "QuaternionT_double.normalize"]

/-- Lean's auxiliary constants of a definition (the unsafe implementation of a `partial def`, `match`/`proof`
auxiliaries, compiler stages), not counted as functions of the translation. -/
def isAux (n : Name) : Bool :=
  match n with
  | .str _ s => s == "_unsafe_rec" || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_cstage" ||
      s.startsWith "_closed" || s.startsWith "_spec" || s.startsWith "_lambda" || s.startsWith "_boxed" ||
      s.startsWith "_redArg" || s.startsWith "eq_" || s.startsWith "_sunfold" || s.startsWith "_private" ||
      s.startsWith "_aux" || s.startsWith "_elambda"
  | _ => true

def status (ci : ConstantInfo) : String :=
  match ci with
  | .defnInfo d => if d.safety == .unsafe then "unsafe def" else if d.safety == .partial then "partial def" else "def"
  | .opaqueInfo _ => "OPAQUE"
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "AXIOM"
  | .inductInfo _ => "inductive"      -- (a structure or enumeration of the translation; with its constructors and
  | .ctorInfo _ => "constructor"      -- recursor; the theorems are Lean's own: `mk.inj`, `sizeOf_spec`, `deriving` proofs)
  | .recInfo _ => "recursor"
  | _ => "other"

/-- The opaque constants, unsafe definitions and axioms reached from `n` through definitions (theorems not entered). -/
def reach (env : Environment) (ns : Name) (n : Name) : Array (Name × String) × Nat := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[n]
  let mut out : Array (Name × String) := #[]
  let mut nVeh := 0
  -- every constant is entered once: at most as many iterations as the environment has constants
  for _ in [0:env.constants.map₁.size + env.constants.map₂.toList.length + 1] do
    match todo.back? with
    | none => break
    | some c =>
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      if ns.isPrefixOf c then nVeh := nVeh + 1
      match env.find? c with
      | some (.defnInfo d) =>
        if d.safety != .safe then out := out.push (c, status (.defnInfo d))
        else
          for u in d.value.getUsedConstants do
            if !seen.contains u then todo := todo.push u
      | some (.opaqueInfo _) => out := out.push (c, "opaque")
      | some (.axiomInfo _) => out := out.push (c, "axiom")
      | _ => pure ()
  return (out, nVeh)

/-- Both reports for the constants under `ns` and the functions `keys` (names relative to `ns`). -/
def audit (ns : Name) (keys : List String) : CoreM Unit := do
  let env ← getEnv
  let mut counts : Std.HashMap String Nat := {}
  let mut opaques : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if ns.isPrefixOf n && !isAux n then
      let s := status ci
      counts := counts.insert s (counts.getD s 0 + 1)
      if s == "OPAQUE" then opaques := opaques.push n
  IO.println s!"constants of {ns} (Lean's auxiliary constants apart): {counts.toList}"
  IO.println s!"opaque ({opaques.size}): {(opaques.qsort (·.toString < ·.toString)).toList}"
  IO.println ""
  let mut clean := 0
  for k in keys do
    let n := ns ++ k.toName
    match env.find? n with
    | none => IO.println s!"{k}: NOT FOUND"
    | some ci =>
      let (bad, nNs) := reach env ns n
      if bad.isEmpty then clean := clean + 1
      IO.println s!"{k}: {status ci}; reaches {nNs} constants of {ns}; opaque/unsafe/axiom reached: {if bad.isEmpty then "none" else toString bad.toList}"
  IO.println s!"key functions: {keys.length}, of which {clean} reach no opaque constant, unsafe definition or axiom"

#eval audit `Vehicle_lib keyFns

#eval show CoreM Unit from do
  IO.println ""
  audit `Estimator_lib estKeyFns

end TransparencyAudit
