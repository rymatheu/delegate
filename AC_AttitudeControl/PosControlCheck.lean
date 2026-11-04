import AC_AttitudeControl.AC_PosControl

/-!
# Spot check for the `AC_PosControl` port

Steps the position controller from hover with a 1 m north setpoint and prints the lean-angle
targets and the throttle that `D_update_controller` hands to `set_throttle_out`. The estimates are
held fixed (the vehicle does not move: no plant), so the output is the controller's response to a
constant 1 m error. Setup follows `ModeAuto::wp_start` → `AC_WPNav::wp_and_spline_init`
(`AC_WPNav.cpp:223-235`) with the default `WPNAV_SPD = 10`, `WPNAV_ACC = 2.5`, `WPNAV_SPD_UP = 2.5`,
`WPNAV_SPD_DN = 1.5`, `WPNAV_ACC_Z = 1`, then each tick does what `AC_WPNav::update_wpnav` and
`ModeAuto::wp_run` do with the position controller: `set_pos_vel_accel_NED_m`, then
`NE_update_controller`, then `D_update_controller` (WPNav's S-curve is replaced by the constant
setpoint). Run with `lake env lean --run AC_AttitudeControl/PosControlCheck.lean` after
`lake build AC_AttitudeControl`. Not imported by `AC_AttitudeControl.lean`.
-/

open AP_Math AC_PosControl

namespace AC_PosControl.Check

def hex (width : Nat) (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "0x" ++ String.ofList (List.replicate (width - s.length) '0') ++ s

def f (x : Float32) : String := s!"{x} [{hex 8 x.toBits.toNat}]"

/-- 400 Hz. -/
def dt : ftype := 0.0025

/-- Hover at 10 m above the EKF origin, level, yaw north. -/
def est : AHRSEstimates :=
  { relative_position_NED_origin := ⟨0.0, 0.0, -10.0⟩, relative_position_NED_origin_ok := true,
    relative_position_D_origin_float := none,
    velocity_NED := {}, velocity_NED_ok := true, vert_pos_rate_D := some 0.0 }

def ahrs : AHRSInputs :=
  { cos_yaw := 1.0, sin_yaw := 0.0, yaw := 0.0, get_accel_ef := ⟨0.0, 0.0, -GRAVITY_MSS⟩ }

/-- `MOT_THST_HOVER = 0.35` (the default), no saturation. -/
def motors : AP_Motors.Inputs := {}

/-- Level attitude target; `ANGLE_MAX = 30` deg, `ATC_RATE_R_MAX = ATC_RATE_P_MAX = 0`,
`ATC_ACCEL_R_MAX = ATC_ACCEL_P_MAX = 1100` deg/s/s, `ATC_RATE_FF_ENAB = 1`; throttle at hover. -/
def att : AttitudeControlInputs :=
  { get_att_target_euler_rad := {}, get_althold_lean_angle_max_rad := radians 30.0,
    lean_angle_max_rad := radians 30.0, get_throttle_in := 0.35,
    get_ang_vel_roll_max_rads := radians 0.0, get_ang_vel_pitch_max_rads := radians 0.0,
    get_accel_roll_max_radss := radians 1100.0, get_accel_pitch_max_radss := radians 1100.0,
    get_bf_feedforward := true }

def clockAt (tick : Nat) : Clock :=
  { ticks32 := UInt32.ofNat tick, millis := UInt32.ofNat (tick * 5 / 2) }

end AC_PosControl.Check

open AC_PosControl.Check in
def main : IO Unit := do
  let p := AC_PosControl.defaults
  let t0 := 1000
  -- wp_and_spline_init
  let mut s := AC_PosControl.init p
  s := set_dt_s s dt
  s := update_estimates s est
  s := NE_set_max_speed_accel_m p s att 10.0 2.5
  s := NE_set_correction_speed_accel_m p s 10.0 2.5
  s := D_set_max_speed_accel_m p s 1.5 2.5 1.0
  s := D_set_correction_speed_accel_m p s 1.5 2.5 1.0
  if !NE_is_active s (clockAt t0) then
    s := NE_init_controller p s ahrs att (clockAt t0)
  if !D_is_active s (clockAt t0) then
    s := D_init_controller p s ahrs motors att (clockAt t0)
  IO.println s!"jerk_max_ne {f s._jerk_max_ne_msss}  jerk_max_d {f s._jerk_max_d_msss}"
  IO.println s!"p_pos_ne error_max {f (NE_get_pos_error_max_m s)}"
  -- 1 m north of the current position, same altitude
  let target : Vector3p := ⟨1.0, 0.0, -10.0⟩
  for k in [1:9] do
    let clock := clockAt (t0 + k)
    s := update_estimates s est
    s := set_pos_vel_accel_NED_m s target {} {}
    s := NE_update_controller p s ahrs att clock
    let (s', thr) := D_update_controller p s ahrs motors att clock
    s := s'
    IO.println s!"tick {k}: roll {f (get_roll_rad s)} pitch {f (get_pitch_rad s)} yaw {f (get_yaw_rad s)}"
    IO.println s!"        accel_target_N {f s._accel_target_ned_mss.x} vel_target_N {f s._vel_target_ned_ms.x} thrust_vector_z {f (get_thrust_vector s).z}"
    IO.println s!"        set_throttle_out({f thr.throttle_in}, {thr.apply_angle_boost}, {f thr.filt_cutoff})"
