import Vehicle

/-!
# The parameters of the mission world, as an executed check

`MissionWorld` (`Contracts/Mission/Spec.lean`) states, besides `construct courseLines = .ok w`, the
values of the fields that the proofs about the navigator read: the mission's waypoints, the
navigator's parameters, the position controller's position gains and shaping jerk, and the attitude
controller's limits that the navigator reads. Lean's kernel cannot evaluate `construct courseLines`
(`String.splitOn` is well-founded recursion, `Vehicle.parseDecimal` a `while` loop), so these values
are not derived in Lean: `missionParamsOk` compares them bit for bit, and `mission_world_check`
evaluates it on the world built from the embedded course texts. That evaluation is a trusted step
(`MISSION.md`); `Contracts.Mission.missionParams_of_ok` turns the Boolean into the equalities.

No Mathlib, so that the executable can use it.
-/

namespace MissionData

open Vehicle

/-- The mission's waypoints as the navigator stores them (doubles, NED m): the `waypoint` lines of
`copter-cf2x.txt`. -/
def missionWps : Array AC_WPNav_lib.Vector3p.State :=
  #[{ x := 0, y := 0, z := -0.8 }, { x := 1.25, y := 1.25, z := -1.0 }, { x := 0, y := 2.5, z := -1.2 },
    { x := -1.25, y := 1.25, z := -1.4 }, { x := 1.25, y := -1.25, z := -1.6 },
    { x := 0, y := -2.5, z := -1.4 }, { x := -1.25, y := -1.25, z := -1.1 },
    { x := 0, y := 0, z := -0.8 }]

/-- The navigator's parameters: `WP_SPD 1`, `WP_SPD_UP 2.5`, `WP_SPD_DN 1.5`, `WP_RADIUS_M 0.1`,
`WP_ACC 1.5`, `WP_ACC_CNR 0`, `WP_ACC_Z 1`, `WP_JERK 5`, `WP_TER_MARGIN 10`, `WP_RFND_USE 1`. -/
def wppC : AC_WPNav_lib.AC_WPNav.Params :=
  { _wp_speed_ms := 1, _wp_speed_up_ms := 2.5, _wp_speed_down_ms := 1.5, _wp_radius_m := 0.1,
    _wp_accel_mss := 1.5, _wp_accel_c_mss := 0, _wp_accel_z_mss := 1, _wp_jerk_msss := 5,
    _terrain_margin_m := 10, _rangefinder_use := 1 }

/-- Bitwise equality of `float`s. -/
def eq32 (a b : Float32) : Bool := a.toBits == b.toBits

/-- Bitwise equality of `double`s. -/
def eq64 (a b : Float) : Bool := a.toBits == b.toBits

/-- Bitwise equality of the navigator's points. -/
def eqP3 (a b : AC_WPNav_lib.Vector3p.State) : Bool := eq64 a.x b.x && eq64 a.y b.y && eq64 a.z b.z

/-- Bitwise equality of the navigator's parameters. -/
def eqWpp (a b : AC_WPNav_lib.AC_WPNav.Params) : Bool :=
  eq32 a._wp_speed_ms b._wp_speed_ms && eq32 a._wp_speed_up_ms b._wp_speed_up_ms &&
  eq32 a._wp_speed_down_ms b._wp_speed_down_ms && eq32 a._wp_radius_m b._wp_radius_m &&
  eq32 a._wp_accel_mss b._wp_accel_mss && eq32 a._wp_accel_c_mss b._wp_accel_c_mss &&
  eq32 a._wp_accel_z_mss b._wp_accel_z_mss && eq32 a._wp_jerk_msss b._wp_jerk_msss &&
  eq32 a._terrain_margin_m b._terrain_margin_m && a._rangefinder_use == b._rangefinder_use

/-- **The parameters of the mission world**, bit for bit: the eight waypoints, the navigator's
parameters (`wppC`), `PSC_NE_POS_P 1.5`, `PSC_D_POS_P 1`, `PSC_NE_JERK 5`, `ATC_RATE_R_MAX 0`,
`ATC_RATE_P_MAX 0`, `ATC_ACC_R_MAX 1800`, `ATC_ACC_P_MAX 1800`, `ATC_INPUT_TC 0.05`. -/
def missionParamsOk (w : World) : Bool :=
  w.mission.size == 8 &&
  eqP3 w.mission[0]! missionWps[0]! && eqP3 w.mission[1]! missionWps[1]! &&
  eqP3 w.mission[2]! missionWps[2]! && eqP3 w.mission[3]! missionWps[3]! &&
  eqP3 w.mission[4]! missionWps[4]! && eqP3 w.mission[5]! missionWps[5]! &&
  eqP3 w.mission[6]! missionWps[6]! && eqP3 w.mission[7]! missionWps[7]! &&
  eqWpp w.wpp wppC &&
  eq32 w.pp._p_pos_ne_m._kp 1.5 && eq32 w.pp._p_pos_d_m._kp 1 &&
  eq32 w.pp._shaping_jerk_ne_msss 5 &&
  eq32 w.ap._ang_vel_roll_max_degs 0 && eq32 w.ap._ang_vel_pitch_max_degs 0 &&
  eq32 w.ap._accel_roll_max_degss 1800 && eq32 w.ap._accel_pitch_max_degss 1800 &&
  eq32 w.ap._input_tc 0.05

end MissionData
