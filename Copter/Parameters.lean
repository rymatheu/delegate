import AC_WPNav
import AC_AttitudeControl
import AP_Motors
import Copter.Text

/-!
# `Copter.Parameters`: every parameter record of the stack, and the run overrides

The parameters the ported cascade reads, grouped as in ArduCopter's parameter tree
(`ArduCopter/Parameters.cpp` at 802db19de1): `ATC_` (`attitude_control`, `:384`), `PSC`
(`pos_control`, `:388`), `WP_` (`wp_nav`, `:370`), `MOT_` (`motors`, `:460`), and the vehicle
scalars `WP_YAW_BEHAVIOR` (`:123`), `PILOT_Y_RATE_TC` (`command_model_pilot_y`, `:970`, default
rate time constant `0.0f` at `:1249`) and `ACRO_RP_RATE_TC` (`command_model_acro_rp`, `:1242`).
The defaults are the code defaults of each library record, except for the run overrides below.

## Run overrides (deviations from the code defaults), one comment per deviation in `defaults`

- `MOT_HOVER_LEARN 0` (code default 2, `AP_MotorsMulticopter.cpp:163`): hover learning off, so the
  100 Hz `Copter::update_throttle_hover` task (`Copter.cpp:177`, `Attitude.cpp:31-66`) is a no-op
  and the per-tick loop is one rate (PORT.md).
- `MOT_THST_HOVER 0.39` (code default 0.35): the hover throttle is a run parameter (learning is
  off); 0.39 is SITL's `Tools/autotest/default_params/copter.parm:71`.
- `MOT_BAT_VOLT_MAX 0`: this is the code default, kept on purpose although SITL's `copter.parm:73`
  sets 12.8 (with `MOT_BAT_VOLT_MIN 9.6`, `:72`): the port has no battery-voltage compensation
  (`AP_Motors_Thrust_Linearization.lean`, `Faithful`), so an oracle run must set it to 0 too.
  `MOT_BAT_VOLT_MIN` keeps its code default 0; it is not read while `MOT_BAT_VOLT_MAX ≤ 0`.
- `ATC_RAT_YAW_P 0.3`, `ATC_RAT_YAW_I 0.02` (code defaults 0.18, 0.018,
  `AC_AttitudeControl_Multi.h:26-27`): SITL's `copter.parm:5-6`, applied so the port and a SITL
  oracle with its default parameter file agree.
- `MOT_THST_EXPO 0.65` in `copter.parm:70` equals the code default; nothing to apply.
- The other `copter.parm` lines (RC, compass, INS calibration, fence, flight modes, battery
  monitor, `FRAME_CLASS 1`/`FRAME_TYPE 0` = quad X, which the port hard-wires) do not reach the
  ported code.

Two values are not ArduPilot parameters and are named in lower case:
- `run.air_density_ratio` (default 1): `AP::ahrs().get_air_density_ratio()`, which
  `Thrust_Linearization::get_compensation_gain` divides by. SITL derives it from the barometer
  (about 0.94 at the default home altitude), so a bit-for-bit comparison must pass the oracle's
  value.
- `run.start_hover` (default 1): the harness's initial condition, see `Copter.takeover` in
  `Copter/Loop.lean` (1: the vehicle was hovering at `MOT_THST_HOVER` in a mode that held the
  current attitude; 0: every object as constructed at boot, throttle 0).
- the mission (`waypoint N E D` lines in a parameter file).

## Names

Keys are the ArduPilot parameter names at this commit, including the `AC_PID`/`AC_P` subgroup
suffixes (`ATC_RAT_RLL_P`, `ATC_RAT_RLL_FLTD`, `ATC_ANG_PIT_P`, ...). The pre-4.7 `WPNAV_` names
are accepted as aliases, converted as `AC_WPNav::convert_parameters` does
(`AC_WPNav.cpp:117-162`, Copter table `:151-160`): `WPNAV_SPEED`, `WPNAV_RADIUS`,
`WPNAV_SPEED_UP`, `WPNAV_SPEED_DN`, `WPNAV_ACCEL`, `WPNAV_ACCEL_Z`, `WPNAV_ACCEL_C` were in cm,
cm/s, cm/s² and are multiplied by `0.01f`; `WPNAV_JERK`, `WPNAV_TER_MARGIN`, `WPNAV_RFND_USE`
map unchanged to `WP_JERK`, `WP_TER_MARGIN`, `WP_RFND_USE`.

Setting `MOT_BAT_VOLT_MAX > 0`, `MOT_BAT_CURR_MAX > 0`, a nonzero `*_SMAX`, `*_NTF` or `*_NEF`
leaves the `Faithful` configurations of the ported libraries: the code then no longer equals the
C++ (those paths are not ported). The parser accepts them; `--print-params` shows them.
-/

namespace Copter

open AP_Math

/-- The parameter records of the stack. -/
structure Parameters where
  /-- `ATC_`: `AC_AttitudeControl_Multi` (with the base class). -/
  att : AC_AttitudeControl_Multi.Params
  /-- `PSC`: `AC_PosControl`. -/
  psc : AC_PosControl.Params
  /-- `WP_`: `AC_WPNav`. -/
  wpnav : AC_WPNav.Params
  /-- `MOT_`: `AP_MotorsMulticopter` / `AP_MotorsMatrix`. -/
  mot : AP_MotorsMulticopter.Params
  /-- `WP_YAW_BEHAVIOR` (`Parameters.cpp:123`, default `LOOK_AT_NEXT_WP_EXCEPT_RTL = 2`,
  `config.h:468-469`). -/
  WP_YAW_BEHAVIOR : Int8 := 2
  /-- `PILOT_Y_RATE_TC` (`command_model_pilot_y` rate time constant, default 0). -/
  PILOT_Y_RATE_TC : ftype := 0.0
  /-- `ACRO_RP_RATE_TC` (`command_model_acro_rp` rate time constant, default 0). -/
  ACRO_RP_RATE_TC : ftype := 0.0
  /-- Not a parameter: `AP::ahrs().get_air_density_ratio()` (header). -/
  air_density_ratio : ftype := 1.0
  /-- Not a parameter: start from a steady hover (`Copter.takeover`, header). -/
  start_hover : Bool := true
  /-- Not a parameter: the mission, NED positions in m from the EKF origin. -/
  mission : List Vector3p := []

/-- `WPYawBehavior` (`Copter.h`): `NONE = 0`, `LOOK_AT_NEXT_WP = 1`, `LOOK_AT_NEXT_WP_EXCEPT_RTL =
2`, `LOOK_AHEAD = 3`. -/
def WP_YAW_BEHAVIOR_NONE : Int8 := 0
def WP_YAW_BEHAVIOR_LOOK_AT_NEXT_WP : Int8 := 1
def WP_YAW_BEHAVIOR_LOOK_AT_NEXT_WP_EXCEPT_RTL : Int8 := 2
def WP_YAW_BEHAVIOR_LOOK_AHEAD : Int8 := 3

/-- The built-in mission: climb to 5 m above the origin, fly 10 m north, then 10 m east (the
mission of `Flight/Main.lean`, without its yaw column). -/
def defaultMission : List Vector3p := [⟨0, 0, -5⟩, ⟨10, 0, -5⟩, ⟨10, 10, -5⟩]

/-- Code defaults with the run overrides of the header. -/
def defaults : Parameters :=
  let att : AC_AttitudeControl_Multi.Params := {}
  { att := { att with
      -- deviation: SITL copter.parm:5-6 (code defaults 0.18, 0.018)
      ATC_RAT_YAW := { att.ATC_RAT_YAW with P := 0.3, I := 0.02 } }
    psc := AC_PosControl.defaults
    wpnav := {}
    mot := {
      -- deviation: hover learning off (code default 2, HOVER_LEARN_AND_SAVE)
      MOT_HOVER_LEARN := 0
      -- deviation: run parameter, SITL copter.parm:71 (code default 0.35)
      MOT_THST_HOVER := 0.39
      -- MOT_BAT_VOLT_MAX stays at its code default 0 (SITL copter.parm:73 sets 12.8, header)
      MOT_BAT_VOLT_MAX := 0.0 }
    mission := defaultMission }

/-! ### The parameter table -/

open Copter.Text

/-- One named parameter: how to print it and how to set it from a decimal. -/
structure Entry where
  name : String
  get : Parameters → String
  set : Parameters → Decimal → Option Parameters

/-- A `float` parameter. -/
def fEntry (name : String) (get : Parameters → ftype) (set : Parameters → ftype → Parameters) : Entry :=
  { name, get := fun q => exactDecimal32 (get q), set := fun q d => some (set q d.toFloat32) }

/-- An `AP_Int8` parameter. -/
def i8Entry (name : String) (get : Parameters → Int8) (set : Parameters → Int8 → Parameters) : Entry :=
  { name, get := fun q => toString (get q).toInt,
    set := fun q d => d.toInt?.bind fun n =>
      if -128 ≤ n && n ≤ 127 then some (set q (Int8.ofInt n)) else none }

/-- An `AP_Int16` parameter. -/
def i16Entry (name : String) (get : Parameters → Int16) (set : Parameters → Int16 → Parameters) : Entry :=
  { name, get := fun q => toString (get q).toInt,
    set := fun q d => d.toInt?.bind fun n =>
      if -32768 ≤ n && n ≤ 32767 then some (set q (Int16.ofInt n)) else none }

/-- The `AC_PID` subgroup `pre` (`AC_PID.cpp:9-100`: `P`, `I`, `D`, `FF`, `IMAX`, `FLTT`, `FLTE`,
`FLTD`, `SMAX`, `PDMX`, `D_FF`, `NTF`, `NEF`). -/
def pidEntries (pre : String) (get : Parameters → AC_PID.Params)
    (set : Parameters → AC_PID.Params → Parameters) : List Entry :=
  [ fEntry (pre ++ "P") (fun q => (get q).P) (fun q v => set q { get q with P := v }),
    fEntry (pre ++ "I") (fun q => (get q).I) (fun q v => set q { get q with I := v }),
    fEntry (pre ++ "D") (fun q => (get q).D) (fun q v => set q { get q with D := v }),
    fEntry (pre ++ "FF") (fun q => (get q).FF) (fun q v => set q { get q with FF := v }),
    fEntry (pre ++ "IMAX") (fun q => (get q).IMAX) (fun q v => set q { get q with IMAX := v }),
    fEntry (pre ++ "FLTT") (fun q => (get q).FLTT) (fun q v => set q { get q with FLTT := v }),
    fEntry (pre ++ "FLTE") (fun q => (get q).FLTE) (fun q v => set q { get q with FLTE := v }),
    fEntry (pre ++ "FLTD") (fun q => (get q).FLTD) (fun q v => set q { get q with FLTD := v }),
    fEntry (pre ++ "SMAX") (fun q => (get q).SMAX) (fun q v => set q { get q with SMAX := v }),
    fEntry (pre ++ "PDMX") (fun q => (get q).PDMX) (fun q v => set q { get q with PDMX := v }),
    fEntry (pre ++ "D_FF") (fun q => (get q).D_FF) (fun q v => set q { get q with D_FF := v }),
    i8Entry (pre ++ "NTF") (fun q => (get q).NTF) (fun q v => set q { get q with NTF := v }),
    i8Entry (pre ++ "NEF") (fun q => (get q).NEF) (fun q v => set q { get q with NEF := v }) ]

/-- `ATC_` (`AC_AttitudeControl.cpp:32-206`, `AC_AttitudeControl_Multi.cpp:8-335`). -/
def attEntries : List Entry :=
  let A (name : String) (get : AC_AttitudeControl_Multi.Params → ftype)
      (set : AC_AttitudeControl_Multi.Params → ftype → AC_AttitudeControl_Multi.Params) :=
    fEntry name (fun q => get q.att) (fun q v => { q with att := set q.att v })
  [ i8Entry "ATC_RATE_FF_ENAB" (·.att.ATC_RATE_FF_ENAB) (fun q v => { q with att := { q.att with ATC_RATE_FF_ENAB := v } }),
    i8Entry "ATC_ANGLE_BOOST" (·.att.ATC_ANGLE_BOOST) (fun q v => { q with att := { q.att with ATC_ANGLE_BOOST := v } }),
    A "ATC_ANG_RLL_P" (·.ATC_ANG_RLL.P) (fun a v => { a with ATC_ANG_RLL := { P := v } }),
    A "ATC_ANG_PIT_P" (·.ATC_ANG_PIT.P) (fun a v => { a with ATC_ANG_PIT := { P := v } }),
    A "ATC_ANG_YAW_P" (·.ATC_ANG_YAW.P) (fun a v => { a with ATC_ANG_YAW := { P := v } }),
    A "ATC_ANG_LIM_TC" (·.ATC_ANG_LIM_TC) (fun a v => { a with ATC_ANG_LIM_TC := v }),
    A "ATC_RATE_R_MAX" (·.ATC_RATE_R_MAX) (fun a v => { a with ATC_RATE_R_MAX := v }),
    A "ATC_RATE_P_MAX" (·.ATC_RATE_P_MAX) (fun a v => { a with ATC_RATE_P_MAX := v }),
    A "ATC_RATE_Y_MAX" (·.ATC_RATE_Y_MAX) (fun a v => { a with ATC_RATE_Y_MAX := v }),
    A "ATC_INPUT_TC" (·.ATC_INPUT_TC) (fun a v => { a with ATC_INPUT_TC := v }),
    A "ATC_ANGLE_MAX" (·.ATC_ANGLE_MAX) (fun a v => { a with ATC_ANGLE_MAX := v }),
    A "ATC_RATE_WPY_MAX" (·.ATC_RATE_WPY_MAX) (fun a v => { a with ATC_RATE_WPY_MAX := v }),
    A "ATC_ACC_Y_MAX" (·.ATC_ACC_Y_MAX) (fun a v => { a with ATC_ACC_Y_MAX := v }),
    A "ATC_ACC_R_MAX" (·.ATC_ACC_R_MAX) (fun a v => { a with ATC_ACC_R_MAX := v }),
    A "ATC_ACC_P_MAX" (·.ATC_ACC_P_MAX) (fun a v => { a with ATC_ACC_P_MAX := v }) ] ++
  pidEntries "ATC_RAT_RLL_" (·.att.ATC_RAT_RLL) (fun q v => { q with att := { q.att with ATC_RAT_RLL := v } }) ++
  pidEntries "ATC_RAT_PIT_" (·.att.ATC_RAT_PIT) (fun q v => { q with att := { q.att with ATC_RAT_PIT := v } }) ++
  pidEntries "ATC_RAT_YAW_" (·.att.ATC_RAT_YAW) (fun q v => { q with att := { q.att with ATC_RAT_YAW := v } }) ++
  [ A "ATC_THR_MIX_MIN" (·.ATC_THR_MIX_MIN) (fun a v => { a with ATC_THR_MIX_MIN := v }),
    A "ATC_THR_MIX_MAX" (·.ATC_THR_MIX_MAX) (fun a v => { a with ATC_THR_MIX_MAX := v }),
    A "ATC_THR_MIX_MAN" (·.ATC_THR_MIX_MAN) (fun a v => { a with ATC_THR_MIX_MAN := v }),
    A "ATC_THR_G_BOOST" (·.ATC_THR_G_BOOST) (fun a v => { a with ATC_THR_G_BOOST := v }) ]

/-- `PSC` (`AC_PosControl.cpp:91-347`). -/
def pscEntries : List Entry :=
  let P (name : String) (get : AC_PosControl.Params → ftype)
      (set : AC_PosControl.Params → ftype → AC_PosControl.Params) :=
    fEntry name (fun q => get q.psc) (fun q v => { q with psc := set q.psc v })
  [ P "PSC_D_POS_P" (·.PSC_D_POS_P) (fun a v => { a with PSC_D_POS_P := v }),
    P "PSC_NE_POS_P" (·.PSC_NE_POS_P) (fun a v => { a with PSC_NE_POS_P := v }),
    P "PSC_ANGLE_MAX" (·.PSC_ANGLE_MAX) (fun a v => { a with PSC_ANGLE_MAX := v }),
    P "PSC_NE_JERK" (·.PSC_NE_JERK) (fun a v => { a with PSC_NE_JERK := v }),
    P "PSC_D_JERK" (·.PSC_D_JERK) (fun a v => { a with PSC_D_JERK := v }),
    P "PSC_D_VEL_P" (·.PSC_D_VEL_P) (fun a v => { a with PSC_D_VEL_P := v }),
    P "PSC_D_VEL_I" (·.PSC_D_VEL_I) (fun a v => { a with PSC_D_VEL_I := v }),
    P "PSC_D_VEL_IMAX" (·.PSC_D_VEL_IMAX) (fun a v => { a with PSC_D_VEL_IMAX := v }),
    P "PSC_D_VEL_FLTE" (·.PSC_D_VEL_FLTE) (fun a v => { a with PSC_D_VEL_FLTE := v }),
    P "PSC_D_VEL_D" (·.PSC_D_VEL_D) (fun a v => { a with PSC_D_VEL_D := v }),
    P "PSC_D_VEL_FLTD" (·.PSC_D_VEL_FLTD) (fun a v => { a with PSC_D_VEL_FLTD := v }),
    P "PSC_D_VEL_FF" (·.PSC_D_VEL_FF) (fun a v => { a with PSC_D_VEL_FF := v }),
    P "PSC_D_ACC_P" (·.PSC_D_ACC_P) (fun a v => { a with PSC_D_ACC_P := v }),
    P "PSC_D_ACC_I" (·.PSC_D_ACC_I) (fun a v => { a with PSC_D_ACC_I := v }),
    P "PSC_D_ACC_D" (·.PSC_D_ACC_D) (fun a v => { a with PSC_D_ACC_D := v }),
    P "PSC_D_ACC_FF" (·.PSC_D_ACC_FF) (fun a v => { a with PSC_D_ACC_FF := v }),
    P "PSC_D_ACC_IMAX" (·.PSC_D_ACC_IMAX) (fun a v => { a with PSC_D_ACC_IMAX := v }),
    P "PSC_D_ACC_FLTT" (·.PSC_D_ACC_FLTT) (fun a v => { a with PSC_D_ACC_FLTT := v }),
    P "PSC_D_ACC_FLTE" (·.PSC_D_ACC_FLTE) (fun a v => { a with PSC_D_ACC_FLTE := v }),
    P "PSC_D_ACC_FLTD" (·.PSC_D_ACC_FLTD) (fun a v => { a with PSC_D_ACC_FLTD := v }),
    P "PSC_D_ACC_SMAX" (·.PSC_D_ACC_SMAX) (fun a v => { a with PSC_D_ACC_SMAX := v }),
    P "PSC_D_ACC_PDMX" (·.PSC_D_ACC_PDMX) (fun a v => { a with PSC_D_ACC_PDMX := v }),
    P "PSC_D_ACC_D_FF" (·.PSC_D_ACC_D_FF) (fun a v => { a with PSC_D_ACC_D_FF := v }),
    i8Entry "PSC_D_ACC_NTF" (·.psc.PSC_D_ACC_NTF) (fun q v => { q with psc := { q.psc with PSC_D_ACC_NTF := v } }),
    i8Entry "PSC_D_ACC_NEF" (·.psc.PSC_D_ACC_NEF) (fun q v => { q with psc := { q.psc with PSC_D_ACC_NEF := v } }),
    P "PSC_NE_VEL_P" (·.PSC_NE_VEL_P) (fun a v => { a with PSC_NE_VEL_P := v }),
    P "PSC_NE_VEL_I" (·.PSC_NE_VEL_I) (fun a v => { a with PSC_NE_VEL_I := v }),
    P "PSC_NE_VEL_IMAX" (·.PSC_NE_VEL_IMAX) (fun a v => { a with PSC_NE_VEL_IMAX := v }),
    P "PSC_NE_VEL_FLTE" (·.PSC_NE_VEL_FLTE) (fun a v => { a with PSC_NE_VEL_FLTE := v }),
    P "PSC_NE_VEL_D" (·.PSC_NE_VEL_D) (fun a v => { a with PSC_NE_VEL_D := v }),
    P "PSC_NE_VEL_FLTD" (·.PSC_NE_VEL_FLTD) (fun a v => { a with PSC_NE_VEL_FLTD := v }),
    P "PSC_NE_VEL_FF" (·.PSC_NE_VEL_FF) (fun a v => { a with PSC_NE_VEL_FF := v }) ]

/-- `WP_` (`AC_WPNav.cpp:16-114`). -/
def wpEntries : List Entry :=
  let W (name : String) (get : AC_WPNav.Params → ftype) (set : AC_WPNav.Params → ftype → AC_WPNav.Params) :=
    fEntry name (fun q => get q.wpnav) (fun q v => { q with wpnav := set q.wpnav v })
  [ i8Entry "WP_RFND_USE" (·.wpnav.WP_RFND_USE) (fun q v => { q with wpnav := { q.wpnav with WP_RFND_USE := v } }),
    W "WP_JERK" (·.WP_JERK) (fun a v => { a with WP_JERK := v }),
    W "WP_TER_MARGIN" (·.WP_TER_MARGIN) (fun a v => { a with WP_TER_MARGIN := v }),
    W "WP_SPD" (·.WP_SPD) (fun a v => { a with WP_SPD := v }),
    W "WP_RADIUS_M" (·.WP_RADIUS_M) (fun a v => { a with WP_RADIUS_M := v }),
    W "WP_SPD_UP" (·.WP_SPD_UP) (fun a v => { a with WP_SPD_UP := v }),
    W "WP_SPD_DN" (·.WP_SPD_DN) (fun a v => { a with WP_SPD_DN := v }),
    W "WP_ACC" (·.WP_ACC) (fun a v => { a with WP_ACC := v }),
    W "WP_ACC_Z" (·.WP_ACC_Z) (fun a v => { a with WP_ACC_Z := v }),
    W "WP_ACC_CNR" (·.WP_ACC_CNR) (fun a v => { a with WP_ACC_CNR := v }) ]

/-- `MOT_` (`AP_MotorsMulticopter.cpp:36-262`). -/
def motEntries : List Entry :=
  let M (name : String) (get : AP_MotorsMulticopter.Params → ftype)
      (set : AP_MotorsMulticopter.Params → ftype → AP_MotorsMulticopter.Params) :=
    fEntry name (fun q => get q.mot) (fun q v => { q with mot := set q.mot v })
  [ i16Entry "MOT_YAW_HEADROOM" (·.mot.MOT_YAW_HEADROOM) (fun q v => { q with mot := { q.mot with MOT_YAW_HEADROOM := v } }),
    M "MOT_THST_EXPO" (·.MOT_THST_EXPO) (fun a v => { a with MOT_THST_EXPO := v }),
    M "MOT_SPIN_MAX" (·.MOT_SPIN_MAX) (fun a v => { a with MOT_SPIN_MAX := v }),
    M "MOT_BAT_VOLT_MAX" (·.MOT_BAT_VOLT_MAX) (fun a v => { a with MOT_BAT_VOLT_MAX := v }),
    M "MOT_BAT_VOLT_MIN" (·.MOT_BAT_VOLT_MIN) (fun a v => { a with MOT_BAT_VOLT_MIN := v }),
    M "MOT_BAT_CURR_MAX" (·.MOT_BAT_CURR_MAX) (fun a v => { a with MOT_BAT_CURR_MAX := v }),
    M "MOT_SPIN_MIN" (·.MOT_SPIN_MIN) (fun a v => { a with MOT_SPIN_MIN := v }),
    M "MOT_SPIN_ARM" (·.MOT_SPIN_ARM) (fun a v => { a with MOT_SPIN_ARM := v }),
    M "MOT_THST_HOVER" (·.MOT_THST_HOVER) (fun a v => { a with MOT_THST_HOVER := v }),
    i8Entry "MOT_HOVER_LEARN" (·.mot.MOT_HOVER_LEARN) (fun q v => { q with mot := { q.mot with MOT_HOVER_LEARN := v } }),
    i8Entry "MOT_SAFE_DISARM" (·.mot.MOT_SAFE_DISARM) (fun q v => { q with mot := { q.mot with MOT_SAFE_DISARM := v } }),
    M "MOT_SPOOL_TIME" (·.MOT_SPOOL_TIME) (fun a v => { a with MOT_SPOOL_TIME := v }),
    M "MOT_SLEW_UP_TIME" (·.MOT_SLEW_UP_TIME) (fun a v => { a with MOT_SLEW_UP_TIME := v }),
    M "MOT_SLEW_DN_TIME" (·.MOT_SLEW_DN_TIME) (fun a v => { a with MOT_SLEW_DN_TIME := v }),
    M "MOT_SAFE_TIME" (·.MOT_SAFE_TIME) (fun a v => { a with MOT_SAFE_TIME := v }) ]

/-- Vehicle scalars and the run value. -/
def vehicleEntries : List Entry :=
  [ i8Entry "WP_YAW_BEHAVIOR" (·.WP_YAW_BEHAVIOR) (fun q v => { q with WP_YAW_BEHAVIOR := v }),
    fEntry "PILOT_Y_RATE_TC" (·.PILOT_Y_RATE_TC) (fun q v => { q with PILOT_Y_RATE_TC := v }),
    fEntry "ACRO_RP_RATE_TC" (·.ACRO_RP_RATE_TC) (fun q v => { q with ACRO_RP_RATE_TC := v }),
    fEntry "run.air_density_ratio" (·.air_density_ratio) (fun q v => { q with air_density_ratio := v }),
    { name := "run.start_hover", get := fun q => if q.start_hover then "1" else "0",
      set := fun q d => match d.toInt? with
        | some 0 => some { q with start_hover := false }
        | some 1 => some { q with start_hover := true }
        | _ => none } ]

/-- Every parameter, in print order. -/
def table : List Entry := attEntries ++ pscEntries ++ wpEntries ++ motEntries ++ vehicleEntries

/-- The pre-4.7 `WPNAV_` names (header): the new name and whether the value is scaled by `0.01f`
(`AP_Param::convert_old_parameters_scaled(..., 0.01, 0)`, `AC_WPNav.cpp:161`). -/
def aliases : List (String × String × Bool) :=
  [ ("WPNAV_SPEED", "WP_SPD", true), ("WPNAV_RADIUS", "WP_RADIUS_M", true),
    ("WPNAV_SPEED_UP", "WP_SPD_UP", true), ("WPNAV_SPEED_DN", "WP_SPD_DN", true),
    ("WPNAV_ACCEL", "WP_ACC", true), ("WPNAV_ACCEL_Z", "WP_ACC_Z", true),
    ("WPNAV_ACCEL_C", "WP_ACC_CNR", true), ("WPNAV_JERK", "WP_JERK", false),
    ("WPNAV_TER_MARGIN", "WP_TER_MARGIN", false), ("WPNAV_RFND_USE", "WP_RFND_USE", false) ]

/-- Set one parameter by name; `none` if the name is unknown or the value does not fit. -/
def setParam (q : Parameters) (name : String) (d : Decimal) : Option Parameters :=
  match aliases.find? (·.1 == name) with
  | some (_, new, true) =>
    -- `float` value times `0.01f`, then stored as the new parameter
    (table.find? (·.name == new)).bind fun e =>
      let v : Float32 := d.toFloat32 * 0.01
      let bits := v.toFloat
      -- hand the scaled `float` back as an exact decimal (widening is exact, so this is `v`)
      let exact := parseDecimal? (exactDecimal bits)
      exact.bind (e.set q ·)
  | some (_, new, false) => (table.find? (·.name == new)).bind (·.set q d)
  | none => (table.find? (·.name == name)).bind (·.set q d)

/-- The parameters in the override-file format, `NAME VALUE` per line (values exact), followed by
the mission. -/
def showParams (q : Parameters) : List String :=
  table.map (fun e => s!"{e.name} {e.get q}") ++
  q.mission.map (fun w => s!"waypoint {exactDecimal w.x} {exactDecimal w.y} {exactDecimal w.z}")

end Copter
