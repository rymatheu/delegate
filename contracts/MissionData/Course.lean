/-!
# The course parameter texts

Byte-for-byte copies of the three parameter files the mission flights pass to the vehicle, in the
order of `sim/spec/mission-course.json` (`params`):
`--params params/copter-cf2x.txt --params params/copter-course-speed.txt --params params/copter-cf2x-tuned.txt`.
`courseLines` is the list of lines `VehicleMain.lean` builds from them (`readLines`: each file split
at `\n`, concatenated in order). The executable `mission_world_check` compares these texts with the
files and prints the parameters of the world they construct (as `copter_lean --print-params`).

SHA-1 of the files at the time of the copy:
* `sim/params/copter-cf2x.txt`: `a4c29b8d25295f37135241231cf8e72bca6d3330`
* `sim/params/copter-course-speed.txt`: `02684a0f639a0c8afe95183c9807f3768abe8750`
* `sim/params/copter-cf2x-tuned.txt`: `c4a7d6defb6c315f201d44c727619c19b4a84188`
-/

namespace MissionData

/-- `sim/params/copter-cf2x.txt`, verbatim. -/
def cf2xText : String := r#"# Crazyflie CF2X (gym-pybullet-drones, PYB physics, gravity 9.80665, control 400 Hz, physics 1200 Hz)
# for the copter vehicles (`--params`, sim/PROTOCOL.md). One `NAME value` per line with the ArduPilot
# parameter names; every parameter not listed keeps the ArduPilot default. `#` starts a comment.

# Motors: linear thrust. run_copter.py maps an actuator a of slot i to the thrust fraction a of the
# maximum per-motor thrust (rpm = MAX_RPM sqrt(a)); the simulator models no ESC or thrust curve, so
# the actuator must already be the thrust fraction, which is AP_Motors' actuator_to_thrust with
# expo 0 and spin range [0, 1].
MOT_THST_EXPO 0
MOT_SPIN_MIN 0
MOT_SPIN_MAX 1
MOT_BAT_VOLT_MAX 0           # no battery-voltage compensation (the simulator has no battery)
MOT_HOVER_LEARN 0            # fixed hover throttle
MOT_THST_HOVER 0.4444        # CF2X thrust-to-weight 2.25: hover at 1/2.25 of full thrust

# Mission: the figure-eight course of cf2x-course.txt, NED meters (north, east, down) from the start
# point. Two diamonds of 1.25 m half-diagonal that meet over the origin: the first lobe turns left and
# climbs from 0.8 m to 1.4 m, the leg through the crossing climbs to 1.6 m, and the second lobe
# turns right and descends back to 0.8 m over the start (13.8 m in all).
waypoint 0 0 -0.8
waypoint 1.25 1.25 -1.0
waypoint 0 2.5 -1.2
waypoint -1.25 1.25 -1.4
waypoint 1.25 -1.25 -1.6
waypoint 0 -2.5 -1.4
waypoint -1.25 -1.25 -1.1
waypoint 0 0 -0.8
"#

/-- `sim/params/copter-course-speed.txt`, verbatim. -/
def courseSpeedText : String := r#"# Path speed and acceleration for the figure-eight course of copter-cf2x.txt: 1 m/s, 1.5 m/s^2
# with the ArduPilot names, for a second flight of the course; pass it after copter-cf2x.txt:
#   run_copter.py --params params/copter-cf2x.txt --params params/copter-course-speed.txt
# Everything else (gains, WP_RADIUS_M, jerk, corner acceleration) stays at the ArduPilot default.
WP_SPD 1
WP_ACC 1.5
"#

/-- `sim/params/copter-cf2x-tuned.txt`, verbatim. -/
def tunedText : String := r#"# Tuned gains for the copter vehicles on the CF2X (27 g, 400 Hz control), an overlay to pass after
# copter-cf2x.txt and copter-course-speed.txt:
#   run_copter.py --params params/copter-cf2x.txt --params params/copter-course-speed.txt \
#     --params params/copter-cf2x-tuned.txt
# Parameters only, every value inside ArduPilot's @Range. ardupilot/AC_Attitude.json's `tuned` run
# uses the ATC_ values; sim/fly.sh passes this file on every flight (UNTUNED=1 omits it).

# Attitude input shaping: input time constant (default 0.1 s), roll and pitch acceleration limits
# (default 1100 deg/s^2)
ATC_INPUT_TC 0.05
ATC_ACC_R_MAX 1800
ATC_ACC_P_MAX 1800

# Angle P (default 4.5)
ATC_ANG_RLL_P 9
ATC_ANG_PIT_P 9

# Horizontal position P (default 1), velocity P and D (defaults 2 and 0.5)
PSC_NE_POS_P 1.5
PSC_NE_VEL_P 6
PSC_NE_VEL_D 0.5

# Navigator: waypoint radius (default 2 m) and jerk (default 1 m/s^3)
WP_RADIUS_M 0.1
WP_JERK 5
"#

/-- The parameter files in the order they are passed. -/
def courseFiles : List String :=
  ["sim/params/copter-cf2x.txt", "sim/params/copter-course-speed.txt", "sim/params/copter-cf2x-tuned.txt"]

/-- The texts in the same order. -/
def courseTexts : List String := [cf2xText, courseSpeedText, tunedText]

/-- The lines `VehicleMain.lean` passes to `construct` for the three files (`readLines` of each, in order). -/
def courseLines : List String := courseTexts.flatMap (·.splitOn "\n")

end MissionData
