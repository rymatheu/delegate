// stubs.cpp: what is cut from the guidance module, and what stands in for it.
//
// ardupilot/build.sh compiles adapter.cpp and stubs.cpp; the stubs are split by what they stand for
// into the files included here (each lists its symbols, why they are outside the module and what
// stands in). The compiler's dependency output names every included file, so all of them are in
// the code hash.
//
//   stubs_posctl.cpp    the position controller (AC_PosControl), another stage
//   stubs_hal.cpp       the clock, panic, and ArduPilot's SITL debug printf
//   stubs_param.cpp     parameter storage
//   stubs_frames.cpp    terrain, Location and the EKF origin (not reached)
//   stubs_logging.cpp   the logger and the internal-error reporter
//
// The attitude controller (AC_AttitudeControl), also another stage, needs no stub: AC_WPNav
// reads only its parameters, through inline accessors (calc_scurve_jerk_and_snap,
// AC_WPNav.cpp:1073-1085), which adapter.cpp loads from the parameter record.
#include "stubs_posctl.cpp"
#include "stubs_hal.cpp"
#include "stubs_param.cpp"
#include "stubs_frames.cpp"
#include "stubs_logging.cpp"
