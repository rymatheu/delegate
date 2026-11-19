// stubs.cpp: what is cut from the loiter module, and what stands in for it.
//
// The stand-ins are split by what they stand for, one file each, compiled as this one translation
// unit (ardupilot/build.sh compiles adapter.cpp and stubs.cpp; the compiler's dependency output
// lists every included file, so each is part of the code hash):
//   stubs_hal.cpp        the HAL: clock, panic
//   stubs_ahrs.cpp       the estimator: AP_AHRS's active estimates (the ground-speed limit)
//   stubs_posctl.cpp     the position controller: the hand-over and the reads (signals pc_*)
//   stubs_param.cpp      parameter storage
//   stubs_misc.cpp       the internal-error reporter
// The attitude controller is not stubbed: AC_AttitudeControl.cpp is compiled (sources.txt).
// Each file lists its symbols, why each is outside the stage, and what stands in.
#include "stubs_hal.cpp"
#include "stubs_ahrs.cpp"
#include "stubs_posctl.cpp"
#include "stubs_param.cpp"
#include "stubs_misc.cpp"

// --- reset of the cut's state, at every init
void harness_reset_cut()
{
    harness_reset_ahrs();
    harness_clock_ms = 0;
    harness_gnd_spd_limit = 0.0f;
    memset(&harness_loiter_calls, 0, sizeof harness_loiter_calls);
    harness_current_seq = 0;
    harness_pc_stopping_point.zero();
    harness_pc_lean_angle_max = 0.0f;
    harness_att_target_roll = harness_att_target_pitch = 0.0f;
}
