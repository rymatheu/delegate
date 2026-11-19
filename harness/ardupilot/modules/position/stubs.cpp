// stubs.cpp: what is cut from the position module, and what stands in for it.
//
// The stand-ins are split by what they stand for, one file each, compiled as this one translation
// unit (ardupilot/build.sh compiles adapter.cpp and stubs.cpp; the compiler's dependency output
// lists every included file, so each is part of the code hash):
//   stubs_hal.cpp        the HAL: clock, panic, the hal object
//   stubs_scheduler.cpp  the scheduler's tick counter and the SITL singleton
//   stubs_ahrs.cpp       the estimator: AP_AHRS and the AP_AHRS_View (signals est_*)
//   stubs_attitude.cpp   the attitude controller (signals ac_*, output throttle_in)
//   stubs_motors.cpp     the mixer (limit flags, hover throttle)
//   stubs_param.cpp      parameter storage
//   stubs_misc.cpp       internal-error reporter, logger, filter definitions, board config
// Each file lists its symbols, why each is outside the stage, and what stands in.
#include "stubs_hal.cpp"
#include "stubs_scheduler.cpp"
#include "stubs_ahrs.cpp"
#include "stubs_attitude.cpp"
#include "stubs_motors.cpp"
#include "stubs_param.cpp"
#include "stubs_misc.cpp"

// --- reset of the cut's state, at every init
void harness_reset_cut()
{
    memset(&harness_cut, 0, sizeof harness_cut);
    harness_reset_scheduler();
    harness_reset_ahrs();
}
