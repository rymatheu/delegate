// stubs.cpp: what is cut from the attitude module, and what stands in for it.
//
// ardupilot/build.sh compiles one stub file per module; this one is that translation unit and
// includes the stubs grouped by what they stand for. Every included file is read by the compiler
// and so is part of the module's code hash.
#include "stubs_hal.cpp"
#include "stubs_param.cpp"
#include "stubs_error.cpp"
#include "stubs_ahrs.cpp"
#include "stubs_motors.cpp"
#include "stubs_filter.cpp"

// --- reset of the cut's state, at every init
void harness_reset_cut()
{
    harness_reset_scheduler();
    harness_reset_ahrs();
}
