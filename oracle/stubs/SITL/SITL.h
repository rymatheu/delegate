// ORACLE STUB: replaces libraries/SITL/SITL.h (reached in the real build through
// AP_AHRS.h -> AP_AHRS_SIM.h). AC_PosControl::has_good_timing (AC_PosControl.cpp:1797-1806) reads
// AP::sitl()->state.is_lock_step_scheduled to decide whether a late controller call is reported as
// an internal error (diagnostic only). The oracle is lock-stepped by construction: true.
#pragma once

namespace SITL {
struct sitl_fdm {
    bool is_lock_step_scheduled = true;
};
class SIM {
public:
    sitl_fdm state;
};
}

namespace AP {
    SITL::SIM *sitl();
};
