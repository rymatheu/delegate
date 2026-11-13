// The environment of the EKF difftests (README.md, "Phase 3: EKF data structures"): what the
// translated ArduPilot sources call outside the translation. AP_InternalError::error is left out of
// the model (cpp2lean --drop); here it records nothing, and the singleton accessor returns one object.
#include <AP_InternalError/AP_InternalError.h>

void AP_InternalError::error(const AP_InternalError::error_t, uint16_t) {}

namespace AP {
AP_InternalError &internalerror()
{
    static AP_InternalError e;
    return e;
}
}
