// AP_NavEKF's EKFGSF_yaw (README.md, "Phase 3: EKF data structures"): the bank of yaw estimators that
// EKF3 allocates per core (AP_NavEKF3_core.cpp:182), double precision (`ftype`), included unmodified;
// with the flags of EKFGSF_yaw.cpp's unit in the reference build.
#include <AP_NavEKF/EKFGSF_yaw.cpp>
// the AP_Math functions it calls that are defined out of line (as in AP_Math's own translation)
#include <AP_Math/AP_Math.cpp>
#include <AP_Math/vector2.cpp>
#include <AP_Math/vector3.cpp>
#include <AP_Math/matrix3.cpp>
