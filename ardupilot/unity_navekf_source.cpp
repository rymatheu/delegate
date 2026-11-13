// AP_NavEKF_Source, EKF3's source selection (README.md "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source"),
// included unmodified with the flags of its unit in the reference build, with AP_Param's parameter classes: its
// source sets `_source_set[3]` are AP_Enum parameters in an array of structs (--param-ext). The object is the one
// NavEKF3 holds as its member `sources` (AP_NavEKF3.h), here at file scope; AP_DAL (the compass's and barometer's
// counts it reads) is the boundary.
#include <AP_NavEKF/AP_NavEKF_Source.cpp>
#include <AP_Param/AP_ParamT.cpp>

AP_NavEKF_Source sources;
