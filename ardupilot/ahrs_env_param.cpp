// The AP_Param member functions the AP_AHRS translation's C++ side calls that AP_ParamT.cpp defines (README.md,
// "Phase 3: AP_AHRS translated"; ardupilot/ahrs_difftest.py), as explicit specializations in a unit of their own (the
// AHRS and NavEKF3 headers instantiate them implicitly). Their effect on the parameter's value as AP_ParamT.cpp has it;
// AP_Param's parameter count cache and storage are outside the model.
#include <AP_Param/AP_Param.h>

// AP_ParamT.cpp:33-41 (`ekf3.EKF3.set_enable(true)`, AP_AHRS.cpp:324): the value set
template<> void AP_ParamTBase<int8_t, AP_PARAM_INT8>::set_enable(const int8_t &v) { _value = v; }
// AP_ParamT.cpp:91-100 (AP_AHRS::record_origin, AP_AHRS.cpp:915): an equal value is not set
template<> void AP_ParamTBase<float, AP_PARAM_FLOAT>::set_and_save_ifchanged(const float &v)
{
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wfloat-equal"
    if (v == _value) {
#pragma GCC diagnostic pop
        return;
    }
    set(v);
}
