// stubs_param.cpp: the parameter system.
//
//   symbol                                   why it is outside the stage, and what stands in
//   AP_Param::setup_object_defaults(...)     parameter storage: defaults from var_info. No-op; the
//                                            adapter sets every AP_Param member the stage reads
//                                            from the parameter record (the rest stay 0).
//   AP_ParamTBase<float>::set_and_save       parameter storage. Reached at init:
//                                            AC_AttitudeControl_Multi::parameter_sanity_check
//                                            rewrites ATC_THR_MIX_MIN/MAX/MAN when they are out of
//                                            its limits (never under the assumption's documented
//                                            ranges). Sets the value as the real one does; the
//                                            EEPROM write is cut.
//   AP_Param::save(bool)                     parameter storage (EEPROM); only the motors'
//                                            save_params_on_disarm (the mixer's). Abort.
#include <AP_Param/AP_Param.h>

void AP_Param::setup_object_defaults(const void *object_pointer,
                                     const struct GroupInfo *group_info)
{
}

template <>
void AP_ParamTBase<float, AP_PARAM_FLOAT>::set_and_save(const float &v)
{
    set(v);
}

void AP_Param::save(bool force_save)
{
    unreachable("AP_Param::save");
}
