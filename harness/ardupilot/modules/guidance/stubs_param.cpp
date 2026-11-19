// stubs_param.cpp: parameter storage (AP_Param), outside every module.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP_Param::setup_object_defaults(...)     loads defaults from var_info (AC_WPNav's
//                                            constructor). No-op; adapter.cpp sets every AP_Param
//                                            member the module reads from the parameter record.
//   AP_ParamTBase<float>::set_and_save_ifchanged(v)
//                                            AP_ParamT.cpp:91-99: set the value if it differs and
//                                            save it to EEPROM. wp_and_spline_init_m calls it to
//                                            raise WP_RADIUS_M to 0.05 and WP_SPD to 0.01
//                                            (AC_WPNav.cpp:217, 220): a parameter rewritten at
//                                            run time. The stand-in sets the value as the real
//                                            one does and skips the save (EEPROM). The documented
//                                            ranges in the assumption exclude the rewrite.
//   AP_Param::configured()                   only AC_WPNav::convert_parameters (boot-time
//   AP_Param::convert_old_parameters_scaled  parameter conversion), never called. Abort.
#include <stdio.h>
#include <stdlib.h>

#include <AP_Param/AP_Param.h>

__attribute__((noreturn)) static void param_unreachable(const char *what)
{
    fprintf(stderr, "guidance: cut symbol reached: %s\n", what);
    abort();
}

void AP_Param::setup_object_defaults(const void *object_pointer, const struct GroupInfo *group_info)
{
}

template <>
void AP_ParamTBase<float, AP_PARAM_FLOAT>::set_and_save_ifchanged(const float &v)
{
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wfloat-equal"
    if (v == _value) {
#pragma GCC diagnostic pop
        return;
    }
    set(v);
}

bool AP_Param::configured(void) const
{
    param_unreachable("AP_Param::configured");
}

void AP_Param::convert_old_parameters_scaled(const ConversionInfo *conversion_table, uint8_t table_size, float scaler, uint8_t flags)
{
    param_unreachable("AP_Param::convert_old_parameters_scaled");
}
