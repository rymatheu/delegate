// ardupilot/vehicle/vehicle_env.cpp: out-of-line definitions the reference vehicle needs beyond
// ardupilot/stubs/oracle_env.cpp, for the navigator's code that the harness never calls.
#include <AP_HAL/AP_HAL.h>
#include <AP_Param/AP_Param.h>

// AC_WPNav::convert_parameters (AC_WPNav.cpp:116-163): parameter storage conversion, not called
void AP_Param::convert_old_parameters_scaled(const ConversionInfo *conversion_table, uint8_t table_size, float scaler, uint8_t flags)
{
    AP_HAL::panic("convert_old_parameters_scaled");
}
