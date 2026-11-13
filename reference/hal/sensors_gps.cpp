/* cpp2lean reference vehicle: the GPS back-end stand-in (sensors.cpp). */

#include <AP_HAL/AP_HAL.h>
#include <SITL/SITL.h>
#include <AP_GPS/AP_GPS_SITL.h>

#include "est_input.h"

extern const AP_HAL::HAL& hal;

// ------------------------------------------------------------------------------------------------
// GPS

// AP_GPS_SITL's simulation_timeval and gps_time, with the stand-in's fixed start time: the UTC time is
// start_time_UTC plus the clock (SITL's simulation_timeval with its first call's time of day at 0 us,
// without static locals or struct timeval; the same values)
static uint32_t gps_time_week_ms(uint16_t &time_week)
{
    const uint64_t now = AP_HAL::micros64();
    const uint64_t tv_sec = uint64_t(AP::sitl()->start_time_UTC) + now / 1000000ULL;
    const uint64_t tv_usec = now % 1000000ULL;
    const uint32_t epoch = 86400*(10*365 + (1980-1969)/4 + 1 + 6 - 2) - (GPS_LEAPSECONDS_MILLIS / 1000ULL);
    uint32_t epoch_seconds = uint32_t(tv_sec - epoch);
    time_week = epoch_seconds / AP_SEC_PER_WEEK;
    uint32_t t_ms = uint32_t(tv_usec / 1000);
    return (epoch_seconds % AP_SEC_PER_WEEK) * AP_MSEC_PER_SEC + ((t_ms/200) * 200);
}

bool AP_GPS_SITL::read(void)
{
    if (!est_gps_pending()) {
        return false;
    }
    const EstRecord gps_record = est_gps_take();
    const uint32_t now = AP_HAL::millis();
    last_update_ms = now;

    const double latitude = gps_record.gps_lat_deg;
    const double longitude = gps_record.gps_lon_deg;
    const float altitude = gps_record.gps_alt_m;
    const double speedN = gps_record.gps_vn;
    const double speedE = gps_record.gps_ve;
    const double speedD = gps_record.gps_vd;

    uint16_t time_week = 0;
    const uint32_t time_week_ms = gps_time_week_ms(time_week);
    state.time_week = time_week;
    state.time_week_ms = time_week_ms;
    state.status = AP_GPS_FixType::FIX_3D;
    state.num_sats = 15;
    state.location = Location{
        int32_t(latitude*1e7),
        int32_t(longitude*1e7),
        int32_t(altitude*100),
        Location::AltFrame::ABSOLUTE
    };
    state.hdop = 100;
    state.vdop = 100;
    state.have_vertical_velocity = true;
    state.velocity.x = speedN;
    state.velocity.y = speedE;
    state.velocity.z = speedD;
    velocity_to_speed_course(state);
    state.have_speed_accuracy = true;
    state.have_horizontal_accuracy = true;
    state.have_vertical_accuracy = true;
    state.have_vertical_velocity = true;
    state.last_gps_time_ms = now;
    return true;
}
