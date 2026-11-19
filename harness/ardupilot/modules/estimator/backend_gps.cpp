// backend_gps.cpp: the GPS driver, a stand-in for ArduPilot's SITL GPS driver.
//
// GPS1_TYPE 100 (the X500's stored value) makes AP_GPS::_detect_instance create an AP_GPS_SITL
// driver (AP_GPS.cpp:730). This file defines its read() (libraries/AP_GPS/AP_GPS_SITL.h) in place
// of AP_GPS_SITL.cpp, which reads the simulator's position: here the fix is the input record's.
// A fix that arrives (gps_fresh) waits in the driver, as bytes wait in a UART, until the front
// end's update() calls read(); read() then fills the state exactly as the SITL driver does:
// FIX_3D, 15 satellites, hdop and vdop 1.00, the location (altitude in cm, absolute), the NED
// velocity with have_vertical_velocity, speed and course (velocity_to_speed_course), the three
// have_*_accuracy flags set with the accuracies left at 0 as SITL leaves them, the GPS week and
// time of week from the clock, last_gps_time_ms.
// Differences from the SITL driver: SITL returns a fix every 200 ms of its own clock and
// computes it from the simulator's state at that moment; here a fix is returned once, at the
// first read() after the plant produced it (5 Hz). The GPS time starts at a fixed UTC time
// (HARNESS_GPS_START_UTC below) where SITL starts at its start_time_UTC (the host's clock unless
// --start-time is given); only the GPS time fields depend on it.
#include <AP_GPS/AP_GPS_SITL.h>
#include <AP_HAL/AP_HAL.h>

#include "harness_cut.h"

static const uint32_t HARNESS_GPS_START_UTC = 1798761600;   // 2027-01-01T00:00:00Z

static bool fix_pending;
static int32_t fix_lat_e7, fix_lon_e7;
static float fix_alt, fix_vel[3];

// bytes arriving on the GPS's UART: called by the adapter for every tick
void harness_gps_receive()
{
    const HarnessTick &t = harness_tick;
    if (!t.gps_fresh) {
        return;
    }
    fix_pending = true;
    fix_lat_e7 = t.gps_lat_e7;
    fix_lon_e7 = t.gps_lon_e7;
    fix_alt = t.gps_alt;
    for (uint8_t i = 0; i < 3; i++) {
        fix_vel[i] = t.gps_vel[i];
    }
}

void harness_reset_gps_driver()
{
    fix_pending = false;
}

// GPS week and time of week of the clock, as AP_GPS_SITL.cpp's gps_time with
// start_time_UTC = HARNESS_GPS_START_UTC
static void gps_time(uint16_t *time_week, uint32_t *time_week_ms)
{
    const uint64_t now = AP_HAL::micros64();
    const uint64_t tv_sec = HARNESS_GPS_START_UTC + now / 1000000ULL;
    const uint32_t tv_usec = now % 1000000ULL;
    const uint32_t epoch = 86400*(10*365 + (1980-1969)/4 + 1 + 6 - 2) - (GPS_LEAPSECONDS_MILLIS / 1000ULL);
    const uint32_t epoch_seconds = uint32_t(tv_sec) - epoch;
    *time_week = epoch_seconds / AP_SEC_PER_WEEK;
    const uint32_t t_ms = tv_usec / 1000;
    *time_week_ms = (epoch_seconds % AP_SEC_PER_WEEK) * AP_MSEC_PER_SEC + ((t_ms/200) * 200);
}

bool AP_GPS_SITL::read(void)
{
    if (!fix_pending) {
        return false;
    }
    fix_pending = false;
    const uint32_t now = AP_HAL::millis();
    last_update_ms = now;

    uint16_t time_week;
    uint32_t time_week_ms;
    gps_time(&time_week, &time_week_ms);

    state.time_week = time_week;
    state.time_week_ms = time_week_ms;
    state.status = AP_GPS_FixType::FIX_3D;
    state.num_sats = 15;

    state.location = Location{
        fix_lat_e7,
        fix_lon_e7,
        int32_t(fix_alt*100),
        Location::AltFrame::ABSOLUTE
    };

    state.hdop = 100;
    state.vdop = 100;

    state.have_vertical_velocity = true;
    state.velocity.x = fix_vel[0];
    state.velocity.y = fix_vel[1];
    state.velocity.z = fix_vel[2];

    velocity_to_speed_course(state);

    state.have_speed_accuracy = true;
    state.have_horizontal_accuracy = true;
    state.have_vertical_accuracy = true;
    state.have_vertical_velocity = true;

    state.last_gps_time_ms = now;

    return true;
}
