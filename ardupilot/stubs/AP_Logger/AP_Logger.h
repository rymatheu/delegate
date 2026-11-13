// ORACLE STUB: replaces libraries/AP_Logger/AP_Logger.h.
// Why: the real logger pulls in AP_Mission, AP_Rally, the backends and MAVLink. The compiled code
// only calls AP::logger().WriteBlock (AP_MotorsMulticopter.cpp:454, AP_Motors_Class.cpp:303, in
// logging methods the oracle never calls) and AP::logger().Write. The stub drops every record.
// The real AP_Logger/LogStructure.h and AP_Logger_config.h are used unchanged.
#pragma once

#include <AP_Logger/AP_Logger_config.h>
#include <AP_Logger/LogStructure.h>

// AP_Logger.h:114-189, verbatim: the error codes AC_Circle.cpp:147 logs
enum class LogErrorSubsystem : uint8_t {
    MAIN = 1,
    RADIO = 2,
    COMPASS = 3,
    OPTFLOW = 4,   // not used
    FAILSAFE_RADIO = 5,
    FAILSAFE_BATT = 6,
    FAILSAFE_GPS = 7,   // not used
    FAILSAFE_GCS = 8,
    FAILSAFE_FENCE = 9,
    FLIGHT_MODE = 10,
    GPS = 11,
    CRASH_CHECK = 12,
    FLIP = 13,
    AUTOTUNE = 14,  // not used
    PARACHUTES = 15,
    EKFCHECK = 16,
    FAILSAFE_EKFINAV = 17,
    BARO = 18,
    CPU = 19,
    FAILSAFE_ADSB = 20,
    TERRAIN = 21,
    NAVIGATION = 22,
    FAILSAFE_TERRAIN = 23,
    EKF_PRIMARY = 24,
    THRUST_LOSS_CHECK = 25,
    FAILSAFE_SENSORS = 26,
    FAILSAFE_LEAK = 27,
    PILOT_INPUT = 28,
    FAILSAFE_VIBE = 29,
    INTERNAL_ERROR = 30,
    FAILSAFE_DEADRECKON = 31
};

enum class LogErrorCode : uint8_t {
// general error codes
    ERROR_RESOLVED  = 0,
    FAILED_TO_INITIALISE = 1,
    UNHEALTHY = 4,
// subsystem specific error codes -- radio
    RADIO_LATE_FRAME = 2,
// subsystem specific error codes -- failsafe_thr, batt, gps
    FAILSAFE_RESOLVED = 0,
    FAILSAFE_OCCURRED = 1,
// subsystem specific error codes -- main
    MAIN_INS_DELAY = 1,
// subsystem specific error codes -- crash checker
    CRASH_CHECK_CRASH = 1,
    CRASH_CHECK_LOSS_OF_CONTROL = 2,
// subsystem specific error codes -- flip
    FLIP_ABANDONED = 2,
// subsystem specific error codes -- terrain
    MISSING_TERRAIN_DATA = 2,
// subsystem specific error codes -- navigation
    FAILED_TO_SET_DESTINATION = 2,
    RESTARTED_RTL = 3,
    FAILED_CIRCLE_INIT = 4,
    DEST_OUTSIDE_FENCE = 5,
    RTL_MISSING_RNGFND = 6,
// subsystem specific error codes -- internal_error
    INTERNAL_ERRORS_DETECTED = 1,

// parachute failed to deploy because of low altitude or landed
    PARACHUTE_TOO_LOW = 2,
    PARACHUTE_LANDED = 3,
// EKF check definitions
    EKFCHECK_BAD_VARIANCE = 2,
    EKFCHECK_VARIANCE_CLEARED = 0,
// Baro specific error codes
    BARO_GLITCH = 2,
    BAD_DEPTH = 3, // sub-only
// GPS specific error codes
    GPS_GLITCH = 2,
};

class AP_Logger {
public:
    void Write_Error(LogErrorSubsystem sub_system, LogErrorCode error_code) {}
    void WriteBlock(const void *pBuffer, uint16_t size) {}
    void WriteCriticalBlock(const void *pBuffer, uint16_t size) {}
    void Write(const char *name, const char *labels, const char *fmt, ...) {}
    void Write(const char *name, const char *labels, const char *units, const char *mults, const char *fmt, ...) {}
    bool should_log(uint32_t mask) const { return false; }
};

namespace AP {
    AP_Logger &logger();
};

// AP_Logger.h:633 (HAL_LOGGING_ENABLED)
#define LOGGER_WRITE_ERROR(subsys, err) AP::logger().Write_Error(subsys, err)
