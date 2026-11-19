// ORACLE STUB: replaces libraries/GCS_MAVLink/GCS_MAVLink.h.
// Why: the real header includes the generated MAVLink headers (modules/mavlink, an empty submodule
// in this checkout). The compiled control code needs only the MAV_TYPE enumeration
// (AP_Motors_Class.h:334,444; AP_MotorsMatrix.cpp frame setup), the MAV_SEVERITY values and the
// GCS_SEND_TEXT macro. Enumerator values are MAVLink's common.xml values; they never reach the
// computation. Text messages are dropped.
#pragma once
#include <stdint.h>

enum MAV_TYPE : uint8_t {
    MAV_TYPE_GENERIC = 0,
    MAV_TYPE_QUADROTOR = 2,
    MAV_TYPE_HEXAROTOR = 13,
    MAV_TYPE_OCTOROTOR = 14,
    MAV_TYPE_TRICOPTER = 15,
    MAV_TYPE_DODECAROTOR = 29,
    MAV_TYPE_DECAROTOR = 35,
};

enum MAV_SEVERITY : uint8_t {
    MAV_SEVERITY_EMERGENCY = 0,
    MAV_SEVERITY_ALERT = 1,
    MAV_SEVERITY_CRITICAL = 2,
    MAV_SEVERITY_ERROR = 3,
    MAV_SEVERITY_WARNING = 4,
    MAV_SEVERITY_NOTICE = 5,
    MAV_SEVERITY_INFO = 6,
    MAV_SEVERITY_DEBUG = 7,
};

#define GCS_SEND_TEXT(severity, format, args...) do {} while (0)
