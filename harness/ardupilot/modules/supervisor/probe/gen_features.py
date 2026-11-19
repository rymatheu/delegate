#!/usr/bin/env python3
"""Write features.txt: the compile-time feature switches of the supervisor module.

Every define of ArduPilot's Tools/scripts/build_options.py is set to 0, except those in KEEP; then
EXTRA (defines of ArduCopter/config.h and library *_config.h files that build_options.py does not
list) is appended. Usage: python3 -I gen_features.py $ARDUPILOT_ROOT > features.txt
"""
import sys

KEEP = {
    # the estimator's configuration, as the estimator stage builds it (headers only here)
    'HAL_NAVEKF3_AVAILABLE': 1,
    'AP_AHRS_EKF_RESET_ENABLED': 1,
    # modes the flows use (STABILIZE and LAND have no switch)
    'MODE_ALTHOLD_ENABLED': 1,
    # frame
    'AP_MOTORS_FRAME_QUAD_ENABLED': 1,
    # what QGroundControl asks for at connection
    'AP_MAVLINK_MAV_CMD_REQUEST_AUTOPILOT_CAPABILITIES_ENABLED': 1,
    'AP_MAVLINK_AUTOPILOT_VERSION_REQUEST_ENABLED': 1,
    'AP_MAVLINK_MAV_CMD_GET_HOME_POSITION_ENABLED': 1,
    'AP_MAVLINK_MSG_RC_CHANNELS_RAW_ENABLED': 0,
}

EXTRA = [
    # ArduCopter/config.h modes not in build_options.py
    ('MODE_AUTO_ENABLED', 1), ('MODE_GUIDED_ENABLED', 1), ('MODE_LOITER_ENABLED', 1),
    ('MODE_RTL_ENABLED', 1), ('MODE_CIRCLE_ENABLED', 1),  # AUTO requires CIRCLE (config.h)
    ('MODE_ACRO_ENABLED', 0), ('MODE_POSHOLD_ENABLED', 0),
    ('MODE_SMARTRTL_ENABLED', 0), ('MODE_DRIFT_ENABLED', 0), ('MODE_AUTOROTATE_ENABLED', 0),
    ('AUTOTUNE_ENABLED', 0), ('WEATHERVANE_ENABLED', 0), ('AC_NAV_GUIDED', 1),
    ('TOY_MODE_ENABLED', 0), ('USER_PARAMS_ENABLED', 0),
    # libraries' *_config.h
    ('AP_MISSION_ENABLED', 1),
    ('AP_TERRAIN_AVAILABLE', 0),
    ('AP_STATS_ENABLED', 0),
    ('AP_SCRIPTING_ENABLED', 0),
    ('HAL_MOUNT_ENABLED', 0), ('AP_CAMERA_ENABLED', 0), ('AP_BEACON_ENABLED', 0),
    ('AP_OPTICALFLOW_ENABLED', 0), ('AP_RANGEFINDER_ENABLED', 0), ('AP_RPM_ENABLED', 0),
    ('AP_AIRSPEED_ENABLED', 0), ('HAL_WITH_ESC_TELEM', 0), ('AP_VIDEOTX_ENABLED', 0),
    ('AP_RCPROTOCOL_ENABLED', 0), ('HAL_LOGGING_ENABLED', 0),
    ('AP_FENCE_ENABLED', 0), ('HAL_RALLY_ENABLED', 0),
    ('AP_DDS_ENABLED', 0), ('AP_OPENDRONEID_ENABLED', 0), ('AP_SIGNED_FIRMWARE', 0),
    ('HAL_NUM_CAN_IFACES', 0), ('HAL_WITH_DSP', 0),
    # SITL's configure defines it (boards.py); 0 does not compile with CONFIG_HAL_BOARD SITL
    # (AP::sitl() is used under CONFIG_HAL_BOARD == HAL_BOARD_SITL alone)
    ('AP_SIM_ENABLED', 1),
    # hardware-side drivers SITL builds by default
    ('HAL_SUPPORT_RCOUT_SERIAL', 0), ('AP_NOTIFY_LP5562_ENABLED', 0),
    ('AP_NOTIFY_IS31FL3195_ENABLED', 0), ('AP_NOTIFY_NCP5623_ENABLED', 0),
    ('AP_NOTIFY_PCA9685_ENABLED', 0), ('AP_NOTIFY_TOSHIBALED_ENABLED', 0),
    ('AP_NOTIFY_BUZZER_ENABLED', 0),
    # accelerometer calibration from the ground station (estimator-side)
    ('HAL_INS_ACCELCAL_ENABLED', 0),
    ('HAL_PROXIMITY_ENABLED', 0), ('AP_WINCH_ENABLED', 0), ('AP_LANDINGGEAR_ENABLED', 0),
    ('AP_SURFACEDISTANCE_ENABLED', 0), ('AP_ICENGINE_ENABLED', 0),
    ('AP_GENERATOR_ENABLED', 0), ('AP_EFI_ENABLED', 0),
    ('AP_SERVO_TELEM_ENABLED', 0), ('AP_TEMPERATURE_SENSOR_ENABLED', 0),
    ('HAL_SPRAYER_ENABLED', 0), ('AP_GRIPPER_ENABLED', 0),
    ('AP_BATTERY_ANALOG_ENABLED', 1), ('AP_BATTERY_AD7091R5_ENABLED', 0),

    ('AP_NOTIFY_SITL_ENABLED', 0),
    ('AP_EXTERNAL_CONTROL_ENABLED', 0),
    ('AP_RSSI_ENABLED', 0),
    ('AP_COPTER_AHRS_AUTO_TRIM_ENABLED', 0),
]


def main():
    sys.path.insert(0, sys.argv[1] + '/Tools/scripts')
    import build_options
    out = ['# written by gen_features.py: every build_options.py define 0 unless kept']
    seen = set()
    for f in build_options.BUILD_OPTIONS:
        v = KEEP.get(f.define, 0)
        seen.add(f.define)
        out.append('-D%s=%d' % (f.define, v))
    out.append('# ArduCopter/config.h and libraries *_config.h')
    for d, v in EXTRA:
        if d in seen:
            out = [l for l in out if not l.startswith('-D%s=' % d)]
        out.append('-D%s=%d' % (d, v))
    print('\n'.join(out))


main()
