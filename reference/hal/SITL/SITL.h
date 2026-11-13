/* cpp2lean reference vehicle: stand-in for ArduPilot's libraries/SITL/SITL.h (PORT-PLAN.md 3.2, the
   `SITL::SIM` stand-in). The SITL simulator is not part of the reference vehicle: the physics is
   gym-pybullet-drones and the sensor samples arrive through the lock-step HAL (reference/hal). What
   remains is the object `AP_Vehicle::sitl` with the members that SITL-board code outside the simulator
   reads, holding constants, so that the vehicle has no SIM_* parameters (D2). Types and names are those
   of the real header at 802db19de1; this directory comes before libraries/ on the include path. */
#pragma once

#include <AP_HAL/AP_HAL_Boards.h>

#if AP_SIM_ENABLED

#include <AP_Math/AP_Math.h>
#include <AP_Param/AP_Param.h>
#include <AP_Common/Location.h>
#include <AP_Compass/AP_Compass.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include <AP_Baro/AP_Baro.h>
#include <GCS_MAVLink/GCS_MAVLink.h>

namespace SITL {

/* the fields of the real sitl_fdm that code outside the simulator reads (AP_AHRS_SIM, the
   lock-step scheduling flag of AC_PosControl); the HAL leaves them zero except
   is_lock_step_scheduled, which is true as in SITL's lock-step mode */
struct sitl_fdm {
    uint64_t timestamp_us;
    uint64_t flightaxis_imu_frame_num;
    Location home;
    double latitude, longitude;
    double altitude;
    double heading;
    double speedN, speedE, speedD;
    double xAccel, yAccel, zAccel;
    double rollRate, pitchRate, yawRate;
    double rollDeg, pitchDeg, yawDeg;
    Quaternion quaternion;
    double airspeed;
    Vector3f velocity_air_bf;
    double battery_voltage;
    double battery_current;
    bool is_lock_step_scheduled;
    Vector3f wind_ef;
    float height_agl;
};

class SIM {
public:
    SIM();
    CLASS_NO_COPY(SIM);

    static SIM *_singleton;
    static SIM *get_singleton() { return _singleton; }

    // no SIM_* parameters: an empty group, so that ArduCopter's GOBJECT(sitl, "SIM_", SITL::SIM) entry
    // compiles unchanged and contributes nothing
    static const struct AP_Param::GroupInfo var_info[];

    struct sitl_fdm state;
    float throttle;

    // constants (the stand-in's configuration, set by the HAL before setup())
    AP_Int8  imu_count;            // IMUs to create (D5)
    AP_Int8  baro_count;           // barometers to create
    AP_Int32 loop_delay;           // extra loop delay: 0
    AP_Int16 loop_time_jitter_us;  // 0: AP_AHRS::update does not call random()
    AP_Int16 on_hardware_relay_enable_mask;
    AP_Int8  wow_pin;
    AP_Int8  odom_enable;
    AP_Int8  float_exception;
    AP_Int8  telem_baudlimit_enable;
    AP_Int8  mag_save_ids;
    AP_UInt32 mag_devid[MAX_CONNECTED_MAGS];
    AP_Vector3f mag_ofs[HAL_COMPASS_MAX_SENSORS];
    time_t start_time_UTC;
    AP_Vector3f accel_bias[INS_MAX_INSTANCES];   // read by AP_AHRS_SIM: zero

    struct {
        AP_Float roll;
        AP_Float pitch;
        AP_Float yaw;
    } sim_ahrs_offset;

    // the simulator's SIMSTATE / SIM_STATE messages: not sent (the true state stays outside)
    void simstate_send(mavlink_channel_t chan) const {}
    void sim_state_send(mavlink_channel_t chan) const {}
    void Log_Write_SIMSTATE() {}

    bool get_mag_offsets_for_devid(uint32_t devid, Vector3f &offsets) const;
};

} // namespace SITL

namespace AP {
    SITL::SIM *sitl();
};

#endif // AP_SIM_ENABLED
