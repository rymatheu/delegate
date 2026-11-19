// stubs_sensors.cpp: the vehicle's other libraries the estimation chain consults, and what stands in.
//
// ArduCopter has an airspeed library, a rangefinder, beacons, visual odometry, optical flow, wheel
// encoders, the gyro FFT, the motors, the battery monitor, terrain data, the mission store, the
// real-time clock, the serial manager, custom rotations, the accelerometer and compass calibrators.
// None is part of the estimation chain; the X500 in the plant has none of the optional sensors.
// Each stand-in answers as ArduCopter's own object does with that sensor absent or that feature at
// its default; what the estimator never calls aborts.
//
//   symbol                                   why it is outside the module, and what stands in
//   AP::airspeed() (AP_Airspeed)             the airspeed library, ARSPD_TYPE 0 (no sensor):
//                                            healthy, use and get_temperature false, airspeed 0.
//   AP::rangefinder, beacon, visualodom,     optional sensors: null, the value their accessors
//   opticalflow, wheelencoder (pointers)     have when the library is absent; every caller (AP_DAL)
//                                            tests for null. RangeFinder, AP_Beacon, AP_VisualOdom
//                                            methods are reached only through a DAL part that is
//                                            created when the sensor exists: abort.
//   AP::fft(), AP::motors()                  the gyro FFT (absent) and the motors (another stage;
//                                            the INS reads them only for a harmonic notch tracking
//                                            the motors, INS_HNTCH_ENABLE 0): null.
//   AP::battery(), current_amps              the battery monitor: the compass's motor-interference
//                                            compensation reads the current (COMPASS_MOTCT 0, not
//                                            used): no current (false).
//   AP::terrain() (pointer)                  terrain data: null, as with TERRAIN_ENABLE 0 in the
//                                            code paths that test it (Location::get_alt_cm).
//   AP::mission(), write_home_to_storage     the mission store: AP_AHRS::set_home writes home as
//                                            item 0. Dropped (storage).
//   AP::rtc(), AP_RTC::set_utc_usec          the real-time clock the GPS sets: dropped.
//   AP::serialmanager(), find_serial         serial ports: the first GPS port is the GPS's (a sink,
//                                            stubs_hal.cpp), every other none (nullptr).
//   AP::custom_rotations(), rotate           custom board rotations (ROTATION_CUSTOM_*): abort.
//   AP_AccelCal::register_client             the accelerometer calibrator's client list (the INS
//                                            registers itself): nothing kept; running() aborts (it
//                                            is reached only while a calibration runs).
//   AccelCalibrator::*, CompassCalibrator::  calibration procedures started from the ground
//   new_sample, Compass::mag_cal_fixed_yaw   station: abort.
//   Compass::is_calibrating                  false: no compass calibration is running.
//   SRV_Channels::find_channel,              per-motor compass compensation (COMPASS_PMOT_EN 0):
//   RCOutput::scale_esc_to_unity             abort.
#include <stdio.h>
#include <stdlib.h>

#include <AP_HAL/AP_HAL.h>
#include <AP_AccelCal/AP_AccelCal.h>
#include <AP_AccelCal/AccelCalibrator.h>
#include <AP_Airspeed/AP_Airspeed.h>
#include <AP_BattMonitor/AP_BattMonitor.h>
#include <AP_Beacon/AP_Beacon.h>
#include <AP_Compass/AP_Compass.h>
#include <AP_Compass/CompassCalibrator.h>
#include <AP_CustomRotations/AP_CustomRotations.h>
#include <AP_GyroFFT/AP_GyroFFT.h>
#include <AP_Mission/AP_Mission.h>
#include <AP_Motors/AP_Motors_Class.h>
#include <AP_OpticalFlow/AP_OpticalFlow.h>
#include <AP_RangeFinder/AP_RangeFinder.h>
#include <AP_RangeFinder/AP_RangeFinder_Backend.h>
#include <AP_RTC/AP_RTC.h>
#include <AP_SerialManager/AP_SerialManager.h>
#include <AP_Terrain/AP_Terrain.h>
#include <AP_VisualOdom/AP_VisualOdom.h>
#include <AP_WheelEncoder/AP_WheelEncoder.h>
#include <SRV_Channel/SRV_Channel.h>

__attribute__((noreturn)) static void unreachable(const char *what)
{
    fprintf(stderr, "estimator: cut symbol reached: %s\n", what);
    abort();
}

template <typename T>
static T &storage_object()
{
    alignas(T) static unsigned char s[sizeof(T)];
    return *reinterpret_cast<T *>(s);
}

// --- airspeed library, no sensor
AP_Airspeed &AP::airspeed() { return storage_object<AP_Airspeed>(); }
float AP_Airspeed::get_airspeed(uint8_t i) const { return 0.0f; }
bool AP_Airspeed::get_temperature(uint8_t i, float &temperature) const { return false; }
bool AP_Airspeed::use(uint8_t i) const { return false; }
bool AP_Airspeed::healthy(uint8_t i) const { return false; }

// --- optional sensors, absent
RangeFinder *AP::rangefinder() { return nullptr; }
AP_Beacon *AP::beacon() { return nullptr; }
AP_VisualOdom *AP::visualodom() { return nullptr; }
AP_OpticalFlow *AP::opticalflow() { return nullptr; }
AP_WheelEncoder *AP::wheelencoder() { return nullptr; }
AP_GyroFFT *AP::fft() { return nullptr; }
AP_Motors *AP::motors() { return nullptr; }

AP_RangeFinder_Backend *RangeFinder::get_backend(uint8_t id) const { unreachable("RangeFinder"); }
float RangeFinder::max_distance_orient(enum Rotation orientation) const { unreachable("RangeFinder"); }
float RangeFinder::ground_clearance_orient(enum Rotation orientation) const { unreachable("RangeFinder"); }
RangeFinder::Status AP_RangeFinder_Backend::status() const { unreachable("RangeFinder"); }
bool AP_Beacon::enabled(void) const { unreachable("AP_Beacon"); }
bool AP_Beacon::get_origin(Location &origin_loc) const { unreachable("AP_Beacon"); }
bool AP_Beacon::get_vehicle_position_ned(Vector3f &pos, float &accuracy_estimate) const { unreachable("AP_Beacon"); }
uint8_t AP_Beacon::count() const { unreachable("AP_Beacon"); }
bool AP_Beacon::beacon_healthy(uint8_t beacon_instance) const { unreachable("AP_Beacon"); }
float AP_Beacon::beacon_distance(uint8_t beacon_instance) const { unreachable("AP_Beacon"); }
Vector3f AP_Beacon::beacon_position(uint8_t beacon_instance) const { unreachable("AP_Beacon"); }
uint32_t AP_Beacon::beacon_last_update_ms(uint8_t beacon_instance) const { unreachable("AP_Beacon"); }
bool AP_VisualOdom::enabled() const { unreachable("AP_VisualOdom"); }
bool AP_VisualOdom::healthy() const { unreachable("AP_VisualOdom"); }
void AP_VisualOdom::align_position_to_ahrs(bool align_xy, bool align_z) { unreachable("AP_VisualOdom"); }

// --- battery monitor
AP_BattMonitor &AP::battery() { return storage_object<AP_BattMonitor>(); }
bool AP_BattMonitor::current_amps(float &current, const uint8_t instance) const { return false; }

// --- terrain, mission, clock, serial ports
AP_Terrain *AP::terrain() { return nullptr; }
bool AP_Terrain::height_amsl(const Location &loc, float &height, bool corrected) { unreachable("AP_Terrain"); }
AP_Mission &AP::mission() { return storage_object<AP_Mission>(); }
void AP_Mission::write_home_to_storage() {}
AP_RTC &AP::rtc() { return storage_object<AP_RTC>(); }
void AP_RTC::set_utc_usec(uint64_t time_utc_usec, source_type type) {}
AP_SerialManager &AP::serialmanager() { return storage_object<AP_SerialManager>(); }
AP_HAL::UARTDriver *harness_gps_port();
AP_HAL::UARTDriver *AP_SerialManager::find_serial(enum SerialProtocol protocol, uint8_t instance) const
{
    // SITL's serial ports: SERIAL3 carries the GPS (SERIAL3_PROTOCOL 5); nothing else is asked for
    if (protocol == SerialProtocol_GPS && instance == 0) {
        return harness_gps_port();
    }
    return nullptr;
}

// --- custom rotations
AP_CustomRotations &AP::custom_rotations() { return storage_object<AP_CustomRotations>(); }
void AP_CustomRotations::rotate(enum Rotation r, Vector3f &v) { unreachable("AP_CustomRotations"); }

// --- calibrators
void AP_AccelCal::register_client(AP_AccelCal_Client *client) {}
bool AP_AccelCal::running(void) const { unreachable("AP_AccelCal::running"); }
void AccelCalibrator::new_sample(const Vector3f &delta_velocity, float dt) { unreachable("AccelCalibrator"); }
void AccelCalibrator::get_calibration(Vector3f &offset, Vector3f &diag) const { unreachable("AccelCalibrator"); }
bool AccelCalibrator::get_sample_corrected(uint8_t i, Vector3f &s) const { unreachable("AccelCalibrator"); }
void CompassCalibrator::new_sample(const Vector3f &sample) { unreachable("CompassCalibrator"); }
bool Compass::is_calibrating() const { return false; }
bool Compass::mag_cal_fixed_yaw(float yaw_deg, uint8_t compass_mask, float lat_deg, float lon_deg,
                                bool force_use)
{
    unreachable("Compass::mag_cal_fixed_yaw");
}

// --- per-motor compass compensation
bool SRV_Channels::find_channel(SRV_Channel::Function function, uint8_t &chan) { unreachable("SRV_Channels"); }
float AP_HAL::RCOutput::scale_esc_to_unity(uint16_t pwm) const { unreachable("RCOutput"); }
