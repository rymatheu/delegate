// stubs_sensors.cpp: the estimator stage's sensor front ends as shadows (AP_GPS, AP_Baro,
// AP_InertialSensor): the state their inline getters and the ground-station senders read,
// written from the input record, and hand-written answers to their out-of-line queries.
//
//   GPS (AP_GPS::state[0], primary_instance 0, num_instances 1)
//     status, num_sats          est_gps_status, est_gps_num_sats (the estimator's GPS front end)
//     location, velocity        the simulator's GPS sample (gps_lat_e7, gps_lon_e7, gps_alt,
//                               gps_vn/ve/vd), held from the last fresh one (5 Hz)
//     ground_speed, ground_course   from that velocity
//     hdop, vdop                est_gps_hdop, est_gps_vdop
//     last_gps_time_ms          the time of the last fresh sample
//   GPS_RAW_INT: the real AP_GPS::send_mavlink_gps_raw with its accuracy getters (gen/
//   COPY_REAL) on that state; GPS1_TYPE from the real parameter table and the record.
//   AP_GPS::is_healthy(0): est_gps_healthy.
//
//   Barometer (sensors[0], _num_sensors 1, _primary 0)
//     altitude                  est_baro_alt (the estimator's barometer front end)
//     pressure, temperature     the simulator's sample (baro_pa, baro_degc), held from the last
//                               fresh one (before the first: the standard atmosphere at the
//                               origin altitude, 25 degC)
//     healthy, alt_ok, calibrated  est_baro_healthy; AP_Baro::all_healthy too
//
//   IMU (_accel[0], _gyro[0], counts 1, first usable 0)
//     _accel[0], _gyro[0]       est_accel_*, est_gyro_* (the estimator's INS samples)
//     _accel_healthy, _gyro_healthy  est_ins_accel_healthy, est_ins_gyro_healthy
//   answers: calibrating false; accel/gyro_calibrated_ok_all true (constant: no calibration in
//   the simulator); get_accel_health_all, get_gyro_health_all = est_ins_*_healthy;
//   get_vibration_levels = est_vibe_*; get_accel_clip_count = est_accel_clip_count.
//
// Compass: no signal; the shadow has no compass instance (count 0), so COMPASS and the mag
// fields of RAW_IMU report nothing (listed as missing).
#include <AP_GPS/AP_GPS.h>
#include <AP_Baro/AP_Baro.h>
#include <AP_InertialSensor/AP_InertialSensor.h>
#include "supervisor_shadow.h"
#include "module_records.h"

HARNESS_ADDR(AP_GPS, state)
HARNESS_ADDR(AP_GPS, primary_instance)
HARNESS_ADDR(AP_GPS, num_instances)
HARNESS_ADDR(AP_InertialSensor, _accel)
HARNESS_ADDR(AP_InertialSensor, _gyro)
HARNESS_ADDR(AP_InertialSensor, _accel_count)
HARNESS_ADDR(AP_InertialSensor, _gyro_count)
HARNESS_ADDR(AP_InertialSensor, _accel_healthy)
HARNESS_ADDR(AP_InertialSensor, _gyro_healthy)
HARNESS_ADDR(AP_InertialSensor, _first_usable_accel)
HARNESS_ADDR(AP_InertialSensor, _first_usable_gyro)
HARNESS_ADDR(AP_Baro, _num_sensors)
HARNESS_ADDR(AP_Baro, _primary)

// AP_Baro::sensors[] has an unnamed element type: its fields are written inside a friend of
// an explicit instantiation, where the member pointer names them
void harness_baro_fill(AP_Baro &b, float alt, float pressure, float temperature, uint32_t now,
                       bool healthy);
template <typename T, T M>
struct HarnessBaroSensors {
    friend void harness_baro_fill(AP_Baro &b, float alt, float pressure, float temperature,
                                  uint32_t now, bool healthy)
    {
        auto &s = (b.*M)[0];
        s.altitude = alt;
        s.pressure = pressure;
        s.temperature = temperature;
        s.healthy = healthy;
        s.alt_ok = true;
        s.calibrated = true;
        s.last_update_ms = now;
        s.last_change_ms = now;
    }
};
template struct HarnessBaroSensors<decltype(&AP_Baro::sensors), &AP_Baro::sensors>;

static Input sens;

void harness_sensors_fill(const Input &in)
{
    sens = in;
    AP_GPS *g = AP_GPS::get_singleton();
    if (g != nullptr) {
        AP_GPS::GPS_State &st = (&HARNESS_REF(AP_GPS::GPS_State, *g, AP_GPS, state))[0];
        st.instance = 0;
        st.status = AP_GPS_FixType(in.est_gps_status);
        st.num_sats = uint8_t(in.est_gps_num_sats);
        if (in.gps_fresh) {
            st.location = Location(in.gps_lat_e7, in.gps_lon_e7,
                                   int32_t(lroundf(in.gps_alt * 100)), Location::AltFrame::ABSOLUTE);
            st.velocity = Vector3f(in.gps_vn, in.gps_ve, in.gps_vd);
            st.ground_speed = st.velocity.xy().length();
            st.ground_course = wrap_360(degrees(atan2f(in.gps_ve, in.gps_vn)));
            st.last_gps_time_ms = in.now_ms;
        }
        st.hdop = uint16_t(in.est_gps_hdop);
        st.vdop = uint16_t(in.est_gps_vdop);
        st.have_vertical_velocity = true;
        HARNESS_REF(uint8_t, *g, AP_GPS, primary_instance) = 0;
        HARNESS_REF(uint8_t, *g, AP_GPS, num_instances) = 1;
    }
    AP_InertialSensor *ins = AP_InertialSensor::get_singleton();
    if (ins != nullptr) {
        (&HARNESS_REF(Vector3f, *ins, AP_InertialSensor, _accel))[0] =
            Vector3f(in.est_accel_x, in.est_accel_y, in.est_accel_z);
        (&HARNESS_REF(Vector3f, *ins, AP_InertialSensor, _gyro))[0] =
            Vector3f(in.est_gyro_x, in.est_gyro_y, in.est_gyro_z);
        HARNESS_REF(uint8_t, *ins, AP_InertialSensor, _accel_count) = 1;
        HARNESS_REF(uint8_t, *ins, AP_InertialSensor, _gyro_count) = 1;
        (&HARNESS_REF(bool, *ins, AP_InertialSensor, _accel_healthy))[0] = in.est_ins_accel_healthy;
        (&HARNESS_REF(bool, *ins, AP_InertialSensor, _gyro_healthy))[0] = in.est_ins_gyro_healthy;
        HARNESS_REF(uint8_t, *ins, AP_InertialSensor, _first_usable_accel) = 0;
        HARNESS_REF(uint8_t, *ins, AP_InertialSensor, _first_usable_gyro) = 0;
    }
    AP_Baro *b = AP_Baro::get_singleton();
    if (b != nullptr) {
        static float pa = -1, degc = 25;
        if (in.baro_fresh) {
            pa = in.baro_pa;
            degc = in.baro_degc;
        } else if (pa < 0) {   // before the first sample: the standard atmosphere
            const float h = in.est_origin_alt_cm * 0.01f;
            pa = 101325.0f * powf(1.0f - 2.25577e-5f * h, 5.25588f);
        }
        harness_baro_fill(*b, in.est_baro_alt, pa, degc, in.now_ms, in.est_baro_healthy);
        HARNESS_REF(uint8_t, *b, AP_Baro, _num_sensors) = 1;
        HARNESS_REF(uint8_t, *b, AP_Baro, _primary) = 0;
    }
}

bool AP_GPS::is_healthy(uint8_t instance) const
{
    return instance == 0 && sens.est_gps_healthy;
}

bool AP_InertialSensor::calibrating() const { return false; }
bool AP_InertialSensor::accel_calibrated_ok_all() const { return true; }
bool AP_InertialSensor::get_accel_health_all(void) const { return sens.est_ins_accel_healthy; }
bool AP_InertialSensor::get_gyro_health_all(void) const { return sens.est_ins_gyro_healthy; }
Vector3f AP_InertialSensor::get_vibration_levels(uint8_t instance) const
{
    return Vector3f(sens.est_vibe_x, sens.est_vibe_y, sens.est_vibe_z);
}
uint32_t AP_InertialSensor::get_accel_clip_count(uint8_t instance) const
{
    return sens.est_accel_clip_count;
}

bool AP_Baro::all_healthy(void) const { return sens.est_baro_healthy; }
bool AP_InertialSensor::gyro_calibrated_ok_all() const { return true; }
