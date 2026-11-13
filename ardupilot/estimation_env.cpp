// The C++ environment of the estimator World's difftest (ardupilot/Estimation.json; README.md "Phase 3: the estimator
// World and the EKF3 replay"): the sensor World's environment (ardupilot/sensors_env.cpp, included) plus what AP_DAL and
// NavEKF3 reach outside the translation, compiled with the reference build's flags against the real headers:
//   - the HAL's Util answers AP_DAL's memory queries: `available_memory` the line's input, `malloc_type` (the EKF3
//     cores, AP_NavEKF3.cpp:850) zeroed memory recorded as the driver records `malloc` (a heap slot of the World);
//   - AP::ahrs(): the members AP_DAL::start_frame reads (AP_DAL.cpp:56-80: home, vehicle class, fly forward, takeoff and
//     touchdown expected, trim, configured EKF type, the vehicle-to-autopilot body rotation) are data members of the
//     never-constructed object's storage, set from the line's inputs; `set_takeoff_expected` is recorded in the output log;
//   - AP::vehicle(): its storage, whose `likely_flying` and `_last_flying_ms` give the line's time flying through
//     AP_Vehicle::get_time_flying_ms (AP_Vehicle.h:175); AP::wheelencoder(): none;
//   - AP_BoardConfig::allocation_error: never reached (allocation does not fail here).
#include <AP_HAL/AP_HAL.h>
#include <cstdlib>
#include <cstring>
void *cpp2lean_env_raw_alloc(size_t n);       // the driver's (Estimation.json "globals"): malloc recorded, zeroed
uint32_t cpp2lean_available_memory = 512 * 1024;      // a constant input (Estimation.json "const_inputs"): the reference HAL's
#define CPP2LEAN_ENV_UTIL_EXTRA \
    uint32_t available_memory(void) override { return cpp2lean_available_memory; } \
    void *malloc_type(size_t size, Memory_Type) override { return cpp2lean_env_raw_alloc(size); } \
    void free_type(void *, size_t, Memory_Type) override {}
#include "sensors_env.cpp"
#include <AP_Vehicle/AP_Vehicle.h>
#include <AP_WheelEncoder/AP_WheelEncoder.h>
#include <AP_BoardConfig/AP_BoardConfig.h>

// AP_AHRS's storage (sensors_env.cpp: never constructed), the members AP_DAL reads through inline getters
static AP_AHRS &env_ahrs() { return AP::ahrs(); }
void cpp2lean_ahrs_home(int part, long long v)
{
    Location &h = env_ahrs()._home;
    switch (part) {
    case 0: h.relative_alt = v; break;
    case 1: h.loiter_ccw = v; break;
    case 2: h.terrain_alt = v; break;
    case 3: h.origin_alt = v; break;
    case 4: h.loiter_xtrack = v; break;
    case 5: h.alt = v; break;
    case 6: h.lat = v; break;
    case 7: h.lng = v; break;
    }
}
void cpp2lean_ahrs_vehicle_class(unsigned v) { env_ahrs()._vehicle_class = AP_AHRS::VehicleClass(v); }
void cpp2lean_ahrs_fly_forward(bool v) { env_ahrs().fly_forward = v; }
void cpp2lean_ahrs_takeoff_expected(bool v) { env_ahrs().takeoff_expected = v; }
void cpp2lean_ahrs_touchdown_expected(bool v) { env_ahrs().touchdown_expected = v; }
void cpp2lean_ahrs_ekf_type(int v) { env_ahrs().state.configured_ekf_type = AP_AHRS::EKFType(v); }
void cpp2lean_ahrs_trim(int k, float v)
{
    Vector3f t = env_ahrs()._trim.get();
    (k == 0 ? t.x : k == 1 ? t.y : t.z) = v;
    env_ahrs()._trim.set(t);
}
void cpp2lean_ahrs_rot(int row, int k, float v)
{
    Vector3f &r = row == 0 ? env_ahrs()._rotation_vehicle_body_to_autopilot_body.a : row == 1 ? env_ahrs()._rotation_vehicle_body_to_autopilot_body.b
                                                                                              : env_ahrs()._rotation_vehicle_body_to_autopilot_body.c;
    (k == 0 ? r.x : k == 1 ? r.y : r.z) = v;
}
void AP_AHRS::set_takeoff_expected(bool b) { cpp2lean_ev("set_takeoff_expected"); cpp2lean_ev_b(b); }

// AP_Vehicle (abstract): its storage, read through its inline getter get_time_flying_ms only
alignas(16) static unsigned char vehicle_storage[sizeof(AP_Vehicle)];
AP_Vehicle *AP::vehicle() { return reinterpret_cast<AP_Vehicle *>(vehicle_storage); }
void cpp2lean_time_flying(uint32_t ms)
{
    AP_Vehicle *v = AP::vehicle();
    v->likely_flying = ms != 0;
    v->_last_flying_ms = AP_HAL::millis() - ms;
}
AP_WheelEncoder *AP::wheelencoder() { return nullptr; }
void AP_BoardConfig::allocation_error(const char *fmt, ...) { abort(); }
