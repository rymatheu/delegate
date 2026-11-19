// stubs_params.cpp: other stages' parameters are read-only from the ground station (decision 3).
//
// The other stages get their parameters at init only, so a PARAM_SET of one of them is refused
// the way ArduPilot refuses a parameter marked @READONLY in a defaults file: AP_Param's
// param_overrides table (AP_Param.h) gets an entry with read_only = true for every parameter
// that lives inside a shadow object (the AHRS, IMU, GPS, barometer and compass front ends, the
// EKF3, the attitude, position, waypoint, loiter and circle controllers with their PIDs, the
// motors). GCS_MAVLINK::handle_param_set then answers with STATUSTEXT "Param write denied
// (NAME)", PARAM_ERROR(MAV_PARAM_ERROR_PERMISSION_DENIED) and PARAM_VALUE with the unchanged
// value (GCS_Param.cpp). harness_param_set_seen counts such requests from the received bytes.
// Side effect: AP_Param::configured() is true for these parameters (they count as set in a
// defaults file); no covered code path of the supervisor asks.
#include <AP_Param/AP_Param.h>
#include "Copter.h"
#include "supervisor_shadow.h"

// AP_Param's private static table, built inside a friend of an explicit instantiation (its
// element type is private: named here only through the member pointer's type)
#include <type_traits>
void harness_set_overrides(AP_Param *const *ptrs, const float *vals, uint16_t n);
template <typename T, T P1, typename U, U P2, typename V, V P3, typename W, W P4>
struct HarnessParamStatics {
    friend void harness_set_overrides(AP_Param *const *ptrs, const float *vals, uint16_t n)
    {
        typedef typename std::remove_pointer<typename std::remove_pointer<T>::type>::type E;
        E *table = static_cast<E *>(calloc(n + 1, sizeof(E)));
        for (uint16_t k = 0; k < n; k++) {
            table[k].object_ptr = ptrs[k];
            table[k].value = vals[k];
            table[k].read_only = true;
        }
        *P1 = table;
        *P2 = n;
        *P3 = n;
        *P4 = n;
    }
};
template struct HarnessParamStatics<
    decltype(&AP_Param::param_overrides), &AP_Param::param_overrides,
    decltype(&AP_Param::num_param_overrides), &AP_Param::num_param_overrides,
    decltype(&AP_Param::param_overrides_len), &AP_Param::param_overrides_len,
    decltype(&AP_Param::num_read_only), &AP_Param::num_read_only>;

HARNESS_ADDR(Copter, attitude_control)
HARNESS_ADDR(Copter, pos_control)
HARNESS_ADDR(Copter, wp_nav)
HARNESS_ADDR(Copter, loiter_nav)
HARNESS_ADDR(Copter, circle_nav)

struct Range {
    const uint8_t *lo, *hi;
};
static Range ranges[16];
static uint32_t nranges;

static void add(const void *p, size_t n)
{
    if (p != nullptr && nranges < 16) {
        ranges[nranges].lo = static_cast<const uint8_t *>(p);
        ranges[nranges].hi = ranges[nranges].lo + n;
        nranges++;
    }
}

bool harness_param_is_other_stage(const AP_Param *vp)
{
    const uint8_t *p = reinterpret_cast<const uint8_t *>(vp);
    for (uint32_t k = 0; k < nranges; k++) {
        if (p >= ranges[k].lo && p < ranges[k].hi) {
            return true;
        }
    }
    return false;
}


uint32_t harness_params_readonly_init()
{
    nranges = 0;
    add(&AP::ahrs(), sizeof(AP_AHRS));
    add(&AP::ins(), sizeof(AP_InertialSensor));
    add(&AP::gps(), sizeof(AP_GPS));
    add(&AP::baro(), sizeof(AP_Baro));
    add(&AP::compass(), sizeof(Compass));
    add(&AP_AHRS_NavEKF3::EKF3, sizeof(NavEKF3));
    add(HARNESS_REF(AC_AttitudeControl *, copter, Copter, attitude_control),
        sizeof(AC_AttitudeControl_Multi));
    add(HARNESS_REF(AC_PosControl *, copter, Copter, pos_control), sizeof(AC_PosControl));
    add(HARNESS_REF(AC_WPNav *, copter, Copter, wp_nav), sizeof(AC_WPNav));
    add(HARNESS_REF(AC_Loiter *, copter, Copter, loiter_nav), sizeof(AC_Loiter));
    add(HARNESS_REF(AC_Circle *, copter, Copter, circle_nav), sizeof(AC_Circle));
    add(AP::motors(), sizeof(AP_MotorsMatrix));
    uint32_t n = 0;
    AP_Param::ParamToken token;
    enum ap_var_type type;
    for (AP_Param *vp = AP_Param::first(&token, &type); vp != nullptr;
         vp = AP_Param::next_scalar(&token, &type)) {
        if (harness_param_is_other_stage(vp)) {
            n++;
        }
    }
    AP_Param **ptrs = static_cast<AP_Param **>(calloc(n + 1, sizeof(AP_Param *)));
    float *vals = static_cast<float *>(calloc(n + 1, sizeof(float)));
    uint32_t k = 0;
    for (AP_Param *vp = AP_Param::first(&token, &type); vp != nullptr;
         vp = AP_Param::next_scalar(&token, &type)) {
        if (harness_param_is_other_stage(vp) && k < n) {
            ptrs[k] = vp;
            vals[k] = vp->cast_to_float(type);
            k++;
        }
    }
    harness_set_overrides(ptrs, vals, uint16_t(k));
    return k;
}

// PARAM_SET requests in the received bytes whose parameter is another stage's
static mavlink_message_t rx_msg;
static mavlink_status_t rx_status;
uint32_t harness_param_set_refused;

void harness_param_scan(const uint8_t *b, size_t n)
{
    for (size_t k = 0; k < n; k++) {
        mavlink_message_t msg;
        mavlink_status_t st;
        if (mavlink_frame_char_buffer(&rx_msg, &rx_status, b[k], &msg, &st) ==
                MAVLINK_FRAMING_OK &&
            msg.msgid == MAVLINK_MSG_ID_PARAM_SET) {
            mavlink_param_set_t ps;
            mavlink_msg_param_set_decode(&msg, &ps);
            char key[AP_MAX_NAME_SIZE + 1];
            strncpy(key, ps.param_id, AP_MAX_NAME_SIZE);
            key[AP_MAX_NAME_SIZE] = 0;
            enum ap_var_type t;
            AP_Param *vp = AP_Param::find(key, &t);
            if (vp != nullptr && harness_param_is_other_stage(vp)) {
                harness_param_set_refused++;
            }
        }
    }
}
