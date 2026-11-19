#include <cmath>

float constrain_float(float v, float lo, float hi) {
    if (std::isnan(v)) return (lo + hi) * 0.5f;
    if (v < lo) return lo;
    if (v > hi) return hi;
    return v;
}

// ArduPilot's angle boost: the thrust the motors get, from the thrust asked for
float throttle_boosted(float throttle_in, float cos_pitch, float cos_roll, float thrust_angle) {
    float cos_tilt = cos_pitch * cos_roll;
    float inverted_factor = constrain_float(10.0f * cos_tilt, 0.0f, 1.0f);
    float cos_tilt_target = cosf(thrust_angle);
    float boost_factor = 1.0f / constrain_float(cos_tilt_target, 0.1f, 1.0f);
    return throttle_in * inverted_factor * boost_factor;
}

// half-angle sine the way the C++ compiles it: double trig, narrowed
float half_angle_sin(float theta) {
    return (float)sin(0.5 * theta);
}
