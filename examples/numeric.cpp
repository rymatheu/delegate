// cpp2lean demo (phase 1): free functions over numbers. Bodies marked "ArduPilot" follow the
// ArduPilot source at the cited lines (commit 802db19de1); the rest is written for the demo.
#include <cfloat>
#include <cmath>

// ArduPilot AP_Math.cpp:282-304, constrain_value_line<float>: NaN maps to the midpoint.
float constrain_float(float amt, float low, float high)
{
    if (isnan(amt)) {
        return (low + high) / 2;
    }
    if (amt < low) {
        return low;
    }
    if (amt > high) {
        return high;
    }
    return amt;
}

// ArduPilot ftype.h:61-63, is_zero(float).
bool is_zero(float x) { return fabsf(x) < FLT_EPSILON; }

// ArduPilot AP_Math.cpp:72-81, safe_sqrt<double> (isgreaterequal(val, 0) written as val >= 0).
float safe_sqrt(double v)
{
    const float val = static_cast<float>(v);
    if (val >= 0) {
        return sqrtf(val);
    }
    return 0;
}

// ArduPilot AP_Motors_Thrust_Linearization.cpp:119-133, apply_thrust_curve_and_volt_scaling with
// battery_scale = 1: solves thrust = (1-e)*u + e*u^2 for u. The literals are doubles, as there.
float thrust_curve(float thrust, float expo, float lift_max)
{
    float thrust_curve_expo = constrain_float(expo, -1.0, 1.0);
    if (is_zero(thrust_curve_expo)) {
        return lift_max * thrust;
    }
    float throttle_ratio = ((thrust_curve_expo - 1.0) + safe_sqrt((1.0 - thrust_curve_expo) * (1.0 - thrust_curve_expo) + 4.0 * thrust_curve_expo * lift_max * thrust)) / (2.0 * thrust_curve_expo);
    return constrain_float(throttle_ratio, 0.0, 1.0);
}

// Horner evaluation of a fixed polynomial, coefficients from a constant array.
static const float horner_coeffs[5] = {1.0f, -0.5f, 0.25f, -0.125f, 0.0625f};

float horner(float x)
{
    float acc = 0.0f;
    for (int i = 0; i < 5; i++) {
        acc = acc * x + horner_coeffs[4 - i];
    }
    return acc;
}

// Single precision throughout, then the float -> double -> float chain of mixed code.
float half_angle_sin(float theta) { return sinf(0.5f * theta); }
float half_angle_sin_d(float theta) { return (float)sin(0.5 * theta); }

// Early returns, a ternary, and a bounded loop with break and continue.
int clamp_steps(int n, float x)
{
    if (n <= 0) {
        return 0;
    }
    if (isnan(x)) return -1;
    int steps = n > 8 ? 8 : n;
    int count = 0;
    float y = x;
    for (int i = 0; i < 8; ++i) {
        if (i >= steps) break;
        y *= 0.5f;
        if (fabsf(y) < 1.0f) continue;
        count += i;
    }
    return 2 * count + (y > 0 ? 1 : 0);
}
