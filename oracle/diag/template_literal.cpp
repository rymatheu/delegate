// Evidence for the port deviation in RESULTS.md: Apple clang applies -cl-single-precision-constant
// to a floating literal in ordinary code but not inside a function template, and the AP_Math types
// are templates (QuaternionT<T>, Vector3<T>, ...). With HAL_WITH_EKF_DOUBLE, ftype.h:15-21 makes
// sinF/cosF plain sin/cos, so QuaternionT<float>::from_axis_angle (quaternion.cpp:477, :479)
// computes (float)sin((double)theta * 0.5). Compile with
//   clang++ -std=gnu++11 -O2 -cl-single-precision-constant -ffp-contract=off -S -o - template_literal.cpp
// and read the calls: plain() calls sinf, templated<float>() converts to double and calls sin.
#include <cmath>

float plain(float theta) { return sin(0.5*theta); }

template <typename T> T templated(T theta) { return sin(0.5*theta); }
template float templated<float>(float);
