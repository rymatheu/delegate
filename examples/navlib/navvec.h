// cpp2lean demo library (a --lib-dir for examples/navigate.cpp): a value class in the form of
// AP_Math's Vector2/Vector3 (vector3.h), translated only as far as the example uses it.
#pragma once
#include <cmath>

class NV2 {
public:
    double x, y;
    constexpr NV2() : x(0), y(0) {}
    constexpr NV2(double x0, double y0) : x(x0), y(y0) {}
    void zero() { x = 0; y = 0; }
};

class NV3 {
public:
    double x, y, z;
    constexpr NV3() : x(0), y(0), z(0) {}
    constexpr NV3(double x0, double y0, double z0) : x(x0), y(y0), z(z0) {}
    NV3 operator+(const NV3 &v) const { return NV3(x + v.x, y + v.y, z + v.z); }
    NV3 operator-(const NV3 &v) const { return NV3(x - v.x, y - v.y, z - v.z); }
    NV3 operator*(const double k) const { return NV3(x * k, y * k, z * k); }
    double length() const { return sqrt(x * x + y * y + z * z); }
    // a writable view of the first two members (vector3.h:316-323)
    const NV2 &xy() const { return *(const NV2 *)this; }
    NV2 &xy() { return *(NV2 *)this; }
};
