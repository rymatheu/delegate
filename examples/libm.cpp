// cpp2lean demo: every function of the C library that the translations call, one wrapper each, so
// that the differential test compares each on its own (corner values: zeros, subnormals, huge values
// that take the large-argument reduction of sin and cos, infinities, NaNs). The functions that IEEE
// 754 defines exactly are FloatLib operations in Lean (CFloat.lean); the others are the translation
// of musl's C sources (libm/, Musl.lean), and the C++ side links the same musl sources
// (libm/build_musl.sh), so both sides run the same algorithm (README.md, "The C library").
#include <cmath>

float f_sinf(float x) { return sinf(x); }
float f_cosf(float x) { return cosf(x); }
float f_tanf(float x) { return tanf(x); }
float f_asinf(float x) { return asinf(x); }
float f_acosf(float x) { return acosf(x); }
float f_atanf(float x) { return atanf(x); }
float f_atan2f(float y, float x) { return atan2f(y, x); }
float f_expf(float x) { return expf(x); }
float f_logf(float x) { return logf(x); }
float f_log2f(float x) { return log2f(x); }
float f_powf(float x, float y) { return powf(x, y); }
float f_fmodf(float x, float y) { return fmodf(x, y); }
double f_sin(double x) { return sin(x); }
double f_cos(double x) { return cos(x); }
double f_tan(double x) { return tan(x); }
double f_asin(double x) { return asin(x); }
double f_acos(double x) { return acos(x); }
double f_atan(double x) { return atan(x); }
double f_atan2(double y, double x) { return atan2(y, x); }
double f_exp(double x) { return exp(x); }
double f_log(double x) { return log(x); }
double f_log2(double x) { return log2(x); }
double f_pow(double x, double y) { return pow(x, y); }
double f_fmod(double x, double y) { return fmod(x, y); }

// IEEE 754's exact functions: musl's C sources on the C++ side, FloatLib's operations in Lean.
float f_sqrtf(float x) { return sqrtf(x); }
float f_fabsf(float x) { return fabsf(x); }
float f_fminf(float x, float y) { return fminf(x, y); }
float f_fmaxf(float x, float y) { return fmaxf(x, y); }
float f_floorf(float x) { return floorf(x); }
float f_ceilf(float x) { return ceilf(x); }
float f_truncf(float x) { return truncf(x); }
float f_roundf(float x) { return roundf(x); }
float f_copysignf(float x, float y) { return copysignf(x, y); }
float f_scalbnf(float x, int n) { return scalbnf(x, n); }
double f_sqrt(double x) { return sqrt(x); }
double f_fabs(double x) { return fabs(x); }
double f_fmin(double x, double y) { return fmin(x, y); }
double f_fmax(double x, double y) { return fmax(x, y); }
double f_floor(double x) { return floor(x); }
double f_ceil(double x) { return ceil(x); }
double f_trunc(double x) { return trunc(x); }
double f_round(double x) { return round(x); }
double f_copysign(double x, double y) { return copysign(x, y); }
double f_scalbn(double x, int n) { return scalbn(x, n); }
