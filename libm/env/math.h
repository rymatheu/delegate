/* cpp2lean: the part of <math.h> that musl's src/math files use, for compiling and translating them
   outside musl's build (libm/README in cpp2lean/README.md, "The C library"). musl's own include/math.h
   classifies through unions and sizeof dispatch; here the classification macros are clang's builtins,
   which compute the same predicates. Constants and types are those of musl's include/math.h and of
   arch/aarch64 (FLT_EVAL_METHOD == 0). */
#ifndef CPP2LEAN_MUSL_MATH_H
#define CPP2LEAN_MUSL_MATH_H

/* musl src/include/features.h */
#ifndef hidden
#define hidden __attribute__((__visibility__("hidden")))
#endif

typedef float float_t;
typedef double double_t;

#define INFINITY __builtin_inff()
#define NAN __builtin_nanf("")
#define M_PI_2 1.57079632679489661923

#define isnan(x) __builtin_isnan(x)
#define signbit(x) __builtin_signbit(x)

float sinf(float);
float cosf(float);
float tanf(float);
float asinf(float);
float acosf(float);
float atanf(float);
float atan2f(float, float);
float expf(float);
float logf(float);
float log2f(float);
float powf(float, float);
float fmodf(float, float);
double sin(double);
double cos(double);
double tan(double);
double asin(double);
double acos(double);
double atan(double);
double atan2(double, double);
double exp(double);
double log(double);
double log2(double);
double pow(double, double);
double fmod(double, double);
float sqrtf(float);
double sqrt(double);
float fabsf(float);
double fabs(double);
float fminf(float, float);
double fmin(double, double);
float fmaxf(float, float);
double fmax(double, double);
float floorf(float);
double floor(double);
float ceilf(float);
double ceil(double);
float truncf(float);
double trunc(double);
float roundf(float);
double round(double);
float copysignf(float, float);
double copysign(double, double);
float scalbnf(float, int);
double scalbn(double, int);

#endif
