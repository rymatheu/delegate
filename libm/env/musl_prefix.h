/* cpp2lean: included (-include) only when ardupilot/vehicle/build.sh and difftest.py compile musl's
   sources into the C++ reference (libm/build_musl.sh): every external name of those sources gets the
   prefix cpp2lean_musl_, so that they cannot clash with the platform's libm. The reference's own code
   reaches them through the link (libm/build_musl.sh prints the -alias options that bind the C names).
   The translation (libm/translate_libm.sh) does not use this header: it keeps musl's names. */
#ifndef CPP2LEAN_MUSL_PREFIX_H
#define CPP2LEAN_MUSL_PREFIX_H
#define sinf cpp2lean_musl_sinf
#define cosf cpp2lean_musl_cosf
#define tanf cpp2lean_musl_tanf
#define asinf cpp2lean_musl_asinf
#define acosf cpp2lean_musl_acosf
#define atanf cpp2lean_musl_atanf
#define atan2f cpp2lean_musl_atan2f
#define expf cpp2lean_musl_expf
#define logf cpp2lean_musl_logf
#define log2f cpp2lean_musl_log2f
#define powf cpp2lean_musl_powf
#define fmodf cpp2lean_musl_fmodf
#define sin cpp2lean_musl_sin
#define cos cpp2lean_musl_cos
#define tan cpp2lean_musl_tan
#define asin cpp2lean_musl_asin
#define acos cpp2lean_musl_acos
#define atan cpp2lean_musl_atan
#define atan2 cpp2lean_musl_atan2
#define exp cpp2lean_musl_exp
#define log cpp2lean_musl_log
#define log2 cpp2lean_musl_log2
#define pow cpp2lean_musl_pow
#define fmod cpp2lean_musl_fmod
#define sqrtf cpp2lean_musl_sqrtf
#define sqrt cpp2lean_musl_sqrt
#define fabsf cpp2lean_musl_fabsf
#define fabs cpp2lean_musl_fabs
#define fminf cpp2lean_musl_fminf
#define fmin cpp2lean_musl_fmin
#define fmaxf cpp2lean_musl_fmaxf
#define fmax cpp2lean_musl_fmax
#define floorf cpp2lean_musl_floorf
#define floor cpp2lean_musl_floor
#define ceilf cpp2lean_musl_ceilf
#define ceil cpp2lean_musl_ceil
#define truncf cpp2lean_musl_truncf
#define trunc cpp2lean_musl_trunc
#define roundf cpp2lean_musl_roundf
#define round cpp2lean_musl_round
#define copysignf cpp2lean_musl_copysignf
#define copysign cpp2lean_musl_copysign
#define scalbnf cpp2lean_musl_scalbnf
#define scalbn cpp2lean_musl_scalbn
#define __sindf cpp2lean_musl___sindf
#define __cosdf cpp2lean_musl___cosdf
#define __tandf cpp2lean_musl___tandf
#define __rem_pio2f cpp2lean_musl___rem_pio2f
#define __rem_pio2 cpp2lean_musl___rem_pio2
#define __rem_pio2_large cpp2lean_musl___rem_pio2_large
#define __sin cpp2lean_musl___sin
#define __cos cpp2lean_musl___cos
#define __tan cpp2lean_musl___tan
#define __math_oflowf cpp2lean_musl___math_oflowf
#define __math_uflowf cpp2lean_musl___math_uflowf
#define __math_xflowf cpp2lean_musl___math_xflowf
#define __math_invalidf cpp2lean_musl___math_invalidf
#define __math_divzerof cpp2lean_musl___math_divzerof
#define __math_oflow cpp2lean_musl___math_oflow
#define __math_uflow cpp2lean_musl___math_uflow
#define __math_xflow cpp2lean_musl___math_xflow
#define __math_invalid cpp2lean_musl___math_invalid
#define __math_divzero cpp2lean_musl___math_divzero
#define __exp2f_data cpp2lean_musl___exp2f_data
#define __logf_data cpp2lean_musl___logf_data
#define __log2f_data cpp2lean_musl___log2f_data
#define __powf_log2_data cpp2lean_musl___powf_log2_data
#define __exp_data cpp2lean_musl___exp_data
#define __log_data cpp2lean_musl___log_data
#define __log2_data cpp2lean_musl___log2_data
#define __pow_log_data cpp2lean_musl___pow_log_data
#define __rsqrt_tab cpp2lean_musl___rsqrt_tab
#endif
