/* cpp2lean: the translation unit of musl's pow for the translator (libm/translate_libm.sh): pow.c and
   the files of the helpers it calls (libm/unity/groups.txt), each unmodified and preprocessed as in
   its own translation unit (ardupilot/check_unity.py). */
#include "pow.c"
#include "pow_data.c"
#include "exp_data.c"
#include "__math_oflow.c"
#include "__math_uflow.c"
#include "__math_xflow.c"
#include "__math_invalid.c"
