/* cpp2lean: the translation unit of musl's exp for the translator (libm/translate_libm.sh): exp.c and
   the files of the helpers it calls (libm/unity/groups.txt), each unmodified and preprocessed as in
   its own translation unit (ardupilot/check_unity.py). */
#include "exp.c"
#include "exp_data.c"
#include "__math_oflow.c"
#include "__math_uflow.c"
#include "__math_xflow.c"
