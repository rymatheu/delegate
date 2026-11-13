/* cpp2lean: the translation unit of musl's powf for the translator (libm/translate_libm.sh): powf.c and
   the files of the helpers it calls (libm/unity/groups.txt), each unmodified and preprocessed as in
   its own translation unit (ardupilot/check_unity.py). */
#include "powf.c"
#include "powf_data.c"
#include "exp2f_data.c"
#include "__math_oflowf.c"
#include "__math_uflowf.c"
#include "__math_xflowf.c"
#include "__math_invalidf.c"
