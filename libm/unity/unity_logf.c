/* cpp2lean: the translation unit of musl's logf for the translator (libm/translate_libm.sh): logf.c and
   the files of the helpers it calls (libm/unity/groups.txt), each unmodified and preprocessed as in
   its own translation unit (ardupilot/check_unity.py). */
#include "logf.c"
#include "logf_data.c"
#include "__math_divzerof.c"
#include "__math_invalidf.c"
