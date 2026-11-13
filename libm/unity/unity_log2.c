/* cpp2lean: the translation unit of musl's log2 for the translator (libm/translate_libm.sh): log2.c and
   the files of the helpers it calls (libm/unity/groups.txt), each unmodified and preprocessed as in
   its own translation unit (ardupilot/check_unity.py). */
#include "log2.c"
#include "log2_data.c"
#include "__math_divzero.c"
#include "__math_invalid.c"
