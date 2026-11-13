/* cpp2lean: the translation unit of musl's sin for the translator (libm/translate_libm.sh): sin.c and
   the files of the helpers it calls (libm/unity/groups.txt), each unmodified and preprocessed as in
   its own translation unit (ardupilot/check_unity.py); __rem_pio2 is its own translation (Musl.__rem_pio2). */
#include "sin.c"
#include "__sin.c"
#include "__cos.c"
