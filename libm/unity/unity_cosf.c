/* cpp2lean: the translation unit of musl's cosf for the translator (libm/translate_libm.sh): cosf.c and
   the files of the helpers it calls (libm/unity/groups.txt), each unmodified and preprocessed as in
   its own translation unit (ardupilot/check_unity.py); __rem_pio2f is its own translation (Musl.__rem_pio2f). */
#include "cosf.c"
#include "__sindf.c"
#include "__cosdf.c"
