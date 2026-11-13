/* cpp2lean: musl's src/include/features.h, the one definition musl's src/math uses from it
   (`hidden`, also defined by libm/env/math.h). */
#ifndef CPP2LEAN_MUSL_FEATURES_H
#define CPP2LEAN_MUSL_FEATURES_H
#ifndef hidden
#define hidden __attribute__((__visibility__("hidden")))
#endif
#endif
