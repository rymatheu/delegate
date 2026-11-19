// cpp2lean difftest: the C++ side of the output log (--output-log). The environment appends one
// event per boundary call, ` e:<name>` and the typed argument tokens, exactly as the Lean driver
// prints its `Output` values; the class driver prints and clears the log after each call.
#pragma once
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string>

extern std::string cpp2lean_events;

static inline void cpp2lean_ev(const char *name) { cpp2lean_events += " e:"; cpp2lean_events += name; }
static inline void cpp2lean_ev_i(long long v) { char b[32]; snprintf(b, sizeof b, " i:%lld", v); cpp2lean_events += b; }
static inline void cpp2lean_ev_u(unsigned long long v) { char b[32]; snprintf(b, sizeof b, " i:%llu", v); cpp2lean_events += b; }
static inline void cpp2lean_ev_b(bool v) { cpp2lean_events += v ? " b:1" : " b:0"; }
static inline void cpp2lean_ev_f(float f) { uint32_t u; memcpy(&u, &f, 4); char b[32]; snprintf(b, sizeof b, " f:%08x", u); cpp2lean_events += b; }

// The number of boundary calls recorded since the driver last printed the log (the start of the
// member function under test). A stand-in for a --boundary-live class returns, for each read, the
// line's value plus 0.125 times this count (plus 0.5, 0.25, ... times its floating arguments), as the
// Lean driver's live Inputs functions do, so that the difftest sees which calls a read follows.
static inline int cpp2lean_ev_count()
{
    int n = 0;
    for (size_t i = cpp2lean_events.find(" e:"); i != std::string::npos; i = cpp2lean_events.find(" e:", i + 1)) {
        n++;
    }
    return n;
}
static inline float cpp2lean_live_f(float v) { return v + 0.125f * (float)cpp2lean_ev_count(); }
static inline double cpp2lean_live_d(double v) { return v + 0.125 * (double)cpp2lean_ev_count(); }
static inline void cpp2lean_ev_d(double d) { uint64_t u; memcpy(&u, &d, 8); char b[32]; snprintf(b, sizeof b, " d:%016llx", (unsigned long long)u); cpp2lean_events += b; }
