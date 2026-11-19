// supervisor_shadow.h: what the generated stand-ins (gen/out/shadow_*.cpp) and the hand-written
// ones (stand_ins/*.cpp) share: the tick's command log and the abort for unanswered queries.
#pragma once

#include <stdint.h>
#include <string.h>
#include <type_traits>

#include <AP_Math/AP_Math.h>
#include <AP_Common/Location.h>

// one entry per stand-in command call: the method id (gen/out/cmd_table.inc) and up to
// SUP_CMD_MAX_ARGS argument words (floats as their bits, integers as two's complement, vectors
// and locations component-wise; doubles are narrowed to float, which loses precision beyond
// 2^-24 relative)
#define SUP_CMD_MAX_ARGS 12
#define SUP_CMD_LOG_MAX 64
struct SupCmd {
    uint32_t id;
    uint32_t nargs;
    uint32_t arg[SUP_CMD_MAX_ARGS];
    bool arg_is_float[SUP_CMD_MAX_ARGS];
};
extern SupCmd sup_cmd_log[SUP_CMD_LOG_MAX];
extern uint32_t sup_cmd_count;
extern uint32_t sup_cmd_overflow;

void sup_cmd_begin(uint32_t id);
void sup_cmd_word(uint32_t w, bool is_float);
void sup_cmd_end();
[[noreturn]] void sup_unanswered(const char *method);

inline void sup_arg_float(float f) { uint32_t w; memcpy(&w, &f, 4); sup_cmd_word(w, true); }

template <typename T>
typename std::enable_if<std::is_floating_point<T>::value>::type sup_arg(const T &v)
{
    sup_arg_float(float(v));
}
template <typename T>
typename std::enable_if<std::is_integral<T>::value>::type sup_arg(const T &v)
{
    sup_cmd_word(uint32_t(int64_t(v)), false);
}
template <typename T>
typename std::enable_if<std::is_enum<T>::value>::type sup_arg(const T &v)
{
    sup_cmd_word(uint32_t(int64_t(v)), false);
}
template <typename T>
void sup_arg(T *const &p)
{
    sup_cmd_word(p == nullptr ? 0 : 1, false);   // a pointer argument: only whether it is set
}
template <typename T>
void sup_arg(const Vector2<T> &v) { sup_arg(v.x); sup_arg(v.y); }
template <typename T>
void sup_arg(const Vector3<T> &v) { sup_arg(v.x); sup_arg(v.y); sup_arg(v.z); }
template <typename T>
void sup_arg(const QuaternionT<T> &q) { sup_arg(q.q1); sup_arg(q.q2); sup_arg(q.q3); sup_arg(q.q4); }
inline void sup_arg(const Location &l)
{
    sup_arg(l.lat); sup_arg(l.lng); sup_arg(l.alt); sup_arg(uint32_t(l.get_alt_frame()));
}
// any other class argument (structs, objects passed by reference): FNV-1a of its bytes, so the
// log shows that the call happened and whether the argument changed; a placeholder until the
// command has its own fields (padding bytes make the hash unreliable across builds)
template <typename T>
typename std::enable_if<std::is_class<T>::value || std::is_union<T>::value>::type sup_arg(const T &v)
{
    const uint8_t *p = reinterpret_cast<const uint8_t *>(&v);
    uint32_t h = 2166136261u;
    for (size_t k = 0; k < sizeof(T); k++) {
        h = (h ^ p[k]) * 16777619u;
    }
    sup_cmd_word(h, false);
}

// ids of the hand-written command stand-ins (the generated ones are 1..999, cmd_table.inc)
#define SUP_CMD_HAND_MOTORS_ARMED 1001
#define SUP_CMD_HAND_MOTORS_SET_DESIRED_SPOOL_STATE 1002
#define SUP_CMD_HAND_AHRS_SET_HOME 1003
#define SUP_CMD_HAND_TABLE \
    {SUP_CMD_HAND_AHRS_SET_HOME, "estimator", "AP_AHRS::set_home"}, \
    {SUP_CMD_HAND_MOTORS_ARMED, "mixer", "AP_Motors::armed"}, \
    {SUP_CMD_HAND_MOTORS_SET_DESIRED_SPOOL_STATE, "mixer", \
     "AP_MotorsMulticopter::set_desired_spool_state"},

// Private members of a shadow class, reached by the rule that access is not checked in the
// template arguments of an explicit instantiation (as the mixer adapter reaches
// AP_MotorsMatrix::_singleton). HARNESS_PRIVATE(C, T, m) declares the accessor; then
// HARNESS_FIELD(obj, C, m) is obj.m as an lvalue. T must be a simple type name (typedef arrays).
#define HARNESS_PRIVATE(CLASS, TYPE, MEMBER)                                              \
    TYPE CLASS::*harness_mp_##CLASS##_##MEMBER();                                         \
    template <TYPE CLASS::*M>                                                             \
    struct harness_rob_##CLASS##_##MEMBER {                                               \
        friend TYPE CLASS::*harness_mp_##CLASS##_##MEMBER() { return M; }                 \
    };                                                                                    \
    template struct harness_rob_##CLASS##_##MEMBER<&CLASS::MEMBER>;
#define HARNESS_FIELD(OBJ, CLASS, MEMBER) ((OBJ).*harness_mp_##CLASS##_##MEMBER())

// The fills: each writes its stage's shadow state from the input record (module_records.h)
struct Input;
void harness_estimator_fill(const Input &in);
void harness_position_fill(const Input &in);
void harness_attitude_fill(const Input &in);
void harness_guidance_fill(const Input &in);
void harness_mixer_fill(const Input &in);

// true if the stand-in of METHOD ("Class::method") has been called in this tick
bool sup_cmd_called(const char *method);
// the "Class::method" name of a command id, and its stage (nullptr if unknown)
const char *sup_cmd_method(uint32_t id, const char **stage);

// an unanswered query returns its type's zero and is counted in sup_unanswered_count (output
// `unanswered`, guaranteed 0), unless SUP_STRICT=1, where it aborts
bool sup_lenient(const char *method);
extern uint32_t sup_unanswered_count;
template <typename T>
struct SupZero {
    static T get() { return T{}; }
};
template <typename T>
struct SupZero<T &> {
    static T &get()
    {
        static typename std::remove_const<T>::type z{};
        return z;
    }
};
void harness_mixer_boot();

// HARNESS_ADDR(C, m) declares an accessor for the address of C::m whatever its type (named or
// not, protected or private: the explicit-instantiation rule); HARNESS_REF(T, obj, C, m) is
// that member as a T lvalue. T must be m's type (or layout-identical, for unnamed structs).
#define HARNESS_ADDR(CLASS, MEMBER)                                                       \
    void *harness_addr_##CLASS##_##MEMBER(CLASS &o);                                      \
    template <typename T, T M>                                                            \
    struct harness_addr_rob_##CLASS##_##MEMBER {                                          \
        friend void *harness_addr_##CLASS##_##MEMBER(CLASS &o) { return (void *)&(o.*M); } \
    };                                                                                    \
    template struct harness_addr_rob_##CLASS##_##MEMBER<decltype(&CLASS::MEMBER), &CLASS::MEMBER>;
#define HARNESS_REF(TYPE, OBJ, CLASS, MEMBER) \
    (*static_cast<TYPE *>(harness_addr_##CLASS##_##MEMBER(OBJ)))

// a command recorded by a hand-written stand-in or by the adapter's inline-setter detection,
// under its "Class::method" name (ids from 2000 up, assigned on first use)
uint32_t sup_named_id(const char *method, const char *stage);
inline void sup_cmd_begin_named(const char *method, const char *stage)
{
    sup_cmd_begin(sup_named_id(method, stage));
}

// words of a log entry
inline float sup_word_f(const SupCmd &c, uint32_t k)
{
    float f = 0;
    if (k < c.nargs) {
        memcpy(&f, &c.arg[k], 4);
    }
    return f;
}
inline uint32_t sup_word_u(const SupCmd &c, uint32_t k) { return k < c.nargs ? c.arg[k] : 0; }

// strict mode (SUP_STRICT=1): an unanswered query or an unfilled shadow value reaching an output
// aborts; otherwise it is counted (output `unanswered`) and the run goes on
bool sup_strict();
void sup_unfilled(const char *what);

// The poison trap (SUP_POISON=1): before each tick every float-valued field of the controller
// shadows (generated per class by gen/gen_shadows.py, POISON) is set to a quiet NaN; the fills
// then overwrite the fields that have a source. A NaN that reaches an f32 output field at the
// end of the tick (a command argument, a signal) is a read of state nothing fills: counted in
// `poisoned_reads`, named in the trace, and an abort with SUP_STRICT=1. Reads that only steer a
// comparison or branch are not caught (a NaN compares false and leaves no trace in the outputs).
#define HARNESS_PADDR(CLASS, MEMBER)                                                      \
    void *harness_paddr_##CLASS##_##MEMBER(CLASS &o);                                     \
    template <typename T, T M>                                                            \
    struct harness_paddr_rob_##CLASS##_##MEMBER {                                         \
        friend void *harness_paddr_##CLASS##_##MEMBER(CLASS &o) { return (void *)&(o.*M); } \
    };                                                                                    \
    template struct harness_paddr_rob_##CLASS##_##MEMBER<decltype(&CLASS::MEMBER), &CLASS::MEMBER>;
bool sup_poison_on();
inline void sup_poison(float &x) { x = NAN; }
inline void sup_poison(double &x) { x = NAN; }
template <typename T> inline void sup_poison(Vector2<T> &v) { v.x = v.y = NAN; }
template <typename T> inline void sup_poison(Vector3<T> &v) { v.x = v.y = v.z = NAN; }
template <typename T> inline void sup_poison(QuaternionT<T> &q) { q.q1 = q.q2 = q.q3 = q.q4 = NAN; }
template <typename T> inline void sup_poison(Matrix3<T> &m) { sup_poison(m.a); sup_poison(m.b); sup_poison(m.c); }
