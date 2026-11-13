// cpp2lean demo (phase 3, fourth part; the World since Phase 1 of PORT-PLAN.md): the constructs
// added for AC_WPNav, SCurve and SplineCurve, each in the form the ArduPilot code uses it (cited at
// 802db19de1). The class Planner plays the position controller: the navigator calls into it and
// reads it again afterwards. Both are World objects (--world), so a read after a call sees the call,
// as in C++. The clock is the boundary (navigate_env.h). Translated with the options of navigate.json.
#include <cmath>
#include <cstdint>
#include <cstdio>
#include "navlib/navvec.h"

namespace clk {
uint32_t now_ms();      // --boundary-fn clk::now_ms (AP_HAL::millis)
}

// A parameter class with AP_Float's conversions (AP_Param.h:1006-1016): `operator const float &`
// and the explicit `operator double` (--param-class Param=float).
class Param {
public:
    float get() const { return _v; }
    void set(float v) { _v = v; }
    operator const float &() const { return _v; }
    explicit operator double () const { return (double)_v; }
private:
    float _v;
};

// A member object of the planner reached through an accessor (AC_P_2D through
// AC_PosControl::NE_get_pos_p(), AC_WPNav.cpp:589), with a parameter.
class PGain {
public:
    Param &kP() { return _kp; }
    Param _kp;
};

// The position controller's part: what the navigator reads from it depends on the calls it made
// into it before, in the same member function (AC_WPNav::wp_and_spline_init_m reads the stopping
// point after NE_set_max_speed_accel_m, AC_WPNav.cpp:232-253).
class Planner {
public:
    Planner() { _gain._kp.set(0.5f); }
    void reset() { _est = NV3(); _resets++; }       // calls whose result is discarded
    void set_limits(float speed, float accel) { _speed = speed; _accel = accel; }
    void send(const NV3 &pos, const NV3 &vel) { _est = pos + vel; _sends++; }    // struct arguments by const reference (AC_WPNav.cpp:636)
    float speed_limit() const { return _speed; }
    void stopping_point(NV2 &out) const { out.x = _est.x + 1.0; out.y = _est.y - (double)_accel; }    // a reference parameter (AC_WPNav.cpp:549)
    float scaler(float a, float b) const { return _accel * 0.125f + 0.5f * a + 0.25f * b; }      // with arguments (terrain_scaler_D_m, AC_WPNav.cpp:566)
    const NV3 &estimate() const { return _est; }    // returning a reference (get_pos_offset_NED_m)
    PGain &gain() { return _gain; }                 // an accessor of a member object
private:
    float _speed;
    float _accel;
    NV3 _est;
    int32_t _resets;
    int32_t _sends;
    PGain _gain;
};

// SCurve's segment table (SCurve.h:236-244): an array of an anonymous struct, a count bounding the
// loops, one-bit flags (AC_WPNav.h:362-366), an array of value-class objects (SplineCurve.h:57).
class Leg {
public:
    Leg() { init(); }

    void init()
    {
        num = 0;
        limit = 1.0f;
        add(num, 0.0f, 0.0f);
        flags.done = false;
        flags.fast = 0;
    }

    // `add_segment(uint8_t &index, ...)` (SCurve.cpp:1201-1210)
    void add(uint8_t &index, float t, float v)
    {
        seg[index].t = t;
        seg[index].v = v;
        index++;
    }

    void extend(float t, float v)
    {
        if (num < n_max) {
            add(num, t, v);
        }
        flags.done = num >= n_max;
        flags.fast ^= 1;          // a one-bit field stores its value modulo 2
    }

    // a loop bounded by a member in a const member function (SCurve::valid, SCurve.cpp:1218)
    bool valid() const
    {
        for (uint8_t i = 0; i < num; i++) {
            if (!std::isfinite(seg[i].t) || seg[i].v < 0.0f) {
                return false;
            }
        }
        return num > 0;
    }

    // a loop from a variable start to an inclusive variable bound (SCurve::fill_empty_segments, SCurve.cpp:1184-1195)
    void fill(uint8_t first, uint8_t last, float t)
    {
        if (last >= n_max) {
            return;
        }
        for (uint8_t i = first; i <= last; i++) {
            seg[i].t = t;
            seg[i].v = 0.0f;
        }
    }

    // a reference parameter that the caller binds to a member the function also reads
    // (SplineCurve::calc_dt_speed_max writes `speed_max` and reads `_destination_speed_max`,
    // SplineCurve.cpp:93, :214-215)
    void cap(float v, float &speed_max)
    {
        speed_max = v * 2.0f;
        speed_max = fminf(speed_max, limit + cap_store);
    }

    void update_cap(float v) { cap(v, cap_store); }
    void cap_local(float v) { float c = v; cap(v, c); last = c; }

    // value-class objects in an array, set as wholes and read by member functions
    void set_points(const NV3 &a, const NV3 &b)
    {
        pts[0] = a;
        pts[1] = a + b * 2.0;
    }
    double span() const { return (pts[1] - pts[0]).length(); }

    static const uint8_t n_max = 6;
    uint8_t num;
    struct {
        float t;
        float v;
    } seg[n_max];
    NV3 pts[2];
    struct {
        uint8_t done : 1;
        uint8_t fast : 1;
    } flags;
    float limit;
    float cap_store;
    float last;
};

// The navigator: a reference member to the planner, a World object; its reads follow its calls.
class Navigator {
public:
    Navigator(Planner &planner) : _planner(planner) { _k.set(0.75f); }

    // calls into the planner, then reads it (AC_WPNav::wp_and_spline_init_m)
    void start(float speed)
    {
        _planner.reset();
        _planner.set_limits(speed, 2.0f * speed);
        _planner.stopping_point(_dest.xy());     // a view of a member as the reference argument
        _dest.z = speed_now();                    // a read in a member function this one calls
        _started_ms = clk::now_ms();
    }

    float speed_now() const { return _planner.speed_limit() * _planner.scaler(_dest.z, 0.5f); }

    // a view of a reference parameter as the reference argument (AC_WPNav.cpp:549)
    void stopping(NV3 &out) const
    {
        _planner.stopping_point(out.xy());
        out.z = (double)_k;                       // `explicit operator double` of a parameter
    }

    // a local reference to a member another object returns: each use reads it again (AC_WPNav.cpp:572-575)
    void step(float dt)
    {
        const NV3 &est = _planner.estimate();
        NV3 before = est;
        _planner.send(_dest, before * (double)dt);
        _offset = est - before;                   // the estimate after the call
        _gain = _planner.gain().kP() * dt;        // a parameter of a member object of the planner
        static bool logged;                       // a logging latch (SCurve.cpp:1043-1061), --drop
        if (!logged) {
            logged = true;
            printf("step at %u ms\n", (unsigned)clk::now_ms());
        }
        _leg.extend(dt, (float)before.length());
    }

    void fill(uint8_t first, uint8_t last, float t) { _leg.fill(first, last, t); }
    void cap(float v) { _leg.update_cap(v); _leg.cap_local(v); }
    void points(const NV3 &a, const NV3 &b) { _leg.set_points(a, b); }
    bool valid() const { return _leg.valid(); }
    double span() const { return _leg.span(); }

private:
    Planner &_planner;
    Param _k;
    NV3 _dest;
    NV3 _offset;
    float _gain;
    uint32_t _started_ms;
    Leg _leg;
};

Planner planner;
Navigator navigator(planner);
