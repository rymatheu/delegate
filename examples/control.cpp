// cpp2lean demo (phase 3, third part): the constructs added for AC_AttitudeControl and
// AC_PosControl, each in the form the ArduPilot code uses it (cited at 802db19de1).
// Translated with: --boundary Nav --boundary-query Nav::armed
#include <cmath>
#include <cstdint>

// Vector2/Vector3 in miniature (AP_Math/vector2.h, vector3.h): a class with member functions and
// a non-const operator that returns *this.
class V2 {
public:
    float x, y;
    constexpr V2() : x(0), y(0) {}
    constexpr V2(float x0, float y0) : x(x0), y(y0) {}
    void zero() { x = 0; y = 0; }
    V2 &operator*=(const float k) { x *= k; y *= k; return *this; }
    float length() const { return sqrtf(x * x + y * y); }
};

class V3 {
public:
    float x, y, z;
    constexpr V3() : x(0), y(0), z(0) {}
    constexpr V3(float x0, float y0, float z0) : x(x0), y(y0), z(z0) {}
    // a view of the first two members as a V2, writable through the non-const overload
    // (vector3.h:316-323; AC_PosControl writes `_pos_target_ned_m.xy() = ...` and calls
    // `_vel_desired_ned_ms.xy().zero()`)
    const V2 &xy() const { return *(const V2 *)this; }
    V2 &xy() { return *(V2 *)this; }
    V3 scaled(float k) const { return V3{x * k, y * k, z * k}; }
};

// a free function writing through a reference parameter (update_pos_vel_accel_xy, control.cpp)
static void advance(V2 &pos, const V2 &vel, float dt)
{
    pos.x += vel.x * dt;
    pos.y += vel.y * dt;
}

// Boundary (not translated): the navigator. A const getter returning a reference to a struct (its
// value is an input, field by field in the difftest), a non-const getter that does not change the
// object (an input with --boundary-query, as AC_AttitudeControl::get_bf_feedforward,
// AC_AttitudeControl.h:396), a scalar member.
class Nav {
public:
    V3 tgt;
    bool on;
    float trim;
    const V3 &target() const { return tgt; }
    bool armed() { return on; }
};

// A gain object whose constructor binds its argument to a const reference: a member initializer
// `_gain(3.0f)` materializes a temporary (AC_P(const float &), initialized as `_p_angle_roll(4.5f)`,
// AC_AttitudeControl.h:51).
class Gain {
public:
    Gain(const float &k) : _k(k) {}
    float apply(float x) const { return _k * x; }
    void scale(float f) { _k *= f; }
    float k() const { return _k; }
private:
    float _k;
};

enum class Mode : uint8_t { Angle, Rate, Both };

// a struct parameter with an enum member (AC_AttitudeControl::HeadingCommand, :716-720)
struct Command {
    float angle;
    float rate;
    Mode mode;
};

// The base class reaches the derived class's member object through a pure virtual accessor that
// returns a reference (get_rate_roll_pid(), AC_AttitudeControl.h:83-88, overridden by
// `return _pid_rate_roll;` in AC_AttitudeControl_Multi.h:48-53).
class Loop {
public:
    Loop(Nav &nav) : _nav(nav) {}
    virtual ~Loop() {}
    virtual Gain &gain() = 0;
    virtual const Gain &gain() const = 0;

    void boost(float f) { gain().scale(f); }
    float output(float x) const { return gain().apply(x); }
    float gain_k() const { return gain().k(); }

    // a static constexpr member of a class type, defined out of line (VECTORF_111,
    // AC_AttitudeControl.h:549, AC_AttitudeControl.cpp:208)
    static constexpr V3 HOME{1.0f, 2.0f, -3.0f};
    void go_home() { _pos = HOME; }

protected:
    Nav &_nav;
    V3 _pos;
    float _last;
    float _heading;
};
constexpr V3 Loop::HOME;

class Hold : public Loop {
public:
    Hold(Nav &nav) : Loop(nav), _gain(3.0f) {}
    Gain &gain() override { return _gain; }
    const Gain &gain() const override { return _gain; }

    void run(float dt)
    {
        // a local const reference to a boundary read: a copy (the boundary does not change during
        // the call), as `const Vector3f &att_target_euler_rad = _attitude_control.get_att_target_euler_rad();`
        // (AC_PosControl.cpp:550)
        const V3 &t = _nav.target();
        if (!_nav.armed()) {
            _pos.xy().zero();                   // a non-const call on the view
            return;
        }
        V2 vel(t.x - _pos.x, t.y - _pos.y);
        advance(_pos.xy(), vel, dt);            // the view as a reference argument
        _pos.xy() *= output(0.5f);              // an operator on the view
        _pos.z = _nav.target().z + _nav.trim;   // a member of a boundary read (AC_PosControl.h:607)
        _last = _pos.scaled(2.0f).x;            // a member of a call's value
    }

    void place(float x, float y)
    {
        V2 q(x, y);
        _pos.xy() = q;                          // an assignment to the view
        _pos.xy().x = x * 2.0f;                 // a member of the view
    }

    void apply(Command c)
    {
        switch (c.mode) {
        case Mode::Angle:
            _heading = c.angle;
            break;
        case Mode::Rate:
            _heading += c.rate;
            break;
        case Mode::Both:
            _heading = c.angle + c.rate;
            break;
        }
    }

    float last() const { return _last; }
    float speed() const { return _pos.xy().length(); }

private:
    Gain _gain;
};
