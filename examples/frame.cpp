// cpp2lean demo (phase 3, AP_Motors and AP_Math constructs): a motor frame and its thrust curve, in
// the shape of ArduPilot's AP_MotorsMatrix and Thrust_Linearization, written for the demo. It uses the
// constructs the translator gained for AP_Motors so that they are tested without the ArduPilot tree:
// a member object with a back-reference to its owner (`Lin lin {*this}`), boundary outputs as an
// ordered call log (--output-log) through static functions of a boundary class, a --boundary-call
// member function and a write to a boundary class's static data, a local reference to a boundary
// object and a boundary query with a variable argument (--site-inputs), parameters with
// `set_default`, `configured` and a call through an accessor (`gain().set_default(x)`), an enum
// parameter (AP_Enum), a constant table of structs passed as `const T *` (--array-params) with
// ARRAY_SIZE and a loop bounded by the count, a counter declared before its loops, a `const auto &`
// local, `const char *` strings, an anonymous struct member, data members left out (--drop), and a
// `switch` case left early by `if (c) { ...; break; }`.
#include <cmath>
#include <cstdint>

#define ARRAY_SIZE(a) (sizeof(a) / sizeof(a[0]))

// ---- a stand-in for ArduPilot's AP_Param (only what --ap-param relies on)
enum ap_var_type { AP_PARAM_NONE = 0, AP_PARAM_INT8, AP_PARAM_INT16, AP_PARAM_INT32, AP_PARAM_FLOAT };
bool frame_param_storage();             // storage state of the parameters (frame_env.h)
template <typename T, ap_var_type PT>
class AP_ParamT {
public:
    const T &get() const { return _value; }
    void set(const T &v) { _value = v; }
    void set_default(const T &v) { if (!configured()) { set(v); } }
    bool configured() const { return frame_param_storage(); }
    operator const T &() const { return _value; }
protected:
    T _value;
};
typedef AP_ParamT<float, AP_PARAM_FLOAT> AP_Float;
typedef AP_ParamT<int8_t, AP_PARAM_INT8> AP_Int8;
template <typename E>
class AP_Enum : public AP_Int8 {
public:
    operator const E () const { return (E)_value; }
    void set(E v) { AP_Int8::set(int8_t(v)); }
};

// ---- the boundary (--boundary Servo,Sensor,Notify): defined by the environment (frame_env.h)
class Servo {
public:
    static void write(uint8_t chan, uint16_t pwm);      // an output: one event per call, in order
    static uint32_t channel_mask(uint8_t chan);          // a query of the configuration
};
class Sensor {
public:
    float read_at(int i) const;                          // a query with a variable argument
};
namespace AP {
    Sensor &sensor();
}
class Notify {
public:
    struct Flags { bool armed; };
    static Flags flags;                                  // written: an output event
};

class Host;

// A thrust curve that reads its owner's gain and trim through a back-reference.
class Lin {
public:
    Lin(Host &host_in) : lift(1.0f), host(host_in) {}
    float actuator(float thrust) const;
    void relax(float k) { lift = lift + k * (1.0f - lift); }
    AP_Float expo;
    float lift;
private:
    Host &host;
};

class Host {
public:
    enum class Mode : uint8_t { OFF = 0, ON = 1, BOOST = 2 };
    struct Def {
        float angle_deg;
        float yaw;
        uint8_t order;
    };

    Host()
    {
        gain().set_default(0.5f);
        lin.expo.set_default(0.25f);
        if (_singleton != nullptr) {
            note_duplicate();
        }
        _singleton = this;
    }

    AP_Float &gain() { return _gain; }
    float scale() const { return _gain * 2.0f; }
    float trim;

    // a frame from a constant table
    bool setup(uint8_t kind)
    {
        int8_t i;
        for (i = 0; i < 4; i++) {
            _enabled[i] = false;
            _roll[i] = 0.0f;
        }
        static const Def quad[] {
            {   45, 1, 1 },
            { -135, 1, 3 },
            {  -45, -1, 4 },
            {  135, -1, 2 },
        };
        static const Def tri[] {
            {   60, 1, 1 },
            {  -60, -1, 2 },
            {  180, 1, 3 },
        };
        switch (kind) {
        case 0:
            _name = "QUAD";
            add_all(quad, ARRAY_SIZE(quad));
            break;
        case 1:
            _name = "TRI";
            add_all(tri, ARRAY_SIZE(tri));
            break;
        default:
            _name = "NONE";
            return false;
        }
        for (i = 0; i < 4; i++) {
            if (_enabled[i]) {
                _scaled.mask |= 1U << i;
            }
        }
        return true;
    }

    void add_all(const Def *defs, uint8_t n)
    {
        for (uint8_t k = 0; k < n; k++) {
            const auto &d = defs[k];
            _enabled[k] = true;
            _roll[k] = cosf((d.angle_deg + 90.0f) * 0.0174532925f) * d.yaw;
            _order[k] = d.order;
        }
    }

    // one output step: the thrust curve (through the back-reference), the servo writes in order
    void step(float thrust)
    {
        for (uint8_t k = 0; k < 4; k++) {
            if (_enabled[k]) {
                _out[k] = lin.actuator(thrust + _roll[k] * _roll_in);
                Servo::write(k, (uint16_t)(1000.0f + 1000.0f * _out[k]));
            }
        }
        if (_mode == Mode::BOOST) {
            emit(9);
        }
        lin.relax(0.1f);
        _dropped_count = 0;
    }

    void arm(bool on)
    {
        if (_armed != on) {
            _armed = on;
            Notify::flags.armed = on;
        }
    }

    void set_mode(uint8_t m)
    {
        switch (m) {
        case 0:
            _mode.set(Mode::OFF);
            break;
        case 1:
            if (_armed) {
                _mode.set(Mode::ON);
                break;
            }
            _mode.set(Mode::OFF);
            emit(1);
            break;
        default:
            _mode.set(Mode::BOOST);
            break;
        }
    }

    void set_roll(float r) { _roll_in = r; }
    void configure() { if (!_gain.configured()) { _gain.set(0.75f); } }

    float sample(int i) const
    {
        Sensor &sens = AP::sensor();
        return sens.read_at(i) * scale() + (float)Servo::channel_mask(2);
    }

    const char *name() const { return _name; }

    void emit(uint8_t code);            // --boundary-call: the environment's (frame_env.h)
    void note_duplicate() { _note_count++; }   // --drop

    Lin lin {*this};

private:
    AP_Float _gain;
    AP_Enum<Mode> _mode;
    bool _armed;
    float _roll_in;
    bool _enabled[4];
    float _roll[4];
    uint8_t _order[4];
    float _out[4];
    const char *_name = "";
    struct {
        uint32_t mask;
        float offset;
    } _scaled;
    static Host *_singleton;            // --drop
    int _dropped_count;                 // --drop
    int _note_count;
};

float Lin::actuator(float thrust) const
{
    const float e = fminf(fmaxf(expo.get(), -1.0f), 1.0f);
    const float t = fminf(fmaxf(thrust, 0.0f), 1.0f);
    return lift * (host.trim + ((1.0f - e) * t + e * t * t) * host.scale());
}

Host *Host::_singleton;
