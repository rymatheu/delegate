// The constructs of ArduPilot's AP_InertialSensor and AP_GPS that cpp2lean --ins-gps translates (README.md "Phase 3:
// AP_InertialSensor, AP_GPS and AP_NavEKF_Source"), each in a small form, as one World: back ends whose reference
// members are bound to elements of the front end's arrays (`AP_GPS_Backend::state`, bound to `state[instance]`) and
// whose class inherits its constructor (`using AP_GPS_Backend::AP_GPS_Backend;`); a port the boundary returns, the
// World's one port object or null (AP_SerialManager::find_serial and the GPS port stand-in); a call whose every
// overrider returns `false` (`get_RTCMV3`), with a byte pointer used only in the branch it guards; a call through a
// subscript of a pointer to a class without objects (`_accel_calibrator[i].get_status()`); arrays of class members
// default-constructed by a zeroing constructor (`memset`, `x = T()`: LowPassFilter2p) and by a non-zero one (AP_GPS's
// parameter groups); an uninitialized local array of a class whose default constructor gives zero (`Vector3f
// last_average[3]`); a local reference to an element indexed by a loop counter of a loop without a constant trip count;
// ordering comparisons of an enum class; `if (_singleton)`; a parameter named `s`; a pointer parameter nothing reads.
#include <cstdint>
#include <cstring>
#include <new>

#define NEW_NOTHROW new (std::nothrow)

// --- a serial port: the interface, and the World's one port --------------------------------------------------
class Port {
public:
    virtual uint32_t baud() const = 0;
    virtual void begin(uint32_t b) = 0;
    virtual ~Port() {}
};
class PortImpl : public Port {
public:
    uint32_t baud() const override { return _baud; }
    void begin(uint32_t b) override { if (b != 0) { _baud = b; } _begun++; }
    uint32_t _baud = 9600;
    uint16_t _begun;
};

// --- the boundary: the port manager -----------------------------------------------------------------------------
class Manager {
public:
    Port *find(uint8_t instance) const;
};
const Manager &manager();

// --- value classes ------------------------------------------------------------------------------------------------
struct Vec {
    Vec() : x(0), y(0) {}
    Vec(float a, float b) : x(a), y(b) {}
    float x, y;
};
class Filter {
public:
    Filter() { memset(&_p, 0, sizeof(_p)); _state = Vec(); }
    float apply(float v) { _p.last = _p.gain * v + (1.0f - _p.gain) * _p.last; _state.x += v; return _p.last; }
    void set_gain(float g) { _p.gain = g; }
    struct P { float gain; float last; } _p;
    Vec _state;
};
class Group {
public:
    Group() { rate = 5; gain = 0.25f; }
    int16_t rate;
    float gain;
};
class Calib {
public:
    int status() const { return _status; }
    int _status;
};
enum class FixType : uint8_t { NONE = 0, FIX_2D = 2, FIX_3D = 3 };
struct Fix {
    FixType status;
    float speed;
    float course;
    bool have;
    uint32_t reads;
};

// --- the front end and its back ends -------------------------------------------------------------------------------
class Front;

class Driver {
public:
    Driver(Front &f, Group &group, Fix &fix, Port *port) : _port(port), _front(f), _fix(fix), _group(group) { _fix.have = false; }
    virtual ~Driver() {}
    virtual bool read() = 0;
    virtual bool rtcm(const uint8_t *&bytes, uint16_t &len) { return false; }
    static void halve(Fix &s) { s.speed = s.speed * 0.5f; }
protected:
    Port *_port;
    Front &_front;
    Fix &_fix;
    Group &_group;
    uint32_t _reads;
};

class SimDriver : public Driver {
public:
    using Driver::Driver;
    bool read() override;
private:
    uint32_t _last;
};

static const uint16_t RATES[] = { 5, 10 };
uint8_t pick(const uint16_t table[], uint8_t i) { return i < 2 ? i : 0; }

class Front {
public:
    Front();
    static Front *_singleton;
    void init();
    void update(float v);
    Driver *create(uint8_t i);
    void average(float v);
    float speed(uint8_t i) const { return fixes[i].speed; }
    Fix fixes[2];
    Group groups[2];
    Filter filters[2];
    Driver *drivers[2];
    Port *ports[2];
    Calib *_calib;
    uint8_t _count;
    uint8_t _hits;
    Vec _avg;
    float _input;
};
Front *Front::_singleton = nullptr;

Front::Front()
{
    if (_singleton) {
        _count = 9;
    }
    _singleton = this;
}

void Front::init()
{
    for (uint8_t i = 0; i < 2 && i < 3; i++) {
        auto &rate = groups[i].rate;
        if (rate <= 0 || rate > 20) {
            rate = 20;
        }
    }
    const Manager &m = manager();
    for (uint8_t i = 0; i < 2; i++) {
        ports[i] = m.find(i);
        filters[i].set_gain(groups[i].gain);
    }
}

Driver *Front::create(uint8_t i)
{
    Port *port = ports[i];
    if (port == nullptr) {
        return nullptr;
    }
    if (port->baud() < 19200) {
        port->begin(19200);
    }
    return NEW_NOTHROW SimDriver(*this, groups[i], fixes[i], port);
}

bool SimDriver::read()
{
    _reads++;
    _fix.reads++;
    _fix.speed = _front._input * float(_group.rate);
    _fix.course = _fix.speed * 2.0f;
    _fix.status = _fix.speed > 1.0f ? FixType::FIX_3D : FixType::FIX_2D;
    halve(_fix);
    _last = _reads;
    return _fix.speed > 0.0f;
}

void Front::update(float v)
{
    _input = v;
    for (uint8_t i = 0; i < 2; i++) {
        if (drivers[i] == nullptr) {
            drivers[i] = create(pick(RATES, i));
            continue;
        }
        if (drivers[i]->read() && fixes[i].status >= FixType::FIX_2D) {
            _hits++;
        }
        if (fixes[i].status < FixType::FIX_3D) {
            fixes[i].have = true;
        }
        const uint8_t *data;
        uint16_t len;
        if (drivers[i]->rtcm(data, len)) {
            _hits += data[0] + len;
        }
        if (_calib != nullptr && _calib[i].status() == 1) {
            _hits = 0;
        }
    }
    average(_input);
}

void Front::average(float v)
{
    Vec acc[2];
    for (uint8_t k = 0; k < 2; k++) {
        acc[k].x = filters[k].apply(v + float(k));
        acc[k].y = fixes[k].speed;
    }
    _avg = Vec((acc[0].x + acc[1].x) * 0.5f, (acc[0].y + acc[1].y) * 0.5f);
}

// the objects as a vehicle defines them
PortImpl port;
Front front;
