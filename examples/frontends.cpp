// The constructs of ArduPilot's sensor front ends that cpp2lean --front-ends translates (README.md "Phase 3:
// sensor front ends and AP_Param"), each in a small form, as one World: a class defined inside a namespace
// with a singleton accessor returning a pointer (SITL::SIM, AP::sitl()); the HAL as a boundary object whose
// scheduler pointer is the World's scheduler object (`hal.scheduler->delay(...)`); a type-safe index with
// `operator++(int)` (an unnamed parameter) and an array wrapper whose `operator[]` returns a reference
// (AP_Common/TSIndex.h); a union of a struct of multi-bit bit-fields and an integer (AP_HAL::Device's bus
// id); a file-scope table of an anonymous struct type (AP_Baro_atmosphere.cpp); range-for over a member
// array; local references and pointers to elements that change while they are live; a loop without a
// constant trip count with `continue`; a nullable `const T *` parameter with a null default; a member
// initialized from another member; a static data member defined `= 0`; back ends created at init whose
// classes read the boundary (one set of inputs per class); a second counter of the same name in a function.
#include <cstdint>
#include <cstddef>
#include <new>

#define NEW_NOTHROW new (std::nothrow)

// --- the HAL (the boundary) ------------------------------------------------------------------------------
class Scheduler {
public:
    virtual void delay(uint16_t ms) = 0;
    virtual ~Scheduler() {}
};
class Util {
public:
    bool armed() const { return _armed; }
    bool _armed;
};
class HAL {
public:
    Scheduler *scheduler;
    Util *util;
};
extern const HAL &hal;

// --- the simulator object: a class of a namespace, a singleton reached through a pointer accessor -------
namespace SimNS {
class Sim {
public:
    Sim();
    static Sim *_singleton;
    static Sim *get_singleton() { return _singleton; }
    uint8_t count;
    float bias;
};
Sim *Sim::_singleton = nullptr;
Sim::Sim()
{
    if (_singleton != nullptr) {
        count = 0;
    }
    _singleton = this;
    count = 2;
    bias = 0.5f;
}
}  // namespace SimNS

namespace AP {
SimNS::Sim *sim() { return SimNS::Sim::get_singleton(); }
}

// --- the scheduler: delays step a clock -----------------------------------------------------------------
class SchedImpl : public Scheduler {
public:
    void delay(uint16_t ms) override { _clock_ms += ms; _delays++; }
    uint32_t _clock_ms;
    uint16_t _delays;
};

// --- AP_Common/TSIndex.h --------------------------------------------------------------------------------
template <class base_type, class tag> class typesafe_index
{
public:
    explicit typesafe_index(base_type i = base_type()) : p(i) {}
    constexpr base_type get_int() const { return p; }
    typesafe_index operator++(int) { return typesafe_index(p++); }
    bool operator<(const base_type& val) const { return (p < val); }
private:
    base_type p;
};
class TAG_Slot;
typedef typesafe_index<uint8_t, TAG_Slot> SlotIndex;

template <class base_type, uint32_t num_instances, typename accessor_type> class RestrictArray
{
public:
    base_type _priv_instance[num_instances];
    base_type& operator[](const accessor_type& index) { return _priv_instance[index.get_int()]; }
    const base_type& operator[](const accessor_type& index) const { return _priv_instance[index.get_int()]; }
};

// --- a bus id: a struct of bit-fields over an integer ----------------------------------------------------
enum BusKind { BUS_NONE = 0, BUS_I2C = 1, BUS_SPI = 2, BUS_SIM = 4 };
struct BusFields {
    enum BusKind kind : 3;
    uint8_t bus : 5;
    uint8_t address;
    uint8_t devtype;
};
union BusId {
    struct BusFields f;
    uint32_t value;
};

uint32_t make_bus_id(enum BusKind kind, uint8_t bus, uint8_t address, uint8_t devtype)
{
    union BusId d {};
    d.f.kind = kind;
    d.f.bus = bus;
    d.f.address = address;
    d.f.devtype = devtype;
    return d.value;
}

// --- a table of an anonymous struct type -----------------------------------------------------------------
static const struct {
    float above;
    float gain;
} gain_table[] = {
    { -100.0f, 0.5f },
    { 0.0f, 1.0f },
    { 1000.0f, 1.5f },
};

// --- the front end and its back ends -----------------------------------------------------------------------
class Front;

class Backend {
public:
    Backend(Front &front, uint8_t index);
    virtual ~Backend() {}
    virtual void update() = 0;
protected:
    Front &_front;
    uint8_t _index;
    uint8_t _copy_of_index{_index};
};

struct Slot {
    float value;
    float sum;
    uint32_t bus_id;
    bool healthy;
};

class Front {
public:
    void init();
    void update();
    void calibrate();
    float weighted(const float *scale = nullptr) const;
    void publish(uint8_t i, float v);
    float sum_healthy() const;
    uint8_t first_unhealthy() const;
    uint8_t count() const { return _count; }
    RestrictArray<Slot, 3, SlotIndex> _slots;
    Backend *_backends[3];
    uint8_t _count;
    float _weights[3];
    uint32_t _calibrations;
};

class SimBackend : public Backend {
public:
    SimBackend(Front &front, uint8_t index) : Backend(front, index) {}
    void update() override
    {
        const SimNS::Sim *sp = AP::sim();
        if (sp == nullptr) {
            return;
        }
        float v = hal.util->armed() ? 1.0f : 0.0f;
        _front.publish(_index, v + sp->bias + float(_updates));
        _updates++;
    }
    static uint8_t created;
private:
    uint32_t _updates;
};
uint8_t SimBackend::created = 0;

Backend::Backend(Front &front, uint8_t index) : _front(front), _index(index) {}

void Front::init()
{
    for (auto &w : _weights) {
        w = 1.0f;
    }
    for (SlotIndex i(0); i < 3; i++) {
        _slots[i].bus_id = make_bus_id(BUS_SIM, i.get_int(), 1, 7);
    }
    const uint8_t n = AP::sim()->count;
    for (uint8_t i = 0; i < n && _count < 3; i++) {
        _backends[_count] = NEW_NOTHROW SimBackend(*this, _count);
        _count++;
        SimBackend::created++;
    }
}

void Front::publish(uint8_t i, float v)
{
    Slot &slot = _slots[SlotIndex(i)];
    slot.value = v;
    slot.sum += v;
    slot.healthy = v == v;
}

void Front::update()
{
    for (uint8_t i = 0; i < _count; i++) {
        _backends[i]->update();
    }
    Slot *last = &_slots._priv_instance[_count > 0 ? _count - 1 : 0];
    last->sum *= 0.5f;
}

void Front::calibrate()
{
    for (SlotIndex i(0); i < 3; i++) {
        if (!_slots[i].healthy) {
            continue;
        }
        const float &v = _slots[i].value;
        _weights[i.get_int()] = v;
        _slots[i].value = v * 2.0f;
        _weights[i.get_int()] += v;
    }
    for (uint8_t k = 0; k < 3; k++) {
        if (gain_table[k].above < _weights[0]) {
            _weights[k] *= gain_table[k].gain;
        }
    }
    hal.scheduler->delay(10);
    _calibrations++;
}

float Front::weighted(const float *scale) const
{
    float acc = 0.0f;
    for (SlotIndex i(0); i < 3; i++) {
        acc += _slots[i].value * _weights[i.get_int()];
    }
    if (scale) {
        acc *= *scale;
    }
    return acc;
}

float Front::sum_healthy() const
{
    float acc = 0.0f;
    for (SlotIndex i(0); i < 3; i++) {
        if (_slots[i].healthy) {
            acc += _slots[i].sum;
        }
    }
    return acc;
}

uint8_t Front::first_unhealthy() const
{
    for (SlotIndex i(0); i < 3; i++) {
        if (!_slots[i].healthy) {
            return i.get_int();
        }
    }
    return 3;
}

// the objects as a vehicle defines them
SimNS::Sim sim;
SchedImpl sched;
Front front;

float scaled_weight(float s)
{
    return front.weighted(&s) + front.weighted();
}
