// cpp2lean-options: --nest --world --world-pointers --front-ends --ins-gps --pointer-params --runtime-loops --general-loops --ekf-types --ekf-arrays --boundary Manager
// The limits of --ins-gps (README.md "Phase 3: AP_InertialSensor, AP_GPS and AP_NavEKF_Source"): each line marked
// expect-reject is reported, nothing else.
#include <cstdint>
#include <new>

class Port {
public:
    virtual uint32_t baud() const = 0;
    virtual ~Port() {}
};
class PortImpl : public Port {
public:
    uint32_t baud() const override { return 9600; }
};
class Manager {
public:
    Port *find(uint8_t kind, uint8_t instance) const;
};
const Manager &manager();

struct Slot {
    float v;
};
struct Count {
    Count() : n(1) {}
    uint8_t n;
};

class Front;
class Back {
public:
    Back(Front &f, Slot &slot) : _front(f), _slot(slot) {}
    virtual ~Back() {}
    virtual void run() { _slot.v += 1.0f; }
private:
    Front &_front;
    Slot &_slot;
};

class Front {
public:
    void make(uint8_t i) {
        Slot local[2];
        _backs[i] = new (std::nothrow) Back(*this, local[i]);   // expect-reject
    }
    void ports(uint8_t a, uint8_t b) {
        _port = manager().find(a, b);                           // expect-reject
    }
    uint8_t counts() {
        Count c[2];                                             // expect-reject
        return c[0].n;
    }
    Slot slots[2];
    Back *_backs[2];
    Port *_port;
};

PortImpl port;
Front front;
