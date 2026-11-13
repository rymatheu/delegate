// cpp2lean-options: --nest --world --world-pointers --member-pointers --ahrs-ext --reachable --use Ahrs::update --use Ahrs::outside --use Ahrs::fields --use Ahrs::sub --use Ahrs::pass --use Ahrs::bytes --use Other::poke --use Holder::touch
// The limits of --member-pointers and --ahrs-ext (README.md "Phase 3: AP_AHRS translated"): each line marked
// expect-reject is reported, nothing else. A pointer to member objects is modeled only in the member functions of
// the object that holds them; a member is read or written through one only if every object it may designate is of
// one class (calls dispatch); no subscript; an argument for a reference parameter modeled as a tag must designate
// one of them; a reference member of an unnamed struct must be bound to a member object; a pointer whose class has
// member objects and other objects is rejected (not exercised here); `memcmp` only as `memcmp(this, &x, sizeof(*this))`.
#include <cstdint>
#include <cstring>

class Backend {
public:
    struct Estimates {
        bool healthy;
        float roll;
    };
    virtual void update(float x) = 0;
    float gain;
};

class A : public Backend {
public:
    void update(float x) override { acc += x * gain; }
    float acc;
};

class B : public Backend {
public:
    void update(float x) override { n++; }
    uint16_t n;
};

class Other;

class Ahrs {
public:
    Ahrs() {
        backend = &a;
        estimates = &a_est;
        if (count > 3) {
            backend = &b;
        }
    }
    void update(float x) {
        backend->update(x);
        estimates->roll = x;
    }
    float fields() {
        return backend->gain;                               // expect-reject
    }
    float sub() {
        return estimates[1].roll;                           // expect-reject
    }
    void take(const Backend::Estimates &e) {
        if (&e == estimates) {
            count++;
        }
    }
    void pass() {
        Backend::Estimates local {};
        take(local);                                        // expect-reject
    }
    bool bytes(const Ahrs &other) const {
        return memcmp(&other, this, sizeof(*this)) == 0;    // expect-reject
    }
    Backend::Estimates *outside();
    A a;
    Backend::Estimates a_est;
    B b;
    Backend::Estimates b_est;
    Backend *backend;
    Backend::Estimates *estimates;
    uint32_t count;
};

class Holder {
public:
    void touch() {
        refs[0].e.healthy = true;
    }
    struct Inner {
        Backend::Estimates e;
    } inner;
    struct {
        Backend::Estimates &e;
    } refs[1] {
        { inner.e },                                        // expect-reject
    };
};

class Other {
public:
    void poke(Ahrs &h) {
        h.estimates->healthy = true;                        // expect-reject
    }
};

Backend::Estimates *Ahrs::outside()
{
    return &b_est;
}

Ahrs ahrs;
Holder holder;
Other other;
