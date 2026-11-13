// --member-pointers (README.md, "Phase 3: AP_AHRS translated"): pointers and references to the member
// objects of a World object, in small, on AP_AHRS's patterns. The AHRS holds its backends and their
// results as member objects (`dcm`, `ekf3`, `dcm_estimates`, ...), selects them through pointer members
// set from `&member` (`backend_for_type`, `estimates_for_type`), calls virtual member functions and reads
// and writes fields through those pointers, passes `*p` to reference parameters, compares addresses, and
// iterates over a member array of structs of two references bound to the members
// (`backends_and_estimates[]`, AP_AHRS.h:1051). With the option each member object of a World object whose
// address is taken (or which such a reference is bound to) has a `WPtr` tag; a pointer to it is the tag,
// a reference member bound to it is the tag, a call through it a `match` over the running object's own
// members, a read or write through it a field selected by the tag.
#include <cstdint>

class Engine {
public:
    void step(float x) {
        t += 1;
        level = level * 0.75f + x;
    }
    bool good() const { return t > 3 && level > -5.0f; }
    float level;
    uint32_t t;
};

class Backend {
public:
    struct Estimates {
        bool healthy;
        bool initialised;
        float roll;
        double pos;
        uint16_t resets;
        bool provides_origin;
        bool get_roll(float &r) const {
            r = roll;
            return healthy;
        }
    };
    virtual void update(float x) = 0;
    virtual void get_results(Estimates &results) = 0;
    virtual bool get_origin(double &o) const { return false; }
    virtual bool set_origin(double o) { return false; }
    virtual void reset() {}
    virtual uint8_t kind() const = 0;
};

// the fallback (AP_AHRS_DCM): state of its own
class Fallback : public Backend {
public:
    void update(float x) override {
        acc = acc * 0.5f + x;
        n++;
    }
    void get_results(Estimates &r) override {
        r.healthy = n > 2;
        r.initialised = true;
        r.roll = acc;
        r.pos = acc * 2.0;
        r.resets = n % 7;
        r.provides_origin = false;
    }
    void reset() override {
        acc = 0;
        n = 0;
    }
    uint8_t kind() const override { return 0; }
    float acc;
    uint16_t n;
};

// the main filter (AP_AHRS_NavEKF3): a static member object that is a World object of its own
class Main : public Backend {
public:
    void update(float x) override {
        if (!started) {
            started = x > 0.5f;
            return;
        }
        eng.step(x);
    }
    void get_results(Estimates &r) override {
        r.healthy = started && eng.good();
        r.initialised = started;
        r.roll = eng.level;
        r.pos = have_origin ? origin + eng.level : 0.0;
        r.resets = eng.t % 5;
        r.provides_origin = have_origin;
    }
    bool get_origin(double &o) const override {
        if (!have_origin) {
            return false;
        }
        o = origin;
        return true;
    }
    bool set_origin(double o) override {
        origin = o;
        have_origin = true;
        return true;
    }
    uint8_t kind() const override { return 3; }
    static Engine eng;
    bool started;
    bool have_origin;
    double origin;
};

class Ahrs {
public:
    Ahrs() {
        update_configured();
        update_active();
    }
    void update(float x, uint8_t type) {
        _type = type;
        update_configured();
        configured_backend->update(x);
        *configured_estimates = {};
        configured_backend->get_results(*configured_estimates);
        try_set_origin(*configured_backend, *configured_estimates);
        for (auto &be : backends_and_estimates) {
            if (&be.backend == configured_backend) {
                continue;
            }
            be.backend.update(x);
            be.estimates = {};
            be.backend.get_results(be.estimates);
            try_set_origin(be.backend, be.estimates);
        }
        update_active();
        roll = active_estimates->roll;
        roll_ok = active_estimates->get_roll(roll2);
        if (active_estimates == &fallback_estimates) {
            fallback_count++;
        }
        kinds = configured_backend->kind() * 16 + active_backend->kind();
    }
    void reset() {
        for (auto &be : backends_and_estimates) {
            be.backend.reset();
        }
        done_origin = false;
    }
    bool set_origin(double o) {
        for (auto &be : backends_and_estimates) {
            auto &backend = be.backend;
            if (&backend == active_backend) {
                continue;
            }
            backend.set_origin(o);
        }
        return active_backend->set_origin(o);
    }
    bool healthy() const { return configured_estimates->healthy; }
    bool get_origin(double &o) const {
        const Backend *b = backend_for(_type);
        if (b == nullptr) {
            return false;
        }
        return b->get_origin(o);
    }
    float roll;
    float roll2;
    bool roll_ok;
    uint8_t kinds;
    uint32_t fallback_count;

private:
    Backend *backend_for(uint8_t type) {
        switch (type) {
        case 0:
            return &fallback;
        case 3:
            return &main;
        }
        return nullptr;
    }
    const Backend *backend_for(uint8_t type) const {
        return const_cast<Ahrs *>(this)->backend_for(type);
    }
    Backend::Estimates *estimates_for(uint8_t type) {
        switch (type) {
        case 0:
            return &fallback_estimates;
        case 3:
            return &main_estimates;
        }
        return nullptr;
    }
    void update_configured() {
        Backend *b = backend_for(_type);
        if (b != nullptr) {
            configured_backend = b;
            configured_estimates = estimates_for(_type);
        }
    }
    void update_active() {
        uint8_t t = 0;
        if (_type == 3 && main_estimates.healthy) {
            t = 3;
        }
        active_backend = backend_for(t);
        active_estimates = estimates_for(t);
    }
    void try_set_origin(const Backend &source, const Backend::Estimates &source_estimates) {
        if (done_origin || !source_estimates.provides_origin) {
            return;
        }
        double o;
        if (!source.get_origin(o)) {
            return;
        }
        for (auto &be : backends_and_estimates) {
            if (&be.estimates == &source_estimates) {
                continue;
            }
            be.backend.set_origin(o);
        }
        done_origin = true;
    }
    uint8_t _type;
    bool done_origin;
    Fallback fallback;
    Backend::Estimates fallback_estimates;
    Main main;
    Backend::Estimates main_estimates;
    struct {
        Backend &backend;
        Backend::Estimates &estimates;
    } backends_and_estimates[2] {
        { fallback, fallback_estimates },
        { main, main_estimates },
    };
    Backend *configured_backend;
    Backend::Estimates *configured_estimates;
    Backend *active_backend;
    Backend::Estimates *active_estimates;
};

Engine Main::eng;
Ahrs ahrs;
