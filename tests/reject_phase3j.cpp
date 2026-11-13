// cpp2lean-options: --nest --world --world-pointers --member-objects --pointer-params --array-offsets --swap-out --runtime-loops
// The limits of --array-offsets, --swap-out and --member-objects (README.md "Phase 3: AP_AHRS, and speed"):
// each line marked expect-reject is reported, nothing else. The AP_AHRS patterns that the translator does not
// model yet: pointers to member objects of a World object (`configured_backend = &dcm`, AP_AHRS.cpp:245) and
// calls through them, a range-based `for` over a member array of structs of references (`backends_and_estimates`).
#include <cstdint>
#include <cstring>

class Util {
public:
    static void zero(double *v, uint8_t n) {
        memset(v, 0, n * sizeof(double));
    }
    static void add_into(double *dst, const double *src, uint8_t n) {
        for (uint8_t i = 0; i < n; i++) {
            dst[i] += src[i];
        }
    }
};

class Backend {
public:
    virtual void update() = 0;
    float value;
};

class First : public Backend {
public:
    void update() override { value += 1.0f; }
};

class Second : public Backend {
public:
    void update() override { value *= 0.5f; }
};

class Engine {
public:
    void step(float x) { level += x; }
    float level;
};

class Holder {
public:
    static Engine engine;
    void select(uint8_t k) {
        if (k == 1) {
            active = &second;               // expect-reject
        }
    }
    void update() {
        active->update();                   // expect-reject
        engine.step(1.0f);
    }
    void update_all() {
        for (auto &e : entries) {           // expect-reject
            e.backend.update();
        }
    }
    void rows() {
        Util::zero(&m[1], 3);
        Util::add_into(&m[0], &m[2], 2);    // expect-reject
    }
private:
    First first;
    Second second;
    Backend *active;
    struct {
        Backend &backend;
    } entries[2] {
        { first },                          // expect-reject
        { second },
    };
    double m[6];
};

Engine Holder::engine;
Holder holder;
