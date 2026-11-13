// cpp2lean-options: --world --world-pointers --ekf-types --runtime-loops --reachable --indexed-inputs --boundary Sensor --drop Log::write --use Filt::step --use Filt::count --use Filt::text --use Filt::fill --use Filt::again --use Filt::keep
// cpp2lean rejection test (Phase 3: AP_DAL and NavEKF3): the limits of --reachable, --indexed-inputs, static
// locals, the value range of loop bounds and dropped calls. Each line marked expect-reject must be
// reported, and nothing else.
#include <cstdint>

class Sensor {
public:
    float value(uint8_t i, uint8_t j) const;
    float scaled(uint8_t i) const;
};
Sensor &sensor();

class Log {
public:
    void write(uint32_t v);
};
Log &logger();

struct Pair {
    float a;
    float b;
};

class Filt {
public:
    void step(uint8_t i, uint8_t j) {
        y = sensor().scaled(i);
        x = sensor().value(i, j);                       // expect-reject
    }
    void again() {
        static uint32_t calls = 3;                      // expect-reject
        calls++;
    }
    void keep() {
        static Pair last;                               // expect-reject
        last.a = x;
    }
    uint32_t count() {
        uint32_t n = 0;
        for (uint8_t k = 0; k <= lim; k++) {            // expect-reject
            n++;
        }
        return n;
    }
    void text() {
        logger().write(bump());                         // expect-reject
    }
    void fill(uint8_t v) { lim = v; }
private:
    uint32_t bump() { return ++hits; }
    float x;
    float y;
    uint8_t lim;
    uint32_t hits;
};

Filt filt;
