// cpp2lean-options: --boundary Planner --output-log --drop Seg::noisy::calls --drop Seg::quiet::calls
// cpp2lean rejection test (phase 3, AC_WPNav constructs): the constructs added for AC_WPNav, SCurve
// and SplineCurve, used outside their limits. Each line marked expect-reject must be reported
// (reject_phase3d.expected), and no other line.
#include <cstdint>

class Planner {
public:
    float rate;
    void reset();
    float speed() const;
    const float &scaled(float k) const;
};

class Box {
public:
    float v;
    void set(float x) { v = x; }
};

// an array of objects of a class that is not in a --lib-dir library
class Boxes {
public:
    Box boxes[2];  // expect-reject
    void set(float x) { boxes[0].v = x; }
};

class Seg {
public:
    struct {
        uint8_t on : 1;
    } flags;
    float t[3];
    float gain;
    uint8_t num;
    uint8_t seen;

    // accepted: a one-bit field assigned (modulo 2); an increment would not wrap at 1 in Lean's UInt8
    void mark() { flags.on = 1; }
    void bump() { ++flags.on; }  // expect-reject

    // a loop from a signed variable start (only unsigned starts no wider than the counter)
    float sum_from(int first)
    {
        float acc = 0;
        for (int i = first; i < 3; i++) {  // expect-reject
            acc += t[i];
        }
        return acc;
    }

    // a loop bounded by a member in a non-const member function (the body might change it)
    void count()
    {
        for (uint8_t i = 0; i < num; i++) {  // expect-reject
            seen++;
        }
    }

    // a reference argument that is an element of a member the callee also reaches: only data
    // members are bound to the parameter for the call
    void put(float &x) { x = 1.0f; gain = t[0]; }
    void put_first() { put(t[0]); }  // expect-reject

    // accepted: a static local left out (--drop), and the statements that only touch it
    float quiet() { static int calls; if (!calls) { calls = 1; } return gain; }
    // a static local left out (--drop) whose value is used
    float noisy() { static int calls; if (!calls) { calls = 1; } return gain + calls; }  // expect-reject
};

class Nav {
public:
    // (the limits of the live boundary reads of earlier phases, --boundary-live, are now those of
    // the World, tests/reject_world.cpp)
    explicit Nav(Planner &p) : _p(p) {}
    float after_reset() { _p.reset(); return _p.speed(); }
private:
    Planner &_p;
    float _v;
};
