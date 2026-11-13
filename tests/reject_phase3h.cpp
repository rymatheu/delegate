// cpp2lean-options: --nest --world --world-pointers --front-ends --pointer-params --runtime-loops --general-loops --ekf-types
// The limits of --front-ends (README.md "Phase 3: sensor front ends and AP_Param"): each line marked
// expect-reject is reported, nothing else.
#include <cstdint>
#include <initializer_list>

struct Flags {
    uint8_t kind : 3;               // expect-reject
    uint8_t rest : 5;               // expect-reject
};

class Holder {
public:
    float vals[3];
    float total() const { float t = 0.0f; for (float v : vals) { t += v; } return t; }
    float &pick(uint8_t i) { return i < 3 ? vals[i] : vals[0]; }
    void scale(float k) {
        float &r = pick(1);         // expect-reject
        r *= k;
    }
    void walk_list() {
        for (float v : {1.0f, 2.0f}) {  // expect-reject
            vals[0] += v;
        }
    }
    Flags flags;
};

Holder holder;
