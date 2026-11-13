// cpp2lean-options: --world --ekf-types --ekf-arrays --ring-buffers --runtime-loops
// The limits of the Phase 3 EKF data structures (README.md, "Phase 3: EKF data structures"): each
// construct is rejected at the line marked expect-reject.
#include <cstdint>
#include <cstdlib>
#include <cstring>

typedef struct {
    uint32_t time_ms;
} stamp_t;

struct item : stamp_t {
    float v;
};

class erased {
public:
    erased(uint8_t n) : elsize(n), buffer(nullptr) {}
    bool init(uint8_t k) {
        buffer = calloc(k, elsize);
        return true;
    }
    void put(uint8_t i, const void *e) {
        memcpy(get_offset(i), e, 4);                    // expect-reject
    }
private:
    const uint8_t elsize;
    void *buffer;
    void *get_offset(uint8_t idx) const {
        return (void*)(((uint8_t*)buffer)+idx*uint32_t(elsize));
    }
};

template <typename T>
class Wrap : erased {
public:
    Wrap() : erased(sizeof(T)) {}
    bool init(uint8_t k) { return erased::init(k); }
    void put(uint8_t i, const T &e) { erased::put(i, &e); }
};

class erased2 {
public:
    erased2(uint8_t n) : elsize(n), buffer(nullptr) {}
    void *first() const {                               // expect-reject
        return buffer;
    }
private:
    const uint8_t elsize;
    void *buffer;
};

class Holder {
public:
    void drain(uint8_t n) {
        while (count > 0) {                             // expect-reject
            if (n > 3) {
                count--;
            }
        }
    }
    void zero_row() {
        memset(M[1], 0, sizeof(M[1]));                  // expect-reject
    }
    void alias(uint8_t i) {
        double &e = A[i];                               // expect-reject
        i++;
        e = i;
    }
    void copy_bits(float f) {
        uint32_t u;
        memcpy(&u, &f, sizeof(u));                      // expect-reject
        count = u;
    }
    uint8_t count;
    double M[3][4];
    double A[4];
};

struct V3 { double x, y, z; };
struct Mixed { float a; int32_t b; float c; };

class Bad {
public:
    union {                                             // expect-reject
        float arr[3];
        Mixed s;
    };
    union {                                             // expect-reject
        struct {
            uint8_t two : 2;
            bool one : 1;
        } flags;
        uint32_t value;
    } wide;                                             // expect-reject
    static V3 shared;                                   // expect-reject
};

V3 Bad::shared;
Wrap<item> wrap;
Holder holder;
