// Phase 3 (README.md, "Phase 3: EKF data structures"): the data forms of EKF3, as file-scope objects
// of a World (--world), translated with --ekf-types --ekf-arrays --ring-buffers --runtime-loops.
// - a type-erased ring buffer (`void *` storage + element size, calloc/memcpy/memset, an accessor
//   returning a pointer to an element) used only through a typed wrapper `Ring<T>` (EKF_Buffer.h/.cpp);
// - a struct named by a typedef and a struct deriving from it (EKF_obs_element_t, gps_elements);
// - `T a[N][M]` members and locals (flat row-major), `memset` of whole arrays and objects, `memcpy`
//   between objects with the same scalars, an array of structs holding 2D arrays written in place;
// - a runtime index into a field-index view and a local reference to it (EKFGSF_yaw::updateRotMat);
// - a union of an array and a struct (the struct a view of the array: EKF3's statesArray/stateStruct);
// - unions of one-bit bit-fields over an integer, named (`flags`) and anonymous (nav_filter_status,
//   gpsCheckStatus); a brace-initialized constant member; a mutable static array (KHP) shared by
//   every object, a field of the World; a `while (count > 0)` loop that counts down.
#include <cstdint>
#include <cstdlib>
#include <cstring>

typedef struct {
    uint32_t time_ms;
} stamp_t;

struct sample : stamp_t {
    float value;
    bool good;
};

class erased_ring {
public:
    erased_ring(uint8_t _elsize) : elsize(_elsize), buffer(nullptr) {}
    bool init(uint8_t _size) {
        if (buffer) {
            free(buffer);
        }
        buffer = calloc(_size, elsize);
        if (buffer == nullptr) {
            return false;
        }
        size = _size;
        count = 0;
        oldest = 0;
        return true;
    }
    void push(const void *element) {
        if (buffer == nullptr) {
            return;
        }
        const uint8_t head = (oldest + count) % size;
        memcpy(get_offset(head), element, elsize);
        if (count < size) {
            count++;
        } else {
            oldest = (oldest + 1) % size;
        }
    }
    bool pop_until(void *element, uint32_t t) {
        bool ret = false;
        while (count > 0) {
            stamp_t *el = (stamp_t *)get_offset(oldest);
            if (el->time_ms > t) {
                break;
            }
            memcpy(element, get_offset(oldest), elsize);
            ret = true;
            count--;
            oldest = (oldest + 1) % size;
        }
        return ret;
    }
    void clear() {
        memset(buffer, 0, size * uint32_t(elsize));
        count = 0;
    }
private:
    const uint8_t elsize;
    void *buffer;
    uint8_t size, oldest, count;
    void *get_offset(uint8_t idx) const {
        return (void*)(((uint8_t*)buffer)+idx*uint32_t(elsize));
    }
};

template <typename T>
class Ring : erased_ring {
public:
    Ring() : erased_ring(sizeof(T)) {}
    bool init(uint8_t n) { return erased_ring::init(n); }
    void push(const T &e) { erased_ring::push(&e); }
    bool pop_until(T &e, uint32_t t) { return erased_ring::pop_until(&e, t); }
    void clear() { erased_ring::clear(); }
};

struct V3 {
    double x, y, z;
    double &operator[](uint8_t i) { double *_v = &x; return _v[i]; }
};

struct M3 {
    V3 a, b, c;
    V3 &operator[](uint8_t i) { V3 *_v = &a; return _v[i]; }
};

struct Cell {
    double P[2][2];
    double X[2];
};

union health {
    struct {
        bool attitude : 1;
        bool velocity : 1;
        bool position : 1;
    } flags;
    uint32_t value;
};

class Common {
protected:
    static double KHP[4][4];
};

double Common::KHP[4][4];

class Data : Common {
public:
    Data() : ring() {}
    const double gain{0.25};

    void add_sample(uint32_t t, float v, bool g) {
        sample s1;
        s1.time_ms = t;
        s1.value = v;
        s1.good = g;
        ring.push(s1);
    }
    bool take(uint32_t t) {
        sample s1;
        s1.time_ms = 0;
        s1.value = 0;
        s1.good = false;
        bool ok = ring.pop_until(s1, t);
        last_value = s1.value;
        return ok;
    }
    void start(uint8_t n) { ring.init(n); }
    void flush() { ring.clear(); }

    void set_m(uint8_t i, uint8_t j, double v) { M[i % 3][j % 4] = v; }
    double row_sum(uint8_t i) {
        double s2 = 0;
        for (uint8_t j = 0; j < 4; j++) {
            s2 += M[i % 3][j];
        }
        return s2;
    }
    void zero_m() { memset(&M[0][0], 0, sizeof(M)); }
    void copy_rows(double k) {
        double first[2][4];
        memcpy(&first, &M, sizeof(first));
        for (uint8_t i = 0; i < 2; i++) {
            for (uint8_t j = 0; j < 4; j++) {
                M[i + 1][j] = first[i][j] * k;
            }
        }
    }
    void cell_step(uint8_t c, double v) {
        uint8_t m = c % 3;
        for (uint8_t i = 0; i < 2; i++) {
            for (uint8_t j = 0; j < 2; j++) {
                cells[m].P[i][j] = cells[m].P[j][i] * gain + v;
            }
            cells[m].X[i] += cells[m].P[i][i];
        }
    }
    double cell_trace(uint8_t c) { return cells[c % 3].P[0][0] + cells[c % 3].P[1][1]; }
    void scale_rows(double k) {
        for (uint8_t r = 0; r < 3; r++) {
            V3 &row = R[r];
            row[0] = row[0] * k + r;
            row[2] = row[1] - k;
        }
    }
    void set_state(uint8_t i, double v) { states[i % 6] = v; }
    double state_b_y() { return st.b.y; }
    void move(double dx) {
        st.a.x += dx;
        st.b = st.a;
    }
    void set_health(bool att, bool vel, uint8_t pos) {
        status.flags.attitude = att;
        status.flags.velocity = vel;
        status.flags.position = pos > 2;
        checks.bad_gps = !att;
        checks.bad_mag = vel && att;
    }
    uint32_t health_word() { return status.value + 16 * checks.value; }
    bool position_ok() { return status.flags.position && !checks.bad_mag; }
    void reset_health() {
        memset(&status, 0, sizeof(status));
        checks.value = 0;
    }
    void scratch(uint8_t i, double v) {
        KHP[i % 4][(i + 1) % 4] = v;
        auto &next = KHP;
        next[0][0] += v;
    }
    double scratch_sum() {
        double s3 = 0;
        for (uint8_t i = 0; i < 4; i++) {
            s3 += KHP[i][i] + KHP[i][(i + 1) % 4];
        }
        return s3;
    }
    float last() const { return last_value; }

private:
    Ring<sample> ring;
    float last_value;
    double M[3][4];
    Cell cells[3];
    M3 R;
    struct S { V3 a; V3 b; };
    union {
        double states[6];
        struct S st;
    };
    health status;
    union {
        struct {
            bool bad_gps : 1;
            bool bad_mag : 1;
        };
        uint16_t value;
    } checks;
};

Data data;
