// cpp2lean demo (phase 2, the leaf libraries: AP_Math's matrix_alg.cpp and crc.cpp, LowPassFilter2p,
// AP_Declination, AP_Common's Location and Bitmask), written for the demo. It uses the constructs the
// translator gained for them so that they are tested without the ArduPilot tree:
// pointer parameters into arrays (--pointer-params): `const T *` read by subscript, `T []` written
// (returned as for `T &`), a pointer that moves (`*p++`, `p != end`), a `const void *` read as bytes,
// a scalar out-pointer (`*acc += v`), a slice `a + k` / `&a[k]` written back after the call;
// local pointers holding arrays of their own (`new (std::nothrow) T[k]`, a function returning one,
// `delete[]`); `memset`, `memcpy` and `memcmp(...) == 0` over k elements; a local array written
// element by element before any read; loops bounded by runtime values (--runtime-loops): a signed
// counter from a runtime start, downward, to a runtime bound, `while (k--)`, a pointer loop; a local
// reference to a member of a local; a byte view of an integer; a constant table of two dimensions;
// static const members defined out of line; a static member called through an object; a value of a
// --drop function read only by left-out conditions; `memset(this, 0, sizeof(*this))`; `operator=`
// with a body; `__builtin_popcount`, `__builtin_ffs`, `labs`, `atan2(int, int)`, `copysign(float,
// double)`, `isnan` of an integer; `do { ... } while (false)`.
// Every function with array arguments is reached from a function of numbers, which the difftest drives.
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <new>

// ---- pointer parameters
static float sum(const float *x, uint16_t n)
{
    float s = 0.0f;
    for (uint16_t i = 0; i < n; i++) {
        s += x[i];
    }
    return s;
}

static void scale(float y[], uint16_t n, float k)
{
    for (uint16_t i = 0; i < n; i++) {
        y[i] *= k;
    }
}

static uint32_t checksum(const uint8_t *p, uint16_t len)
{
    uint32_t c = 0;
    while (len--) {
        c = (c << 1) ^ *p++;
    }
    return c;
}

static uint8_t xor_bytes(const void *data, uint32_t length)
{
    const uint8_t *p = (const uint8_t *)data;
    const uint8_t *end = p + length;
    uint8_t r = 0;
    for (; p != end; p++) {
        r ^= *p;
    }
    return r;
}

static void accumulate(uint64_t *acc, uint32_t v)
{
    *acc += v;
    *acc *= 3;
}

// ---- arrays of their own
static float *make(uint16_t n)
{
    float *r = new (std::nothrow) float[n];
    memset(r, 0, n * sizeof(float));
    return r;
}

float pipeline(float a, float b, float c, float d)
{
    float in[4] = {a, b, c, d};
    float *tmp = make(4);
    memcpy(tmp, in, 4 * sizeof(float));
    scale(tmp, 4, 2.0f);
    scale(tmp + 2, 2, -1.0f);
    const float s = sum(tmp, 4) + sum(&tmp[1], 3);
    delete[] tmp;
    return s;
}

uint32_t checksum4(uint8_t a, uint8_t b, uint8_t c, uint8_t d)
{
    const uint8_t buf[4] = {a, b, c, d};
    return checksum(buf, 4) + 7 * xor_bytes(buf, 3);
}

uint64_t accumulate3(uint32_t a, uint32_t b, uint32_t c)
{
    uint64_t acc = 1;
    accumulate(&acc, a);
    accumulate(&acc, b);
    accumulate(&acc, c);
    return acc;
}

bool same_prefix(uint32_t a, uint32_t b, uint32_t c)
{
    uint32_t x[3] = {a, b, c};
    uint32_t y[3] = {a, b, 0};
    memcpy(&y[2], &x[2], sizeof(uint32_t));
    return memcmp(x, y, 3 * sizeof(x[0])) == 0;
}

// ---- runtime-bounded loops
int32_t triangle(int32_t n)
{
    const int32_t m = n & 15;
    int32_t t = 0;
    for (int32_t i = m - 1; i >= 0; i--) {
        for (int32_t j = i + 1; j < m; j++) {
            t += j - i;
        }
    }
    return t;
}

// ---- a local array written before it is read, a local reference to a member
struct Pair {
    float x;
    float y;
};

float written_first(float a, float b)
{
    float w[3];
    w[0] = a;
    w[2] = b;
    w[1] = a * b;
    Pair p = Pair();
    p.x = a;
    p.y = b;
    float &r = p.y;
    r += w[1];
    return w[0] + w[1] - w[2] + p.y;
}

// ---- byte view, 2D table, bit builtins, integer and mixed library calls
uint8_t byte_of(uint32_t v, uint8_t j)
{
    return ((uint8_t *)&v)[j & 3];
}

static const float table[3][4] = {
    {1.5f, 2.5f, 3.5f, 4.5f},
    {-1.0f, -2.0f, -3.0f, -4.0f},
    {0.25f, 0.5f, 0.75f, 1.0f},
};

float lookup(uint8_t i, uint8_t j)
{
    return table[i % 3][j % 4];
}

int32_t bits(uint32_t v)
{
    return __builtin_popcount(v) * 100 + __builtin_ffs((int)v);
}

int64_t magnitude(int32_t a, int32_t b)
{
    return labs(a) + labs(b);
}

double bearing(int32_t dy, int32_t dx)
{
    return atan2(dy, dx) + copysign(1.0f, (double)dx);
}

bool int_nan(int32_t a)
{
    return isnan(a);
}

// ---- a value of a --drop function (an effect outside the model) read only by left-out conditions
int trap_mask(int m)
{
    return m;
}

float guarded(float a)
{
    float r = a * 2.0f;
    int old = trap_mask(1);
    if (old < 0) {
        // a report the model leaves out
    }
    r += 1.0f;
    if (old >= 0 && trap_mask(old) < 0) {
    }
    return r;
}

// ---- static const members defined out of line, a static member called through an object,
// `memset(this, 0, sizeof(*this))`, `operator=` with a body, `do { ... } while (false)`
class Grid {
public:
    Grid() { clear(); }
    void clear() { memset(this, 0, sizeof(*this)); }
    Grid &operator=(const Grid &other)
    {
        memcpy(cells, other.cells, sizeof(cells[0]) * 4);
        return *this;
    }
    static float unit(uint8_t i) { return SCALE * (float)(i % 4); }
    void put(uint8_t i, float v)
    {
        do {
            cells[i % 4] = v;
            count++;
        } while (false);
    }
    float weighted(const Grid &other) const
    {
        float acc = 0.0f;
        for (uint8_t i = 0; i < 4; i++) {
            acc += cells[i] * other.unit(i) + OFFSETS[i % 2];
        }
        return acc;
    }
    float get(uint8_t i) const { return cells[i % 4]; }
    static const float SCALE;
    static const float OFFSETS[2];
    float cells[4];
    uint16_t count;
};

const float Grid::SCALE = 0.5f;
const float Grid::OFFSETS[2] = {1.0f, -1.0f};

float grid_demo(float a, float b, uint8_t i)
{
    Grid g;
    g.put(i, a);
    g.put(i + 1, b);
    Grid h;
    h = g;
    h.put(i, b);
    return g.weighted(h) + h.get(i);
}
