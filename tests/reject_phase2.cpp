// cpp2lean-options: --pointer-params --runtime-loops --drop trap
// The limits of the phase 2 constructs (pointers into arrays, loops bounded by runtime values):
// each function is rejected at the line marked expect-reject.
#include <cstdint>
#include <cstring>
#include <new>

int trap(int m) { return m; }

int32_t r_diff(const float *p, const float *q) { return (int32_t)(q - p); }  // expect-reject

static void addto(float *y, const float *x, uint16_t n)
{
    for (uint16_t i = 0; i < n; i++) {
        y[i] += x[i];
    }
}

float r_alias(float a)
{
    float v[2] = {a, a};
    addto(v, v, 2);  // expect-reject
    return v[0];
}

float r_memset_value(float a)
{
    float v[2] = {a, a};
    memset(v, 1, 2 * sizeof(float));  // expect-reject
    return v[0];
}

float r_memset_bytes(float a)
{
    float v[2] = {a, a};
    memset(v, 0, 8);  // expect-reject
    return v[0];
}

float r_memcpy_overlap(float a)
{
    float v[2] = {a, a};
    memcpy(v, v + 1, sizeof(float));  // expect-reject
    return v[0];
}

bool r_memcmp_order(uint32_t a, uint32_t b)
{
    uint32_t x[1] = {a};
    uint32_t y[1] = {b};
    return memcmp(x, y, sizeof(uint32_t)) < 0;  // expect-reject
}

float r_new_scalar(float a)
{
    float *p = new (std::nothrow) float;  // expect-reject
    *p = a;
    float r = *p;
    delete p;
    return r;
}

float r_owned_moved(float a)
{
    float *q = new (std::nothrow) float[4];  // expect-reject
    q[1] = a;
    q++;
    float r = q[0];
    return r;
}

uint32_t r_wrap(uint16_t n)
{
    uint32_t t = 0;
    for (uint8_t i = 0; i < n; i++) {  // expect-reject
        t += i;
    }
    return t;
}

int32_t r_bound_changes(int32_t n)
{
    int32_t t = 0;
    for (int32_t i = 0; i < n; i++) {  // expect-reject
        n--;
        t += i;
    }
    return t;
}

uint32_t r_while_break(uint16_t k)
{
    uint32_t t = 0;
    while (k--) {  // expect-reject
        if (t > 5) {
            break;
        }
        t += k;
    }
    return t;
}

int32_t r_while_signed(int16_t k)
{
    int32_t t = 0;
    while (k--) {  // expect-reject
        t += k;
    }
    return t;
}

static uint32_t sum_skip(const uint8_t *p, uint32_t len)
{
    const uint8_t *end = p + len;
    uint32_t s = 0;
    for (; p != end; p++) {  // expect-reject
        if (*p == 0) {
            continue;
        }
        s += *p;
    }
    return s;
}

uint32_t r_continue(uint8_t a)
{
    uint8_t b[2] = {a, a};
    return sum_skip(b, 2);
}

float r_ref_element(float a, uint8_t i)
{
    float v[2] = {a, a};
    float &r = v[i & 1];  // expect-reject
    r = 2.0f;
    return v[0];
}

float r_matrix(float a)
{
    float m[2][2];  // expect-reject
    m[0][0] = a;
    return m[0][0];
}

uint32_t r_byte_write(uint32_t v)
{
    ((uint8_t *)&v)[0] = 1;  // expect-reject
    return v;
}

int r_dropped_value(int a)
{
    int old = trap(a);
    return old;  // expect-reject
}

bool r_cmp_arrays(const float *a, const float *b) { return a < b; }  // expect-reject

static float first(const float *p) { return p[0]; }

float r_cmp_caller(float a)
{
    float x[1] = {a};
    float y[1] = {a};
    return r_cmp_arrays(x, y) ? first(x) : first(y);
}
