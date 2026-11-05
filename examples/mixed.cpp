// cpp2lean demo (phase 1), second file: the rest of the phase 1 subset. Every <cmath> mapping,
// integer widths and conversions, bitwise operators, a counted while loop, side effects inside
// expressions, short circuit with an effect. Written so that no input executes undefined behavior.
#include <cmath>
#include <cstddef>
#include <cstdint>

constexpr int kTaps = 4;
static const double kScale = 0.1;
static const float kWeights[3] = {0.5f, 0.25f, 0.125f};

float trig_mix(float x, float y)
{
    float a = sinf(x) + cosf(y) - tanf(x * 0.25f);
    float b = atan2f(y, x) + asinf(fmaxf(-1.0f, fminf(1.0f, x))) + acosf(fminf(fmaxf(y, -1.0f), 1.0f));
    float c = expf(fminf(x, 10.0f)) + logf(fabsf(y) + 1.0f) + powf(fabsf(x), 0.5f) + sqrtf(fabsf(y));
    return a * b + c + atanf(x) + floorf(x) + ceilf(y) + roundf(x);
}

double trig_mix_d(double x, double y)
{
    double a = sin(x) + cos(y) - tan(x * 0.25);
    double b = atan2(y, x) + asin(fmax(-1.0, fmin(1.0, x))) + acos(fmin(fmax(y, -1.0), 1.0));
    double c = exp(fmin(x, 10.0)) + log(fabs(y) + 1.0) + pow(fabs(x), 0.5) + sqrt(fabs(y));
    return a * b + c + atan(x) + floor(x) + ceil(y) + round(x);
}

int classify(double x)
{
    if (std::isnan(x)) return 0;
    else if (std::isinf(x)) return x > 0 ? 1 : -1;
    else if (!std::isfinite(x)) return 99;
    return x == 0.0 ? 2 : 3;
}

// -x flips the sign bit; 0 - x does not (they differ at x = +0 and for NaN signs).
float negate(float x) { return -x; }
float zero_minus(float x) { return 0.0f - x; }

// Integer widths and conversions, division and remainder of negatives, shifts, bitwise.
int32_t int_mix(int32_t a, int32_t b)
{
    int64_t wide = (int64_t)a * b;
    int32_t d = (b == 0 || (a == INT32_MIN && b == -1)) ? 7 : a / b;
    int32_t r = (b == 0 || b == -1) ? 3 : a % b;
    uint32_t u = (uint32_t)a ^ ((uint32_t)b << (b & 31));
    int8_t small = (int8_t)a;
    uint16_t mid = (uint16_t)b;
    int32_t shifted = a >> 3;
    u += mid;
    bool neg = a < 0;
    int32_t acc = small + mid + neg;
    acc ^= (int32_t)(wide >> 32);
    acc = (acc & 0xFFFF) + (int32_t)(u % 1000u);
    return (int32_t)((uint32_t)acc + (uint32_t)d + (uint32_t)r + (uint32_t)shifted + ~u);
}

// Float to integer conversions on a clamped value; a variable assigned on both branches.
int32_t quantize(float x, int32_t steps)
{
    float c;
    if (isnan(x)) c = 0.0f;
    else c = fmaxf(-1000.0f, fminf(1000.0f, x));
    int32_t q = (int32_t)(c * 100.0f);
    int16_t s = (int16_t)c;
    double dc = c;
    dc *= kScale;
    unsigned uu = (unsigned)(c + 1000.0f);
    bool nz = c;
    bool nzi = steps;
    q += nz + nzi;
    int k = (int)dc;
    return q + s + (int32_t)uu + k + (int32_t)(uint8_t)uu;
}

// A counted while loop, side effects inside expressions, short circuit with an effect.
float effects(float x, int n)
{
    int i = 0;
    int j = 0;
    int hits = 0;
    float acc = x;
    while (i < kTaps) {
        acc = acc * 0.5f + j++;
        if (n > 0 && ++j > n) {
            acc -= 1.0;
        }
        i++;
    }
    int k = (n > 3) ? j-- : (j += 2);
    for (int m = 10; m > 0; m -= 3) {
        acc += m * 0.25f;
    }
    for (size_t s = 0; s < 3; ++s) acc += kWeights[s];
    for (unsigned w = 0; w != 8u; w += 2) {
        if (w == 4u) continue;
        acc *= 1.5f;
    }
    bool flag = (k & 1) || (++hits > 0);
    return acc + k + hits + (flag ? 0.5f : 0.0f);
}

// Integer promotions of narrow types, 64-bit division, bool comparison (promoted to int).
uint8_t add_u8(uint8_t a, uint8_t b) { return a + b; }
int64_t div_i64(int64_t a) { return a / 3 + a % 3 + (a >> 2); }
bool implies_eq(bool p, bool q) { bool r = p; r = !r || q; return r == p; }
