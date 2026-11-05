// cpp2lean rejection test: three functions outside the phase 1 subset. The translator must report
// each at the line and column named in reject_cases.expected (the lines marked expect-reject) and
// exit with status 2.
#include <cmath>

// A pointer parameter.
float sum_pointer(const float *v, int n)  // expect-reject
{
    float s = 0.0f;
    for (int i = 0; i < 4; i++) s += v[i];
    return n > 0 ? s : 0.0f;
}

// Recursion.
int factorial(int n)
{
    if (n <= 1) return 1;
    return n * factorial(n - 1);  // expect-reject
}

// A loop whose trip count depends on an input.
float halve_until_small(float x)
{
    while (fabsf(x) > 1.0f) {  // expect-reject
        x *= 0.5f;
    }
    return x;
}
