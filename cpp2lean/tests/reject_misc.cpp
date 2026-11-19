// cpp2lean rejection test: more constructs outside the phase 1 subset, one per declaration. Each
// line marked expect-reject must be reported (reject_misc.expected), and no other line.
#include <cmath>

float global_state = 0.0f;  // expect-reject

struct Pair { float a, b; };  // accepted since phase 2 (a plain struct)

int for_with_input_bound(int n)
{
    int s = 0;
    for (int i = 0; i < n; i++) s += i;  // expect-reject
    return s;
}

float uses_goto(float x)
{
    if (x > 0) goto done;  // expect-reject
    x = -x;
done:
    return x;
}

float reads_uninitialized(bool c)
{
    float y;
    if (c) y = 1.0f;
    return y;  // expect-reject
}

float allocates(float x)
{
    float *p = new float(x);  // expect-reject
    return *p;
}

void no_result(float x) { (void)x; }  // expect-reject

float mutual_a(float x);
float mutual_b(float x) { return x > 1.0f ? mutual_a(x * 0.5f) : x; }  // expect-reject
float mutual_a(float x) { return mutual_b(x - 1.0f); }  // expect-reject

float with_switch(int k)
{
    switch (k) {  // accepted since phase 2 (switch on an integer)
    case 0: return 1.0f;
    default: return 0.0f;
    }
}

float counter_modified(float x)
{
    for (int i = 0; i < 4; i++) {  // expect-reject
        x += 1.0f;
        i += 1;
    }
    return x;
}

float string_length() { return (float)sizeof("abc"); }  // expect-reject
