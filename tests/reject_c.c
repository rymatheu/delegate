// cpp2lean-options: --general-loops
/* cpp2lean rejection test: the limits of the C constructs (README.md, "The C library"). */
#include <stdint.h>

float wide_union(float x)
{
	union {
		float f;
		uint64_t i; // expect-reject
	} u = {x};
	return u.f;
}

int continue_in_for(int n)
{
	int s = 0, i;
	for (i = 0; i * i < n; i++) { // expect-reject
		if (i == 2)
			continue;
		s += i;
	}
	return s;
}

int falls_through(int x)
{
	if (x > 5)
		goto out; // expect-reject
	x++;
	if (x > 2) {
out:
		x += 2;
	}
	return x;
}

int back_from_loop(int x)
{
	int i;
again:
	x++;
	for (i = 0; i < 3; i++) {
		if (x < 10)
			goto again; // expect-reject
	}
	return x;
}

float both_ways(float *p) // expect-reject
{
	return *p + p[1];
}

float caller(float x)
{
	return both_ways(&x);
}
