// --array-offsets and --swap-out (README.md, "Phase 3: AP_AHRS, and speed"): the calls that copied arrays in
// the NavEKF3 translation, in small. A pointer into a row of a matrix passed to a function that zeroes part of
// it through `memset` (`zero_range(&Pmut[row][0], 0, 23)`, AP_NavEKF3_core.cpp: zeroStatesVarCov), a function
// whose pointer moves (`*v = ...; v++`), `memcpy` between pointers into two arrays, a const pointer read by
// subscript; cores in raw memory (placement new) whose member functions write their state, called by index
// from a file-scope front end (`core[i].UpdateFilter()`), and a file-scope object whose member function writes
// its state, called from another one through a reference member. With --array-offsets a pointer is the whole
// array and an offset, written back whole; with --swap-out the state of a heap or World object is taken out
// of the World for a call that writes it, so its arrays are written in place. With --member-objects a static
// data member of a translated class (`static NavEKF3 EKF3;` of AP_AHRS_NavEKF3) is a World object.
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <new>

class Common {
public:
    // AP_NavEKF_core_common::zero_range
    static void zero_range(double *v, uint8_t n1, uint8_t n2) {
        memset(&v[n1], 0, sizeof(double)*(1+(n2-n1)));
    }
    // a pointer that moves through k elements
    static double scale(double *v, uint8_t k, double g) {
        double acc = 0;
        for (uint8_t i = 0; i < k; i++) {
            *v = *v * g;
            acc += *v;
            v++;
        }
        return acc;
    }
    static void copy_into(double *dst, const double *src, uint8_t k) {
        memcpy(dst, src, k * sizeof(double));
    }
    static double total(const double *v, uint8_t k) {
        double a = 0;
        for (uint8_t i = 0; i < k; i++) {
            a += v[i];
        }
        return a;
    }
};

class Monitor {
public:
    void note(double x) {
        hist[n % 8] = x;
        n++;
        if (x > peak) {
            peak = x;
        }
    }
    double peak;
private:
    double hist[8];
    uint32_t n;
};

class Core : public Common {
public:
    Core(uint8_t index) : idx(index) {
        memset(&P[0][0], 0, sizeof(P));
        for (uint8_t i = 0; i < 6; i++) {
            P[i][i] = 1.0 + i;
        }
    }
    void update(double x, uint8_t first, uint8_t last) {
        for (uint8_t r = 0; r < 6; r++) {
            for (uint8_t c = 0; c < 6; c++) {
                P[r][c] += x * (r + 1) - 0.25 * c;
            }
        }
        if (first <= last && last < 6) {
            for (uint8_t r = first; r <= last; r++) {
                zero_range(&P[r][0], first, last);
            }
        }
        sum = scale(&P[idx % 6][0], 6, 0.5);
        copy_into(&row[1], &P[5][1], 5);
        sum += total(row, 6) + total(&P[2][3], 3);
        count++;
    }
    double sum;
private:
    double P[6][6];
    double row[6];
    uint8_t idx;
    uint32_t count;
};

class Front {
public:
    Front(Monitor &m) : mon(m) {}
    bool init(uint8_t n) {
        if (core != nullptr || n == 0 || n > 2) {
            return false;
        }
        core = (Core *)malloc(sizeof(Core) * n);
        num_cores = n;
        for (uint8_t i = 0; i < num_cores; i++) {
            new (&core[i]) Core(i);
        }
        return true;
    }
    void update(double x, uint8_t first, uint8_t last) {
        double s = 0;
        for (uint8_t i = 0; i < num_cores; i++) {
            core[i].update(x, first, last);
            s += core[i].sum;
        }
        mon.note(s);
        best = s > best ? s : best;
        tally.note(best - s);
    }
    double best;
    static Monitor tally;
private:
    Monitor &mon;
    Core *core;
    uint8_t num_cores;
};

Monitor monitor;
Monitor Front::tally;
Front front(monitor);
