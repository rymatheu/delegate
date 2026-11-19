// cpp2lean demo (phase 3): outputs to the boundary. The rate controller writes its demands to a
// motors object outside the translation, as AC_AttitudeControl writes to AP_Motors through
// `_motors.set_roll(...)` and `_motors.set_throttle_out(...)` (AC_AttitudeControl_Multi.cpp), and
// reads a limit through a const getter with a reference out-parameter.
// Translated with: --boundary Motors
#include <cmath>

// Boundary: not translated. A non-const `void` member function called on it is an output: its
// arguments become fields of the caller's Outputs record (the last call's values). A const member
// function is an input: its result and what it writes into reference parameters are Inputs fields.
class Motors {
public:
    float roll_in;
    float pitch_in;
    float throttle_in;
    bool boost_in;
    float cutoff_in;
    bool lean_ok;
    float lean_max;
    int sat_count;
    float sat_margin;
    void set_roll(float v) { roll_in = v; }
    void set_pitch(float v) { pitch_in = v; }
    void set_throttle_out(float throttle, bool apply_angle_boost, float filt_cutoff)
    {
        throttle_in = throttle;
        boost_in = apply_angle_boost;
        cutoff_in = filt_cutoff;
    }
    bool get_lean_max(float &out) const { out = lean_max; return lean_ok; }
    void get_saturation(int &count, float &margin) const { count = sat_count; margin = margin_of(); }
    float margin_of() const { return sat_margin; }
};

static float clamp_abs(float v, float lim) { return v > lim ? lim : (v < -lim ? -lim : v); }

// Writes two outputs; the second write of `set_roll` replaces the first (last write wins).
class Mixer {
public:
    Mixer(Motors &motors) : _motors(motors) {}

    void output(float roll, float pitch)
    {
        float lim;
        if (!_motors.get_lean_max(lim)) {
            lim = 1.0f;
        }
        _motors.set_roll(clamp_abs(roll, lim));
        _motors.set_pitch(clamp_abs(pitch, lim));
        if (fabsf(roll) > 2.0f * lim) {
            _motors.set_roll(0.0f);
        }
        _last_lim = lim;
    }
    float last_lim() const { return _last_lim; }

private:
    Motors &_motors;
    float _last_lim = 0;
};

// A member object that writes outputs (its Outputs nest in this class's), a multi-argument output,
// and a const getter with two out-parameters and no result.
class Attitude {
public:
    Attitude(Motors &motors) : _mixer(motors), _motors(motors) {}

    void run(float roll, float pitch, float throttle, bool boost)
    {
        _mixer.output(roll, pitch);
        int count = 0;
        float margin = 0.0f;
        _motors.get_saturation(count, margin);
        _saturated = count > 0;
        const float thr = _saturated ? throttle * margin : throttle;
        _motors.set_throttle_out(thr, boost, 2.0f);
        _runs++;
    }
    void idle() { _motors.set_throttle_out(0.0f, false, 0.5f); }

private:
    Mixer _mixer;
    Motors &_motors;
    bool _saturated = false;
    int _runs = 0;
};
