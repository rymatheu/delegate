// cpp2lean demo (phase 2): a PID controller modeled on ArduPilot's AC_PID (AC_PID.h:14-216,
// AC_PID.cpp:193-388 at commit 802db19de1): gains as parameters, low-pass filters on the target,
// the error and the derivative, an integrator with anti-windup and a limit, a PD sum limit. The
// gain scaler is read from an object outside the translation (the boundary).
// Translated with: --param-class AP_Float=float --boundary AHRS --extern ext_sqrt:Binary32.sqrt
#include <cfloat>
#include <cmath>
#include <cstdint>

// Stand-in for ArduPilot's AP_Float (AP_Param.h:910-1030, the members the controller uses).
class AP_Float {
public:
    const float &get(void) const { return _value; }
    void set(const float &v) { _value = v; }
    operator const float &() const { return _value; }
    float operator -() const { return -_value; }
private:
    float _value;
};

// Boundary: not translated. What the controller reads from it becomes a field of PID::Inputs.
class AHRS {
public:
    float gain_scaler = 1.0f;
    float air_density_ratio = 1.0f;
    float get_control_gain_scaler() const { return gain_scaler; }
    float get_air_density_ratio() const { return air_density_ratio; }
};

// ArduPilot's singleton accessor (AP_AHRS.h: `namespace AP { AP_AHRS &ahrs(); }`), and a function
// defined outside the translated file (mapped to a Lean function by --extern).
namespace AP {
AHRS &ahrs();
}
float ext_sqrt(float x);

// AP_Math.h / AP_Math.cpp helpers.
static bool is_zero(float x) { return fabsf(x) < FLT_EPSILON; }
static bool is_positive(float x) { return x >= FLT_EPSILON; }
static bool is_negative(float x) { return x <= (-1.0 * FLT_EPSILON); }
static float constrain_float(float amt, float low, float high)
{
    if (isnan(amt)) return (low + high) / 2;
    return amt < low ? low : (amt > high ? high : amt);
}
static float calc_lowpass_alpha_dt(float dt, float cutoff_freq)
{
    if (is_negative(dt) || is_negative(cutoff_freq)) return 1.0;
    if (is_zero(cutoff_freq)) return 1.0;
    if (is_zero(dt)) return 0.0;
    float rc = 1.0f / (2 * M_PI * cutoff_freq);
    return dt / (dt + rc);
}

// AP_PIDInfo (AP_PIDInfo.h): a plain struct with default member initializers.
struct PIDInfo {
    float target = 0;
    float actual = 0;
    float error = 0;
    float P = 0;
    float I = 0;
    float D = 0;
    bool limit = false;
    bool PD_limit = false;
};

class PID {
public:
    PID(AHRS &ahrs, float initial_p, float initial_i, float initial_d, float initial_imax, float filt_hz)
        : _ahrs(ahrs)
    {
        _kp.set(initial_p);
        _ki.set(initial_i);
        _kd.set(initial_d);
        _kimax.set(fabsf(initial_imax));
        _filt_E_hz.set(filt_hz);
        _filt_D_hz.set(filt_hz * 2);
        _flags._reset_filter = true;
    }

    // AC_PID::update_all (AC_PID.cpp:193-311), without notch filters and slew limiter.
    float update_all(float target, float measurement, float dt, bool limit = false, float pd_scale = 1.0f)
    {
        if (!isfinite(target) || !isfinite(measurement)) {
            return 0.0f;
        }
        if (_flags._reset_filter) {
            _flags._reset_filter = false;
            _target = target;
            _error = _target - measurement;
            _derivative = 0.0f;
        } else {
            _target += get_filt_alpha(dt, _filt_T_hz) * (target - _target);
            const float error_last = _error;
            _error += get_filt_alpha(dt, _filt_E_hz) * ((_target - measurement) - _error);
            if (is_positive(dt)) {
                float derivative = (_error - error_last) / dt;
                _derivative += get_filt_alpha(dt, _filt_D_hz) * (derivative - _derivative);
            }
        }
        update_i(dt, limit);
        const float scaler = _ahrs.get_control_gain_scaler();
        float P_out = (_error * _kp) * scaler;
        float D_out = (_derivative * _kd) * scaler;
        P_out *= pd_scale;
        D_out *= pd_scale;
        _info.PD_limit = false;
        if (is_positive(_kpdmax)) {
            const float PD_sum_abs = fabsf(P_out + D_out);
            if (PD_sum_abs > _kpdmax) {
                const float pd_limit_scale = _kpdmax / PD_sum_abs;
                P_out *= pd_limit_scale;
                D_out *= pd_limit_scale;
                _info.PD_limit = true;
            }
        }
        _info.target = _target;
        _info.actual = measurement;
        _info.error = _error;
        _info.P = P_out;
        _info.I = _integrator;
        _info.D = D_out;
        _info.limit = limit;
        _flags._I_set = false;
        return P_out + D_out + _integrator;
    }

    // AC_PID::update_error (AC_PID.cpp:313-335).
    float update_error(float error, float dt, bool limit = false)
    {
        if (!isfinite(error)) {
            return 0.0f;
        }
        _target = 0.0f;
        const float output = update_all(0.0f, -error, dt, limit);
        _info.target = 0.0f;
        _info.actual = 0.0f;
        return output;
    }

    void reset_I() { _flags._I_set = true; _integrator = 0.0f; }
    void reset_filter() { _flags._reset_filter = true; }
    float get_i() const { return _integrator; }
    float get_pid_sum() const { return _info.P + _info.I + _info.D; }
    void set_kP(float v) { _kp.set(v); }
    void set_imax(float v) { _kimax.set(fabsf(v)); }
    void set_pdmax(float v) { _kpdmax.set(fabsf(v)); }

    // Two results through reference parameters.
    void get_terms(float &p_out, float &d_out) const { p_out = _info.P; d_out = _info.D; }

    // AC_PID::relax_integrator (AC_PID.cpp:439-448).
    void relax_integrator(float integrator, float dt, float time_constant)
    {
        integrator = constrain_float(integrator, -_kimax, _kimax);
        if (is_positive(dt)) {
            _flags._I_set = true;
            _integrator = _integrator + (integrator - _integrator) * (dt / (dt + time_constant));
        }
    }

private:
    // AC_PID::update_i (AC_PID.cpp:337-351).
    void update_i(float dt, bool limit)
    {
        if (!is_zero(_ki) && is_positive(dt)) {
            if (!limit || ((is_positive(_integrator) && is_negative(_error)) || (is_negative(_integrator) && is_positive(_error)))) {
                _integrator += (_error * _ki) * dt;
                _integrator = constrain_float(_integrator, -_kimax, _kimax);
            }
        } else {
            _integrator = 0.0f;
        }
    }

    float get_filt_alpha(float dt, float hz) const { return calc_lowpass_alpha_dt(dt, hz); }

    AHRS &_ahrs;
    AP_Float _kp;
    AP_Float _ki;
    AP_Float _kd;
    AP_Float _kimax;
    AP_Float _kpdmax;
    AP_Float _filt_T_hz;
    AP_Float _filt_E_hz;
    AP_Float _filt_D_hz;
    struct pid_flags {
        bool _reset_filter : 1;
        bool _I_set : 1;
    } _flags;
    float _integrator;
    float _target;
    float _error;
    float _derivative;
    PIDInfo _info;
};

// Composition, as AC_AttitudeControl holds its rate PIDs: two PID members (their parameters, state
// and boundary reads nest in RateControl's), a read through the singleton accessor, an extern call.
class RateControl {
public:
    RateControl(AHRS &ahrs)
        : _pid_roll(ahrs, 0.135f, 0.135f, 0.0036f, 0.5f, 20.0f), _pid_pitch(ahrs, 0.135f, 0.135f, 0.0036f, 0.5f, 20.0f) {}

    float update(float target_roll, float rate_roll, float target_pitch, float rate_pitch, float dt)
    {
        const float density = AP::ahrs().get_air_density_ratio();
        const float scale = density > 0.0f ? 1.0f / ext_sqrt(density) : 1.0f;
        _out_roll = _pid_roll.update_all(target_roll, rate_roll, dt, _limit) * scale;
        _out_pitch = _pid_pitch.update_all(target_pitch, rate_pitch, dt, _limit) * scale;
        _limit = fabsf(_out_roll) > 1.0f || fabsf(_out_pitch) > 1.0f;
        return _out_roll + _out_pitch;
    }
    void reset() { _pid_roll.reset_I(); _pid_pitch.reset_filter(); }
    void set_gain(float kp) { _pid_roll.set_kP(kp); _pid_pitch.set_kP(kp * 0.5f); }
    float get_roll_i() const { return _pid_roll.get_i(); }

private:
    PID _pid_roll;
    PID _pid_pitch;
    float _out_roll = 0;
    float _out_pitch = 0;
    bool _limit = false;
};
