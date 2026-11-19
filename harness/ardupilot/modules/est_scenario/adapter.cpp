// adapter.cpp: est_scenario, the estimator tests' schedule (Module.lean): motors off and the vehicle
// disarmed, then all motors at hover_pwm, armed and flying, for hover_from_us <= t_us < hover_until_us.
#include "module_protocol.h"

static Params prm;

void module_init(const Params &p)
{
    prm = p;
}

void module_step(const Input &in, Output &out)
{
    const bool flight = prm.hover_from_us <= in.t_us && in.t_us < prm.hover_until_us;
    const uint32_t pwm = flight ? prm.hover_pwm : 1000;
    out.pwm0 = out.pwm1 = out.pwm2 = out.pwm3 = pwm;
    out.armed = flight;
    out.likely_flying = flight;
}
