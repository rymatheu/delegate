// cpp2lean difftest environment of examples/navigate.cpp (C++ side only): the boundary classes
// Planner and PGain and the clock. Each call into the planner is recorded in the output log, as the
// Lean side's `Output` events; each read returns the driver's value plus 0.125 times the number of
// calls recorded so far in the member function under test (plus 0.5 and 0.25 times the arguments
// of `scaler`), as the Lean driver's live Inputs functions (ardupilot/cpp2lean_events.h). The value
// `estimate()` refers to is a member that every call into the planner updates, as a member of the
// real object would change, so a reference to it sees the calls made after it was bound.
#include "../ardupilot/cpp2lean_events.h"

std::string cpp2lean_events;
uint32_t nav_now;                       // the driver's input `now_ms`
float nav_speed, nav_scaler, nav_kp;    // the driver's inputs (before the live shift)
NV2 nav_stop;
NV3 nav_est_base, nav_est;
static Param nav_kp_param;
static PGain nav_gain;

uint32_t clk::now_ms() { return nav_now; }

static void nav_refresh() { nav_est = NV3(cpp2lean_live_d(nav_est_base.x), cpp2lean_live_d(nav_est_base.y), cpp2lean_live_d(nav_est_base.z)); }
void Planner::reset() { cpp2lean_ev("reset"); nav_refresh(); }
void Planner::set_limits(float speed, float accel) { cpp2lean_ev("set_limits"); cpp2lean_ev_f(speed); cpp2lean_ev_f(accel); nav_refresh(); }
void Planner::send(const NV3 &pos, const NV3 &vel)
{
    cpp2lean_ev("send");
    cpp2lean_ev_d(pos.x); cpp2lean_ev_d(pos.y); cpp2lean_ev_d(pos.z);
    cpp2lean_ev_d(vel.x); cpp2lean_ev_d(vel.y); cpp2lean_ev_d(vel.z);
    nav_refresh();
}
float Planner::speed_limit() const { return cpp2lean_live_f(nav_speed); }
void Planner::stopping_point(NV2 &out) const { out = NV2(cpp2lean_live_d(nav_stop.x), cpp2lean_live_d(nav_stop.y)); }
float Planner::scaler(float a, float b) const { return cpp2lean_live_f(nav_scaler) + 0.5f * a + 0.25f * b; }
const NV3 &Planner::estimate() const { nav_refresh(); return nav_est; }
PGain &Planner::gain() { return nav_gain; }
Param &PGain::kP() { nav_kp_param.set(cpp2lean_live_f(nav_kp)); return nav_kp_param; }
