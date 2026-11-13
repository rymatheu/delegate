// The HAL scheduler stand-in of the estimator translation (reference/hal/est_scheduler.cpp, PORT-PLAN.md
// "Phase 3:" decision on delays) as a World with ArduPilot's real headers and the reference configuration,
// and a timer process registered as the sensor stand-ins register theirs (FUNCTOR_BIND_MEMBER).
#include "est_scheduler.cpp"

class TimerProbe {
public:
    void start() { est_scheduler.register_timer_process(FUNCTOR_BIND_MEMBER(&TimerProbe::tick, void)); }
    void tick() {
        _n++;
        _last_t = AP_HAL::micros64();
        if (est_scheduler.current().baro) {
            _p = est_scheduler.current().baro_pa;
        }
    }
    uint32_t _n;
    uint64_t _last_t;
    float _p;
};

TimerProbe probe;
