// stubs_scheduler.cpp: the scheduler and the simulator singleton.
//
//   symbol                    why it is outside the stage, and what stands in
//   AP::scheduler()           the scheduler (vehicle main loop). AC_PosControl reads its tick
//                             counter, ticks32(), in NE/D_is_active and stores it in the inits and
//                             updates: an update with no init or update at the previous tick
//                             re-initializes and raises INTERNAL_ERROR(flow_of_control). Zeroed
//                             storage; ticks32() is ArduPilot's inline accessor.
//   AP_Scheduler::tick()      the scheduler's per-loop counter step (AP_Scheduler.cpp:169), called
//                             by the adapter once per step: one step is one main-loop tick. The
//                             stand-in increments the two counters, as the real body does.
//   AP::sitl()                the simulator singleton, read by has_good_timing(). Returns null:
//                             timing is good, as on a real board or lock-step SITL, so an update
//                             without init raises the internal error.
#include <AP_Scheduler/AP_Scheduler.h>
#include <SITL/SITL.h>

alignas(AP_Scheduler) static unsigned char scheduler_storage[sizeof(AP_Scheduler)];
alignas(AP_Scheduler) static unsigned char scheduler_lookahead[sizeof(AP_Scheduler)];
static AP_Scheduler *scheduler_ptr = reinterpret_cast<AP_Scheduler *>(scheduler_storage);

AP_Scheduler &AP::scheduler()
{
    return *scheduler_ptr;
}

void AP_Scheduler::tick(void)
{
    _tick_counter++;
    _tick_counter32++;
}

// The outputs pc_ne_active, pc_d_active: NE/D_is_active() evaluated on a copy of the scheduler
// one tick on, i.e. as the next tick's mode code reads it before calling anything.
void harness_scheduler_lookahead(bool on)
{
    if (on) {
        memcpy(scheduler_lookahead, scheduler_storage, sizeof scheduler_storage);
        scheduler_ptr = reinterpret_cast<AP_Scheduler *>(scheduler_lookahead);
        scheduler_ptr->tick();
    } else {
        scheduler_ptr = reinterpret_cast<AP_Scheduler *>(scheduler_storage);
    }
}

static void harness_reset_scheduler()
{
    memset(scheduler_storage, 0, sizeof scheduler_storage);
    scheduler_ptr = reinterpret_cast<AP_Scheduler *>(scheduler_storage);
}

namespace AP {
SITL::SIM *sitl()
{
    return nullptr;
}
}
