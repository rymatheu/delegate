// px4_shim.h: the generic stand-ins that turn one PX4 module into a harness module.
//
// A PX4 module is compiled from its real, unmodified sources, with PX4's real headers and its real
// uORB client classes (Subscription, SubscriptionInterval, SubscriptionCallback, Publication),
// work-item classes (WorkItem, ScheduledWorkItem), ModuleBase, ModuleParams and Param classes. What
// is outside a module is replaced, behind PX4's own interfaces, by the stand-ins in this directory:
//
//   bus.cpp     the message bus: uORB::Manager's static functions and the orb_* C API, one node per
//               (topic, instance), with PX4's generation and queue semantics (uORBDeviceNode.hpp)
//   sched.cpp   the clock (hrt_absolute_time and the hrt callouts behind ScheduleDelayed /
//               ScheduleOnInterval) and the work queues (px4::WorkQueue, WorkQueueFindOrCreate),
//               run in this thread, in lock-step with the harness
//   tasks.cpp   the module's own tasks and threads (px4_task_spawn_cmd, pthread_create), run one at
//               a time and handed control once per step until they block (px4_usleep, px4_poll,
//               px4_sem_wait, pthread_join), with the harness clock
//   params.cpp  the parameter store (the param_* C API) over PX4's generated parameter table, set from
//               the parameter record
//   platform.cpp  device files (none), shutdown requests (refused), board hooks, SubscriptionBlocking's
//               timed wait
//   stream.cpp  byte-stream devices behind open/read/write/poll/tc*attr, for a serial link (mavlink)
//   log.cpp     logging (PX4_INFO/WARN/ERR, to stderr only with PX4_SHIM_LOG=1; errors are counted)
//   adapter.cpp module_init / module_step, the same for every module
//
// What is specific to a module is generated (px4/ports.py): px4_ports.cpp copies the records to
// and from PX4's uORB structs and calls the module's entry point.
#pragma once

#include <stddef.h>
#include <stdint.h>
#include <functional>

#include <uORB/uORB.h>
#include <px4_platform_common/param.h>   // px4_parameters.hpp, which has no include guard

namespace px4_shim
{
// bus
void bus_reset();
void inject(const orb_metadata *meta, uint8_t instance, const void *data);
bool collect(const orb_metadata *meta, uint8_t instance, void *data, size_t size);
void collect_queue(const orb_metadata *meta, uint8_t instance, void *data, size_t size, unsigned slots,
		   unsigned *count, unsigned *lost);
bool orb_fd_updated(int handle);
unsigned bus_writes();   // messages written on the bus so far
void hide_published();   // the harness sees only messages published from now on
// an output with more slots than the topic's queue: every message written in a step (bus.cpp)
void tap(const orb_metadata *meta, uint8_t instance, unsigned slots);
void collect_tap(const orb_metadata *meta, uint8_t instance, void *data, size_t size, unsigned slots,
		 unsigned *count, unsigned *lost);
// clock and work queues
void sched_reset();
void set_time(uint64_t now_us);
void fire_due_callouts();
void run_queues();
bool queues_running();
uint64_t next_callout();
// tasks
void run_all();          // the work queues and every runnable task, until nothing is runnable
unsigned task_count();
// a blocking wait from any thread (a task blocks; the harness thread runs the tasks and moves the
// clock): true when `until` held before `deadline`
bool wait_until(std::function<bool()> until, uint64_t deadline);
// byte-stream devices (stream.cpp, linked only into modules with a `stream` line)
void stream_register(const char *path);
void stream_inject(const char *path, const uint32_t *words, uint32_t len, uint32_t max_words);
void stream_collect(const char *path, uint32_t *words, uint32_t max_words, uint32_t *len, uint32_t *pending,
		    uint32_t *rx_dropped);
// parameter store
void params_reset();
void param_store(px4::params p, const void *value);
void params_readonly();    // from now on the module's param_set / param_reset fail
// logging
void log_reset();
uint32_t error_count();
}
