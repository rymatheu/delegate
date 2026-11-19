// sched.cpp: the clock and the work queues (see px4_shim.h).
//
// The clock is the harness's: hrt_absolute_time() returns the time set by the step (input t_us),
// as PX4's lockstep scheduler returns the simulator's time. The hrt callouts behind
// ScheduledWorkItem (ScheduleDelayed, ScheduleOnInterval, ScheduleAt) are kept in a list and fired
// by the step when their deadline is reached, in deadline order, a periodic callout as often as its
// period fits (as the HRT's callout loop does).
//
// px4::WorkItem and px4::ScheduledWorkItem are PX4's own (WorkItem.cpp, ScheduledWorkItem.cpp);
// px4::WorkQueue's member functions are defined here instead of in WorkQueue.cpp: a queue is not a
// thread but a FIFO that the step drains in this thread. All queues are drained in order of their
// configured priority (rate_ctrl first), until no item is scheduled. That is one admissible
// schedule of PX4's threads under lockstep, made deterministic.
#include "px4_shim.h"

#include <errno.h>
#include <string.h>
#include <vector>
#include <algorithm>

#include <drivers/drv_hrt.h>
#include <px4_platform_common/px4_work_queue/WorkQueue.hpp>
#include <px4_platform_common/px4_work_queue/WorkItem.hpp>
#include <px4_platform_common/time.h>
#include <px4_platform_common/tasks.h>

namespace
{
uint64_t now_us = 0;
std::vector<hrt_call *> callouts;    // armed entries
std::vector<px4::WorkQueue *> queues;    // never freed (WorkItems keep pointers)
unsigned long adds = 0;                  // WorkQueue::Add calls so far

void disarm(hrt_call *e)
{
	callouts.erase(std::remove(callouts.begin(), callouts.end(), e), callouts.end());
}

void arm(hrt_call *e, hrt_abstime deadline, hrt_abstime interval, hrt_callout callout, void *arg)
{
	disarm(e);
	e->deadline = deadline;
	e->period = interval;
	e->callout = callout;
	e->arg = arg;
	callouts.push_back(e);
}
} // namespace

// ---- clock and callouts (drv_hrt.h)
hrt_abstime hrt_absolute_time() { return now_us; }
void hrt_store_absolute_time(volatile hrt_abstime *t) { *t = now_us; }
void hrt_call_after(struct hrt_call *e, hrt_abstime delay, hrt_callout callout, void *arg) { arm(e, now_us + delay, 0, callout, arg); }
void hrt_call_at(struct hrt_call *e, hrt_abstime calltime, hrt_callout callout, void *arg) { arm(e, calltime, 0, callout, arg); }
void hrt_call_every(struct hrt_call *e, hrt_abstime delay, hrt_abstime interval, hrt_callout callout, void *arg)
{
	arm(e, now_us + delay, interval, callout, arg);
}
// as drv_hrt.c: true when the entry has run and been removed, or was never entered
bool hrt_called(struct hrt_call *e) { return e->deadline == 0; }
void hrt_cancel(struct hrt_call *e)
{
	disarm(e);
	e->deadline = 0;
	e->period = 0;
}
void hrt_call_init(struct hrt_call *e) { memset(e, 0, sizeof(*e)); }
void hrt_call_delay(struct hrt_call *e, hrt_abstime delay) { e->deadline = now_us + delay; }
void hrt_init() {}

// lockstep: the harness is the lockstep; nothing to register or wait for
int px4_lockstep_register_component() { return 0; }
void px4_lockstep_unregister_component(int) {}
void px4_lockstep_progress(int) {}
void px4_lockstep_wait_for_components() {}

// px4_usleep, px4_sleep and px4_task_delete are in tasks.cpp (a sleep on the harness thread still
// only runs the work queues when the module has no task of its own)
// CLOCK_REALTIME is the harness clock plus the offset a module set with px4_clock_settime (mavlink's
// timesync sets it from the ground station's SYSTEM_TIME), as PX4's posix clock does under lockstep
static int64_t realtime_offset_us = 0;
int px4_clock_gettime(clockid_t clk, struct timespec *tp)
{
	abstime_to_ts(tp, clk == CLOCK_REALTIME ? (hrt_abstime)((int64_t)now_us + realtime_offset_us) : now_us);
	return 0;
}
int px4_clock_settime(clockid_t clk, const struct timespec *tp)
{
	if (clk != CLOCK_REALTIME) {
		errno = EINVAL;
		return -1;
	}

	realtime_offset_us = (int64_t)ts_to_abstime(tp) - (int64_t)now_us;
	return 0;
}

// ---- work queues (WorkQueue.hpp, WorkQueueManager.hpp)
namespace px4
{
WorkQueue::WorkQueue(const wq_config_t &config) : _config(config) {}
WorkQueue::~WorkQueue() {}
bool WorkQueue::Attach(WorkItem *item) { _work_items.add(item); return true; }
void WorkQueue::Detach(WorkItem *item) { _work_items.remove(item); }
void WorkQueue::Add(WorkItem *item) { _q.push(item); adds++; }    // IntrusiveQueue ignores an item already queued
void WorkQueue::Remove(WorkItem *item) { _q.remove(item); }
void WorkQueue::Clear() { while (!_q.empty()) { _q.pop(); } }
void WorkQueue::Run()
{
	// the body of WorkQueue::Run's loop, without the thread and its semaphores
	while (!_q.empty()) {
		WorkItem *item = _q.pop();
		item->RunPreamble();
		item->Run();
	}
}

WorkQueue *WorkQueueFindOrCreate(const wq_config_t &config)
{
	for (WorkQueue *q : queues) {
		if (strcmp(q->get_name(), config.name) == 0) {
			return q;
		}
	}

	WorkQueue *q = new WorkQueue(config);
	queues.push_back(q);
	std::stable_sort(queues.begin(), queues.end(), [](WorkQueue * a, WorkQueue * b) {
		return a->get_config().relative_priority > b->get_config().relative_priority;
	});
	return q;
}

int WorkQueueManagerStart() { return 0; }
int WorkQueueManagerStop() { return 0; }
int WorkQueueManagerStatus() { return 0; }
const wq_config_t &ins_instance_to_wq(uint8_t instance)
{
	static const wq_config_t *ins[] = {&wq_configurations::INS0, &wq_configurations::INS1,
					   &wq_configurations::INS2, &wq_configurations::INS3
					  };
	return *ins[instance < 4 ? instance : 0];
}
} // namespace px4

// ---- the harness side
namespace px4_shim
{
void sched_reset()
{
	for (hrt_call *e : callouts) {
		e->deadline = 0;
	}

	callouts.clear();

	for (px4::WorkQueue *q : queues) {
		q->Clear();
	}

	now_us = 0;
	realtime_offset_us = 0;
}

void set_time(uint64_t t) { now_us = t; }

void fire_due_callouts()
{
	for (int guard = 0; guard < 1000000; guard++) {
		hrt_call *next = nullptr;

		for (hrt_call *e : callouts) {
			if (e->deadline <= now_us && (next == nullptr || e->deadline < next->deadline)) {
				next = e;
			}
		}

		if (next == nullptr) {
			return;
		}

		if (next->period > 0) {
			next->deadline += next->period;

		} else {
			disarm(next);
			next->deadline = 0;
		}

		if (next->callout) {
			next->callout(next->arg);
		}
	}
}

uint64_t next_callout()
{
	uint64_t next = UINT64_MAX;

	for (hrt_call *e : callouts) {
		if (e->deadline < next) {
			next = e->deadline;
		}
	}

	return next;
}

static int depth = 0;   // px4_usleep inside a Run must not re-enter the queues

bool queues_running() { return depth > 0; }

void run_queues()
{

	if (depth > 0) {
		return;
	}

	depth++;

	// drain every queue, highest priority first; again while a pass scheduled anything
	for (int guard = 0; guard < 100000; guard++) {
		const unsigned long before = adds;

		for (px4::WorkQueue *q : queues) {
			q->Run();
		}

		if (adds == before) {
			break;
		}
	}

	depth--;
}
} // namespace px4_shim
