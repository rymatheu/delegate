// tasks.cpp: a module's own tasks and threads, run one at a time in lock-step with the harness
// (see px4_shim.h).
//
// PX4's task modules (commander, navigator, dataman, mavlink) run loops of the form
// `while (!should_exit()) { block; work }` on threads they create with px4_task_spawn_cmd or
// pthread_create, where `block` is px4_usleep, px4_poll, px4_sem_wait or pthread_join. Here each
// such task is a real thread, but only one thread runs at a time: the harness thread hands control
// (the baton) to a task and the task hands it back at its next blocking call, recording what it
// waits for: a deadline on the harness clock, an update of a polled uORB subscription, a semaphore
// count, another task's end. A step (run_all) drains the work queues and resumes, in order of
// creation, every task whose wait is over, again until no task is runnable and no work item is
// queued. The clock does not move while tasks run: a task that sleeps 10 ms at t wakes at the first
// step with t_us >= t + 10 ms. So a step runs one admissible schedule of PX4's threads under
// lockstep, deterministically, and no thread ever runs free.
//
// Outside steps (the module's own start and stop commands, which wait for their tasks with
// px4_usleep, px4_sem_wait or pthread_join on the harness thread) a wait runs the runnable tasks
// and moves the clock to the next deadline, as PX4's lockstep simulator does while the shell
// sleeps. A module that has no task of its own sleeps exactly as before (only the work queues run).
#include "px4_shim.h"

#include <dlfcn.h>
#include <errno.h>
#include <poll.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <functional>
#include <vector>

#include <drivers/drv_hrt.h>
#include <px4_platform_common/log.h>
#include <px4_platform_common/posix.h>
#include <px4_platform_common/sem.h>
#include <px4_platform_common/tasks.h>

namespace
{
constexpr uint64_t NEVER = UINT64_MAX;
constexpr unsigned long MAX_RESUMES = 100000;   // per step: a task that never blocks is an error

struct Task {
	int id{0};
	char name[24] {};
	px4_main_t entry{nullptr};            // a PX4 task: entry(argc, argv)
	int argc{0};
	char **argv{nullptr};
	void *(*start)(void *) {nullptr};     // a pthread: start(arg)
	void *arg{nullptr};
	void *result{nullptr};
	pthread_cond_t cv = PTHREAD_COND_INITIALIZER;
	std::function<bool()> until;          // what it waits for; empty: only the deadline
	uint64_t deadline{0};                 // runnable at this time at the latest; 0: at once
	bool timed_out{false};
	bool done{false};                     // its function returned
	bool dropped{false};                  // px4_task_delete: never resumed again
};

pthread_mutex_t baton = PTHREAD_MUTEX_INITIALIZER;
pthread_cond_t harness_cv = PTHREAD_COND_INITIALIZER;
Task *running = nullptr;                  // the task holding the baton; nullptr: the harness thread
std::vector<Task *> tasks;                // in creation order; never freed (handles stay valid)
thread_local Task *self = nullptr;        // the task this thread is (nullptr: the harness thread)
unsigned long resumes = 0;

typedef int (*pthread_create_fn)(pthread_t *, const pthread_attr_t *, void *(*)(void *), void *);

// pthread_create is defined below for the module's code; the shim's own threads use libSystem's
pthread_create_fn system_pthread_create()
{
	static pthread_create_fn f = (pthread_create_fn)dlsym(RTLD_NEXT, "pthread_create");
	return f;
}

void *thread_main(void *p)
{
	Task *t = static_cast<Task *>(p);
	self = t;
	pthread_mutex_lock(&baton);

	while (running != t) {
		pthread_cond_wait(&t->cv, &baton);
	}

	pthread_mutex_unlock(&baton);

	if (t->entry) {
		t->result = (void *)(intptr_t)t->entry(t->argc, t->argv);

	} else {
		t->result = t->start(t->arg);
	}

	pthread_mutex_lock(&baton);
	t->done = true;
	running = nullptr;
	pthread_cond_signal(&harness_cv);
	pthread_mutex_unlock(&baton);
	return nullptr;
}

Task *create(const char *name)
{
	Task *t = new Task();
	t->id = (int)tasks.size();
	strncpy(t->name, name, sizeof(t->name) - 1);
	tasks.push_back(t);
	pthread_attr_t a;
	pthread_attr_init(&a);
	pthread_attr_setstacksize(&a, 8u << 20);
	pthread_attr_setdetachstate(&a, PTHREAD_CREATE_DETACHED);
	pthread_t th;

	if (system_pthread_create()(&th, &a, thread_main, t) != 0) {
		PX4_ERR("shim: cannot create a thread for task %s", name);
		t->dropped = true;
	}

	pthread_attr_destroy(&a);
	return t;
}

// harness thread: let t run until it blocks or returns
void resume(Task *t)
{
	pthread_mutex_lock(&baton);
	running = t;
	pthread_cond_signal(&t->cv);

	while (running != nullptr) {
		pthread_cond_wait(&harness_cv, &baton);
	}

	pthread_mutex_unlock(&baton);
}

// task thread: hand the baton back until `until` holds or the clock reaches `deadline`;
// true when `until` held (a pure sleep, with no condition, returns true)
bool block(std::function<bool()> until, uint64_t deadline)
{
	Task *t = self;
	t->until = std::move(until);
	t->deadline = deadline;
	t->timed_out = false;
	pthread_mutex_lock(&baton);
	running = nullptr;
	pthread_cond_signal(&harness_cv);

	while (running != t) {
		pthread_cond_wait(&t->cv, &baton);
	}

	pthread_mutex_unlock(&baton);
	t->until = nullptr;
	return !t->timed_out;
}

bool runnable(Task *t)
{
	if (t->done || t->dropped) {
		return false;
	}

	if (t->until && t->until()) {
		return true;
	}

	if (hrt_absolute_time() >= t->deadline) {
		t->timed_out = (bool)t->until;
		return true;
	}

	return false;
}

// one pass over the tasks in creation order (a task created in the pass runs in it); true when
// any ran
bool run_ready_tasks()
{
	bool any = false;

	for (size_t i = 0; i < tasks.size() && resumes < MAX_RESUMES; i++) {
		if (runnable(tasks[i])) {
			resume(tasks[i]);
			resumes++;
			any = true;
		}
	}

	return any;
}

// harness thread, outside a step: run the tasks and move the clock until `until` holds or the
// clock reaches `deadline`
bool harness_wait(const std::function<bool()> &until, uint64_t deadline)
{
	for (int guard = 0; guard < 1000000; guard++) {
		px4_shim::run_all();

		if (until && until()) {
			return true;
		}

		const uint64_t now = hrt_absolute_time();

		if (now >= deadline) {
			return !until;
		}

		uint64_t next = deadline;

		for (Task *t : tasks) {
			if (!t->done && !t->dropped && t->deadline > now && t->deadline < next) {
				next = t->deadline;
			}
		}

		const uint64_t c = px4_shim::next_callout();
		next = c < next ? c : next;

		if (next == NEVER) {
			PX4_ERR("shim: the harness thread waits for something no task will do");
			return false;
		}

		px4_shim::set_time(next);
		px4_shim::fire_due_callouts();
	}

	return false;
}

// a blocking wait from whichever thread calls it
bool wait_for(std::function<bool()> until, uint64_t deadline)
{
	if (self) {
		return block(std::move(until), deadline);
	}

	return harness_wait(until, deadline);
}

uint64_t after_us(uint64_t us)
{
	const uint64_t now = hrt_absolute_time();
	return (us > NEVER - now) ? NEVER : now + us;
}
} // namespace

// ---- sleeping (px4_platform_common/time.h)
int px4_usleep(useconds_t us)
{
	if (self) {
		block(nullptr, after_us(us));

	} else if (tasks.empty() || px4_shim::queues_running()) {
		// as before tasks existed: sleeping lets the work queues run; the clock does not move
		px4_shim::run_queues();

	} else {
		harness_wait(nullptr, after_us(us));
	}

	return 0;
}

unsigned int px4_sleep(unsigned int s)
{
	px4_usleep((useconds_t)s * 1000000u);
	return 0;
}

// ---- tasks (px4_platform_common/tasks.h), as platforms/posix/src/px4/common/tasks.cpp: argv[0]
// is the task's name, then the arguments
px4_task_t px4_task_spawn_cmd(const char *name, int scheduler, int priority, int stack_size, px4_main_t entry,
			      char *const argv[])
{
	(void)scheduler;
	(void)priority;
	(void)stack_size;
	int argc = 0;

	while (argv && argv[argc]) {
		argc++;
	}

	char **av = static_cast<char **>(calloc(argc + 2, sizeof(char *)));
	av[0] = strdup(name);

	for (int i = 0; i < argc; i++) {
		av[i + 1] = strdup(argv[i]);
	}

	Task *t = create(name);
	t->entry = entry;
	t->argc = argc + 1;
	t->argv = av;
	return t->dropped ? -1 : t->id;
}

// a task cannot be killed safely; it is never resumed again (ModuleBase::stop_command after its
// wait). A work-queue module has none.
int px4_task_delete(px4_task_t id)
{
	if (id < 0 || id >= (int)tasks.size()) {
		return -1;
	}

	tasks[id]->dropped = true;
	return 0;
}

px4_task_t px4_getpid() { return self ? self->id : -1; }

// the shell's list_tasks: the module's tasks, on the log (stdout is the harness's pipe)
void px4_show_tasks()
{
	for (Task *t : tasks) {
		PX4_INFO("task %d %s%s", t->id, t->name, t->done ? " (ended)" : (t->dropped ? " (deleted)" : ""));
	}
}
int px4_prctl(int, const char *, px4_task_t) { return 0; }

// ---- threads: pthread_create and pthread_join, for the module's code (commander's worker thread,
// mavlink's receiver); every other pthread function is libSystem's
extern "C" int pthread_create(pthread_t *thread, const pthread_attr_t *attr, void *(*start)(void *), void *arg)
{
	(void)attr;
	Task *t = create("pthread");
	t->start = start;
	t->arg = arg;
	*thread = reinterpret_cast<pthread_t>(t);
	return t->dropped ? EAGAIN : 0;
}

extern "C" int pthread_join(pthread_t thread, void **value)
{
	Task *t = reinterpret_cast<Task *>(thread);
	wait_for([t] { return t->done; }, NEVER);

	if (value) {
		*value = t->result;
	}

	return 0;
}

// ---- uORB poll (px4_platform_common/posix.h): POLLIN on a subscription handle (orb_subscribe)
// when it is updated (bus.cpp)
int px4_poll(px4_pollfd_struct_t *fds, unsigned int nfds, int timeout)
{
	auto check = [fds, nfds]() {
		int n = 0;

		for (unsigned i = 0; i < nfds; i++) {
			fds[i].revents = 0;

			if ((fds[i].events & POLLIN) && px4_shim::orb_fd_updated(fds[i].fd)) {
				fds[i].revents |= POLLIN;
				n++;
			}
		}

		return n;
	};

	const int n = check();

	if (n > 0 || timeout == 0) {
		return n;
	}

	wait_for([&check] { return check() > 0; }, timeout < 0 ? NEVER : after_us((uint64_t)timeout * 1000));
	return check();
}

// ---- semaphores (px4_platform_common/sem.h): a count; a wait blocks the task until it is positive
int px4_sem_init(px4_sem_t *s, int pshared, unsigned value)
{
	(void)pshared;
	s->value = (int)value;
	return 0;
}

int px4_sem_setprotocol(px4_sem_t *s, int protocol)
{
	(void)s;
	(void)protocol;
	return 0;
}

int px4_sem_wait(px4_sem_t *s)
{
	if (s->value <= 0) {
		wait_for([s] { return s->value > 0; }, NEVER);
	}

	if (s->value <= 0) {
		errno = EINVAL;
		return -1;
	}

	s->value--;
	return 0;
}

int px4_sem_trywait(px4_sem_t *s)
{
	if (s->value <= 0) {
		errno = EAGAIN;
		return -1;
	}

	s->value--;
	return 0;
}

// abstime on the module's clock (px4_clock_gettime is the harness clock)
int px4_sem_timedwait(px4_sem_t *s, const struct timespec *abstime)
{
	const uint64_t deadline = (uint64_t)abstime->tv_sec * 1000000u + (uint64_t)abstime->tv_nsec / 1000u;

	if (s->value <= 0) {
		wait_for([s] { return s->value > 0; }, deadline);
	}

	if (s->value <= 0) {
		errno = ETIMEDOUT;
		return -1;
	}

	s->value--;
	return 0;
}

int px4_sem_post(px4_sem_t *s)
{
	s->value++;
	return 0;
}

int px4_sem_getvalue(px4_sem_t *s, int *sval)
{
	*sval = s->value;
	return 0;
}

int px4_sem_destroy(px4_sem_t *s)
{
	(void)s;
	return 0;
}

// ---- the harness side
namespace px4_shim
{
void run_all()
{
	resumes = 0;

	for (;;) {
		run_queues();

		if (!run_ready_tasks()) {
			break;
		}

		if (resumes >= MAX_RESUMES) {
			PX4_ERR("shim: tasks still runnable after %lu resumptions in one step", resumes);
			break;
		}
	}
}

unsigned task_count() { return (unsigned)tasks.size(); }

bool wait_until(std::function<bool()> until, uint64_t deadline) { return wait_for(std::move(until), deadline); }
} // namespace px4_shim
