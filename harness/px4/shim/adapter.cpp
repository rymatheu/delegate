// adapter.cpp: module_init and module_step for any PX4 module (see px4_shim.h).
//
// init  clears the bus, the clock, the work queues and the parameter store, stores the parameter
//       record, and starts the modules with their own entry points: first the other PX4 modules
//       the module runs with (px4.txt `start` lines, e.g. dataman), then the module itself with
//       "start", as PX4's startup script does; then runs what they made runnable. With
//       `process fresh` what they published while starting is not shown in the outputs; with
//       `reuse` it is reported as updated at the first step, as before.
//       A second init starts the case afresh in one of two ways (px4.txt `process`):
//       reuse  (default) stop the module and the others with their own "stop" commands first;
//       fresh  hand the protocol to a copy of this process made at the first init before any PX4
//              code ran, which runs this init itself; this process ends. A task module's static
//              state (client counters, instance lists) is then that of a fresh boot in every case.
// step  sets the clock to t_us, fires the hrt callouts that are due (ScheduleOnInterval,
//       ScheduleDelayed), publishes every input topic whose <topic>_updated is true (or, for a
//       queued topic, the first <topic>_count slots), which schedules the work items registered
//       on it, then runs the work queues and the module's tasks until nothing is runnable
//       (tasks.cpp), and reads every output topic.
#include "module_protocol.h"
#include "px4_shim.h"

#include <unistd.h>

int px4_ports_main(int argc, char *argv[]);
extern const char *const px4_ports_start_argv[];
extern const int px4_ports_start_argc;
extern const bool px4_ports_fresh_process;
void px4_ports_start_others();
void px4_ports_stop_others();
void px4_ports_after_start();
void px4_ports_params(const Params &p);
void px4_ports_inject(const Input &in);
void px4_ports_collect(Output &out);

static bool started = false;
static int twin = -1;   // `process fresh`: the pipe to the copy that takes over at the next init

static bool transfer(int fd, void *buf, size_t n, bool out)
{
	uint8_t *b = static_cast<uint8_t *>(buf);

	while (n > 0) {
		const ssize_t r = out ? write(fd, b, n) : read(fd, b, n);

		if (r <= 0) {
			return false;
		}

		b += r;
		n -= (size_t)r;
	}

	return true;
}

// Before any PX4 code ran: fork a copy of this process that waits for the next init. In the copy,
// when it is handed a parameter record, this returns with `p` replaced (after making its own copy);
// when this process ends without handing over, the copy ends too.
static void fork_twin(Params &p)
{
	for (;;) {
		int fd[2];

		if (pipe(fd) != 0) {
			return;
		}

		fflush(stdout);
		fflush(stderr);
		const pid_t pid = fork();

		if (pid < 0) {
			close(fd[0]);
			close(fd[1]);
			return;
		}

		if (pid > 0) {
			close(fd[0]);
			twin = fd[1];
			return;
		}

		close(fd[1]);
		Params next;

		if (!transfer(fd[0], &next, sizeof next, false)) {
			_exit(0);
		}

		close(fd[0]);
		p = next;
	}
}

void module_init(const Params &p0)
{
	Params p = p0;

	if (started && px4_ports_fresh_process && twin >= 0) {
		// the copy replies to this init and serves the case; this process ends
		if (transfer(twin, &p, sizeof p, true)) {
			_exit(0);
		}
	}

	if (!started && px4_ports_fresh_process) {
		fork_twin(p);
	}

	if (started) {
		// ModuleBase::stop_command: request_stop, then wait for the module's Run to exit; a work-
		// item module only runs when scheduled, so after its wait PX4 deletes the object itself
		char *stop[] = {const_cast<char *>(px4_ports_start_argv[0]), const_cast<char *>("stop"), nullptr};
		px4_ports_main(2, stop);
		px4_ports_stop_others();
	}

	px4_shim::sched_reset();
	px4_shim::bus_reset();
	px4_shim::params_reset();
	px4_shim::log_reset();
	px4_ports_params(p);
	px4_ports_start_others();
	// a writable copy: px4_getopt reorders argv in place
	char *argv[16] {};

	for (int i = 0; i < px4_ports_start_argc && i < 15; i++) {
		argv[i] = const_cast<char *>(px4_ports_start_argv[i]);
	}

	px4_ports_main(px4_ports_start_argc, argv);
	px4_shim::run_all();
	px4_ports_after_start();   // px4.txt `run` lines, e.g. `mavlink boot_complete`
	px4_shim::run_all();

	if (px4_ports_fresh_process) {
		// `process fresh`: the outputs show only what is published from the first step on, so at
		// the first step <topic>_updated means published during that step and the fields are 0
		// until a message is. A start can publish nondeterministic bytes: DatamanClient's
		// DM_GET_ID request leaves index and item uninitialized (DatamanClient.cpp:60-63) and
		// dataman echoes them. Modules with `process reuse` keep showing start-time messages at
		// the first step, as before. The modules' own subscriptions are not affected.
		px4_shim::hide_published();
	}

	started = true;
}

void module_step(const Input &in, Output &out)
{
	px4_shim::set_time(in.t_us);
	px4_shim::fire_due_callouts();
	px4_ports_inject(in);
	px4_shim::run_all();
	px4_ports_collect(out);
}
