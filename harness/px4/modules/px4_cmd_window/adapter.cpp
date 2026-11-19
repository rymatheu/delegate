// adapter.cpp: px4_cmd_window, an OBSERVER (see Module.lean): the number of vehicle_command messages
// published in the last 400 ticks (this tick included). Not PX4 code and no PX4 logic: a sliding sum
// of one input over a fixed window.
#include "module_protocol.h"

static const unsigned WINDOW = 400;   // ticks: 1 s at 400 Hz
static uint32_t counts[WINDOW];
static unsigned at;                   // the slot of the current tick
static uint32_t sum;

void module_init(const Params &)
{
	for (unsigned i = 0; i < WINDOW; i++) {
		counts[i] = 0;
	}

	at = 0;
	sum = 0;
}

void module_step(const Input &in, Output &out)
{
	sum -= counts[at];                 // the tick that leaves the window
	counts[at] = in.vehicle_command_count;
	sum += counts[at];
	at = (at + 1) % WINDOW;
	out.vehicle_command_last_400_ticks = sum;
}
