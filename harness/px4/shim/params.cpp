// params.cpp: the parameter store (see px4_shim.h).
//
// PX4's Param classes, ModuleParams and the generated px4_parameters.hpp are used unmodified; the
// param_* C functions they call (src/lib/parameters/param.h) are defined here instead of in
// parameters.cpp. The store holds one value per parameter of the module's generated table: PX4's
// default, overwritten at init by the parameter record. A write by the module (param_set,
// commit_no_notification) changes the store for the rest of the case, as on the vehicle; it is
// not an output. param_set and param_notify_changes publish parameter_update on the module's bus,
// as parameters.cpp does.
#include "px4_shim.h"

#include <string.h>
#include <math.h>

#include <px4_platform_common/log.h>

#include <uORB/Publication.hpp>
#include <uORB/topics/parameter_update.h>

namespace
{
constexpr unsigned N = sizeof(px4::parameters) / sizeof(px4::parameters[0]);
param_value_u values[N > 0 ? N : 1];
bool changed[N > 0 ? N : 1];
unsigned update_count = 0;

bool valid(param_t p) { return p < N; }
bool readonly = false;     // px4.txt `params readonly`: the module's writes fail

void notify()
{
	static orb_advert_t pub = nullptr;
	parameter_update_s u{};
	u.timestamp = hrt_absolute_time();
	u.instance = ++update_count;

	if (pub == nullptr) {
		pub = orb_advertise(ORB_ID(parameter_update), &u);

	} else {
		orb_publish(ORB_ID(parameter_update), pub, &u);
	}
}
} // namespace

param_t param_find(const char *name)
{
	for (unsigned i = 0; i < N; i++) {
		if (strcmp(px4::parameters[i].name, name) == 0) {
			return (param_t)i;
		}
	}

	// not in the module's table: as in a PX4 build without that parameter (shown with PX4_SHIM_LOG=1,
	// to find what a module's px4.txt is missing)
	px4_log_raw(_PX4_LOG_LEVEL_DEBUG, "param_find: %s is not a parameter of this module\n", name);
	return PARAM_INVALID;
}
param_t param_find_no_notification(const char *name) { return param_find(name); }
unsigned param_count() { return N; }
unsigned param_count_used() { return N; }
bool param_used(param_t p) { return valid(p); }
param_t param_for_index(unsigned i) { return i < N ? (param_t)i : PARAM_INVALID; }
param_t param_for_used_index(unsigned i) { return param_for_index(i); }
int param_get_index(param_t p) { return valid(p) ? (int)p : -1; }
int param_get_used_index(param_t p) { return param_get_index(p); }
const char *param_name(param_t p) { return valid(p) ? px4::parameters[p].name : nullptr; }
bool param_is_volatile(param_t) { return false; }
param_type_t param_type(param_t p) { return valid(p) ? px4::parameters_type[p] : PARAM_TYPE_UNKNOWN; }
size_t param_size(param_t p) { return valid(p) ? 4 : 0; }
void param_set_used(param_t) {}

// param.h makes param_get a macro for C++ callers; this is the C function behind it
int (param_get)(param_t p, void *val)
{
	if (!valid(p) || val == nullptr) {
		return -1;
	}

	memcpy(val, &values[p], 4);
	return 0;
}

int param_get_default_value(param_t p, void *val)
{
	if (!valid(p) || val == nullptr) {
		return -1;
	}

	memcpy(val, &px4::parameters[p].val, 4);
	return 0;
}
int param_get_system_default_value(param_t p, void *val) { return param_get_default_value(p, val); }

bool param_value_is_default(param_t p)
{
	return valid(p) && memcmp(&values[p], &px4::parameters[p].val, 4) == 0;
}
bool param_value_unsaved(param_t p) { return valid(p) && changed[p]; }

int param_set_no_notification(param_t p, const void *val)
{
	if (!valid(p) || val == nullptr || readonly) {
		return -1;
	}

	memcpy(&values[p], val, 4);
	changed[p] = true;
	return 0;
}

int param_set(param_t p, const void *val)
{
	const int r = param_set_no_notification(p, val);

	if (r == 0) {
		notify();
	}

	return r;
}
int param_set_no_remote_update(param_t p, const void *val, bool notify_) { return notify_ ? param_set(p, val) : param_set_no_notification(p, val); }
int param_set_default_value(param_t, const void *) { return -1; }   // the defaults are PX4's table
void param_notify_changes() { notify(); }
int param_reset_no_notification(param_t p) { return (valid(p) && !readonly) ? (memcpy(&values[p], &px4::parameters[p].val, 4), 0) : -1; }
int param_reset(param_t p) { const int r = param_reset_no_notification(p); notify(); return r; }

// resets, as parameters.cpp: a pattern ending in '*' matches every name with that prefix
static bool matches(const char *name, const char *pattern)
{
	const size_t n = strlen(pattern);
	return (n > 0 && pattern[n - 1] == '*') ? strncmp(name, pattern, n - 1) == 0 : strcmp(name, pattern) == 0;
}

static void reset_where(bool (*keep)(const char *, const char *const *, int), const char *const *list, int n)
{
	for (unsigned i = 0; i < N; i++) {
		if (!keep(px4::parameters[i].name, list, n)) {
			param_reset_no_notification((param_t)i);
		}
	}

	notify();
}

static bool listed(const char *name, const char *const *list, int n)
{
	for (int k = 0; k < n; k++) {
		if (matches(name, list[k])) {
			return true;
		}
	}

	return false;
}

static bool not_listed(const char *name, const char *const *list, int n) { return !listed(name, list, n); }

void param_reset_all() { reset_where(not_listed, nullptr, 0); }
void param_reset_excludes(const char *excludes[], int num_excludes) { reset_where(listed, excludes, num_excludes); }
void param_reset_specific(const char *resets[], int num_resets) { reset_where(not_listed, resets, num_resets); }

// no persistent storage: saving and loading do nothing and succeed, as with an empty parameter file
int param_save_default(bool blocking) { (void)blocking; return 0; }
int param_load_default() { return 0; }
int param_export(const char *filename, param_filter_func filter) { (void)filename; (void)filter; return 0; }
void param_control_autosave(bool enable) { (void)enable; }

// as parameters.cpp: CRC32 (crc32part, PX4's table-driven reflected CRC with polynomial
// 0xEDB88320, no initial or final xor) over every used parameter's name and 4-byte value
uint32_t param_hash_check()
{
	uint32_t crc = 0;
	auto part = [&crc](const uint8_t *p, size_t n) {
		for (size_t i = 0; i < n; i++) {
			crc ^= p[i];

			for (int k = 0; k < 8; k++) {
				crc = (crc >> 1) ^ (0xEDB88320u & (0u - (crc & 1u)));
			}
		}
	};

	for (unsigned i = 0; i < N; i++) {
		part(reinterpret_cast<const uint8_t *>(px4::parameters[i].name), strlen(px4::parameters[i].name));
		part(reinterpret_cast<const uint8_t *>(&values[i]), 4);
	}

	return crc;
}

namespace px4_shim
{
void params_reset()
{
	for (unsigned i = 0; i < N; i++) {
		memcpy(&values[i], &px4::parameters[i].val, 4);
		changed[i] = false;
	}

	update_count = 0;
	readonly = false;
}

void params_readonly() { readonly = true; }

void param_store(px4::params p, const void *value)
{
	memcpy(&values[(unsigned)p], value, 4);
}
} // namespace px4_shim
