// log.cpp: logging (see px4_shim.h).
//
// PX4's log functions print to stdout, which here is the harness pipe; they are defined here
// instead of in px4_log.cpp. A message goes to stderr when the environment has PX4_SHIM_LOG=1, and
// is dropped otherwise. Errors and panics are counted; the count is the output px4_errors.
#include "px4_shim.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

#include <px4_platform_common/log.h>

namespace
{
uint32_t errors = 0;

bool enabled()
{
	static int e = -1;

	if (e < 0) {
		const char *v = getenv("PX4_SHIM_LOG");
		e = (v != nullptr && v[0] == '1') ? 1 : 0;
	}

	return e == 1;
}
} // namespace

const char *__px4_log_level_str[_PX4_LOG_LEVEL_PANIC + 1] = {"DEBUG", "INFO", "WARN", "ERROR", "PANIC"};

void px4_log_initialize() {}

void px4_log_modulename(int level, const char *module_name, const char *fmt, ...)
{
	if (level >= _PX4_LOG_LEVEL_ERROR) {
		errors++;
	}

	if (enabled()) {
		fprintf(stderr, "%s [%s] ", __px4_log_level_str[level], module_name);
		va_list a;
		va_start(a, fmt);
		vfprintf(stderr, fmt, a);
		va_end(a);
		fputc('\n', stderr);
	}
}

void px4_log_raw(int level, const char *fmt, ...)
{
	(void)level;

	if (enabled()) {
		va_list a;
		va_start(a, fmt);
		vfprintf(stderr, fmt, a);
		va_end(a);
	}
}

namespace px4_shim
{
void log_reset() { errors = 0; }
uint32_t error_count() { return errors; }
}
