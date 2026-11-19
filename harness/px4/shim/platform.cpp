// platform.cpp: the rest of the platform a module may call (see px4_shim.h), defined here instead of
// in platforms/posix and the board support package. The harness vehicle has no device files, no
// power button, and cannot be shut down or rebooted from inside a module.
#include "px4_shim.h"

#include <errno.h>
#include <pthread.h>

#include <board_config.h>   // the SITL board, which includes board_common.h
#include <px4_platform_common/external_reset_lockout.h>
#include <px4_platform_common/posix.h>
#include <px4_platform_common/shutdown.h>
#include <px4_platform_common/time.h>

// device files (px4_open ...): none. commander_helper's LED init then reports "LED: open failed"
// at INFO level, as on a board without LEDs.
int px4_open(const char *path, int flags, ...)
{
	(void)path;
	(void)flags;
	errno = ENOENT;
	return -1;
}
int px4_close(int fd) { (void)fd; errno = EBADF; return -1; }
int px4_ioctl(int fd, int cmd, unsigned long arg) { (void)fd; (void)cmd; (void)arg; errno = EBADF; return -1; }

// the shell's list_files: there are no device files
void px4_show_files() {}

// shutdown and reboot requests are refused (commander then denies the command)
int px4_shutdown_request(uint32_t delay_us) { (void)delay_us; return -EINVAL; }

int board_register_power_state_notification_cb(power_button_state_notification_t cb) { (void)cb; return 0; }
void px4_indicate_external_reset_lockout(LockoutComponent component, bool enabled) { (void)component; (void)enabled; }

// uORB::SubscriptionBlocking's timed wait: the condition variable is signaled from a topic callback,
// so the wait ends at the next publication on the bus (a spurious wake-up for other topics, which
// the caller's updated() check absorbs) or at the deadline
int px4_pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t *mutex, const struct timespec *abstime)
{
	(void)cond;
	const uint64_t deadline = (uint64_t)abstime->tv_sec * 1000000u + (uint64_t)abstime->tv_nsec / 1000u;
	const unsigned writes = px4_shim::bus_writes();
	pthread_mutex_unlock(mutex);
	const bool woken = px4_shim::wait_until([writes] { return px4_shim::bus_writes() != writes; }, deadline);
	pthread_mutex_lock(mutex);
	return woken ? 0 : ETIMEDOUT;
}
