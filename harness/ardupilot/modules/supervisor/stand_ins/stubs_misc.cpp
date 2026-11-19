// stubs_misc.cpp: libraries the supervisor's code reaches that are switched off or hardware.
//
//   symbol                                   why outside, and what stands in
//   AP::FS(), AP_Filesystem::open, close,    the filesystem (the SITL board's POSIX backend):
//   fgets, stat                              no files; open and stat fail (-1), as for a missing
//                                            file (reached by the parameter-defaults file and
//                                            AP_Param's @ROMFS lookups)
//   AP_SurfaceDistance::data_stale,          the rangefinder surface tracker; its .cpp is all under
//   enabled_and_healthy                      AP_RANGEFINDER_ENABLED (= 0 here) but sensors.cpp calls
//                                            it unguarded. Same bodies as the real ones
//                                            (AP_SurfaceDistance.cpp:188-197); the members stay at
//                                            their zero values: not enabled, not healthy, stale.
//   AP_BoardConfig::board_setup,             board drivers (board_drivers.cpp): SPI/I2C probing,
//   board_init_safety, board_init_debug      safety switch and debug pins. No hardware: no-ops.
//   AP_BattMonitor_AD7091R5 (ctor)           switched off by AP_BATTERY_AD7091R5_ENABLED = 0
//   SocketAPM_native::SocketAPM_native,      SITL's socket class (AP_HAL/utility): a member of a
//   ~SocketAPM_native                        SITL sub-simulator held by value (stubs_sitl.cpp).
//                                            Constructed, never used: no socket is opened.
#include <AP_HAL/AP_HAL.h>
#include <AP_Filesystem/AP_Filesystem.h>
#include <AP_SurfaceDistance/AP_SurfaceDistance.h>
#include <AP_BoardConfig/AP_BoardConfig.h>
#include <AP_HAL/utility/Socket_native.h>

#ifndef RANGEFINDER_TIMEOUT_MS
#define RANGEFINDER_TIMEOUT_MS 1000   // AP_SurfaceDistance.cpp:5-6
#endif

static AP_Filesystem harness_fs;

namespace AP {
AP_Filesystem &FS()
{
    return harness_fs;
}
}

int AP_Filesystem::open(const char *fname, int flags, bool allow_absolute_paths)
{
    errno = ENOENT;
    return -1;
}

int AP_Filesystem::close(int fd)
{
    return -1;
}

bool AP_Filesystem::fgets(char *buf, uint8_t buflen, int fd)
{
    return false;
}

int AP_Filesystem::stat(const char *pathname, struct stat *stbuf)
{
    errno = ENOENT;
    return -1;
}

bool AP_SurfaceDistance::data_stale(void)
{
    return (AP_HAL::millis() - last_healthy_ms) > RANGEFINDER_TIMEOUT_MS;
}

bool AP_SurfaceDistance::enabled_and_healthy(void) const
{
    return enabled && alt_healthy;
}

void AP_BoardConfig::board_setup() {}
void AP_BoardConfig::board_init_safety() {}
void AP_BoardConfig::board_init_debug() {}

SocketAPM_native::SocketAPM_native(bool _datagram) {}
SocketAPM_native::~SocketAPM_native() {}
