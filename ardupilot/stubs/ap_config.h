// ORACLE STUB: replaces the waf-generated build/sitl/ap_config.h (wscript:675, `-include ap_config.h`).
// Holds the cfg.define() values the SITL board writes there (Tools/ardupilotwaf/boards.py:886-893)
// that the compiled sources can see, plus _GNU_SOURCE (wscript:667). Defines that waf passes on the
// command line (env.DEFINES / CXXFLAGS) are in build.sh, not here.
#ifndef _AP_CONFIG_H_
#define _AP_CONFIG_H_
#define _GNU_SOURCE 1
#define AP_SIM_ENABLED 1
#define HAL_WITH_SPI 1
#define HAL_WITH_RAMTRON 1
#define AP_OPENDRONEID_ENABLED 1
#define AP_SIGNED_FIRMWARE 0
#define AP_NOTIFY_LP5562_BUS 2
#define AP_NOTIFY_LP5562_ADDR 0x30
#endif
