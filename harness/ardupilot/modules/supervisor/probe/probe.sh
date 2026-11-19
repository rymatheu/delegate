#!/usr/bin/env bash
# Compile (no link) the supervisor's candidate sources, to measure what they reach for.
#   ardupilot/modules/supervisor/probe/probe.sh [sources-file]
# Objects, per-source logs and the symbol lists go to build/modules/supervisor/probe/.
# Uses the shared flags of ardupilot/build.sh plus flags.txt-style vehicle flags and features.txt.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
HARNESS="$(cd "$HERE/../../../.." && pwd)"
ARDUPILOT_ROOT="${ARDUPILOT_ROOT:-$HARNESS/deps/ardupilot}"
SRCS="${1:-$HERE/probe_sources.txt}"
OUT="$HARNESS/build/modules/supervisor/probe"
CXX="${CXX:-clang++}"
mkdir -p "$OUT/obj" "$OUT/log" "$OUT/cfg"
cat > "$OUT/cfg/ap_config.h" <<'X'
#pragma once
#define HAVE_CMATH_ISFINITE 1
#define HAVE_CMATH_ISINF 1
#define HAVE_CMATH_ISNAN 1
#define NEED_CMATH_ISFINITE_STD_NAMESPACE 1
#define NEED_CMATH_ISINF_STD_NAMESPACE 1
#define NEED_CMATH_ISNAN_STD_NAMESPACE 1
X
{ echo "#pragma once"
  sed -n 's/^define \(.*\)$/#define \1/p' "$ARDUPILOT_ROOT/libraries/AP_HAL_SITL/hwdef/sitl/hwdef.dat"
} > "$OUT/cfg/hwdef.h"
FLAGS=(-std=gnu++11 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math
       -cl-single-precision-constant -fsigned-char -fno-exceptions -fno-builtin
       -ffunction-sections -fdata-sections -Wno-gnu-designator -Wno-invalid-offsetof
       -DARDUPILOT_BUILD "-D__AP_LINE__=__LINE__"
       -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
       -DAP_NETWORKING_ENABLED=0 -include ap_config.h
       -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter -DFRAME_CONFIG=MULTICOPTER_FRAME
       '-DAP_BUILD_TARGET_NAME="arducopter"')
while IFS= read -r line; do
  line="${line%%#*}"; line="$(echo "$line" | tr -d '[:space:]')"
  [ -n "$line" ] && FLAGS+=("$line")
done < "$HERE/features.txt"
INCLUDES=(-I"$OUT/cfg" -I"$ARDUPILOT_ROOT/libraries" -I"$ARDUPILOT_ROOT/libraries/AP_Common/missing"
          -I"$HARNESS/build/gen/mavlink")
printf '%s\n' "${FLAGS[@]}" "${INCLUDES[@]}" -w > "$OUT/flags.rsp"
export OUT CXX ARDUPILOT_ROOT
grep -v '^#' "$SRCS" | sed '/^$/d' | xargs -n1 -P4 "$HERE/compile_one.sh" | sort > "$OUT/compile_status.txt"
grep -c '^ok' "$OUT/compile_status.txt" | sed 's/^/compiled: /'
grep '^FAIL' "$OUT/compile_status.txt"
