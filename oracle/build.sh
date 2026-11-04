#!/usr/bin/env bash
# Build the C++ oracle: ArduPilot's control classes, compiled unmodified from the ArduPilot tree,
# with the stub include directory oracle/stubs ahead of libraries/ on the include path.
#
# Usage: oracle/build.sh [VARIANT...]   (default: nosincos sincos)
#   nosincos        the oracle. Apple clang, -fno-builtin-sinf -fno-builtin-cosf (no fusion of
#                   sinf/cosf pairs into __sincosf_stret; the flags of the port binary
#                   sim/build/copter-c and of lakefile.toml moreLeancArgs) -> build/oracle-nosincos
#   sincos          Apple clang with its default builtins, as a waf SITL build on this host would
#                   compile -> build/oracle-sincos (it links no __sincosf_stret either: clang finds
#                   no fusable pair in these sources; the two binaries give identical output)
#   gcc             GCC (g++-15) with GCC's flag -fsingle-precision-constant, as a Linux SITL build
#                   would compile (boards.py:410, :521) -> build/oracle-gcc. On this host GCC turns
#                   each sinf/cosf pair into one cexpf call (its sincos lowering on Darwin).
#                   (-fno-builtin-sinf/-cosf does not stop it: libstdc++'s std::sin(float) calls
#                   __builtin_sinf.)
#   diag-floattrig  DIAGNOSTIC ONLY, not the oracle: as nosincos, but AP_Math/quaternion.cpp is
#                   replaced by diag/quaternion.cpp, a copy whose from_axis_angle/from_euler/angle use
#                   float sinf/cosf/asinf (edits marked // ORACLE:, listed in DIFF.md). Set
#                   DIAG_DEFINES="-DORACLE_DIAG_EULER=0 ..." to switch single edits off.
# Environment: AP (ArduPilot tree, default /Users/ryan/Research/delegate/ardupilot), CXX (clang++),
# GXX (g++-15).
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
AP="${AP:-/Users/ryan/Research/delegate/ardupilot}"
L="$AP/libraries"
CXX="${CXX:-clang++}"
GXX="${GXX:-/opt/homebrew/bin/g++-15}"
VARIANTS="${*:-nosincos sincos}"

# ArduPilot sources compiled unmodified: the modules that have a Lean equivalent in the port, and
# the dependencies their .cpp files need (README.md, "What is compiled").
SOURCES=(
  AC_AttitudeControl/AC_PosControl.cpp
  AC_AttitudeControl/AC_AttitudeControl.cpp
  AC_AttitudeControl/AC_AttitudeControl_Multi.cpp
  AP_Motors/AP_Motors_Class.cpp
  AP_Motors/AP_MotorsMulticopter.cpp
  AP_Motors/AP_MotorsMatrix.cpp
  AP_Motors/AP_Motors_Thrust_Linearization.cpp
  AC_PID/AC_PID.cpp
  AC_PID/AC_PID_2D.cpp
  AC_PID/AC_PID_Basic.cpp
  AC_PID/AC_P.cpp
  AC_PID/AC_P_1D.cpp
  AC_PID/AC_P_2D.cpp
  AP_Math/AP_Math.cpp
  AP_Math/control.cpp
  AP_Math/vector2.cpp
  AP_Math/vector3.cpp
  AP_Math/matrix3.cpp
  AP_Math/quaternion.cpp
  Filter/LowPassFilter.cpp
  Filter/SlewLimiter.cpp
  Filter/DerivativeFilter.cpp
  AP_Param/AP_ParamT.cpp
)

# Defines: the SITL board (Tools/ardupilotwaf/boards.py:877-893; the cfg.define()s are in
# stubs/ap_config.h), the vehicle macros of a Copter build (ardupilotwaf.py:143-144,
# ArduCopter/wscript:47), the line macro (boards.py:669), the two double-precision switches
# (SITL's own defaults, AP_HAL_Boards.h:385-386 and board/sitl.h:88-89, made explicit), and
# AP_FILTER_ENABLED 0, which compiles the AC_PID notch-filter paths out (the port has no notch
# filtering; AC_PID.h:176, :199, AC_PID.cpp:83-247).
DEFINES=(
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL
  -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
  -DAP_SCRIPTING_CHECKS=1
  -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1
  -DHAL_NAVEKF2_AVAILABLE=1
  -DARDUPILOT_BUILD
  -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter
  -DAP_BUILD_TARGET_NAME='"ArduCopter"'
  -DFRAME_CONFIG=MULTICOPTER_FRAME
  -D__AP_LINE__=__LINE__
  -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1
  -DAP_FILTER_ENABLED=0
)
INCLUDES=(-I"$HERE/stubs" -I"$L/AP_Common/missing" -I"$L" -include ap_config.h)

# Flags: the C++ dialect and floating-point flags of the waf build (boards.py:395-411, :427-536;
# -cl-single-precision-constant for clang, -fsingle-precision-constant for GCC), with -O2 in place of
# SITL's -O3 (boards.py:944;
# neither changes floating-point semantics: no fast-math, no contraction).
COMMON=(-std=gnu++11 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math
        -fsigned-char -fno-exceptions -fno-rtti -Wno-unused-parameter -Wno-invalid-offsetof)
CLANG_FLAGS=(-cl-single-precision-constant -Wno-inconsistent-missing-override -Wno-gnu-designator
             -Wno-vla-extension -Wno-expansion-to-defined -Wno-trigraphs)
GCC_FLAGS=(-fsingle-precision-constant -Wno-psabi -Wno-trigraphs -Wno-expansion-to-defined)

for v in $VARIANTS; do
  SRCS=()
  for s in "${SOURCES[@]}"; do SRCS+=("$L/$s"); done
  C="$CXX"
  FLAGS=("${COMMON[@]}" "${CLANG_FLAGS[@]}")
  case "$v" in
    nosincos) FLAGS+=(-fno-builtin-sinf -fno-builtin-cosf) ;;
    sincos) ;;
    gcc) C="$GXX"; FLAGS=("${COMMON[@]}" "${GCC_FLAGS[@]}") ;;
    diag-floattrig)
      FLAGS+=(-fno-builtin-sinf -fno-builtin-cosf -I"$L/AP_Math" ${DIAG_DEFINES:-})
      for i in "${!SRCS[@]}"; do
        if [ "${SRCS[$i]}" = "$L/AP_Math/quaternion.cpp" ]; then SRCS[$i]="$HERE/diag/quaternion.cpp"; fi
      done ;;
    *) echo "unknown variant $v" >&2; exit 2 ;;
  esac
  OBJ="$HERE/build/obj-$v"
  mkdir -p "$OBJ"
  objs=()
  for s in "${SRCS[@]}" "$HERE/stubs/oracle_env.cpp" "$HERE/main.cpp"; do
    o="$OBJ/$(echo "${s#$L/}" | tr / _ | sed 's/\.cpp$/.o/')"
    "$C" "${FLAGS[@]}" "${DEFINES[@]}" "${INCLUDES[@]}" -c "$s" -o "$o"
    objs+=("$o")
  done
  "$C" -o "$HERE/build/oracle-$v" "${objs[@]}" -Wl,-dead_strip
  echo "built $HERE/build/oracle-$v; libm imports:" \
    $(nm -u "$HERE/build/oracle-$v" | grep -E '^_(a?(sin|cos|tan)f?|atan2?f?|sqrtf?|powf?|expf?|logf?|fmodf?|cexpf?|__sincos.*)$' | tr '\n' ' ')
done
