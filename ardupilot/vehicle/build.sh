#!/usr/bin/env bash
# Build the two vehicles of the lock-step protocol (sim/PROTOCOL.md):
#   build/vehicle/copter_ref   ardupilot/vehicle/copter_ref.cpp over ArduPilot's classes, compiled
#                              unmodified with the stub headers (ardupilot/stubs) and the flags of the
#                              translations plus the code-generation flags of the compilation
#                              assumptions (README.md), linked with musl's math functions
#                              (libm/build_musl.sh), not the platform's libm
#   lean/.lake/build/bin/copter_lean
#                              lean/Vehicle.lean + lean/VehicleMain.lean over the Lean translations
#                              (ardupilot/out/*), with the parameter tables generated from their
#                              signatures.json (ardupilot/vehicle/gen_params.py -> lean/VehicleParams.lean)
# Usage: ardupilot/vehicle/build.sh [cpp|lean]...   (default: both)
# Environment: AP (ArduPilot tree at commit 802db19de1; default ardupilot/src), CXX (clang++).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$ROOT/ardupilot/stubs"
CXX="${CXX:-clang++}"
WHAT="${*:-cpp lean}"

if [[ " $WHAT " == *" cpp "* ]]; then
  # ArduPilot sources compiled unmodified: the classes the harness drives and what they need
  SOURCES=(
    AC_WPNav/AC_WPNav.cpp
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
    AP_Math/location.cpp
    AP_Math/SCurve.cpp
    AP_Math/SplineCurve.cpp
    AP_Common/Location.cpp
    Filter/LowPassFilter.cpp
    Filter/SlewLimiter.cpp
    Filter/DerivativeFilter.cpp
    AP_Param/AP_ParamT.cpp
  )
  # the SITL board and Copter build defines (as the translations), the terrain database compiled out
  # (AP_Terrain.h needs MAVLink's types; only AC_WPNav.cpp and AP_Common/Location.cpp see the define)
  DEFINES=(-DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
    -DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1
    -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter '-DAP_BUILD_TARGET_NAME="ArduCopter"'
    -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
    -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -DAP_TERRAIN_AVAILABLE=0)
  INCLUDES=(-I"$STUBS" -I"$L/AP_Common/missing" -I"$L" -include ap_config.h)
  FLAGS=(-std=gnu++11 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math -fsigned-char -fno-exceptions -fno-rtti
    -Wno-unused-parameter -Wno-invalid-offsetof -cl-single-precision-constant -Wno-inconsistent-missing-override
    -Wno-gnu-designator -Wno-vla-extension -Wno-expansion-to-defined -Wno-trigraphs
    -fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos -fno-builtin)
  OBJ="$ROOT/build/vehicle/obj"
  mkdir -p "$OBJ"
  objs=()
  for s in "${SOURCES[@]}"; do
    o="$OBJ/$(echo "$s" | tr / _ | sed 's/\.cpp$/.o/')"
    "$CXX" "${FLAGS[@]}" "${DEFINES[@]}" "${INCLUDES[@]}" -c "$L/$s" -o "$o"
    objs+=("$o")
  done
  for s in "$STUBS/oracle_env.cpp" "$HERE/vehicle_env.cpp" "$HERE/copter_ref.cpp"; do
    o="$OBJ/$(basename "$s" .cpp).o"
    "$CXX" "${FLAGS[@]}" "${DEFINES[@]}" "${INCLUDES[@]}" -c "$s" -o "$o"
    objs+=("$o")
  done
  # musl's math functions (the same C sources the Lean side translates), bound to the C names
  MUSL=($(cat "$("$ROOT/libm/build_musl.sh")"))
  "$CXX" -o "$ROOT/build/vehicle/copter_ref" "${objs[@]}" "${MUSL[@]}" -Wl,-dead_strip
  # the C library functions the reference still imports from the platform (none expected)
  IMP=$(nm -u "$ROOT/build/vehicle/copter_ref" | grep -E '^_(a?(sin|cos|tan)h?f?|atan2?f?|sqrtf?|powf?|expf?|exp2f?|logf?|log2f?|log10f?|fmodf?|f(min|max|abs)f?|floorf?|ceilf?|truncf?|roundf?|copysignf?|scalbnf?|ldexpf?|hypotf?|fmaf?|cexpf?|__sincos.*)$' | tr '\n' ' ' || true)
  echo "built build/vehicle/copter_ref; math functions imported from the platform's libm: ${IMP:-none}"
fi

if [[ " $WHAT " == *" lean "* ]]; then
  D="$ROOT/lean"
  for d in Copter AHRS_View; do
    if [ ! -f "$ROOT/ardupilot/out/$d/${d}_lib.lean" ]; then
      echo "build.sh: no translation in ardupilot/out/$d (run ardupilot/translate_*.sh)" >&2
      exit 1
    fi
    cp "$ROOT/ardupilot/out/$d/"*.lean "$D/"
  done
  python3 "$HERE/gen_params.py" "$ROOT/ardupilot/out" > "$D/VehicleParams.lean"
  grep -q '^name = "VehicleLib"' "$D/lakefile.toml" || printf '\n[[lean_lib]]\nname = "VehicleLib"\nroots = ["VehicleParams", "Vehicle"]\n' >> "$D/lakefile.toml"
  grep -q '^name = "copter_lean"' "$D/lakefile.toml" || printf '\n[[lean_exe]]\nname = "copter_lean"\nroot = "VehicleMain"\n' >> "$D/lakefile.toml"
  # the two translations in the Translated library's roots (the first `roots`), if a difftest has not put them there
  python3 - "$D/lakefile.toml" <<'PY2'
import re, sys
p = sys.argv[1]; t = open(p).read()
m = re.search(r'^roots = \[(.*)\]$', t, re.M)
roots = re.findall(r'"([^"]+)"', m.group(1))
new = roots + [r for r in ("Copter_lib", "AHRS_View_lib") if r not in roots]
if new != roots:
    open(p, "w").write(t[:m.start()] + "roots = [%s]" % ", ".join('"%s"' % r for r in new) + t[m.end():])
PY2
  if ! out=$(cd "$D" && lake build copter_lean 2>&1); then echo "$out" | grep -v "^✔"; exit 1; fi
  echo "$out" | grep -v "^✔\|^⣿\|Build completed" || true
  echo "built lean/.lake/build/bin/copter_lean"
fi
