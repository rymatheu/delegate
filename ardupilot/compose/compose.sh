#!/usr/bin/env bash
# Per-tick composition check: the translations of AP_MotorsMatrix (ardupilot/out/AP_Motors),
# AC_AttitudeControl_Multi (out/AC_Attitude) and AC_PosControl (out/AC_PosControl), wired for one
# tick as the reference harness wires the compiled classes (Compose.lean), run on the recorded
# flight, and compared with the oracle's recorded output (ardupilot/data/oracle-nosincos.txt): the four actuators and the other 18 numbers of each tick, bit for bit.
# Usage: ardupilot/compose/compose.sh [N [HOLD_FROM]]   (N ticks from the start, default 500;
#        HOLD_FROM the tick at which AutoYaw switches to HOLD, default 6618, the tick of the recorded flight)
# Environment: AP (ArduPilot tree), RUN (the recorded flight, default ardupilot/data).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"          # cpp2lean/
AP="${AP:-$ROOT/ardupilot/src}"
L="$AP/libraries"
STUBS="$ROOT/ardupilot/stubs"
RUN="${RUN:-$ROOT/ardupilot/data}"
ORACLE_OUT="$ROOT/ardupilot/data/oracle-nosincos.txt"
N="${1:-500}"
HOLD_FROM="${2:-6618}"
B="$ROOT/build/compose"
mkdir -p "$B"

# 1. the environment (the AHRS view of each sample, the navigator's targets): the oracle's stub code,
#    compiled with the reference flags
FLAGS=(-std=gnu++11 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math -fsigned-char -fno-exceptions -fno-rtti
  -Wno-unused-parameter -Wno-invalid-offsetof -cl-single-precision-constant -Wno-inconsistent-missing-override
  -Wno-gnu-designator -Wno-vla-extension -Wno-expansion-to-defined -Wno-trigraphs -fno-builtin-sinf -fno-builtin-cosf
  -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE -DAP_SCRIPTING_CHECKS=1
  -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1 -DARDUPILOT_BUILD -DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter
  '-DAP_BUILD_TARGET_NAME="ArduCopter"' -DFRAME_CONFIG=MULTICOPTER_FRAME -D__AP_LINE__=__LINE__ -DHAL_WITH_POSTYPE_DOUBLE=1
  -DHAL_WITH_EKF_DOUBLE=1 -DAP_FILTER_ENABLED=0 -I"$STUBS" -I"$L/AP_Common/missing" -I"$L" -include ap_config.h)
objs=()
for s in "$HERE/compose_env.cpp" "$L/AP_Math/AP_Math.cpp" "$L/AP_Math/vector2.cpp" "$L/AP_Math/vector3.cpp" "$L/AP_Math/matrix3.cpp" "$L/AP_Math/quaternion.cpp"; do
  o="$B/$(basename "$s" .cpp).o"
  clang++ "${FLAGS[@]}" -c "$s" -o "$o"
  objs+=("$o")
done
clang++ -o "$B/compose_env" "${objs[@]}" -Wl,-dead_strip
"$B/compose_env" "$RUN/inputs.txt" "$RUN/trace.txt" "$N" > "$B/env.txt"

# 2. the Lean side: the translations and Compose.lean in the Lean package, executable `compose`
D="$ROOT/lean"
for d in AP_Motors AC_Attitude AC_PosControl; do cp "$ROOT/ardupilot/out/$d/"*.lean "$D/"; done
cp "$HERE/Compose.lean" "$D/Compose.lean"
if [ -n "${CPP2LEAN_MUTATE:-}" ]; then
  # sensitivity check (README.md): [regex, replacement] pairs applied to one translation's copy
  python3 - "$D/${CPP2LEAN_MUTATE_FILE:-AC_Attitude_lib.lean}" <<'PY'
import json, os, re, sys
t = open(sys.argv[1]).read()
for pat, rep in json.loads(os.environ["CPP2LEAN_MUTATE"]):
    t, k = re.subn(pat, rep, t)
    print("mutation of %s: %d replacements of /%s/" % (os.path.basename(sys.argv[1]), k, pat))
open(sys.argv[1], "w").write(t)
PY
fi
grep -q '^name = "compose"' "$D/lakefile.toml" || printf '\n[[lean_exe]]\nname = "compose"\nroot = "Compose"\n' >> "$D/lakefile.toml"
(cd "$D" && lake build compose 2>&1 | grep -v "^✔\|^⣿\|Build completed" || true)
"$D/.lake/build/bin/compose" "$HOLD_FROM" < "$B/env.txt" > "$B/compose.out"

# 3. compare with the oracle's recorded output
python3 - "$B/compose.out" "$ORACLE_OUT" "$N" <<'PY'
import sys
lean = [l.split() for l in open(sys.argv[1]).read().splitlines()]
orc = [l.split("|")[1].split() for l in open(sys.argv[2]).read().splitlines()]
n = int(sys.argv[3])
names = ["m1", "m2", "m3", "m4", "pos_n", "pos_e", "pos_d", "vel_n", "vel_e", "vel_d", "acc_n", "acc_e", "acc_d",
         "thr_n", "thr_e", "thr_d", "roll_t", "pitch_t", "yaw_t", "p_t", "q_t", "r_t"]
if len(lean) < n:
    sys.exit("compose: %d ticks computed, %d wanted" % (len(lean), n))
act = sum(1 for k in range(n) if lean[k][:4] == orc[k][:4])
allq = sum(1 for k in range(n) if lean[k] == orc[k])
print("composition: %d ticks; actuators bit-identical to the oracle on %d of %d ticks; all 22 values on %d of %d ticks"
      % (n, act, n, allq, n))
badact = [k for k in range(n) if lean[k][:4] != orc[k][:4]]
if badact:
    print("  first actuator difference at tick %d" % (badact[0] + 1))
bad = [k for k in range(n) if lean[k] != orc[k]]
if bad:
    k = bad[0]
    d = [(names[j], orc[k][j], lean[k][j]) for j in range(22) if orc[k][j] != lean[k][j]]
    print("  first difference at tick %d: %s" % (k + 1, ", ".join("%s oracle %s Lean %s" % x for x in d[:6])))
sys.exit(0 if not bad else 1)
PY
