#!/usr/bin/env bash
# Build one harness module executable: ardupilot/build.sh NAME
#
#   1. `harness gen NAME` writes build/gen/NAME/module_records.h from the Lean declaration
#      (so run `lake build` first).
#   2. Every source in ardupilot/modules/NAME/sources.txt (relative to $ARDUPILOT_ROOT, never modified and
#      never built in place), the adapter and the stubs are compiled with the flags below into
#      build/modules/NAME/obj, each with a dependency file listing every file the compiler read.
#   3. The code hash is SHA-256 of build/modules/NAME/code_inputs.txt: one line "sha256  path" per
#      file the compiler read (sorted by path), then the compile flags, the link flags and the
#      compiler version. It is compiled into the executable, which prints it on `describe`.
#   4. Link: build/modules/NAME/NAME.
set -euo pipefail

NAME="${1:?usage: ardupilot/build.sh NAME}"
HARNESS="$(cd "$(dirname "$0")/.." && pwd)"
ARDUPILOT_ROOT="${ARDUPILOT_ROOT:-$HARNESS/deps/ardupilot}"
ARDUPILOT_ROOT="$(cd "$ARDUPILOT_ROOT" && pwd -P)"
CXX="${CXX:-clang++}"
MOD="$HARNESS/ardupilot/modules/$NAME"
OUT="$HARNESS/build/modules/$NAME"
GEN="$HARNESS/build/gen/$NAME"
HARNESS_BIN="$HARNESS/.lake/build/bin/harness"

[ -f "$MOD/sources.txt" ] || { echo "build.sh: no module $NAME ($MOD/sources.txt)" >&2; exit 1; }
[ -x "$HARNESS_BIN" ] || { echo "build.sh: $HARNESS_BIN missing; run 'lake build' first" >&2; exit 1; }

rm -rf "$OUT"
mkdir -p "$OUT/obj" "$OUT/cfg" "$GEN"

# 1. the record definitions, from Lean
(cd "$HARNESS" && "$HARNESS_BIN" gen "$NAME" > /dev/null)

# 2. ArduPilot's configuration for its SITL board, without waf:
#    ap_config.h  the host checks waf's configure writes (cmath functions in namespace std)
#    hwdef.h      the defines of the stock SITL hwdef (libraries/AP_HAL_SITL/hwdef/sitl/hwdef.dat)
cat > "$OUT/cfg/ap_config.h" <<'EOF'
// written by ardupilot/build.sh: the host checks waf's configure writes for the SITL board
#pragma once
#define HAVE_CMATH_ISFINITE 1
#define HAVE_CMATH_ISINF 1
#define HAVE_CMATH_ISNAN 1
#define NEED_CMATH_ISFINITE_STD_NAMESPACE 1
#define NEED_CMATH_ISINF_STD_NAMESPACE 1
#define NEED_CMATH_ISNAN_STD_NAMESPACE 1
EOF
{
  echo "// written by ardupilot/build.sh from libraries/AP_HAL_SITL/hwdef/sitl/hwdef.dat"
  echo "#pragma once"
  sed -n 's/^define \(.*\)$/#define \1/p' "$ARDUPILOT_ROOT/libraries/AP_HAL_SITL/hwdef/sitl/hwdef.dat"
} > "$OUT/cfg/hwdef.h"

# The flags a contract may rely on: binary32 arithmetic as written (no FMA contraction, no
# fast-math), ArduPilot's language standard and its code-generation flags for SITL
# (-cl-single-precision-constant: unsuffixed literals are float; -fsigned-char; -ftrapping-math;
# -fno-builtin), and its SITL configuration.
FLAGS=(-std=gnu++11 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math
       -cl-single-precision-constant -fsigned-char -fno-exceptions -fno-builtin
       -ffunction-sections -fdata-sections -Wno-gnu-designator -Wno-invalid-offsetof
       -DARDUPILOT_BUILD "-D__AP_LINE__=__LINE__"
       -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
       -DAP_NETWORKING_ENABLED=0
       -include ap_config.h)
# a module's own compile flags, one per line in ardupilot/modules/NAME/flags.txt (# comments), appended to the
# shared ones (and so part of the code hash); e.g. the vehicle a library is built for
if [ -f "$MOD/flags.txt" ]; then
  while IFS= read -r line; do
    line="${line%%#*}"
    line="$(echo "$line" | tr -d '[:space:]')"
    [ -n "$line" ] && FLAGS+=("$line")
  done < "$MOD/flags.txt"
fi
# build/gen/mavlink: the MAVLink headers waf would generate (ardupilot/gen_mavlink.sh), for modules
# whose code includes GCS_MAVLink
INCLUDES=(-I"$OUT/cfg" -I"$GEN" -I"$HARNESS/cpp"
          -I"$ARDUPILOT_ROOT/libraries" -I"$ARDUPILOT_ROOT/libraries/AP_Common/missing"
          -I"$HARNESS/build/gen/mavlink")
LINK_FLAGS=(-Wl,-dead_strip)

SOURCES=()
while IFS= read -r line; do
  line="${line%%#*}"
  line="$(echo "$line" | tr -d '[:space:]')"
  [ -n "$line" ] && SOURCES+=("$ARDUPILOT_ROOT/$line")
done < "$MOD/sources.txt"
SOURCES+=("$MOD/adapter.cpp" "$MOD/stubs.cpp")
# further translation units of the module's own, one per line in ardupilot/modules/NAME/local_sources.txt
# (paths relative to the module folder; # comments): a unit that needs its own preprocessor setup
if [ -f "$MOD/local_sources.txt" ]; then
  while IFS= read -r line; do
    line="${line%%#*}"
    line="$(echo "$line" | tr -d '[:space:]')"
    [ -n "$line" ] && SOURCES+=("$MOD/$line")
  done < "$MOD/local_sources.txt"
fi

OBJS=()
for src in "${SOURCES[@]}"; do
  base="$(basename "$src" .cpp)"
  obj="$OUT/obj/$base.o"
  (cd "$OUT/obj" && "$CXX" "${FLAGS[@]}" "${INCLUDES[@]}" -MD -MF "$OUT/obj/$base.d" -c "$src" -o "$obj")
  OBJS+=("$obj")
done

# 3. the code hash: every file named in the dependency files (sources and every header read)
label() {  # absolute path -> label with the two roots abbreviated
  local p="$1"
  case "$p" in
    "$ARDUPILOT_ROOT"/*) echo "\$ARDUPILOT_ROOT/${p#"$ARDUPILOT_ROOT"/}" ;;
    "$HARNESS"/*) echo "\$HARNESS/${p#"$HARNESS"/}" ;;
    *) echo "$p" ;;
  esac
}
DEPS="$OUT/deps.txt"
cat "$OUT"/obj/*.d | sed -e 's/\\$//' -e 's/^[^:]*: *//' | tr ' ' '\n' | sed '/^$/d' | sort -u |
  while IFS= read -r f; do realpath "$f"; done | sort -u > "$DEPS"
COMPILER="$("$CXX" --version | head -1)"
{
  while IFS= read -r f; do
    printf '%s  %s\n' "$(shasum -a 256 "$f" | cut -d' ' -f1)" "$(label "$f")"
  done < "$DEPS" | LC_ALL=C sort -k2
  echo "flags: ${FLAGS[*]}"
  echo "link: ${LINK_FLAGS[*]}"
  echo "compiler: $COMPILER"
} > "$OUT/code_inputs.txt"
CODE_HASH="$(shasum -a 256 "$OUT/code_inputs.txt" | cut -d' ' -f1)"
# where the labels point, for `harness status` to recompute the hash (not part of the hash)
printf 'ARDUPILOT_ROOT=%s\nHARNESS=%s\n' "$ARDUPILOT_ROOT" "$HARNESS" > "$OUT/roots.env"

cat > "$OUT/codehash.cpp" <<EOF
// written by ardupilot/build.sh; not part of the code hash (it holds it)
extern const char harness_code_hash[] = "$CODE_HASH";
extern const char harness_build_flags[] = "${FLAGS[*]}";
extern const char harness_compiler[] = "$COMPILER";
EOF
"$CXX" -c "$OUT/codehash.cpp" -o "$OUT/obj/codehash.o"

# 4. link (libc++ and the system math library)
"$CXX" "${LINK_FLAGS[@]}" "${OBJS[@]}" "$OUT/obj/codehash.o" -o "$OUT/$NAME"
echo "built $OUT/$NAME"
echo "  sources: ${#SOURCES[@]} compiled, $(wc -l < "$DEPS" | tr -d ' ') files read by the compiler"
echo "  code hash: $CODE_HASH"
