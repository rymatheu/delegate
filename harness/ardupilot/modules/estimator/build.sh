#!/usr/bin/env bash
# Build the estimator module: ardupilot/modules/estimator/build.sh
#
# The same steps, flags, code hash and outputs as ardupilot/build.sh (read it first), with three
# differences, all because this module compiles about 60 ArduPilot sources (EKF3 alone is 14,000
# lines) where the others compile a handful:
#   * the compiles run 4 at a time (xargs -P 4);
#   * the module's own sources are every adapter.cpp, stubs_*.cpp and backend_*.cpp in this folder
#     (the cut is split by what each file stands for);
#   * ESTIMATOR_INCREMENTAL=1 (development only) keeps build/modules/estimator/obj and recompiles
#     only the objects whose source or a file in their dependency list is newer. A build for the
#     ledger is a full one (the default), so that the dependency lists are fresh.
# Compiler warnings go to build/modules/estimator/warnings.log.
set -euo pipefail

NAME=estimator
HARNESS="$(cd "$(dirname "$0")/../../.." && pwd)"
ARDUPILOT_ROOT="${ARDUPILOT_ROOT:-$HARNESS/deps/ardupilot}"
ARDUPILOT_ROOT="$(cd "$ARDUPILOT_ROOT" && pwd -P)"
CXX="${CXX:-clang++}"
MOD="$HARNESS/ardupilot/modules/$NAME"
OUT="$HARNESS/build/modules/$NAME"
GEN="$HARNESS/build/gen/$NAME"
HARNESS_BIN="$HARNESS/.lake/build/bin/harness"
INCR="${ESTIMATOR_INCREMENTAL:-0}"

[ -x "$HARNESS_BIN" ] || { echo "build.sh: $HARNESS_BIN missing; run 'lake build' first" >&2; exit 1; }
[ -f "$HARNESS/build/gen/mavlink/include/mavlink/v2.0/all/version.h" ] || {
  echo "build.sh: MAVLink headers missing; run ardupilot/gen_mavlink.sh first" >&2; exit 1; }

if [ "$INCR" != 1 ]; then rm -rf "$OUT"; fi
mkdir -p "$OUT/obj" "$OUT/cfg" "$GEN"
rm -f "$OUT/$NAME"

# 1. the record definitions, from Lean (rewritten only when they change, for the incremental mode)
(cd "$HARNESS" && "$HARNESS_BIN" gen "$NAME" > /dev/null)

# 2. ArduPilot's configuration for its SITL board, as ardupilot/build.sh writes it
cat > "$OUT/cfg/ap_config.h.new" <<'EOF'
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
} > "$OUT/cfg/hwdef.h.new"
for f in ap_config.h hwdef.h; do
  if cmp -s "$OUT/cfg/$f.new" "$OUT/cfg/$f"; then rm "$OUT/cfg/$f.new"; else mv "$OUT/cfg/$f.new" "$OUT/cfg/$f"; fi
done

# the shared flags of ardupilot/build.sh, unchanged
FLAGS=(-std=gnu++11 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math
       -cl-single-precision-constant -fsigned-char -fno-exceptions -fno-builtin
       -ffunction-sections -fdata-sections -Wno-gnu-designator -Wno-invalid-offsetof
       -DARDUPILOT_BUILD "-D__AP_LINE__=__LINE__"
       -DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
       -DAP_NETWORKING_ENABLED=0
       -include ap_config.h)
if [ -f "$MOD/flags.txt" ]; then
  while IFS= read -r line; do
    line="${line%%#*}"
    line="$(echo "$line" | tr -d '[:space:]')"
    [ -n "$line" ] && FLAGS+=("$line")
  done < "$MOD/flags.txt"
fi
INCLUDES=(-I"$OUT/cfg" -I"$GEN" -I"$HARNESS/cpp"
          -I"$ARDUPILOT_ROOT/libraries" -I"$ARDUPILOT_ROOT/libraries/AP_Common/missing"
          -I"$HARNESS/build/gen/mavlink")
LINK_FLAGS=(-Wl,-dead_strip -lpthread)

SOURCES=()
while IFS= read -r line; do
  line="${line%%#*}"
  line="$(echo "$line" | tr -d '[:space:]')"
  [ -n "$line" ] && SOURCES+=("$ARDUPILOT_ROOT/$line")
done < "$MOD/sources.txt"
for f in "$MOD"/adapter.cpp "$MOD"/backend_*.cpp "$MOD"/stubs_*.cpp; do
  [ -f "$f" ] && SOURCES+=("$f")
done

# object names: the source's base name, with its directory prefixed where two sources share one
objname() {
  local src="$1" base
  base="$(basename "$src" .cpp)"
  local n=0
  # the file system may ignore case (location.cpp and Location.cpp), so compare in lower case
  local lbase
  lbase="$(echo "$base" | tr '[:upper:]' '[:lower:]')"
  for s in "${SOURCES[@]}"; do
    [ "$(basename "$s" .cpp | tr '[:upper:]' '[:lower:]')" = "$lbase" ] && n=$((n + 1))
  done
  if [ "$n" -gt 1 ]; then base="$(basename "$(dirname "$src")")_$base"; fi
  echo "$base"
}

# the compile of one source, written as a script line for xargs
FLAGFILE="$OUT/compile_flags.txt"
printf '%s\n' "${FLAGS[@]}" "${INCLUDES[@]}" > "$FLAGFILE.new"
if ! cmp -s "$FLAGFILE.new" "$FLAGFILE"; then
  rm -f "$OUT"/obj/*.o "$OUT"/obj/*.d   # the flags changed: every object is stale
  mv "$FLAGFILE.new" "$FLAGFILE"
else
  rm "$FLAGFILE.new"
fi
JOBS="$OUT/jobs.txt"
: > "$JOBS"
OBJS=()
for src in "${SOURCES[@]}"; do
  base="$(objname "$src")"
  obj="$OUT/obj/$base.o"
  OBJS+=("$obj")
  if [ "$INCR" = 1 ] && [ -f "$obj" ] && [ -f "$OUT/obj/$base.d" ]; then
    stale=0
    while IFS= read -r dep; do
      if [ "$dep" -nt "$obj" ]; then stale=1; break; fi
    done < <(sed -e 's/\\$//' -e 's/^[^:]*: *//' "$OUT/obj/$base.d" | tr ' ' '\n' | sed '/^$/d')
    [ "$stale" = 0 ] && continue
  fi
  printf '%s\t%s\t%s\n' "$src" "$obj" "$OUT/obj/$base.d" >> "$JOBS"
done
: > "$OUT/warnings.log"
if [ -s "$JOBS" ]; then
  echo "compiling $(wc -l < "$JOBS" | tr -d ' ') of ${#SOURCES[@]} sources (4 jobs)"
  export CXX FLAGFILE OUT
  # shellcheck disable=SC2016
  if ! tr '\n' '\0' < "$JOBS" | xargs -0 -n 1 -P 4 sh -c '
      IFS="	" read -r src obj dep <<EOF
$1
EOF
      cd "$OUT/obj" && "$CXX" @"$FLAGFILE" -MD -MF "$dep" -c "$src" -o "$obj" \
        > "$obj.log" 2>&1 || { cat "$obj.log" >&2; exit 255; }' sh; then
    echo "build.sh: compile failed" >&2
    exit 1
  fi
  for log in "$OUT"/obj/*.o.log; do
    [ -s "$log" ] && { echo "== $log"; cat "$log"; } >> "$OUT/warnings.log"
    rm -f "$log"
  done
fi

# 3. the code hash, as ardupilot/build.sh computes it
label() {
  local p="$1"
  case "$p" in
    "$ARDUPILOT_ROOT"/*) echo "\$ARDUPILOT_ROOT/${p#"$ARDUPILOT_ROOT"/}" ;;
    "$HARNESS"/*) echo "\$HARNESS/${p#"$HARNESS"/}" ;;
    *) echo "$p" ;;
  esac
}
DEPS="$OUT/deps.txt"
DFILES=()
for o in "${OBJS[@]}"; do DFILES+=("${o%.o}.d"); done
cat "${DFILES[@]}" | sed -e 's/\\$//' -e 's/^[^:]*: *//' | tr ' ' '\n' | sed '/^$/d' | sort -u |
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
printf 'ARDUPILOT_ROOT=%s\nHARNESS=%s\n' "$ARDUPILOT_ROOT" "$HARNESS" > "$OUT/roots.env"

cat > "$OUT/codehash.cpp" <<EOF
// written by ardupilot/build.sh; not part of the code hash (it holds it)
extern const char harness_code_hash[] = "$CODE_HASH";
extern const char harness_build_flags[] = "${FLAGS[*]}";
extern const char harness_compiler[] = "$COMPILER";
EOF
"$CXX" -c "$OUT/codehash.cpp" -o "$OUT/codehash.o"

# 4. link (libc++, the system math library and pthreads: the boot thread, see adapter.cpp)
"$CXX" "${LINK_FLAGS[@]}" "${OBJS[@]}" "$OUT/codehash.o" -o "$OUT/$NAME"
echo "built $OUT/$NAME"
echo "  sources: ${#SOURCES[@]} compiled, $(wc -l < "$DEPS" | tr -d ' ') files read by the compiler"
echo "  code hash: $CODE_HASH"
