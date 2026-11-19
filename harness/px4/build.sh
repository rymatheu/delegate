#!/usr/bin/env bash
# Build one PX4 harness module executable: px4/build.sh NAME   (px4/gen.sh once first)
#
#   1. px4/ports.py NAME writes px4/modules/NAME/Ports.lean, build/gen/NAME/px4_ports.cpp and the
#      module's parameter table, from px4/modules/NAME/px4.txt and PX4's own definitions.
#   2. `lake build` (if Ports.lean changed) and `harness gen NAME` (module_records.h, from Lean).
#   3. Compile, each with a dependency file: the module's sources (px4.txt, relative to $PX4_ROOT,
#      never modified), PX4's framework sources every module uses (below), PX4's generated uORB
#      metadata, the generated ports and the generic shim (px4/shim).
#   4. The code hash, as ardupilot/build.sh: SHA-256 of build/modules/NAME/code_inputs.txt, one line
#      per file the compiler read, then the flags, the link flags and the compiler version.
#   5. Link: build/modules/NAME/NAME.
set -euo pipefail

NAME="${1:?usage: px4/build.sh NAME}"
HARNESS="$(cd "$(dirname "$0")/.." && pwd)"
PX4_ROOT="${PX4_ROOT:-$HARNESS/deps/px4}"
PX4_ROOT="$(cd "$PX4_ROOT" && pwd -P)"
CXX="${CXX:-clang++}"
CC="${CC:-clang}"
MOD="$HARNESS/px4/modules/$NAME"
OUT="$HARNESS/build/modules/$NAME"
GEN="$HARNESS/build/gen/$NAME"
PXGEN="$HARNESS/build/gen/px4"
SHIM="$HARNESS/px4/shim"
HARNESS_BIN="$HARNESS/.lake/build/bin/harness"

# a PX4-stack module with no PX4 sources (a bridge to the simulator, a test driver): only its
# adapter.cpp, built by px4/plain_build.sh
if [ ! -f "$MOD/px4.txt" ] && [ -f "$MOD/adapter.cpp" ]; then exec "$HARNESS/px4/plain_build.sh" "$NAME"; fi
[ -f "$MOD/px4.txt" ] || { echo "px4_build.sh: no PX4 module $NAME ($MOD/px4.txt)" >&2; exit 1; }
[ -f "$PXGEN/source.txt" ] || { echo "px4_build.sh: run px4/gen.sh first" >&2; exit 1; }

# 1. ports
python3 -I "$HARNESS/px4/ports.py" "$NAME"
# a merge node (px4.txt `merge`): no PX4 code, only the generated word copying and the protocol
if grep -q '^merge ' "$MOD/px4.txt"; then
  (cd "$HARNESS" && LEAN_NUM_THREADS=1 lake build > /dev/null)
  rm -rf "$OUT"; mkdir -p "$OUT/obj"
  (cd "$HARNESS" && "$HARNESS_BIN" gen "$NAME" > /dev/null)
  MFLAGS=(-std=gnu++14 -O2 -ffp-contract=off -fno-fast-math)
  "$CXX" "${MFLAGS[@]}" -I"$GEN" -I"$HARNESS/cpp" -MD -MF "$OUT/obj/merge.d" -c "$GEN/merge.cpp" \
    -o "$OUT/obj/merge.o" > "$OUT/compile.log" 2>&1 || { cat "$OUT/compile.log" >&2; exit 1; }
  sed -e 's/\\$//' -e 's/^[^:]*: *//' "$OUT/obj/merge.d" | tr ' ' '\n' | sed '/^$/d' | sort -u |
    while IFS= read -r f; do realpath "$f"; done | sort -u > "$OUT/deps.txt"
  # labels relative to the harness directory (as below), so the hash does not depend on where it is
  { while IFS= read -r f; do
      case "$f" in "$HARNESS"/*) lf="\$HARNESS/${f#"$HARNESS"/}" ;; *) lf="$f" ;; esac
      printf '%s  %s\n' "$(shasum -a 256 "$f" | cut -d' ' -f1)" "$lf"; done < "$OUT/deps.txt"
    echo "flags: ${MFLAGS[*]}"; echo "compiler: $("$CXX" --version | head -1)"; } > "$OUT/code_inputs.txt"
  H="$(shasum -a 256 "$OUT/code_inputs.txt" | cut -d' ' -f1)"
  printf 'HARNESS=%s\n' "$HARNESS" > "$OUT/roots.env"
  printf 'extern const char harness_code_hash[] = "%s";\nextern const char harness_build_flags[] = "%s";\nextern const char harness_compiler[] = "%s";\n' \
    "$H" "${MFLAGS[*]}" "$("$CXX" --version | head -1)" > "$OUT/codehash.cpp"
  "$CXX" -c "$OUT/codehash.cpp" -o "$OUT/obj/codehash.o"
  "$CXX" "$OUT/obj/merge.o" "$OUT/obj/codehash.o" -o "$OUT/$NAME"
  echo "built $OUT/$NAME (merge node)"; echo "  code hash: $H"
  exit 0
fi
# 1b. a module whose sources include files PX4's build generates (mavlink's C headers, the version
# header) has px4/modules/NAME/generate.sh, which runs PX4's own generators into build/gen/NAME
if [ -x "$MOD/generate.sh" ]; then
  env HARNESS="$HARNESS" PX4_ROOT="$PX4_ROOT" GEN="$GEN" PY="$HARNESS/build/px4venv/bin/python" \
    "$MOD/generate.sh" > "$GEN/generate.log" 2>&1 || { echo "px4_build.sh: $MOD/generate.sh failed (see $GEN/generate.log)" >&2; exit 1; }
fi
# 2. records, from Lean
(cd "$HARNESS" && LEAN_NUM_THREADS=1 lake build > /dev/null)
rm -rf "$OUT"
mkdir -p "$OUT/obj" "$GEN"
(cd "$HARNESS" && "$HARNESS_BIN" gen "$NAME" > /dev/null)

# The flags: binary32 arithmetic as written (as ardupilot/build.sh: no FMA contraction, no fast-math),
# and PX4's own for its posix SITL build (cmake/px4_add_common_flags.cmake,
# platforms/posix/cmake/px4_impl_os.cmake, boards/px4/sitl: C++14, lockstep, macOS host).
FLAGS=(-std=gnu++14 -O2 -ffp-contract=off -fno-fast-math
       -fno-common -fno-math-errno -fno-strict-aliasing -fvisibility=hidden -include visibility.h
       -Wno-c99-designator -Wno-unknown-warning-option -Wno-unused-const-variable -Wno-varargs
       -Wno-vla-cxx-extension -Wno-missing-field-initializers
       -D__PX4_POSIX -D__PX4_DARWIN "-Dnoreturn_function=__attribute__((noreturn))"
       -DCONFIG_ARCH_BOARD_PX4_SITL -D__CUSTOM_FILE_IO__ -D__STDC_FORMAT_MACROS
       -DENABLE_LOCKSTEP_SCHEDULER)
# C sources (PX4 builds C as C11): the same flags with the C standard
CFLAGS=(-std=gnu11 "${FLAGS[@]:1}")
INCLUDES=(-I"$GEN" -I"$PXGEN" -I"$HARNESS/cpp" -I"$SHIM"
          -I"$PX4_ROOT/platforms/posix/src/px4/generic/generic/include"
          -I"$PX4_ROOT/platforms/posix/src/px4/common/include" -I"$PX4_ROOT/platforms/posix/include"
          -I"$PX4_ROOT/platforms/common" -I"$PX4_ROOT/platforms/common/include"
          -I"$PX4_ROOT/src" -I"$PX4_ROOT/src/include" -I"$PX4_ROOT/src/lib" -I"$PX4_ROOT/src/lib/matrix"
          -I"$PX4_ROOT/src/modules" -I"$PX4_ROOT/boards/px4/sitl/src")
LINK_FLAGS=(-Wl,-dead_strip)

MAIN=""
SOURCES=()
DEFINES=()
while IFS= read -r line; do
  line="${line%%#*}"
  set -- $line
  [ $# -ge 2 ] || continue
  case "$1" in
    main) MAIN="$2" ;;
    source) shift; for s in "$@"; do
              case "$s" in
                GEN/*) SOURCES+=("$GEN/${s#GEN/}") ;;   # a source PX4's build generates (generate.sh)
                *) SOURCES+=("$PX4_ROOT/$s") ;;
              esac; done ;;
    define) shift; for s in "$@"; do DEFINES+=("-D$s"); done ;;   # what PX4's CMake defines
    gensource) shift; for s in "$@"; do SOURCES+=("$GEN/$s"); done ;;   # made by a pygen line
    include) shift; for s in "$@"; do
               case "$s" in
                 GEN/*) INCLUDES+=(-I"$GEN/${s#GEN/}") ;;   # a directory of generated headers
                 *) INCLUDES+=(-I"$PX4_ROOT/$s") ;;
               esac; done ;;
  esac
done < "$MOD/px4.txt"
if [ ${#DEFINES[@]} -gt 0 ]; then FLAGS+=("${DEFINES[@]}"); CFLAGS+=("${DEFINES[@]}"); fi
# PX4's framework, real: the uORB client classes, the work-item classes, ModuleBase's mutex and
# usage printing, perf counters, events and mavlink_log (both publish on the bus)
FRAMEWORK=(platforms/common/uORB/Subscription.cpp platforms/common/uORB/SubscriptionInterval.cpp
           platforms/common/px4_work_queue/WorkItem.cpp platforms/common/px4_work_queue/ScheduledWorkItem.cpp
           platforms/common/module.cpp src/lib/perf/perf_counter.cpp src/lib/events/events.cpp
           src/lib/systemlib/mavlink_log.cpp platforms/common/work_queue/queue.c platforms/common/px4_getopt.c)
for s in "${FRAMEWORK[@]}"; do SOURCES+=("$PX4_ROOT/$s"); done
SOURCES+=("$PXGEN/topics_all.cpp" "$GEN/px4_ports.cpp" "$SHIM/bus.cpp" "$SHIM/sched.cpp"
          "$SHIM/tasks.cpp" "$SHIM/platform.cpp" "$SHIM/params.cpp" "$SHIM/log.cpp" "$SHIM/adapter.cpp")
# the byte-stream devices only for a module that has one (they define open/read/write/poll)
if grep -q '^stream ' "$MOD/px4.txt"; then SOURCES+=("$SHIM/stream.cpp"); fi

# compiled JOBS at a time (default 4); compiler messages go to build/modules/NAME/compile.log
JOBS="${JOBS:-4}"
OBJS=()
i=0
: > "$OUT/compile.log"
for src in "${SOURCES[@]}"; do
  while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do sleep 0.05; done
  i=$((i + 1))
  base="$i-$(basename "$src" .cpp)"
  obj="$OUT/obj/$base.o"
  mname="$MAIN"
  case "$src" in
    *.c) (cd "$OUT/obj" && "$CC" "${CFLAGS[@]}" "-DMODULE_NAME=\"$mname\"" "${INCLUDES[@]}" \
            -MD -MF "$OUT/obj/$base.d" -c "$src" -o "$obj" > "$OUT/obj/$base.log" 2>&1 ||
            { echo "FAILED: $src" >> "$OUT/obj/$base.log"; exit 1; }) & ;;
    *) (cd "$OUT/obj" && "$CXX" "${FLAGS[@]}" "-DMODULE_NAME=\"$mname\"" "${INCLUDES[@]}" \
            -MD -MF "$OUT/obj/$base.d" -c "$src" -o "$obj" > "$OUT/obj/$base.log" 2>&1 ||
            { echo "FAILED: $src" >> "$OUT/obj/$base.log"; exit 1; }) & ;;
  esac
  OBJS+=("$obj")
done
FAIL=0
for pid in $(jobs -rp); do wait "$pid" || FAIL=1; done
wait || true
cat "$OUT"/obj/*.log > "$OUT/compile.log" 2>/dev/null || true
for o in "${OBJS[@]}"; do [ -f "$o" ] || FAIL=1; done
if [ "$FAIL" != 0 ]; then
  grep -h -B2 -A8 "error:" "$OUT/compile.log" | head -80 >&2
  echo "px4_build.sh: compile failed (all messages in $OUT/compile.log)" >&2
  exit 1
fi

# 4. the code hash: every file named in the dependency files
label() {
  local p="$1"
  case "$p" in
    "$PX4_ROOT"/*) echo "\$PX4_ROOT/${p#"$PX4_ROOT"/}" ;;
    "$HARNESS"/*) echo "\$HARNESS/${p#"$HARNESS"/}" ;;
    *) echo "$p" ;;
  esac
}
DEPS="$OUT/deps.txt"
cat "$OUT"/obj/*.d | sed -e 's/\\$//' -e 's/^[^:]*: *//' | tr ' ' '\n' | sed '/^$/d' | sort -u |
  while IFS= read -r f; do realpath "$f"; done | sort -u > "$DEPS"
COMPILER="$("$CXX" --version | head -1); $("$CC" --version | head -1)"
ALLFLAGS="${FLAGS[*]} -DMODULE_NAME=\"$MAIN\" (C: ${CFLAGS[*]})"
{
  while IFS= read -r f; do
    printf '%s  %s\n' "$(shasum -a 256 "$f" | cut -d' ' -f1)" "$(label "$f")"
  done < "$DEPS" | LC_ALL=C sort -k2
  echo "flags: $ALLFLAGS"
  echo "link: ${LINK_FLAGS[*]}"
  echo "compiler: $COMPILER"
} > "$OUT/code_inputs.txt"
CODE_HASH="$(shasum -a 256 "$OUT/code_inputs.txt" | cut -d' ' -f1)"
printf 'PX4_ROOT=%s\nHARNESS=%s\n' "$PX4_ROOT" "$HARNESS" > "$OUT/roots.env"
ESC_FLAGS="${ALLFLAGS//\\/\\\\}"; ESC_FLAGS="${ESC_FLAGS//\"/\\\"}"
cat > "$OUT/codehash.cpp" <<EOT
// written by px4/build.sh; not part of the code hash (it holds it)
extern const char harness_code_hash[] = "$CODE_HASH";
extern const char harness_build_flags[] = "$ESC_FLAGS";
extern const char harness_compiler[] = "$COMPILER";
EOT
"$CXX" -c "$OUT/codehash.cpp" -o "$OUT/obj/codehash.o"

# 5. link
"$CXX" "${LINK_FLAGS[@]}" "${OBJS[@]}" "$OUT/obj/codehash.o" -o "$OUT/$NAME"
NPX4=$(grep -c '  \$PX4_ROOT/' "$OUT/code_inputs.txt" || true)
echo "built $OUT/$NAME"
echo "  sources: ${#SOURCES[@]} compiled, $(wc -l < "$DEPS" | tr -d ' ') files read by the compiler ($NPX4 under \$PX4_ROOT)"
echo "  code hash: $CODE_HASH"
