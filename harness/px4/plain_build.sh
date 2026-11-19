#!/usr/bin/env bash
# Build a module that is only its adapter (no flight-stack sources), e.g. a bridge:
# px4/plain_build.sh NAME (px4/build.sh NAME calls it for a module with no px4.txt).
# px4/modules/NAME/adapter.cpp on cpp/module_protocol.h (and px4/px4_test_drive.h), compiled with the
# project's floating-point flags (as ardupilot/build.sh: no FMA contraction, no fast-math), code hash
# in the same format (every file the compiler read, the flags, the compiler).
set -euo pipefail
NAME="${1:?usage: px4/plain_build.sh NAME}"
HARNESS="$(cd "$(dirname "$0")/.." && pwd)"
CXX="${CXX:-clang++}"
OUT="$HARNESS/build/modules/$NAME"
GEN="$HARNESS/build/gen/$NAME"
(cd "$HARNESS" && LEAN_NUM_THREADS=1 lake build > /dev/null)
rm -rf "$OUT"; mkdir -p "$OUT/obj" "$GEN"
(cd "$HARNESS" && .lake/build/bin/harness gen "$NAME" > /dev/null)
FLAGS=(-std=gnu++14 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math -fno-exceptions)
"$CXX" "${FLAGS[@]}" -I"$GEN" -I"$HARNESS/cpp" -I"$HARNESS/px4" -MD -MF "$OUT/obj/adapter.d" \
  -c "$HARNESS/px4/modules/$NAME/adapter.cpp" -o "$OUT/obj/adapter.o"
COMPILER="$("$CXX" --version | head -1)"
{
  sed -e 's/\\$//' -e 's/^[^:]*: *//' "$OUT/obj/adapter.d" | tr ' ' '\n' | sed '/^$/d' |
    while IFS= read -r f; do realpath "$f"; done | sort -u |
    while IFS= read -r f; do
      case "$f" in "$HARNESS"/*) l="\$HARNESS/${f#"$HARNESS"/}" ;; *) l="$f" ;; esac
      printf '%s  %s\n' "$(shasum -a 256 "$f" | cut -d' ' -f1)" "$l"
    done | LC_ALL=C sort -k2
  echo "flags: ${FLAGS[*]}"
  echo "link: "
  echo "compiler: $COMPILER"
} > "$OUT/code_inputs.txt"
CODE_HASH="$(shasum -a 256 "$OUT/code_inputs.txt" | cut -d' ' -f1)"
printf 'HARNESS=%s\n' "$HARNESS" > "$OUT/roots.env"
cat > "$OUT/codehash.cpp" <<EOT
extern const char harness_code_hash[] = "$CODE_HASH";
extern const char harness_build_flags[] = "${FLAGS[*]}";
extern const char harness_compiler[] = "$COMPILER";
EOT
"$CXX" -c "$OUT/codehash.cpp" -o "$OUT/obj/codehash.o"
"$CXX" "$OUT/obj/adapter.o" "$OUT/obj/codehash.o" -o "$OUT/$NAME"
echo "built $OUT/$NAME"; echo "  code hash: $CODE_HASH"
