#!/usr/bin/env bash
# Compile musl's math sources (libm/musl-1.2.5/src/math, the files listed in libm/musl_files.txt)
# for the C++ reference: each file as its own translation unit, as musl's build compiles it, with the
# reference's code-generation flags and the environment headers of libm/env, every external name
# prefixed cpp2lean_musl_ (libm/env/musl_prefix.h). Output: build/libm/*.o and build/libm/link.args, the
# objects and the linker options (-Wl,-alias) that bind the C names the reference calls (sinf, ...) to
# them, so that the reference calls no function of the platform's libm.
# Usage: libm/build_musl.sh   (prints the path of link.args)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
M="$HERE/musl-1.2.5"
OUT="$ROOT/build/libm"
mkdir -p "$OUT"
CC="${CC:-clang}"
# the reference's flags (cpp2lean/README.md, "Compilation assumptions"), as C99
FLAGS=(-x c -std=c99 -O2 -ffp-contract=off -fno-fast-math -fno-builtin -Wno-unknown-pragmas
       -I "$HERE/env" -I "$M/src/internal" -I "$M/src/math" -include "$HERE/env/musl_prefix.h")
ARGS=()
while read -r f; do
  [ -z "$f" ] && continue
  o="$OUT/$f.o"
  if [ ! -f "$o" ] || [ "$M/src/math/$f.c" -nt "$o" ] || [ "$HERE/env/musl_prefix.h" -nt "$o" ] || [ "$0" -nt "$o" ]; then
    "$CC" "${FLAGS[@]}" -c "$M/src/math/$f.c" -o "$o"
  fi
  ARGS+=("$o")
done < "$HERE/musl_files.txt"
while read -r n; do
  [ -z "$n" ] && continue
  ARGS+=("-Wl,-alias,_cpp2lean_musl_$n,_$n")
done < "$HERE/env/musl_names.txt"
printf '%s\n' "${ARGS[@]}" > "$OUT/link.args"
echo "$OUT/link.args"
