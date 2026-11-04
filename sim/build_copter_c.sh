#!/usr/bin/env bash
# Build a standalone binary of the Lean ArduCopter port (`copter`, root module Copter.Main) from the C
# code that the Lean compiler emits; the counterpart of build_c.sh for the `flight` executable.
#
# Lake writes one C file per Lean module to .lake/build/ir/<A>/<B>.c (module A.B) in the package
# root (and to .lake/packages/<dep>/.lake/build/ir/ for modules of dependencies). This script
# collects the import closure of Copter.Main from the `import` lines of the sources (core modules
# Init, Std and Lean are left out: their code is in the toolchain's static archives), copies those C
# files into sim/build/copter-c/ (so the exact C that was compiled stays next to the binary), compiles
# each one with the toolchain's `leanc` (the clang shipped with Lean plus the Lean include path and
# -ffp-contract=off, so no fused multiply-adds change floating-point results), and links them against
# the static Lean runtime archives. The result, sim/build/copter-c, needs neither Lean nor lake at run
# time.
#
# Usage: sim/build_copter_c.sh     (from anywhere; paths are resolved relative to this script)
set -euo pipefail

SIM="$(cd "$(dirname "$0")" && pwd)"
PKG="$(cd "$SIM/.." && pwd)"
OUT="$SIM/build"
CDIR="$OUT/copter-c.d"
ROOT="Copter.Main"

# Step 1: build the Lean executable target, which makes lake (re)generate the C files.
(cd "$PKG" && lake build copter)

# Step 2: locate the toolchain's leanc via lake, so the toolchain pinned by lean-toolchain is used.
LEANC="$(cd "$PKG" && lake env which leanc)"
SYSROOT="$(cd "$PKG" && lake env printenv LEAN_SYSROOT)"
echo "leanc: $LEANC"
echo "LEAN_SYSROOT: $SYSROOT"

# Step 3: the import closure of Copter.Main. A module A.B has its source at A/B.lean in the package
# root or in a dependency under .lake/packages/*/, and its C file at .lake/build/ir/A/B.c next to it.
src_of() {  # module -> source path (empty if not found)
  local rel="${1//.//}.lean"
  for base in "$PKG" "$PKG"/.lake/packages/*; do
    if [ -f "$base/$rel" ]; then echo "$base/$rel"; return; fi
  done
}
c_of() {    # module -> emitted C path (empty if not found)
  local rel="${1//.//}.c"
  for base in "$PKG" "$PKG"/.lake/packages/*; do
    if [ -f "$base/.lake/build/ir/$rel" ]; then echo "$base/.lake/build/ir/$rel"; return; fi
  done
}
imports_of() {  # source path -> imported modules (handles `public`/`meta`/`private` and `import all`)
  sed -nE 's/^[[:space:]]*((public|private|meta)[[:space:]]+)*import[[:space:]]+(all[[:space:]]+)?([A-Za-z0-9_.«»]+).*/\4/p' "$1"
}
CLOSURE=()
SEEN=" "      # space-separated visited modules (bash 3.2, the macOS /bin/bash, has no associative arrays)
visit() {
  local m="$1"
  case "$SEEN" in *" $m "*) return ;; esac
  SEEN="$SEEN$m "
  case "$m" in Init|Init.*|Std|Std.*|Lean|Lean.*) return ;; esac
  local src; src="$(src_of "$m")"
  if [ -z "$src" ]; then echo "no source for module $m" >&2; exit 1; fi
  local dep
  for dep in $(imports_of "$src"); do visit "$dep"; done
  CLOSURE+=("$m")   # post-order: dependencies first
}
visit "$ROOT"
echo "import closure of $ROOT: ${#CLOSURE[@]} modules"

rm -rf "$CDIR"; mkdir -p "$CDIR"
for m in "${CLOSURE[@]}"; do
  c="$(c_of "$m")"
  if [ -z "$c" ]; then echo "no C file for module $m (did lake build it?)" >&2; exit 1; fi
  cp "$c" "$CDIR/${m//./_}.c"
  echo "  $m"
done

# Step 4: compile each emitted C file to an object file. -O3 -DNDEBUG matches what lake uses;
# leanc adds -I<sysroot>/include and -ffp-contract=off itself.
for m in "${CLOSURE[@]}"; do
  "$LEANC" -c -O3 -DNDEBUG -o "$CDIR/${m//./_}.o" "$CDIR/${m//./_}.c"
done

# Step 5: link. leanc's default link line (see `leanc --print-ldflags`) adds the static archives of
# the Lean runtime and core library (libleanrt.a, libInit.a, ...); only macOS system libraries remain
# dynamic.
"$LEANC" -O3 -o "$OUT/copter-c" "$CDIR"/*.o

# Step 6: show what the binary links dynamically (expected: libc++ and libSystem only).
otool -L "$OUT/copter-c"
ls -l "$OUT/copter-c"
