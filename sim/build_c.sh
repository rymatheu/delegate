#!/usr/bin/env bash
# Build a standalone flight-controller binary from the C code that the Lean compiler emits.
#
# The Lean compiler translates every module of the executable's import closure into one C file
# (lake writes them to .lake/build/ir/Flight/*.c in the package root). This script copies those files into
# sim/build/c/, compiles each one with the toolchain's `leanc` (a wrapper around the clang shipped
# with the Lean toolchain that adds the Lean include path and the toolchain's default flags,
# among them -ffp-contract=off so no fused multiply-adds change floating-point results), and links
# them against the static Lean runtime archives. The result, sim/build/flight-c, needs neither Lean
# nor lake at run time.
#
# Usage: sim/build_c.sh            (from anywhere; paths are resolved relative to this script)
set -euo pipefail

SIM="$(cd "$(dirname "$0")" && pwd)"
PKG="$(cd "$SIM/.." && pwd)"
OUT="$SIM/build"
CDIR="$OUT/c"

# Step 1: build the Lean executable target, which makes lake (re)generate the C files.
(cd "$PKG" && lake build flight)

# Step 2: locate the toolchain's leanc via lake, so the toolchain pinned by lean-toolchain is used.
LEANC="$(cd "$PKG" && lake env which leanc)"
SYSROOT="$(cd "$PKG" && lake env printenv LEAN_SYSROOT)"
echo "leanc: $LEANC"
echo "LEAN_SYSROOT: $SYSROOT"

# Step 3: the modules in the import closure of Flight.Main, in dependency order.
MODULES="Arith Types FloatInstance Pid Navigator PositionControl AttitudeTarget AttitudeControl RateControl Mixer Controller TestPlant Main"

rm -rf "$CDIR"; mkdir -p "$CDIR"
for m in $MODULES; do
  cp "$PKG/.lake/build/ir/Flight/$m.c" "$CDIR/Flight_$m.c"
done

# Step 4: compile each emitted C file to an object file. -O3 -DNDEBUG matches what lake uses;
# leanc adds -I<sysroot>/include and -ffp-contract=off itself.
for m in $MODULES; do
  "$LEANC" -c -O3 -DNDEBUG -o "$CDIR/Flight_$m.o" "$CDIR/Flight_$m.c"
done

# Step 5: link. leanc's default link line (see `leanc --print-ldflags`) adds
# -L<sysroot>/lib/lean -lleancpp -lInit -lStd -lLean -lleanrt -lc++ ..., which are static archives
# (.a), so the Lean runtime and the core library Init are linked into the binary; -dead_strip
# removes unused code. Only macOS system libraries remain dynamic.
"$LEANC" -O3 -o "$OUT/flight-c" "$CDIR"/Flight_*.o

# Step 6: show what the binary links dynamically (expected: libc++ and libSystem only).
otool -L "$OUT/flight-c"
ls -l "$OUT/flight-c"
