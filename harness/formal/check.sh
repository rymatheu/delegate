#!/usr/bin/env bash
# Check formal/PlantHarness.lean against the plant's built oleans, without building either
# project. Overridable: HARNESS_DIR, ARDULEAN_DIR, OUT (build products; default a fresh temp
# dir), REQUIRE_FRESH=1 (fail if `lake build Plant --no-build` says the oleans are stale).
set -euo pipefail

HARNESS_DIR="${HARNESS_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
ARDULEAN_DIR="${ARDULEAN_DIR:-$HARNESS_DIR/../ardulean}"   # the plant library (Lean), a sibling subproject
OUT="${OUT:-$(mktemp -d)}"
REQUIRE_FRESH="${REQUIRE_FRESH:-0}"
export LEAN_NUM_THREADS=1
mkdir -p "$OUT/Harness"
echo "output dir: $OUT"

# 1. Are the plant's oleans current? (`--no-build` builds nothing.)
if (cd "$ARDULEAN_DIR" && lake build Plant --no-build >/dev/null 2>&1); then
  echo "plant oleans: current"
else
  echo "plant oleans: lake reports out of date (the check below uses the oleans as they are)"
  if [ "$REQUIRE_FRESH" = 1 ]; then exit 1; fi
fi

# 2. The algebra, core Lean, into OUT (elan picks HARNESS_DIR's toolchain, v4.35.0).
(cd "$HARNESS_DIR" && lean --version && lean -o "$OUT/Harness/Algebra.olean" \
  -i "$OUT/Harness/Algebra.ilean" Harness/Algebra.lean)
echo "Harness/Algebra.lean: ok"

# 3. The plant harness, against the plant's oleans and the algebra in OUT.
PLANT_PATH="$(cd "$ARDULEAN_DIR" && lake env printenv LEAN_PATH)"
export LEAN_PATH="$PLANT_PATH:$OUT"
(cd "$ARDULEAN_DIR" && lean -R "$HARNESS_DIR/formal" -o "$OUT/PlantHarness.olean" \
  -i "$OUT/PlantHarness.ilean" \
  "$HARNESS_DIR/formal/PlantHarness.lean")
echo "formal/PlantHarness.lean: ok"

# 4. No forbidden token in the source; axioms of the main theorems.
if grep -nE '\bsorry\b|^[[:space:]]*axiom[[:space:]]|native_decide' \
    "$HARNESS_DIR/formal/PlantHarness.lean"; then
  echo "forbidden token found"
  exit 1
fi
cat > "$OUT/PlantHarnessAxioms.lean" <<'LEAN'
import PlantHarness
open Harness.Algebra Harness.Formal
#print axioms Ev.ofProof_supported
#print axioms Ev.ofProof_faithful
#print axioms plant_implements
#print axioms plantHarness_valid
#print axioms plantHarness_backed
#print axioms plantHarness_backed_empty
#print axioms plantHarness_faithful
#print axioms closeLoop
#print axioms closeLoop_contract
#print axioms closeLoop_impl
#print axioms closeLoop_backed
#print axioms closeLoop_faithful
#print axioms closeLoop_valid
LEAN
AX="$(cd "$ARDULEAN_DIR" && lean "$OUT/PlantHarnessAxioms.lean")"
echo "$AX"
if echo "$AX" | grep -q sorryAx; then
  echo "sorryAx found"
  exit 1
fi
echo "check: ok"
