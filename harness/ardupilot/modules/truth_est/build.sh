#!/usr/bin/env bash
# Build the truth_est fixture: records from Lean, a launcher, the code hash of adapter + protocol
# + schema (ardupilot/modules/truth_est/build.sh). The launcher writes no bytecode (no __pycache__ in py/).
set -euo pipefail
HARNESS="$(cd "$(dirname "$0")/../../.." && pwd -P)"
OUT="$HARNESS/build/modules/truth_est"
mkdir -p "$OUT"
(cd "$HARNESS" && .lake/build/bin/harness gen truth_est > /dev/null)
{
  for f in "$HARNESS/ardupilot/modules/truth_est/adapter.py" "$HARNESS/py/module_protocol.py" \
           "$HARNESS/build/gen/truth_est/module_schema.json"; do
    printf '%s  %s\n' "$(shasum -a 256 "$f" | cut -d' ' -f1)" "${f#"$HARNESS"/}"
  done
  echo "interpreter: $(python3 --version)"
} > "$OUT/code_inputs.txt"
H="$(shasum -a 256 "$OUT/code_inputs.txt" | cut -d' ' -f1)"
printf '#!/bin/sh\nexec /usr/bin/env TRUTH_EST_HASH=%s python3 -I -B %q "$@"\n' "$H" \
  "$HARNESS/ardupilot/modules/truth_est/adapter.py" > "$OUT/truth_est"
chmod +x "$OUT/truth_est"
echo "built $OUT/truth_est (code hash $H)"
