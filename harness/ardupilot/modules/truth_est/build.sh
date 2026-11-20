#!/usr/bin/env bash
# Build the truth_est fixture: records from Lean, a launcher, the code hash of adapter + protocol
# + schema (ardupilot/modules/truth_est/build.sh). The launcher writes no bytecode (no __pycache__ in py/).
set -euo pipefail
HARNESS="$(cd "$(dirname "$0")/../../.." && pwd -P)"
OUT="$HARNESS/build/modules/truth_est"
# the interpreter: the simulator's Python (sim/setup.sh), the interpreter the launcher runs and the code hash names, never whatever `python3` is first on PATH
PY="$HARNESS/../sim/.venv/bin/python"
[ -x "$PY" ] || { echo "truth_est/build.sh: no simulator environment at $PY: run sim/setup.sh at the repository root" >&2; exit 1; }
mkdir -p "$OUT"
(cd "$HARNESS" && .lake/build/bin/harness gen truth_est > /dev/null)
{
  for f in "$HARNESS/ardupilot/modules/truth_est/adapter.py" "$HARNESS/py/module_protocol.py" \
           "$HARNESS/build/gen/truth_est/module_schema.json"; do
    printf '%s  %s\n' "$(shasum -a 256 "$f" | cut -d' ' -f1)" "${f#"$HARNESS"/}"
  done
  echo "interpreter: $("$PY" --version)"
} > "$OUT/code_inputs.txt"
H="$(shasum -a 256 "$OUT/code_inputs.txt" | cut -d' ' -f1)"
# the launcher finds the harness and the interpreter from its own place, so the build tree can be moved
printf '#!/bin/sh\nH="$(cd "$(dirname "$0")/../../.." && pwd)"\nexec /usr/bin/env TRUTH_EST_HASH=%s "$H/../sim/.venv/bin/python" -I -B "$H/ardupilot/modules/truth_est/adapter.py" "$@"\n' \
  "$H" > "$OUT/truth_est"
chmod +x "$OUT/truth_est"
echo "built $OUT/truth_est (code hash $H)"
