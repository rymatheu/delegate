#!/usr/bin/env bash
# Write the Python ardupilotmega dialect dev/drive.py uses: build/gen/supervisor/py/apm.py, by
# pymavlink's mavgen from deps/mavlink (read only).
set -euo pipefail
HARNESS="$(cd "$(dirname "$0")/../../../.." && pwd)"
# the interpreter: the simulator's Python (sim/setup.sh), never whatever `python3` is first on PATH
PY="${HARNESS_PYTHON:-$HARNESS/../sim/.venv/bin/python}"
[ -x "$PY" ] || { echo "$(basename "$0"): no simulator environment at $PY: run sim/setup.sh at the repository root" >&2; exit 1; }
mkdir -p "$HARNESS/build/gen/supervisor/py"
cd "$HARNESS"
"$PY" -I -c "
import sys
sys.path.insert(0, 'deps/mavlink')
sys.dont_write_bytecode = True
from pymavlink.generator import mavgen
class opts:
    language = 'Python3'
    wire_protocol = '2.0'
    validate = False
    output = 'build/gen/supervisor/py/apm.py'
    strict_units = False
    error_limit = 200
    exit_code = False
mavgen.mavgen(opts(), ['deps/mavlink/message_definitions/v1.0/ardupilotmega.xml'])
" > build/gen/supervisor/py/mavgen.log
echo "wrote build/gen/supervisor/py/apm.py"
