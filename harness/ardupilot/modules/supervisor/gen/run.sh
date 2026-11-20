#!/usr/bin/env bash
# Regenerate gen/out (the shadow stand-ins) from the real headers and sources.
#   ardupilot/modules/supervisor/gen/run.sh       (needs build/modules/supervisor/flags.rsp: run build.sh once,
#                                        or the probe, first)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
HARNESS="$(cd "$HERE/../../../.." && pwd)"
# the interpreter: the simulator's Python (sim/setup.sh), never whatever `python3` is first on PATH
PY="${HARNESS_PYTHON:-$HARNESS/../sim/.venv/bin/python}"
[ -x "$PY" ] || { echo "$(basename "$0"): no simulator environment at $PY: run sim/setup.sh at the repository root" >&2; exit 1; }
ARDUPILOT_ROOT="${ARDUPILOT_ROOT:-$HARNESS/deps/ardupilot}"
B="$HARNESS/build/modules/supervisor"
RSP="${RSP:-$B/probe/flags.rsp}"
CLASSES="$("$PY" -I -c "
import ast,sys
src=open(sys.argv[1]).read()
t=ast.parse(src)
for n in t.body:
    if isinstance(n,ast.Assign) and getattr(n.targets[0],'id','')=='SHADOWS':
        print(' '.join(k.value for k in n.value.keys))
" "$HERE/gen_shadows.py")"
"$PY" -I "$HERE/gen_commands.py" "$HERE/../commands.txt" "$HERE/Commands.lean" "$HERE/out/cmd_emit.inc"
"$PY" -I "$HERE/ast_extract.py" "$RSP" "$ARDUPILOT_ROOT/ArduCopter" "$B/shadow_classes.json" $CLASSES
"$PY" -I "$HERE/gen_shadows.py" "$ARDUPILOT_ROOT" "$B/shadow_classes.json" "$HERE/../stand_ins" "$HERE/out"
