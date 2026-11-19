#!/usr/bin/env bash
# Regenerate gen/out (the shadow stand-ins) from the real headers and sources.
#   ardupilot/modules/supervisor/gen/run.sh       (needs build/modules/supervisor/flags.rsp: run build.sh once,
#                                        or the probe, first)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
HARNESS="$(cd "$HERE/../../../.." && pwd)"
ARDUPILOT_ROOT="${ARDUPILOT_ROOT:-$HARNESS/deps/ardupilot}"
B="$HARNESS/build/modules/supervisor"
RSP="${RSP:-$B/probe/flags.rsp}"
CLASSES="$(python3 -I -c "
import ast,sys
src=open(sys.argv[1]).read()
t=ast.parse(src)
for n in t.body:
    if isinstance(n,ast.Assign) and getattr(n.targets[0],'id','')=='SHADOWS':
        print(' '.join(k.value for k in n.value.keys))
" "$HERE/gen_shadows.py")"
python3 -I "$HERE/gen_commands.py" "$HERE/../commands.txt" "$HERE/Commands.lean" "$HERE/out/cmd_emit.inc"
python3 -I "$HERE/ast_extract.py" "$RSP" "$ARDUPILOT_ROOT/ArduCopter" "$B/shadow_classes.json" $CLASSES
python3 -I "$HERE/gen_shadows.py" "$ARDUPILOT_ROOT" "$B/shadow_classes.json" "$HERE/../stand_ins" "$HERE/out"
