#!/usr/bin/env bash
# Prepare the build copy of ArduPilot for the reference vehicle (REFERENCE.md):
#   build/reference/ap   an APFS clone (cp -c) of build/survey/ap-min (the pinned checkout 802db19de1
#                        with its submodules), restored to the commit and then patched with
#                        reference/patches/*.patch; the ArduPilot checkout itself is never touched
#   build/reference/ap/build/sitl
#                        waf's SITL configuration with reference/cfg/ref.hwdef, built once
#                        (generated MAVLink headers, ap_config.h, compile_commands.json)
# Usage: reference/prepare.sh   (idempotent: skips the clone and the waf build when present)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
SRC="$ROOT/build/survey/ap-min"
AP="$ROOT/build/reference/ap"
PY="${WAF_PYTHON:-$ROOT/build/survey/venv/bin/python}"
if [ ! -d "$AP/.git" ]; then
  mkdir -p "$ROOT/build/reference"
  rm -rf "$AP.tmp"; mkdir -p "$AP.tmp"
  for e in "$SRC"/* "$SRC"/.git "$SRC"/.gitmodules; do
    [ "$(basename "$e")" = build ] && continue
    cp -cR "$e" "$AP.tmp/"
  done
  mv "$AP.tmp" "$AP"
  (cd "$AP" && git checkout -q -- . && test "$(git rev-parse --short=10 HEAD)" = 802db19de1)
  for p in "$HERE"/patches/*.patch; do (cd "$AP" && git apply "$p"); done
fi
if [ ! -f "$AP/build/sitl/compile_commands.json" ] || [ "$HERE/cfg/ref.hwdef" -nt "$AP/build/sitl/compile_commands.json" ]; then
  cd "$AP"
  "$PY" ./waf configure --board sitl --no-submodule-update --disable-networking \
      --extra-hwdef="$HERE/cfg/ref.hwdef" > "$ROOT/build/reference/configure.log" 2>&1
  nice -n 15 "$PY" ./waf copter -j"${JOBS:-4}" > "$ROOT/build/reference/waf_build.log" 2>&1
fi
echo "$AP"
