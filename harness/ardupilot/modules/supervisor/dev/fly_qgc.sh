#!/usr/bin/env bash
# The QGroundControl launcher lives at the stack level: ardupilot/fly_qgc.sh [PORT]. Kept here so
# that the supervisor's notes that name dev/fly_qgc.sh still work.
exec "$(cd "$(dirname "$0")/../../.." && pwd)/fly_qgc.sh" "$@"
