#!/usr/bin/env bash
# Fetch the third-party sources the harness builds read, at pinned commits, into harness/deps/
# (git-ignored, never modified by any build script):
#
#   deps/ardupilot   ArduPilot      802db19de135d4275f227b0cd5081d013de6eafc  (no submodule is compiled;
#                                   ardupilot/gen_mavlink.sh reads the modules/mavlink pin from git)
#   deps/px4         PX4 v1.17.0    d6f12ad1c4f70ad3230afd7d86e971421e02fef4  (with src/lib/events/libevents)
#   deps/mavlink     ArduPilot's mavlink e03dad40efb3a4009ad6d78de5e55997139ac2f3 (with pymavlink)
#
# Usage: tools/fetch_deps.sh
# To reuse clones you already have (read only; nothing is written into them), set any of
#   ARDUPILOT_SRC, PX4_SRC, MAVLINK_SRC
# to a local checkout at the pinned commit; deps/NAME then becomes a symbolic link to it.
set -euo pipefail
HARNESS="$(cd "$(dirname "$0")/.." && pwd)"
DEPS="$HARNESS/deps"
mkdir -p "$DEPS"

# fetch NAME URL COMMIT LOCAL SUBMODULE...
fetch() {
  local name="$1" url="$2" commit="$3" local_src="$4"; shift 4
  local dst="$DEPS/$name"
  if [ -n "$local_src" ]; then
    local have
    have="$(git -C "$local_src" rev-parse HEAD)"
    [ "$have" = "$commit" ] || { echo "fetch_deps.sh: $local_src is at $have, need $commit" >&2; exit 1; }
    if [ -L "$dst" ] || [ ! -e "$dst" ]; then
      ln -sfn "$(cd "$local_src" && pwd -P)" "$dst"
    else
      echo "fetch_deps.sh: $dst exists and is not a link; remove it to use $local_src" >&2; exit 1
    fi
    echo "$name: link to a local checkout at $commit"
    return
  fi
  if [ ! -d "$dst/.git" ] && [ ! -f "$dst/.git" ]; then
    git clone -q --no-checkout "$url" "$dst"
  fi
  git -C "$dst" fetch -q origin "$commit" 2>/dev/null || true
  git -C "$dst" checkout -q "$commit"
  for sm in "$@"; do git -C "$dst" submodule update -q --init "$sm"; done
  [ "$(git -C "$dst" rev-parse HEAD)" = "$commit" ] || { echo "fetch_deps.sh: $dst not at $commit" >&2; exit 1; }
  echo "$name: $commit"
}

fetch ardupilot https://github.com/ArduPilot/ardupilot.git \
  802db19de135d4275f227b0cd5081d013de6eafc "${ARDUPILOT_SRC:-}"
fetch px4 https://github.com/PX4/PX4-Autopilot.git \
  d6f12ad1c4f70ad3230afd7d86e971421e02fef4 "${PX4_SRC:-}" src/lib/events/libevents
fetch mavlink https://github.com/ArduPilot/mavlink.git \
  e03dad40efb3a4009ad6d78de5e55997139ac2f3 "${MAVLINK_SRC:-}" pymavlink
