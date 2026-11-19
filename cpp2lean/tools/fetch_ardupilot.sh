#!/usr/bin/env bash
# Put ArduPilot at the pinned commit into cpp2lean/deps/ardupilot (git-ignored). Nothing in it is modified.
# Usage: tools/fetch_ardupilot.sh
# Environment: ARDUPILOT_LOCAL  an existing clean ArduPilot clone at the pinned commit; if set, deps/ardupilot
#                               becomes a symbolic link to it and nothing is downloaded.
set -euo pipefail
REV=802db19de135d4275f227b0cd5081d013de6eafc
URL=https://github.com/ArduPilot/ardupilot.git
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DEST="$ROOT/deps/ardupilot"
mkdir -p "$ROOT/deps"

if [ -n "${ARDUPILOT_LOCAL:-}" ]; then
  have=$(git -C "$ARDUPILOT_LOCAL" rev-parse HEAD)
  [ "$have" = "$REV" ] || { echo "ARDUPILOT_LOCAL is at $have, want $REV" >&2; exit 1; }
  [ -z "$(git -C "$ARDUPILOT_LOCAL" status --porcelain --untracked-files=no)" ] || { echo "ARDUPILOT_LOCAL has local changes" >&2; exit 1; }
  rm -f "$DEST"
  ln -s "$(cd "$ARDUPILOT_LOCAL" && pwd)" "$DEST"
  echo "deps/ardupilot -> ARDUPILOT_LOCAL ($REV)"
  exit 0
fi

if [ ! -d "$DEST/.git" ]; then
  git init -q "$DEST"
  git -C "$DEST" remote add origin "$URL"
fi
if [ "$(git -C "$DEST" rev-parse HEAD 2>/dev/null)" != "$REV" ]; then
  git -C "$DEST" fetch -q --depth 1 origin "$REV"
  git -C "$DEST" checkout -q --detach FETCH_HEAD
fi
echo "deps/ardupilot at $(git -C "$DEST" rev-parse HEAD)"
