#!/usr/bin/env bash
# Fails if a file that git would commit contains identifying information:
# account names, personal names, e-mail domains, or absolute local paths.
# Usage: tools/check_anonymous.sh [extra-pattern ...]
set -euo pipefail
cd "$(dirname "$0")/.."
pattern='/Users/|/private/tmp|/home/[a-z]|C:\\\\Users'
for extra in "$@"; do pattern="$pattern|$extra"; done
hits=$(git ls-files -co --exclude-standard -z -- . ':!tools/check_anonymous.sh' | xargs -0 grep -InE "$pattern" 2>/dev/null || true)
if [ -n "$hits" ]; then
  echo "$hits" | cut -c1-200
  echo "check_anonymous: $(echo "$hits" | wc -l | tr -d ' ') line(s) with identifying information" >&2
  exit 1
fi
echo "check_anonymous: clean"
