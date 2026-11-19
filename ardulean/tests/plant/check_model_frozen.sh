#!/usr/bin/env bash
# The plant model is frozen (Plant/PLAN.md, rule 2): the files Plant/Model/*.lean must hash to the values recorded in
# Plant/MODEL.sha256. A change to the model is a separate, announced step: re-record only then.
#
#   tests/plant/check_model_frozen.sh            verify: every recorded file has its recorded hash, and Plant/Model has no
#                                          file the record lacks; exit 1 otherwise
#   tests/plant/check_model_frozen.sh --record   (once, when the model is frozen) write MODEL.sha256 from the current files
set -euo pipefail
here="$(cd "$(dirname "$0")/../.." && pwd)"
rec="$here/Plant/MODEL.sha256"

files() { (cd "$here" && ls Plant/Model/*.lean | LC_ALL=C sort -u); }

if [[ "${1:-}" == "--record" ]]; then
  [[ -e "$rec" ]] && { echo "refusing: $rec exists (the model was frozen already)"; exit 1; }
  (cd "$here" && shasum -a 256 $(files)) > "$rec"
  echo "recorded $(wc -l < "$rec" | tr -d ' ') files in $rec"
  exit 0
fi

[[ -f "$rec" ]] || { echo "FAIL: no $rec (run with --record once, when the model is frozen)"; exit 1; }
status=0
if ! out=$(cd "$here" && shasum -a 256 -c "$rec" 2>&1); then
  echo "$out" | grep -v ': OK$' || true
  status=1
fi
missing=$(comm -13 <(awk '{print $2}' "$rec" | LC_ALL=C sort -u) <(files))
if [[ -n "$missing" ]]; then
  echo "FAIL: files in Plant/Model that MODEL.sha256 does not record:"; echo "$missing"; status=1
fi
n=$(wc -l < "$rec" | tr -d ' ')
if ((status == 0)); then echo "OK: $n model files match Plant/MODEL.sha256"; else echo "FAIL: the model changed"; fi
exit $status
