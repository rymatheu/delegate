#!/usr/bin/env bash
# The ArduLean code is frozen (Corpus/PLAN.md, rule 1): the files of the import closure of ArduLean.Vehicle and
# ArduLean.Estimator (the translated modules and the modules they import: ArduLean/Vehicle, ArduLean/Estimator,
# ArduLean/Musl, ArduLean/Runtime) must hash to the values recorded in Corpus/CODE.sha256.
#
#   tests/check_code_frozen.sh            verify: every recorded file has its recorded hash, and the closure has no
#                                         file the record lacks; exit 1 otherwise
#   tests/check_code_frozen.sh --record   (once, when the code is frozen) write CODE.sha256 from the current files
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
root="$here"
rec="$root/Corpus/CODE.sha256"

# the import closure of the two roots, as paths relative to the repository root (imports that are not files of this
# project, such as FloatLib and Mathlib, are outside the code and are pinned by lake-manifest.json instead)
closure() {
  local todo=("ArduLean.Vehicle" "ArduLean.Estimator") seen="" m f
  while ((${#todo[@]})); do
    m="${todo[0]}"; todo=("${todo[@]:1}")
    case " $seen " in *" $m "*) continue;; esac
    seen="$seen $m"
    f="$root/${m//.//}.lean"
    [[ -f "$f" ]] || continue
    echo "${m//.//}.lean"
    while read -r imp; do todo+=("$imp"); done < <(sed -n 's/^import[[:space:]]\{1,\}\([A-Za-z0-9_.]*\).*/\1/p' "$f")
  done | LC_ALL=C sort -u
}

hashes() { (cd "$root" && shasum -a 256 "$@"); }

if [[ "${1:-}" == "--record" ]]; then
  [[ -e "$rec" ]] && { echo "refusing: $rec exists (the code was frozen already)"; exit 1; }
  files=(); while read -r f; do files+=("$f"); done < <(closure)
  hashes "${files[@]}" > "$rec"
  echo "recorded ${#files[@]} files in $rec"
  exit 0
fi

[[ -f "$rec" ]] || { echo "FAIL: no $rec (run with --record once, when the code is frozen)"; exit 1; }
status=0
if ! out=$(cd "$root" && shasum -a 256 -c "$rec" 2>&1); then
  echo "$out" | grep -v ': OK$' || true
  status=1
fi
missing=$(comm -13 <(awk '{print $2}' "$rec" | LC_ALL=C sort -u) <(closure))
if [[ -n "$missing" ]]; then
  echo "FAIL: files in the import closure that CODE.sha256 does not record:"; echo "$missing"; status=1
fi
n=$(wc -l < "$rec" | tr -d ' ')
if ((status == 0)); then echo "OK: $n code files match Corpus/CODE.sha256"; else echo "FAIL: the code changed"; fi
exit $status
