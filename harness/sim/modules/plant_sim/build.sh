#!/usr/bin/env bash
# Build a simulator module: sim/modules/plant_sim/build.sh [plant_sim|plant_formation]   (default plant_sim)
#
# The module is a Python program (sim/modules/plant_sim/adapter.py on py/module_protocol.py) that steps the
# repository's shared gorge simulator (sim/ at the repository root, found from this script; read only, nothing is
# written there) with its Python environment (sim/.venv, made by sim/setup.sh). plant_sim is one X500, plant_formation
# two (the same adapter with --vehicles 2). Nothing is compiled. The build:
#   1. `harness gen NAME` writes build/gen/NAME/module_schema.json from the Lean declaration (run `lake build` first);
#      the adapter reads its schemas from there and checks its own field names against them.
#   2. Writes the launcher build/modules/NAME/NAME: the interpreter with a cleared environment (PYTHONHASHSEED=0, one
#      BLAS/OpenMP thread, no bytecode written, no user site, no script directory on sys.path).
#   3. Runs the launcher once with --code-inputs (one init and one step): every file of sim/ the process read (the
#      simulator's modules, the X500 URDF, the world parameters, the world cache and the collision meshes PyBullet
#      loads) and the package versions. It stops if the process tried to write anything.
#   4. The code hash is SHA-256 of build/modules/NAME/code_inputs.txt: one line "sha256  label" per file (adapter,
#      protocol, schema JSON, the simulator's files; labels relative to $HARNESS and $SIM, so the hash does not depend
#      on where the repository is), then the launcher's command and the versions of Python, pybullet,
#      gym-pybullet-drones, numpy, scipy, gymnasium and pillow. It goes into build/modules/NAME/manifest.json, which
#      the adapter reports on `describe`. One exception to "sha256 of the bytes": the world cache
#      ($SIM/build/world-cache/gorge_s7.pkl, a pickle written by sim/setup.sh) holds build timings and absolute paths,
#      so its line carries the adapter's content digest of it (`world_digest` in adapter.py: every value but
#      `build_s`, `bake_times` and `asset_dir`, with `files` reduced to file names), labelled "(content)". The mesh
#      files it names are hashed by their bytes. So a fresh clone built anywhere, at any time, gets the same hash.
set -euo pipefail

NAME="${1:-plant_sim}"
case "$NAME" in
  plant_sim) VEHICLES=1 ;;
  plant_formation) VEHICLES=2 ;;
  *) echo "usage: sim/modules/plant_sim/build.sh [plant_sim|plant_formation]" >&2; exit 2 ;;
esac
HARNESS="$(cd "$(dirname "$0")/../../.." && pwd -P)"
SIM="$(cd "$HARNESS/../sim" && pwd -P)"
PY="$SIM/.venv/bin/python"
MOD="$HARNESS/sim/modules/plant_sim"
OUT="$HARNESS/build/modules/$NAME"
GEN="$HARNESS/build/gen/$NAME"
HARNESS_BIN="$HARNESS/.lake/build/bin/harness"

[ -x "$HARNESS_BIN" ] || { echo "build.sh: $HARNESS_BIN missing; run 'lake build' first" >&2; exit 1; }
[ -x "$PY" ] || { echo "build.sh: $PY missing; run sim/setup.sh" >&2; exit 1; }

rm -rf "$OUT"
mkdir -p "$OUT" "$GEN"

# 1. the schemas, from Lean
(cd "$HARNESS" && "$HARNESS_BIN" gen "$NAME" > /dev/null)

# 2. the launcher (it finds the repository from its own location at run time)
ENV=(PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1)
PYFLAGS=(-s -B -P)
{
  echo '#!/bin/sh'
  echo "# written by sim/modules/plant_sim/build.sh: the $NAME module executable"
  echo 'H="$(cd "$(dirname "$0")/../../.." && pwd -P)"'
  echo 'S="$(cd "$H/../sim" && pwd -P)"'
  printf 'exec /usr/bin/env -i %s "$S/.venv/bin/python" %s "$H/sim/modules/plant_sim/adapter.py"' "${ENV[*]}" "${PYFLAGS[*]}"
  printf ' --build "$H/build/modules/%s" --sim "$S" --schema "$H/build/gen/%s/module_schema.json" --vehicles %s' \
    "$NAME" "$NAME" "$VEHICLES"
  echo ' "$@"'
} > "$OUT/$NAME"
chmod +x "$OUT/$NAME"

# 3. what the simulator reads
"$OUT/$NAME" --code-inputs > "$OUT/code_inputs.json"
WRITES="$("$PY" -c 'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["written"]))' "$OUT/code_inputs.json")"
if [ -n "$WRITES" ]; then
  echo "build.sh: the simulator tried to write; stopping:" >&2
  echo "$WRITES" >&2
  exit 1
fi

# 4. the code hash
label() {
  local p="$1"
  case "$p" in
    "$SIM"/*) echo "\$SIM/${p#"$SIM"/}" ;;
    "$HARNESS"/*) echo "\$HARNESS/${p#"$HARNESS"/}" ;;
    *) echo "$p" ;;
  esac
}
DIGESTS="$("$PY" -c 'import json,sys; print("\n".join(f"{k}\t{v}" for k, v in json.load(open(sys.argv[1]))["digests"].items()))' "$OUT/code_inputs.json")"
VERSIONS="$("$PY" -c 'import json,sys; v=json.load(open(sys.argv[1]))["versions"]; print(", ".join(f"{k} {x}" for k, x in v.items()))' "$OUT/code_inputs.json")"
FLAGS="env -i ${ENV[*]} python ${PYFLAGS[*]} adapter.py --vehicles $VEHICLES; physics 1200 Hz, 3 substeps per step, wind off"
{
  {
    for f in "$MOD/adapter.py" "$HARNESS/py/module_protocol.py" "$GEN/module_schema.json"; do echo "$f"; done
    "$PY" -c 'import json,sys; print("\n".join(json.load(open(sys.argv[1]))["files"]))' "$OUT/code_inputs.json"
  } | while IFS= read -r f; do
    d="$(printf '%s\n' "$DIGESTS" | awk -F'\t' -v f="$f" '$1 == f { print $2 }')"
    if [ -n "$d" ]; then
      printf '%s  %s (content)\n' "$d" "$(label "$f")"
    else
      printf '%s  %s\n' "$(shasum -a 256 "$f" | cut -d' ' -f1)" "$(label "$f")"
    fi
  done | LC_ALL=C sort -k2
  echo "flags: $FLAGS"
  echo "interpreter: \$SIM/.venv (sim/setup.sh)"
  echo "versions: $VERSIONS"
} > "$OUT/code_inputs.txt"
CODE_HASH="$(shasum -a 256 "$OUT/code_inputs.txt" | cut -d' ' -f1)"
printf 'SIM=%s\nHARNESS=%s\n' "$SIM" "$HARNESS" > "$OUT/roots.env"
"$PY" -c 'import json,sys; json.dump(dict(code_hash=sys.argv[2], flags=sys.argv[3], compiler=sys.argv[4]), open(sys.argv[1], "w"), indent=1)' \
  "$OUT/manifest.json" "$CODE_HASH" "$FLAGS" "$VERSIONS"

echo "built $OUT/$NAME"
echo "  $(grep -c '  ' "$OUT/code_inputs.txt") files in the code hash ($(grep -c '\$SIM' "$OUT/code_inputs.txt") from sim/)"
echo "  code hash: $CODE_HASH"
