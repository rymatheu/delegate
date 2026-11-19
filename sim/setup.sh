#!/bin/sh
# Creates the simulator's two Python environments from the pinned requirements, then builds the gorge world.
#     sim/setup.sh
#   sim/.venv         the simulator: gym-pybullet-drones, PyBullet, NumPy, SciPy, Matplotlib, pymavlink
#   sim/.venv-video   the camera's H.264 encoder and the video check's decoder: PyAV
# Needs Python 3.12 and uv (https://github.com/astral-sh/uv). PyBullet compiles from source (a few minutes).
# The gorge world (sim/build/world-cache/, about 300 MB, git-ignored) is generated from seed 7: about 3 minutes, once.
# An environment that exists is left as it is (delete it to recreate it).
set -e
SIM="$(cd "$(dirname "$0")" && pwd)"
cd "$SIM"
if ! command -v uv >/dev/null 2>&1; then
    echo "setup.sh: uv is missing (https://github.com/astral-sh/uv)." >&2
    exit 1
fi
make_env() {   # directory, requirements file
    if [ -e "$1/bin/python" ]; then echo "$1 exists, left as it is"; return; fi
    uv venv --python 3.12 "$1"
    # -Dfdopen=fdopen: PyBullet's bundled zlib does not compile with the macOS SDK's fdopen macro otherwise
    CFLAGS="-Dfdopen=fdopen" uv pip install --python "$1/bin/python" --no-deps -r "$2"
}
make_env .venv requirements.txt
make_env .venv-video requirements-video.txt
.venv/bin/python -c "import pybullet, gym_pybullet_drones.envs, scipy, matplotlib, pymavlink" 2>/dev/null \
    && echo "sim/.venv ready"
.venv-video/bin/python -c "import av, numpy" && echo "sim/.venv-video ready"
echo "Building the gorge world (seed 7; about 3 minutes the first time, then cached) ..."
# Built through an import, not by running world/gorge.py as a script: the cache stores the world's objects by
# module name, and every program that loads it imports the module `gorge`. A cache written by the script itself
# (objects stored under `__main__`) is unreadable to them; the import below detects that and rebuilds it.
.venv/bin/python -B -c "import sys; sys.path.insert(0, 'world'); import gorge; gorge.Gorge(7).summary()" > /dev/null
echo "Gorge world ready (sim/build/world-cache/)."
