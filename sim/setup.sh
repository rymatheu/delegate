#!/bin/sh
# Creates the three Python environments the simulation scripts use, then builds the gorge world. Run once from anywhere:
#     sh sim/setup.sh
# Needs Python 3.12 and either uv (https://github.com/astral-sh/uv) or python3.12 with venv and pip.
#   sim/.venv               the simulator: gym-pybullet-drones, PyBullet, NumPy, Matplotlib
#   sim/mavlink/.venv       the scripted ground station: pymavlink
#   sim/world/.venv-video   the camera payload's H.264 encoder: PyAV
# The gorge world (sim/world/assets/, about 300 MB, not tracked) is generated from seed 7 by sim/world/gorge.py:
# about 3 minutes, once; the scripts would otherwise build it on first use.
# Scripts find sim/.venv by its path; set LEANFC_PY (Python scripts) or PY (shell scripts) to use another one.
set -e
cd "$(dirname "$0")/.."
make_env() {   # directory, requirements file
    if [ -e "$1/bin/python" ]; then echo "$1 exists, left as it is"; return; fi
    if command -v uv >/dev/null 2>&1; then
        uv venv --python 3.12 "$1" && uv pip install --python "$1/bin/python" -r "$2"
    else
        python3.12 -m venv "$1" && "$1/bin/python" -m pip install --upgrade pip && "$1/bin/python" -m pip install -r "$2"
    fi
}
make_env sim/.venv sim/requirements.txt
make_env sim/mavlink/.venv sim/mavlink/requirements.txt
make_env sim/world/.venv-video sim/world/requirements-video.txt
echo "Python environments ready."
echo "Building the gorge world (seed 7, about 3 minutes, once) ..."
sim/.venv/bin/python -B sim/world/gorge.py > /dev/null && echo "Gorge world ready (sim/world/assets/)."
