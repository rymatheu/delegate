"""gorgesim: the gorge simulator's Python package (sim/README.md, "Interface for flight controllers"). No flight-controller
logic: the plant (plant.Plant, plant.FormationPlant), the physics environment and frames (simulator), the sensor layer
(sensor_layer), the motor map (motors), the missions (missions), the scripted MAVLink ground station (ground_station),
the 100 Hz record (record), the UDP bridge, wall-clock pacer and camera pose feed (udp_bridge), the plan writer
(write_qgc_plans) and the camera launcher (video).

Importing the package puts sim/world/ on sys.path, so that the gorge world's modules (gorge, gorge_plan, geo, airframes,
gorge_aviary, wind, formation_plan, ...) are imported by name, as they import each other.
"""
import sys
from pathlib import Path

SIM_DIR = Path(__file__).resolve().parent.parent          # sim/
WORLD_DIR = SIM_DIR / "world"                             # the world's modules, the X500, origin.params
PLANS_DIR = SIM_DIR / "plans"                             # the QGroundControl plan files
BUILD_DIR = SIM_DIR / "build"                             # generated, git-ignored: world-cache/, runs, checks
SIM_PY = SIM_DIR / ".venv" / "bin" / "python"             # the simulator's environment (sim/setup.sh)
VIDEO_PY = SIM_DIR / ".venv-video" / "bin" / "python"     # the video environment (sim/setup.sh)
if str(WORLD_DIR) not in sys.path:
    sys.path.append(str(WORLD_DIR))
