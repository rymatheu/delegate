"""ArduLean's side of the simulator: the lock-step vehicle program (vehicle.py), its per-step protocol (protocol.py) and
the boot-image parameter writer (storage_params.py). The simulator itself is the repository's shared sim/ (package
gorgesim); importing this package puts sim/ on sys.path (and gorgesim puts sim/world/ there).
"""
import sys
from pathlib import Path

ARDULEAN_SIM = Path(__file__).resolve().parent.parent      # ardulean/sim/
ARDULEAN = ARDULEAN_SIM.parent                              # ardulean/
SHARED_SIM = ARDULEAN.parent / "sim"                        # the shared simulator
if str(SHARED_SIM) not in sys.path:
    sys.path.insert(1, str(SHARED_SIM))
import gorgesim  # noqa: E402,F401   (puts sim/world/ on sys.path)
