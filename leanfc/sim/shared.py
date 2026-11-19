"""Where the shared simulator is: the repository's sim/ (the gorge world, the X500 airframe, the aviaries, the camera,
the plan files and the stand-in checks). leanfc keeps only its own bridge in leanfc/sim/."""
import sys
from pathlib import Path

LEANFC = Path(__file__).resolve().parents[1]      # leanfc/
REPO = LEANFC.parent                              # the repository
SIM = REPO / "sim"                                # the shared simulator
WORLD = SIM / "world"
X500_URDF = WORLD / "x500" / "x500.urdf"
X500_RENDER_URDF = WORLD / "x500" / "x500_render_noprops.urdf"


def use_world():
    """Put the shared sim/ and sim/world/ on the module path (after leanfc's own directories)."""
    for d in (SIM, WORLD):
        if str(d) not in sys.path:
            sys.path.append(str(d))
