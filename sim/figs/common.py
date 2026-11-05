"""Shared helpers of the figure generators in sim/figs: the recorded flights, the closest approaches of
summary.txt, largest-triangle-three-buckets thinning, and TikZ number formatting.

Every number a generator writes comes from the files named here (sim/out/...); nothing is typed in.
"""
from __future__ import annotations

import csv
import re
from pathlib import Path

import numpy as np

FIGS = Path(__file__).resolve().parent
SIM = FIGS.parent
ROOT = SIM.parent
OUT = SIM / "out"
STAGING = Path("/Users/ryan/Research/delegate/staging")
MISSION = "course-1ms"

PALETTE = """\\definecolor{fwInk}{HTML}{22252A}%
\\definecolor{fwMute}{HTML}{8A8F96}%
\\definecolor{fwHair}{HTML}{C9CCD1}%
\\definecolor{fwOchre}{HTML}{C4860F}%
\\definecolor{fwBlue}{HTML}{1E3F7C}%
\\definecolor{fwVerm}{HTML}{C0412B}%
\\definecolor{fwSage}{HTML}{C3D7B4}%"""


def run_dir(vehicle: str, mission: str = MISSION) -> Path:
    """sim/out/<lean|ref>-<mission>."""
    return OUT / f"{vehicle}-{mission}"


def rel(p: Path) -> str:
    """A path inside the project, relative to its root (for header comments)."""
    p = Path(p).resolve()
    return str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p)


def load_flight(run: Path) -> dict[str, np.ndarray]:
    """flight.csv of a run as named float arrays."""
    with open(run / "flight.csv") as f:
        rows = list(csv.reader(f))
    head, body = rows[0], rows[1:]
    a = np.array([[float(v) for v in r] for r in body])
    return {h: a[:, j] for j, h in enumerate(head)}


def summary(run: Path) -> dict:
    """The numbers of summary.txt: ticks, simulated time, waypoints and their closest approaches."""
    s = (run / "summary.txt").read_text()
    end = re.search(r"^end: (.*?); (\d+) ticks, ([\d.]+) s simulated", s, re.M)
    wps = []
    for m in re.finditer(r"^waypoint (\d+) \(([^)]*)\): closest ([\d.]+) cm at ([\d.]+) s"
                         r"(?:, first within ([\d.]+) m at ([\d.]+) s|, not within ([\d.]+) m)", s, re.M):
        wps.append({"i": int(m.group(1)), "ned": tuple(float(v) for v in m.group(2).split(",")),
                    "closest_cm": float(m.group(3)), "t_closest": float(m.group(4)),
                    "t_within": float(m.group(6)) if m.group(6) else None})
    return {"text": s, "end": end.group(1), "ticks": int(end.group(2)), "time": float(end.group(3)),
            "waypoints": wps, "command": s.splitlines()[0]}


def lttb(pts: np.ndarray, n: int) -> np.ndarray:
    """Indices kept by largest-triangle-three-buckets: pts (N x 2, in drawing units, in drawing order)
    thinned to n points. The first and last points are kept; the others are split into n - 2 buckets
    of consecutive points, and each bucket keeps the point of largest triangle area with the point
    kept before it and the mean of the next bucket."""
    N = len(pts)
    if n >= N or n < 3:
        return np.arange(N)
    edges = np.linspace(1, N - 1, n - 1)
    edges = np.floor(edges).astype(int)
    keep = [0]
    a = 0
    for b in range(n - 2):
        lo, hi = edges[b], edges[b + 1]
        if b + 2 < n - 1:
            nlo, nhi = edges[b + 1], edges[b + 2]
            nxt = pts[nlo:max(nhi, nlo + 1)].mean(axis=0)
        else:
            nxt = pts[N - 1]
        cand = pts[lo:max(hi, lo + 1)]
        pa = pts[a]
        area = np.abs((pa[0] - nxt[0]) * (cand[:, 1] - pa[1]) - (pa[0] - cand[:, 0]) * (nxt[1] - pa[1]))
        a = lo + int(np.argmax(area))
        keep.append(a)
    keep.append(N - 1)
    return np.array(keep)


def num(v: float, nd: int = 3) -> str:
    """A number for TikZ: rounded to nd decimals, no trailing zeros, no negative zero."""
    s = f"{v:.{nd}f}".rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def coords(xs, ys, nd: int = 3, per_line: int = 10, indent: str = "    ") -> str:
    """`(x,y) (x,y) ...` lines for `plot coordinates {...}`."""
    items = [f"({num(x, nd)},{num(y, nd)})" for x, y in zip(xs, ys)]
    return "\n".join(indent + " ".join(items[i:i + per_line]) for i in range(0, len(items), per_line))


def check_same(a: dict, b: dict, skip=("tick_us",)) -> int:
    """Number of ticks on which two flights differ in any field except the controller round trip."""
    keys = [k for k in a if k not in skip]
    if len(a["t"]) != len(b["t"]):
        return max(len(a["t"]), len(b["t"]))
    diff = np.zeros(len(a["t"]), bool)
    for k in keys:
        diff |= a[k] != b[k]
    return int(diff.sum())


BINARIES = {"lean": ROOT / "lean" / ".lake" / "build" / "bin" / "copter_lean",
            "ref": ROOT / "build" / "vehicle" / "copter_ref"}
COURSE_PARAMS = [SIM / "params" / "copter-cf2x.txt", SIM / "params" / "copter-course-speed.txt"]
TUNED_PARAMS = SIM / "params" / "copter-cf2x-tuned.txt"


def print_params(vehicle: str, tuned: bool = True) -> tuple[str, dict]:
    """The parameter values in effect for the course: `<binary> --params ... --print-params` (the
    course files, with the tuned overlay when tuned), as raw text and as {NAME: value string}."""
    import subprocess
    files = COURSE_PARAMS + ([TUNED_PARAMS] if tuned else [])
    cmd = [str(BINARIES[vehicle])]
    for f in files:
        cmd += ["--params", str(f)]
    res = subprocess.run(cmd + ["--print-params"], cwd=SIM, capture_output=True, text=True, check=True, input="")
    vals = {}
    for ln in res.stdout.splitlines():
        ws = ln.split()
        if len(ws) == 2:
            vals[ws[0]] = ws[1]
    return res.stdout, vals


def angle_max_deg() -> float:
    """ATC_ANGLE_MAX in effect on the tuned course, checked equal for the two vehicles."""
    a, b = print_params("lean")[1], print_params("ref")[1]
    if a["ATC_ANGLE_MAX"] != b["ATC_ANGLE_MAX"]:
        raise SystemExit("the vehicles disagree on ATC_ANGLE_MAX")
    return float(a["ATC_ANGLE_MAX"])
