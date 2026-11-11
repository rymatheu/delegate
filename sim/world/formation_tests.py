"""The scripted formation flights (test_formation_flight.py, real time, MAVLink, both cameras streaming), one
after the other so that each has the machine to itself, and their table (OUT/tests.md, OUT/tests.json).

    python formation_tests.py [--set main|skew|mv|all] [--seeds 0 1 2 3 4] [--out out/formation/tests] [--reuse]

Sets:
  main  both plans, field noise, seeds SEEDS, wind off and 6 2;
  skew  both plans, field noise, seed 0, no wind, vehicle 2's Start Mission -5, -2, +2, +5 s after vehicle 1's;
  mv    both plans, field noise, seed 0, no wind, started as QGroundControl's Multi-Vehicle panel does (Arm both,
        then Start both).
"""
import argparse
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PY = "/Users/ryan/Research/cpp2lean/sim/.venv/bin/python"


def jobs(which, seeds):
    out = []
    for plan in ("abreast", "staggered"):
        if which in ("main", "all"):
            out += [(plan, s, w, 0.0, "single") for w in (None, ("6", "2")) for s in seeds]
        if which in ("skew", "all"):
            out += [(plan, 0, None, sk, "single") for sk in (-5.0, -2.0, 2.0, 5.0)]
        if which in ("mv", "all"):
            out.append((plan, 0, None, 0.0, "mv"))
    return out


def name(plan, seed, wind, skew, start):
    return (f"{plan}-s{seed}-" + ("off" if wind is None else f"w{wind[0]}_{wind[1]}") + (f"-skew{skew:+g}" if skew else "")
            + ("-mv" if start == "mv" else ""))


def fmt(x, nd=2):
    return "–" if x is None else f"{x:.{nd}f}"


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--set", choices=("main", "skew", "mv", "all"), default="all")
    ap.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2, 3, 4])
    ap.add_argument("--out", default=str(HERE / "out" / "formation" / "tests"))
    ap.add_argument("--reuse", action="store_true")
    a = ap.parse_args()
    root = Path(a.out)
    rows = []
    for job in jobs(a.set, a.seeds):
        plan, seed, wind, skew, start = job
        d = root / name(*job)
        if not (a.reuse and (d / "report.json").exists()):
            cmd = [PY, "-B", str(HERE / "test_formation_flight.py"), "--plan", plan, "--seed", str(seed), "--skew", str(skew),
                   "--start", start, "--out", str(d / "session")] + (["--wind", *wind] if wind else [])
            r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
            d.mkdir(parents=True, exist_ok=True)
            (d / "test.log").write_text(r.stdout + r.stderr)
            print(d.name, (r.stdout.strip().splitlines() or ["no output"])[-1], flush=True)
        if (d / "report.json").exists():
            rows.append((job, d, json.loads((d / "report.json").read_text())))
    lines = ["# Formation flights from the ground (test_formation_flight.py)", "",
             "Real time, MAVLink, both cameras streaming (four streams), field noise. Separation: centre to centre from "
             "the simulator every tick, 'route' = both vehicles on items 2..10 (the spline waypoints) and in the air. "
             "Skew: vehicle 2's route start (item 2) minus vehicle 1's, from the controllers' records. Rear heading: "
             "vehicle 2's true heading against the opposite of its direction of travel, after its initial turn "
             "(from the first tick below 5 deg). RTF: simulated / wall seconds after the first 2 s; worst 1 s window.", "",
             "| run | checks | separation route min / mean / max m | abs(d - nominal) p95 / max | min in the air m | route skew s | "
             "clearance v1 / v2 m | tracking max v1 / v2 m | v2 heading vs its travel direction (reversed in staggered) after the turn: max / p95 deg (from N m) | touchdown v1 / v2 m/s | "
             "frames sent / received (4 streams) | RTF, worst 1 s, max lag s |",
             "|---|---:|---|---|---:|---:|---|---|---|---|---|---|"]
    for (plan, seed, wind, skew, start), d, r in rows:
        sp, vs = r["separation"], r["vehicles"]
        h = vs[1]["heading_after_turn"]
        vid = " ; ".join(f"{x['sent']}/{x['received']}" for x in r.get("video", []))
        rt = r.get("realtime", {})
        lines.append(f"| {d.name} | {r['passed']}/{r['checks']} | {fmt(sp['route']['min'])} / {fmt(sp['route']['mean'])} / "
                     f"{fmt(sp['route']['max'])} | {fmt(sp['route']['dev_p95'])} / {fmt(sp['route']['dev_max'])} | "
                     f"{fmt(sp['both_air']['min'])} | {r['skew']['route_start_s']:+.3f} | {fmt(vs[0]['clearance_air'])} / "
                     f"{fmt(vs[1]['clearance_air'])} | {fmt(vs[0]['track_max'])} / {fmt(vs[1]['track_max'])} | "
                     f"{fmt(h['max'], 1)} / {fmt(h['p95'], 1)} ({fmt(h['from_north'], 1)}) | {fmt(vs[0]['touchdown_v'])} / "
                     f"{fmt(vs[1]['touchdown_v'])} | {vid} | {fmt(rt.get('rtf'), 4)}, {fmt(rt.get('rtf_1s_min'), 3)}, "
                     f"{fmt(rt.get('lag_max_s'), 3)} |")
    root.mkdir(parents=True, exist_ok=True)
    (root / f"tests-{a.set}.md").write_text("\n".join(lines) + "\n")
    (root / f"tests-{a.set}.json").write_text(json.dumps([dict(run=d.name, **r) for _, d, r in rows], indent=1) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
