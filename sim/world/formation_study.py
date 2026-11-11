"""The formation study: batch flights of both plans (formation.py, no MAVLink, deterministic) over noise
seeds, wind and start-time skew, and their table (OUT/study.md, OUT/study.json).

    python formation_study.py [--jobs 8] [--seeds 0 1 2 3 4] [--out out/formation/study] [--reuse] [--set main|skew|all]

Sets:
  main  both plans, field noise, seeds SEEDS, wind off, 4 1, 6 2 (up-gorge) and -6 2 (down-gorge), no skew;
        and the deterministic flight (noise none) of each plan;
  skew  both plans, field noise, seed 0, vehicle 2 starting -10, -5, -3, -2, -1, +1, +2, +3, +5, +10 s
        after vehicle 1, without wind and with 6 2.
A run directory that already has formation.json is reused with --reuse (the table is recomputed).
"""
import argparse
import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
PY = __import__("os").environ.get("LEANFC_PY") or str(Path(__file__).resolve().parents[2] / "sim" / ".venv" / "bin" / "python")
WINDS = [None, (4, 1), (6, 2), (-6, 2)]
SKEWS = [-10, -5, -3, -2, -1, 1, 2, 3, 5, 10]


def name(plan, noise, seed, wind, skew):
    w = "off" if wind is None else f"w{wind[0]:+g}_{wind[1]:g}".replace("+", "p").replace("-", "m")
    sk = "" if not skew else f"-skew{skew:+g}"
    return f"{plan}-{noise}-s{seed}-{w}{sk}"


def jobs(sets, seeds, skews=SKEWS, plans=("abreast", "staggered")):
    out = []
    for plan in plans:
        if sets in ("main", "all"):
            out.append((plan, "none", 0, None, 0))
            out += [(plan, "field", s, w, 0) for w in WINDS for s in seeds]
        if sets in ("skew", "all"):
            out += [(plan, "field", 0, w, sk) for w in (None, (6, 2)) for sk in skews]
    return out


def run_one(job, root, reuse):
    plan, noise, seed, wind, skew = job
    d = root / name(*job)
    if reuse and (d / "formation.json").exists():
        return d
    cmd = [PY, "-B", str(HERE / "formation.py"), "--plan", plan, "--noise", noise, "--seed", str(seed),
           "--skew", str(skew), "--out", str(d)] + (["--wind", str(wind[0]), str(wind[1])] if wind else [])
    r = subprocess.run(cmd, capture_output=True, text=True)
    (d.mkdir(parents=True, exist_ok=True), (d / "run.log").write_text(r.stdout + r.stderr))
    print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else f"{d}: FAILED\n{r.stderr[-2000:]}", flush=True)
    return d


def row(job, d):
    m = json.loads((d / "formation.json").read_text())
    s = m.get("summary", {})
    dr = s.get("dist_route", {})
    v1, v2 = s.get("v1", {}), s.get("v2", {})
    c = s.get("contacts", {})
    rear = v2 if m["reverse"][1] else None
    plan, noise, seed, wind, skew = job
    return dict(run=d.name, plan=plan, noise=noise, seed=seed, wind=wind, skew=skew, outcome=m["outcome"],
                completed=m.get("completed_at"), nominal=m["nominal_distance"],
                dmin=dr.get("min"), dmean=dr.get("mean"), dmax=dr.get("max"), dev95=dr.get("dev_p95"), devmax=dr.get("dev_max"),
                dall=s.get("dist_all", {}).get("min"), gap=s.get("gap_min"),
                contacts=c.get("vv", 0) + c.get("v1", 0) + c.get("v2", 0),
                clear1=v1.get("clear_min"), clear2=v2.get("clear_min"), track1=v1.get("track_max"), track2=v2.get("track_max"),
                sat=v1.get("sat_ticks", 0) + v2.get("sat_ticks", 0),
                rear_from=(rear or {}).get("heading_err_after_turn", {}).get("from_north"),
                rear_max=(rear or {}).get("heading_err_after_turn", {}).get("max"),
                rear_p95=(rear or {}).get("heading_err_after_turn", {}).get("p95"),
                rear_rms=(rear or {}).get("heading_err_after_turn", {}).get("rms"),
                fwd_p95=max(v1.get("heading_err_route", {}).get("p95") or 0,
                            (v2.get("heading_err_route", {}).get("p95") or 0) if not m["reverse"][1] else 0))


def fmt(x, nd=2):
    return "–" if x is None else f"{x:.{nd}f}"


def table(rows):
    head = ("| run | outcome | route end s | distance min / mean / max m | abs(d - nominal) p95 / max m | min distance whole flight m | "
            "body gap min m | contacts | clearance v1 / v2 m | tracking max v1 / v2 m | sat ticks | rear heading vs reversed travel: from N m, max / p95 / rms deg |")
    lines = [head, "|---|---|---:|---|---|---:|---:|---:|---|---|---:|---|"]
    for r in rows:
        w = "off" if r["wind"] is None else f"{r['wind'][0]:+g} {r['wind'][1]:g}"
        rear = "–" if r["rear_max"] is None else f"{r['rear_from']:.1f}, {r['rear_max']:.1f} / {r['rear_p95']:.1f} / {r['rear_rms']:.1f}"
        lines.append(f"| {r['plan']} {r['noise']} s{r['seed']} wind {w}" + (f" skew {r['skew']:+g} s" if r["skew"] else "") +
                     f" | {r['outcome']} | {fmt(r['completed'])} | {fmt(r['dmin'])} / {fmt(r['dmean'])} / {fmt(r['dmax'])} | "
                     f"{fmt(r['dev95'])} / {fmt(r['devmax'])} | {fmt(r['dall'])} | {fmt(r['gap'])} | {r['contacts']} | "
                     f"{fmt(r['clear1'])} / {fmt(r['clear2'])} | {fmt(r['track1'])} / {fmt(r['track2'])} | {r['sat']} | {rear} |")
    return lines


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--seeds", type=int, nargs="+", default=[0, 1, 2, 3, 4])
    ap.add_argument("--set", choices=("main", "skew", "all"), default="all")
    ap.add_argument("--out", default=str(HERE / "out" / "formation" / "study"))
    ap.add_argument("--reuse", action="store_true")
    ap.add_argument("--skews", type=float, nargs="+", default=SKEWS, help="the skew set's skews (s)")
    ap.add_argument("--plans", nargs="+", default=["abreast", "staggered"])
    ap.add_argument("--tag", default=None, help="name of the table (default: the set)")
    a = ap.parse_args()
    root = Path(a.out)
    root.mkdir(parents=True, exist_ok=True)
    js = jobs(a.set, a.seeds, a.skews, a.plans)
    tag = a.tag or a.set
    with ThreadPoolExecutor(a.jobs) as ex:
        dirs = list(ex.map(lambda j: run_one(j, root, a.reuse), js))
    rows = [row(j, d) for j, d in zip(js, dirs) if (d / "formation.json").exists()]
    (root / f"study-{tag}.json").write_text(json.dumps(rows, indent=1) + "\n")
    lines = [f"# Formation study ({tag})", "",
             "Batch flights (formation.py): both vehicles start hovering at their route's first point; field noise "
             "(vehicle 2: seed + 100), wind MEAN GUST with uncorrelated gusts per vehicle; skew S: vehicle 2 starts S s "
             "after vehicle 1. Distance: centre to centre from the simulator every tick; 'route': both navigators "
             "between their start and the end of their last leg. Body gap: closest distance between the two collision "
             "cylinders. Clearance: collision body to terrain and boulders, every tick. Rear heading: the angle between "
             "vehicle 2's true heading and the opposite of its horizontal velocity (above 0.5 m/s), from the first tick "
             "it is below 5 deg (the end of its initial 180 deg turn; north of that point in the column) to the end of the route.", ""]
    for plan in ("abreast", "staggered"):
        pr = [r for r in rows if r["plan"] == plan]
        if not pr:
            continue
        lines += [f"## {plan} (nominal {pr[0]['nominal']:.3f} m)", ""] + table(pr) + [""]
        noisy = [r for r in pr if r["noise"] == "field" and not r["skew"]]
        if noisy:
            lines.append(f"Noisy flights without skew ({len(noisy)}): distance over the route min {min(r['dmin'] for r in noisy):.3f} m, "
                         f"max {max(r['dmax'] for r in noisy):.3f} m; abs(d - nominal) max {max(r['devmax'] for r in noisy):.3f} m; "
                         f"contacts {sum(r['contacts'] for r in noisy)}; clearance min {min(min(r['clear1'], r['clear2']) for r in noisy):.3f} m; "
                         f"outcomes {sorted({r['outcome'] for r in noisy})}.")
            lines.append("")
    (root / f"study-{tag}.md").write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
