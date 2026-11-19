#!/usr/bin/env python3
"""A stand-in QGroundControl session of the PX4 stack on test ports, with the video check.

  python3 -I px4/gorge/session_check.py [single|abreast|staggered] --udp-port P --video-port V
          --pose-port X [--out DIR] [--seconds 8]

Starts px4/fly_qgc.sh SCENARIO --udp-port P --video-port V --pose-port X --out DIR/session exactly as a
person would (vehicles send to P, cameras announced on P, video to V...), then on the same port
plays QGroundControl with px4/gorge/gcs.py --camera (parameters, the plans of px4/plans uploaded
with the mission protocol, each camera's heartbeat, CAMERA_INFORMATION and VIDEO_STREAM_INFORMATION,
arm, mission start, the flight to PX4's own disarm). Meanwhile, once the vehicles are up, every video
port is decoded for --seconds by the shared simulator's decoder (sim/checks/video_check.py --decode,
in sim/.venv-video): frames of 640 x 480 (RGB, 10 fps) or 640 x 512 (thermal, 8.7 fps) at 70 to 130 %
of the rate, no decode errors, not blank. Last, SIGTERM to the session: every process it started
(harness, modules, relay, cameras, render workers) must be gone. Prints RESULT PASS or RESULT FAIL;
report.txt in DIR. 14550 and 5600-5607 are refused."""
import argparse
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
PX4_DIR = HERE.parent
HARNESS = PX4_DIR.parent
ROOT = HARNESS.parent
SIM = Path(os.environ.get('SIM_DIR', ROOT / 'sim'))
VPY = os.environ.get('GORGE_VIDEO_PY', str(SIM / '.venv-video' / 'bin' / 'python'))
RGB = ((640, 480), 10.0)
THERMAL = ((640, 512), 8.7)
LINES, RESULTS = [], []


def report(name, ok, detail=''):
    RESULTS.append(bool(ok))
    LINES.append('%s %s%s' % ('PASS' if ok else 'FAIL', name, ' (%s)' % detail if detail else ''))
    print(LINES[-1], flush=True)


def tree(pid):
    ps = subprocess.run(['ps', '-A', '-o', 'pid=,ppid=,command='], capture_output=True, text=True).stdout
    kids, cmd = {}, {}
    for line in ps.splitlines():
        p, pp, c = line.strip().split(None, 2) if len(line.strip().split(None, 2)) == 3 else (*line.strip().split(None, 1), '')
        kids.setdefault(int(pp), []).append(int(p))
        cmd[int(p)] = c
    out, todo = {}, [pid]
    while todo:
        p = todo.pop()
        for k in kids.get(p, []):
            out[k] = cmd.get(k, '')
            todo.append(k)
    return out, cmd


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('scenario', nargs='?', default='single', choices=('single', 'abreast', 'staggered'))
    ap.add_argument('--udp-port', type=int, required=True)
    ap.add_argument('--video-port', type=int, required=True)
    ap.add_argument('--pose-port', type=int, required=True)
    ap.add_argument('--out', default=None)
    ap.add_argument('--seconds', type=float, default=8.0)
    ap.add_argument('--timeout', type=float, default=600.0)
    a = ap.parse_args()
    if a.udp_port in (14550, 14560) or 5600 <= a.video_port <= 5607 + 6:
        raise SystemExit('session_check: not on 14550 / 5600-5607')
    two = a.scenario != 'single'
    out = Path(a.out or PX4_DIR / 'out' / f'session-{a.scenario}').resolve()
    out.mkdir(parents=True, exist_ok=True)
    V = a.video_port
    ports = {'rgb-v1': (V, RGB), 'thermal-v1': (V + 2, THERMAL)}
    if two:
        ports['thermal-v2'] = (V + 6, THERMAL)
    slog = open(out / 'launcher.log', 'w')
    t_start = time.time()
    sess = subprocess.Popen([str(PX4_DIR / 'fly_qgc.sh')] + ([a.scenario] if two else []) +
                            ['--udp-port', str(a.udp_port), '--video-port', str(V), '--pose-port', str(a.pose_port),
                             '--out', str(out / 'session')], stdout=slog, stderr=subprocess.STDOUT,
                            start_new_session=True, cwd=str(PX4_DIR))
    plans = ([f'1={PX4_DIR}/plans/formation-{a.scenario}-v1.plan', f'2={PX4_DIR}/plans/formation-{a.scenario}-v2.plan']
             if two else [f'1={PX4_DIR}/plans/gorge.plan'])
    gl = open(out / 'gcs.log', 'w')
    gcs = subprocess.Popen([str(HARNESS / 'build/px4venv/bin/python'), '-I', str(HERE / 'gcs.py'), '--port',
                            str(a.udp_port), '--camera', '--log', str(out), '--timeout', str(a.timeout)] +
                           sum((['--vehicle', p] for p in plans), []), stdout=gl, stderr=subprocess.STDOUT)
    # decode the video while the vehicles fly (from the mission start; the cameras are up long before)
    t0 = time.time()
    while time.time() - t0 < 400 and gcs.poll() is None:
        if 'MISSION_START accepted' in (out / 'gcs.log').read_text():
            break
        time.sleep(1)
    procs = {tag: subprocess.Popen([VPY, '-B', str(SIM / 'checks' / 'video_check.py'), '--decode', str(port),
                                    str(a.seconds), str(out / f'{tag}.png')], stdout=subprocess.PIPE, text=True)
             for tag, (port, _) in ports.items()}
    for tag, p in procs.items():
        o, _ = p.communicate(timeout=a.seconds + 60)
        try:
            r = json.loads(o.strip().splitlines()[-1])
        except (ValueError, IndexError):
            r = None
        size, fps = ports[tag][1]
        if r is None:
            report(f'{tag}: decoder ran', False)
            continue
        report(f'{tag}: RTP on UDP {r["port"]} decodes to {size[0]}x{size[1]} at about {fps:g} fps',
               r['frames'] > 0 and r['size'] == list(size) and 0.7 * fps <= r['fps'] <= 1.3 * fps and r['errors'] == 0,
               f'{r["packets"]} packets, {r["lost"]} lost, {r["frames"]} frames in {r["span_s"]:.1f} s = '
               f'{r["fps"]:.2f} fps, size {r["size"]}, decode errors {r["errors"]}')
        report(f'{tag}: frames not blank', r['std'] and min(r['std']) > 5,
               f'luma std min {min(r["std"] or [0]):.1f}; saved {r["png"]}')
    gcs.wait()
    gtxt = (out / 'gcs.log').read_text().splitlines()
    for l in gtxt:
        if l.startswith('gcs: V') and (' PASS' in l or ' FAIL' in l):
            LINES.append('  ' + l)
    report('ground station (px4/gorge/gcs.py --camera): every stage', gcs.returncode == 0,
           next((l for l in reversed(gtxt) if l.startswith('gcs: PASS') or l.startswith('gcs: FAIL')), ''))
    procs_before, cmds = tree(sess.pid)
    for p, c in cmds.items():
        if str(out / 'session') in c and p not in procs_before and p != sess.pid:
            procs_before[p] = c
            procs_before.update(tree(p)[0])
    os.kill(sess.pid, signal.SIGTERM)
    try:
        sess.wait(90)
    except subprocess.TimeoutExpired:
        pass
    time.sleep(2.0)
    left = {p: c for p, c in procs_before.items() if subprocess.run(['kill', '-0', str(p)], capture_output=True).returncode == 0}
    report(f'SIGTERM to the session: all {len(procs_before) + 1} of its processes gone', not left and sess.poll() is not None,
           f'exit status {sess.poll()}' + (f'; left: {left}' if left else ''))
    for p in left:
        try:
            os.kill(p, signal.SIGKILL)       # our own strays only
        except ProcessLookupError:
            pass
    slog.close()
    import glob, re, shutil
    for f in glob.glob(str(HARNESS / 'build' / 'serve' / '*.log')):
        if os.path.getmtime(f) >= t_start:
            shutil.copy(f, out / ('serve-' + os.path.basename(f)))
            txt = open(f).read().splitlines()
            inst = [l.strip() for l in txt if re.match(r'\s+\S+: assumption failed in', l)]
            bad = [l for l in inst if 'assumption failed in 0 cases; guarantee violations: none' not in l]
            report(f'monitors of {os.path.basename(f)}: no guarantee violated, no discharge failure', inst and not bad,
                   f'{len(inst)} instances' + ''.join('; ' + l for l in bad))
    rl = [l for l in (out / 'launcher.log').read_text().splitlines() if 'socket closed after' in l]
    LINES.extend('  ' + l for l in rl)
    ok = all(RESULTS)
    LINES.append('RESULT %s (%d/%d)' % ('PASS' if ok else 'FAIL', sum(RESULTS), len(RESULTS)))
    print(LINES[-1], flush=True)
    (out / 'report.txt').write_text('\n'.join(LINES) + '\n')
    return 0 if ok else 1


sys.exit(main())
