"""Test of the map tile server (tile_server.py): tiles at every zoom, the georeference against
QGroundControl's tile arithmetic, and mosaics.

    sim/.venv/bin/python sim/world/test_tiles.py [--out sim/world/out/test-tiles]

Starts tile_server.py on a test port (the default ORIGIN of params/ground.params) and fetches with
urllib:
- the tile under the start at every zoom 0..23: HTTP 200, a 256 x 256 PNG; a tile far from the gorge
  is the uniform background; zoom 24 is 404;
- georeference, with features seen in the tiles: for a boulder, a firebrand's embers and its ash bed,
  the world centroid of the feature as seen from above (its triangles filled on a 5 mm grid, an
  independent rasterization), sent through the controller's `toLatLon` integers (what QGroundControl
  receives for a vehicle there) and QGroundControl's MapProvider.cpp formulas (long2tileX, lat2tileY
  and their fractional pixel), against the centroid of the feature's pixels in the server's class
  tiles (/seg) at zoom 23 and 21; error in cm;
- the start (no feature to see): the arithmetic chain, true position -> toLatLon integers -> QGC pixel
  at zoom 23 -> the server's pixel -> position mapping (tile_server.Tiles._coords), error in cm;
- mosaics: the whole gorge at zoom 20 and 3 x 3 tiles at zoom 23 around a firebrand (PNG).
"""
import argparse
import io
import math
import subprocess
import sys
import time
import urllib.error
import urllib.request
from pathlib import Path
from types import SimpleNamespace

import numpy as np
from PIL import Image

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import geo  # noqa: E402
import gorge as G  # noqa: E402
import tile_server as TS  # noqa: E402

RESULTS = []


def report(name, ok, detail=""):
    RESULTS.append((name, bool(ok)))
    line = f"{'PASS' if ok else 'FAIL'}  {name}{'  ' + detail if detail else ''}"
    print(line, flush=True)
    return line


def fetch(url):
    t0 = time.perf_counter()
    try:
        with urllib.request.urlopen(url, timeout=10) as r:
            body = r.read()
            return r.status, body, time.perf_counter() - t0
    except urllib.error.HTTPError as e:
        return e.code, b"", time.perf_counter() - t0


def silhouette_centroid(tris, step=0.005):
    """Centroid (x, y) of the union of the triangles' top-down projections, filled on a grid."""
    xy = tris[..., :2]
    lo, hi = xy.reshape(-1, 2).min(0), xy.reshape(-1, 2).max(0)
    gx = np.arange(lo[0], hi[0] + step, step) + step / 2
    gy = np.arange(lo[1], hi[1] + step, step) + step / 2
    X, Y = np.meshgrid(gx, gy)
    inside = np.zeros(X.shape, bool)
    for a, b, c in xy:
        d = (b[1] - c[1]) * (a[0] - c[0]) + (c[0] - b[0]) * (a[1] - c[1])
        if abs(d) < 1e-12:
            continue
        l1 = ((b[1] - c[1]) * (X - c[0]) + (c[0] - b[0]) * (Y - c[1])) / d
        l2 = ((c[1] - a[1]) * (X - c[0]) + (a[0] - c[0]) * (Y - c[1])) / d
        inside |= (l1 >= 0) & (l2 >= 0) & (l1 + l2 <= 1)
    return np.array([X[inside].mean(), Y[inside].mean()])


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--port", type=int, default=8798)
    ap.add_argument("--out", default=str(HERE / "out" / "test-tiles"))
    a = ap.parse_args()
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    lines = []
    files = [ROOT / "params/x500.params", ROOT / "params/ground.params"]
    origin = geo.Origin.from_params(files)
    g = G.Gorge(7)
    srv = subprocess.Popen([sys.executable, "-B", str(HERE / "tile_server.py"), "--port", str(a.port)],
                           stdout=open(out / "server.out", "w"), stderr=subprocess.STDOUT)
    base = f"http://127.0.0.1:{a.port}"
    try:
        for _ in range(120):
            try:
                urllib.request.urlopen(base + "/stats", timeout=1)
                break
            except OSError:
                time.sleep(0.5)
        start = g.path[0]
        lat0, lon0 = [v / 1e7 for v in origin.latlon_e7(start[1], start[0])]
        ok, times, sizes = True, [], []
        for z in range(0, 24):
            x, y = geo.long2tileX(lon0, z), geo.lat2tileY(lat0, z)
            st, body, dt = fetch(f"{base}/{z}/{x}/{y}.png")
            im = Image.open(io.BytesIO(body)) if st == 200 else None
            ok &= st == 200 and im.size == (256, 256) and im.format == "PNG"
            times.append(dt * 1000)
            sizes.append(len(body))
        lines.append(report("the tile under the start at every zoom 0..23: HTTP 200, 256 x 256 PNG", ok,
                            f"fetch {np.mean(times):.1f} ms mean, {np.max(times):.1f} max; {min(sizes)}..{max(sizes)} bytes"))
        st, body, _ = fetch(f"{base}/18/{geo.long2tileX(lon0 + 0.05, 18)}/{geo.lat2tileY(lat0, 18)}.png")
        arr = np.asarray(Image.open(io.BytesIO(body)).convert("RGB")) if st == 200 else None
        lines.append(report("a tile 4 km east of the gorge: the uniform neutral background",
                            st == 200 and (arr == TS.BACKGROUND).all(), f"{arr[0, 0].tolist() if arr is not None else st}"))
        st, _, _ = fetch(f"{base}/24/0/0.png")
        lines.append(report("zoom 24 (beyond QGC_MAX_MAP_ZOOM 23): 404", st == 404))

        # georeference by features
        def seg_centroid(e, n, z, cls, idx, span=1):
            """Centroid (n, e) of the pixels of (cls, idx) in the seg tiles around QGC's pixel of the point."""
            la, lo = [v / 1e7 for v in origin.latlon_e7(n, e)]
            X, Y = geo.global_pixel(la, lo, z)
            tx, ty = int(X // 256), int(Y // 256)
            pts = []
            for dy in range(-span, span + 1):
                for dx in range(-span, span + 1):
                    st, body, _ = fetch(f"{base}/seg/{z}/{tx + dx}/{ty + dy}.png")
                    s = np.asarray(Image.open(io.BytesIO(body)).convert("RGB"))
                    ii, jj = np.nonzero((s[..., 0] == cls) & (s[..., 1] == idx))
                    pts += list(zip(256 * (ty + dy) + ii + 0.5, 256 * (tx + dx) + jj + 0.5))
            if not pts:
                return None, 0
            Y_, X_ = np.array(pts).mean(0)
            la2, lo2 = geo.pixel_latlon(X_, Y_, z)
            n2, e2 = origin.ne(la2, lo2)
            return np.array([float(e2), float(n2)]), len(pts)

        open_b = [k for k, b in enumerate(g.boulders) if not b.wall]
        kb = max(open_b, key=lambda k: g.boulders[k].size)
        b = g.boulders[kb]
        fires = [k for k, f in enumerate(g.firebrands) if not f.hidden][:1] + [k for k, f in enumerate(g.firebrands) if f.hidden][:1]
        feats = [(f"boulder {kb} ({b.size:.2f} m, in the open)", silhouette_centroid(b.verts[b.faces]), 2, kb)]
        for kf in fires:
            (av, af), (ev, ef, _) = g.fire_meshes(kf)
            kind = "hidden" if g.firebrands[kf].hidden else "open"
            feats.append((f"firebrand {kf} ({kind}) embers", silhouette_centroid(ev[ef]), 4, kf))
            feats.append((f"firebrand {kf} ({kind}) ash bed", None, 3, kf))
        for z in (23, 21):
            for name, ref, cls, idx in feats:
                if ref is None:              # the ash bed as seen: its disk minus the embers on it
                    (av, af), _ = g.fire_meshes(idx)
                    ref = silhouette_centroid(av[af])
                    tol_note = " (embers on it hide part of the disk)"
                else:
                    tol_note = ""
                got, npx = seg_centroid(ref[0], ref[1], z, cls, idx)
                mpp = geo.meters_per_pixel(lat0, z)
                if got is None:
                    lines.append(report(f"zoom {z}: {name} seen in the tiles", False))
                    continue
                err = np.linalg.norm(got - ref) * 100
                tol = (2.0 if cls != 3 else 6.0) if z == 23 else 100 * mpp
                lines.append(report(f"zoom {z}: {name}: centroid in the tiles vs the world{tol_note}", err <= tol,
                                    f"error {err:.2f} cm (tolerance {tol:.1f} cm; {npx} px of {mpp * 100:.2f} cm)"))
        # the start: arithmetic chain
        la, lo = [v / 1e7 for v in origin.latlon_e7(start[1], start[0])]
        X, Y = geo.global_pixel(la, lo, 23)
        tx, ty = int(X // 256), int(Y // 256)
        n, e = TS.Tiles._coords(SimpleNamespace(origin=origin), 23, tx, ty)
        px, py = X - 256 * tx - 0.5, Y - 256 * ty - 0.5
        e_s, n_s = np.interp(px, np.arange(256), e), np.interp(py, np.arange(256), n)
        err = math.hypot(e_s - start[0], n_s - start[1]) * 100
        lines.append(report("the start (the origin): true position -> toLatLon integers -> QGC pixel at zoom 23 -> server position",
                            err <= 1.0, f"error {err:.2f} cm"))
        end = g.path[-1]                         # the same chain for the landing point, 72 m north, where the integers round
        la, lo = [v / 1e7 for v in origin.latlon_e7(end[1], end[0])]
        X, Y = geo.global_pixel(la, lo, 23)
        tx, ty = int(X // 256), int(Y // 256)
        n, e = TS.Tiles._coords(SimpleNamespace(origin=origin), 23, tx, ty)
        px, py = X - 256 * tx - 0.5, Y - 256 * ty - 0.5
        err = math.hypot(np.interp(px, np.arange(256), e) - end[0], np.interp(py, np.arange(256), n) - end[1]) * 100
        lines.append(report("the landing point: the same chain", err <= 1.0,
                            f"error {err:.2f} cm (the integers' rounding: up to 0.56 cm north, 0.71 cm east)"))

        # mosaics
        def mosaic(z, tx0, ty0, nx, ny, name):
            im = Image.new("RGB", (256 * nx, 256 * ny))
            for j in range(ny):
                for i in range(nx):
                    st, body, _ = fetch(f"{base}/{z}/{tx0 + i}/{ty0 + j}.png")
                    im.paste(Image.open(io.BytesIO(body)).convert("RGB"), (256 * i, 256 * j))
            im.save(out / name)
            return out / name
        x0, x1 = g.grid[..., 0].min(), g.grid[..., 0].max()
        la_n, lo_w = [v / 1e7 for v in origin.latlon_e7(g.grid[..., 1].max(), x0)]
        la_s, lo_e = [v / 1e7 for v in origin.latlon_e7(g.grid[..., 1].min(), x1)]
        z = 20
        tx0, ty0 = geo.long2tileX(lo_w, z), geo.lat2tileY(la_n, z)
        tx1, ty1 = geo.long2tileX(lo_e, z), geo.lat2tileY(la_s, z)
        p1 = mosaic(z, tx0, ty0, tx1 - tx0 + 1, ty1 - ty0 + 1, "mosaic-z20.png")
        f = g.firebrands[fires[0]]
        la, lo = [v / 1e7 for v in origin.latlon_e7(f.center[1], f.center[0])]
        p2 = mosaic(23, geo.long2tileX(lo, 23) - 1, geo.lat2tileY(la, 23) - 1, 3, 3, f"mosaic-z23-firebrand{fires[0]}.png")
        lines.append(f"      mosaics: {p1} ({tx1 - tx0 + 1} x {ty1 - ty0 + 1} tiles), {p2}")
        st, body, _ = fetch(base + "/stats")
        lines.append(f"      server: {body.decode()}")
    finally:
        srv.terminate()
        srv.wait(10)
    n_ok = sum(ok for _, ok in RESULTS)
    lines.append(f"{n_ok}/{len(RESULTS)} passed")
    print(lines[-1])
    (out / "report.txt").write_text("\n".join(lines) + "\n")
    return 0 if n_ok == len(RESULTS) else 1


if __name__ == "__main__":
    sys.exit(main())
