"""Map tiles of the gorge for QGroundControl: an XYZ (Web Mercator) tile server on 127.0.0.1.

    python tile_server.py [--port 8765] [--params FILE ... | --origin LAT LON ALT] [--gorge-seed 7] [--res 0.015]

Serves GET /{z}/{x}/{y}.png (256 x 256 PNG, zoom 0 to 23), the URL form of QGroundControl's provider
"CustomURL Custom" (src/QtLocationPlugin/Providers/GenericMapProvider.cpp: the setting
appSettings.customURL with {x}, {y}, {z} replaced): http://127.0.0.1:8765/{z}/{x}/{y}.png.

The picture: a top-down rendering of the generated gorge (terrain with its baked textures, boulders,
ash beds and embers; gorge.py's assets, nothing else) made once at start with PyBullet's TinyRenderer:
TinyRenderer has no orthographic projection, so each 1024 x 1024 chunk is rendered by a camera
20 km straight above the chunk's center with a field of view of one chunk (parallax: a point z m above
z = 0 at d m from the chunk center is drawn d z / 20000 m off, at most 1.2 cm at the rim). Diffuse light
from the world's sun direction (cast shadows are baked into the textures); ember pixels get their glow
color (gorge.ember_rgb) and a small bloom, as sensors.glow does. The raster is RES m per pixel
(default 0.015 m: zoom 23 at the latitude of Pikes Peak is 1.45 cm per pixel) with box-filtered
mipmaps. Outside the terrain, and on every tile beyond it, a uniform neutral color (BACKGROUND).

Georeference (geo.py): a tile pixel's center (256 x + px + 0.5, 256 y + py + 0.5) is turned into
latitude and longitude with QGroundControl's Web Mercator formulas (MapProvider.cpp tileX2long,
tileY2lat in their fractional form), then into the local north and east with the controller's own
flat-earth conversion from the run's ORIGIN (Format.lean toNE), and sampled from the raster
(bilinear, in the mipmap level whose pixel is closest to the tile's from below). So a world point is
drawn where QGroundControl draws a vehicle that the controller reports at that point.

Also: GET /seg/{z}/{x}/{y}.png (nearest sample of the class raster: R = class 0 background, 1 terrain,
2 boulder, 3 ash, 4 ember; G = index) for the georeference test, and GET /stats (requests served).
"""
import argparse
import io
import json
import math
import re
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import numpy as np
import pybullet as p
from PIL import Image
from scipy.ndimage import gaussian_filter

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE))
import geo  # noqa: E402
import gorge as G  # noqa: E402

BACKGROUND = np.array([138, 132, 118], np.uint8)     # neutral gray-beige, a little darker than the plateau
CHUNK, HEIGHT = 1024, 20000.0
CLASS = {"terrain": 1, "boulder": 2, "ash": 3, "ember": 4}


def render_raster(g, res):
    """Top-down RGB raster and class/index raster of the gorge; (rgb, cls, idx, x0, y1)."""
    c = p.connect(p.DIRECT)
    bodies = g.load(c, "visual")
    x0, x1 = g.grid[..., 0].min(), g.grid[..., 0].max()
    y0, y1 = g.grid[..., 1].min(), g.grid[..., 1].max()
    W, H = int(math.ceil((x1 - x0) / res)), int(math.ceil((y1 - y0) / res))
    rgb = np.empty((H, W, 3), np.uint8)
    cls = np.zeros((H, W), np.uint8)
    idx = np.zeros((H, W), np.uint8)
    lut_c, lut_i = np.zeros(max(bodies) + 2, np.uint8), np.zeros(max(bodies) + 2, np.uint8)   # index: body id + 1
    for b, (k, i) in bodies.items():
        lut_c[b + 1], lut_i[b + 1] = CLASS[k], i
    ember = {b: G.ember_rgb(g.firebrands[i].temp_c) for b, (k, i) in bodies.items() if k == "ember"}
    half = CHUNK * res / 2
    fov = 2 * math.degrees(math.atan(half / HEIGHT))
    proj = p.computeProjectionMatrixFOV(fov, 1.0, HEIGHT - 80.0, HEIGHT + 20.0, physicsClientId=c)
    for r0 in range(0, H, CHUNK):
        for c0 in range(0, W, CHUNK):
            cx, cy = x0 + (c0 + CHUNK / 2) * res, y1 - (r0 + CHUNK / 2) * res
            view = p.computeViewMatrix([cx, cy, HEIGHT], [cx, cy, 0.0], [0, 1, 0], physicsClientId=c)
            _, _, im, _, seg = p.getCameraImage(CHUNK, CHUNK, view, proj, renderer=p.ER_TINY_RENDERER, shadow=0,
                                                lightDirection=G.SUN.tolist(), physicsClientId=c)
            im = np.reshape(im, (CHUNK, CHUNK, 4))[..., :3].astype(float)
            seg = np.reshape(seg, (CHUNK, CHUNK))
            em = np.zeros_like(im)
            for b, col in ember.items():
                m = seg == b
                im[m] = col
                em[m] = col
            if em.any():
                im += 2.0 * np.stack([gaussian_filter(em[..., k], 2.0) for k in range(3)], -1)
            im[seg < 0] = BACKGROUND
            h, w = min(CHUNK, H - r0), min(CHUNK, W - c0)
            rgb[r0:r0 + h, c0:c0 + w] = np.clip(im[:h, :w], 0, 255)
            s = seg[:h, :w]
            cls[r0:r0 + h, c0:c0 + w] = lut_c[s + 1]
            idx[r0:r0 + h, c0:c0 + w] = lut_i[s + 1]
    p.disconnect(c)
    return rgb, cls, idx, float(x0), float(y1)


class Tiles:
    def __init__(self, g, origin, res):
        t0 = time.time()
        self.origin, self.res = origin, res
        rgb, self.cls, self.idx, self.x0, self.y1 = render_raster(g, res)
        self.levels = [rgb]
        while min(self.levels[-1].shape[:2]) > 64:
            a = self.levels[-1].astype(np.float32)
            h, w = a.shape[0] // 2 * 2, a.shape[1] // 2 * 2
            self.levels.append(((a[:h:2, :w:2] + a[1:h:2, :w:2] + a[:h:2, 1:w:2] + a[1:h:2, 1:w:2]) / 4 + 0.5).astype(np.uint8))
        self.served, self.lock = {}, threading.Lock()
        buf = io.BytesIO()
        Image.fromarray(np.broadcast_to(BACKGROUND, (256, 256, 3)).copy()).save(buf, "PNG")
        self.blank = buf.getvalue()
        self.build_s = time.time() - t0

    def _coords(self, z, x, y):
        """North (per tile row) and east (per tile column) of the tile's pixel centers."""
        k = np.arange(256) + 0.5
        lat, _ = geo.pixel_latlon(0.0, 256 * y + k, z)
        _, lon = geo.pixel_latlon(256 * x + k, 0.0, z)
        n, _ = self.origin.ne(lat, self.origin.lon_e7 / 1e7)
        _, e = self.origin.ne(self.origin.lat_e7 / 1e7, lon)
        return np.asarray(n), np.asarray(e)

    def tile(self, z, x, y, seg=False):
        n, e = self._coords(z, x, y)
        H, W = self.cls.shape
        if e[-1] < self.x0 or e[0] > self.x0 + W * self.res or n[0] < self.y1 - H * self.res or n[-1] > self.y1:
            return self.blank if not seg else self._png(np.zeros((256, 256, 3), np.uint8))
        if seg:
            i = np.floor((self.y1 - n) / self.res).astype(int)
            j = np.floor((e - self.x0) / self.res).astype(int)
            vi, vj = (i >= 0) & (i < H), (j >= 0) & (j < W)
            out = np.zeros((256, 256, 3), np.uint8)
            ii, jj = np.clip(i, 0, H - 1), np.clip(j, 0, W - 1)
            out[..., 0] = self.cls[ii][:, jj] * (vi[:, None] & vj[None, :])
            out[..., 1] = self.idx[ii][:, jj] * (vi[:, None] & vj[None, :])
            return self._png(out)
        mpp = abs(e[1] - e[0])
        L = int(np.clip(math.floor(math.log2(max(mpp / self.res, 1.0))), 0, len(self.levels) - 1))
        img, r = self.levels[L], self.res * 2 ** L
        h, w = img.shape[:2]
        fi, fj = (self.y1 - n) / r - 0.5, (e - self.x0) / r - 0.5
        i0, j0 = np.floor(fi).astype(int), np.floor(fj).astype(int)
        wi, wj = (fi - i0)[:, None, None], (fj - j0)[None, :, None]
        a = lambda ii, jj: img[np.clip(ii, 0, h - 1)][:, np.clip(jj, 0, w - 1)].astype(np.float32)
        out = ((1 - wi) * ((1 - wj) * a(i0, j0) + wj * a(i0, j0 + 1)) + wi * ((1 - wj) * a(i0 + 1, j0) + wj * a(i0 + 1, j0 + 1)))
        inside = ((fi >= -0.5) & (fi <= h - 0.5))[:, None] & ((fj >= -0.5) & (fj <= w - 0.5))[None, :]
        out = np.where(inside[..., None], out + 0.5, BACKGROUND).astype(np.uint8)
        return self._png(out)

    @staticmethod
    def _png(a):
        buf = io.BytesIO()
        Image.fromarray(a).save(buf, "PNG", compress_level=1)
        return buf.getvalue()


def serve(tiles, port, log=None):
    pat = re.compile(r"^/(seg/)?(\d+)/(\d+)/(\d+)\.png$")

    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path == "/stats":
                with tiles.lock:
                    body = json.dumps({"served": sum(tiles.served.values()), "by_zoom": tiles.served}).encode()
                return self._reply(200, "application/json", body)
            m = pat.match(self.path.split("?", 1)[0])
            if not m:
                return self._reply(404, "text/plain", b"not found\n")
            z, x, y = int(m[2]), int(m[3]), int(m[4])
            if z > geo.MAX_ZOOM or x >= 2 ** z or y >= 2 ** z:
                return self._reply(404, "text/plain", b"no such tile\n")
            body = tiles.tile(z, x, y, seg=bool(m[1]))
            with tiles.lock:
                tiles.served[z] = tiles.served.get(z, 0) + 1
            if log:
                log.write(f"{time.time():.3f} {self.client_address[0]} {self.path}\n")
            self._reply(200, "image/png", body)

        def _reply(self, code, ctype, body):
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def log_message(self, *a):
            pass

    ThreadingHTTPServer.daemon_threads = True
    srv = ThreadingHTTPServer(("127.0.0.1", port), Handler)
    srv.serve_forever()


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--port", type=int, default=8765)
    ap.add_argument("--params", action="append", default=None, help="parameter files with the ORIGIN line")
    ap.add_argument("--origin", nargs=3, default=None, metavar=("LAT", "LON", "ALT"))
    ap.add_argument("--gorge-seed", type=int, default=7)
    ap.add_argument("--res", type=float, default=0.015, help="raster resolution, m per pixel")
    ap.add_argument("--log", default=None, help="request log")
    a = ap.parse_args()
    origin = geo.Origin.from_params(a.params or [ROOT / "params/x500.params", ROOT / "params/ground.params"], a.origin)
    g = G.Gorge(a.gorge_seed)
    g.write_assets()
    tiles = Tiles(g, origin, a.res)
    h, w = tiles.cls.shape
    print(f"tile server: http://127.0.0.1:{a.port}/{{z}}/{{x}}/{{y}}.png  (gorge seed {g.seed}, raster {w} x {h} at "
          f"{a.res * 100:.2f} cm, {len(tiles.levels)} levels, built in {tiles.build_s:.1f} s; origin {origin.lat_e7} "
          f"{origin.lon_e7})", flush=True)
    serve(tiles, a.port, open(a.log, "a", buffering=1) if a.log else None)


if __name__ == "__main__":
    main()
