"""A procedural mountain gorge with boulders, vegetation and firebrands, deterministic from a seed.

World frame: ENU (x east, y north, z up, meters), as PyBullet. The gorge axis runs north from the
origin with a gentle meander; the floor at the origin is at z ~ 0.

Construction (all generated here, nothing loaded from elsewhere):
- centerline x_c(y), two sines scaled so the axis stays within MAX_HEADING_DEG of north;
- floor width W(y) between 4 and 9 m with two Gaussian narrows; floor height f(y) rising 3.5 % up
  the gorge, with a shallow channel and noise across;
- walls built from horizontal strata: each layer is hard (cliff 80-88 deg, with a bench on top when
  the layer above is soft) or soft (slope 65-74 deg); the wall profile (horizontal distance from the
  toe vs height) is the stack of layers from the floor to the rim (15-25 m above the floor), with
  bench widths and angles varying along the axis; roughness by small vertex displacements;
- the terrain is one triangle mesh on a grid that is sheared to follow the centerline: rows at
  constant y, columns at lateral offsets (floor: fraction of the half width; walls and plateau:
  distance from the toe), so the grid never folds;
- a texture whose texels are colored from the 3D point they cover (strata by height, gravel floor,
  vegetation on benches, floor edges and plateau), with cast shadows baked in from ray tests toward
  the sun; a second texture with the same layout encodes each texel's surface temperature and
  emissivity for the thermal camera (sensors.py);
- boulders: deformed, flattened icospheres (static convex bodies), rejected if they would enter the
  flight corridor;
- firebrands: a cluster of ember pieces on a disk of hot ash, most placed just behind a boulder as
  seen from the approach path.

Run `python gorge.py [--seed N]` to build, write the assets to assets/ and print the world summary.
"""
import argparse
import math
import os
import sys
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np
import pybullet as p
from PIL import Image
from scipy.ndimage import gaussian_filter, map_coordinates

HERE = Path(__file__).resolve().parent
ASSETS = HERE / "assets"

# --- layout ------------------------------------------------------------------------------------
Y0, Y1, ROW_DY = -12.0, 92.0, 0.8          # terrain rows (m north); the flight is y in [0, Y_END]
Y_END = 72.0
MAX_HEADING_DEG = 22.0
XI_PLATEAU = np.array([0.0, 1.5, 4.0, 8.0, 13.0, 19.0])          # plateau columns: distance beyond the rim
ETA_FLOOR = np.linspace(-1, 1, 15)[1:-1]                           # floor interior columns (fraction of W/2)
TEX_W, TEX_H = 1536, 1024
FLIGHT_H = 3.5                             # m above the floor along the centerline
CORRIDOR_HALF, CORRIDOR_Z = 1.25, (3.0, 4.0)

# --- sun and temperatures ----------------------------------------------------------------------
SUN_AZ_DEG, SUN_EL_DEG = 225.0, 55.0       # from the south-west, mid afternoon
SUN = np.array([math.sin(math.radians(SUN_AZ_DEG)) * math.cos(math.radians(SUN_EL_DEG)),
                math.cos(math.radians(SUN_AZ_DEG)) * math.cos(math.radians(SUN_EL_DEG)),
                math.sin(math.radians(SUN_EL_DEG))])               # unit vector toward the sun
T_AIR_C = 30.0
# surface classes: temperature in full shade and at normal incidence in full sun (deg C), emissivity
CLASSES = {
    "floor":     dict(shade=29.0, sun=47.0, emis=0.93),   # gravel and sand
    "rock":      dict(shade=28.0, sun=50.0, emis=0.93),   # sandstone / limestone walls, boulders
    "veg":       dict(shade=27.0, sun=32.0, emis=0.97),   # green shrubs and grass (transpiring)
    "plateau":   dict(shade=30.0, sun=44.0, emis=0.95),   # dry grass and scrub above the rim
    "ash":       dict(shade=150.0, sun=150.0, emis=0.95),  # hot ash bed under a spot fire
    "ember":     dict(shade=None, sun=None, emis=0.90),    # per firebrand, 600-900 deg C
}
CLASS_ID = {k: i for i, k in enumerate(CLASSES)}
T_ENC_MIN, T_ENC_SPAN = 200.0, 1100.0      # K: 16-bit temperature code in R (high) and G (low)


# ------------------------------------------------------------------------------------------------
# noise


class Field2:
    """Smooth unit-variance noise on a periodic grid over a rectangle, sampled bilinearly."""

    def __init__(self, rng, lo, hi, cell, sigma_m):
        self.lo, self.cell = np.asarray(lo, float), float(cell)
        n = np.maximum(np.ceil((np.asarray(hi) - lo) / cell).astype(int), 4)
        a = gaussian_filter(rng.normal(size=n), sigma_m / cell, mode="wrap")
        self.a = a / a.std()

    def __call__(self, u, v):
        c = np.stack([(np.asarray(u) - self.lo[0]) / self.cell, (np.asarray(v) - self.lo[1]) / self.cell])
        return map_coordinates(self.a, c.reshape(2, -1), order=1, mode="grid-wrap").reshape(np.shape(u))


def noise1(rng, y, scale, n=6):
    """Smooth unit-amplitude 1D noise: a few sines with random phases, wavelengths around `scale`."""
    out = np.zeros_like(y, dtype=float)
    for k in range(n):
        lam = scale * rng.uniform(0.5, 1.5) / (1 + 0.5 * k)
        out += rng.uniform(0.5, 1.0) / (1 + k) * np.sin(2 * np.pi * y / lam + rng.uniform(0, 2 * np.pi))
    return out / np.abs(out).max()


def icosphere(subdiv):
    t = (1 + 5 ** 0.5) / 2
    v = [[-1, t, 0], [1, t, 0], [-1, -t, 0], [1, -t, 0], [0, -1, t], [0, 1, t], [0, -1, -t], [0, 1, -t],
         [t, 0, -1], [t, 0, 1], [-t, 0, -1], [-t, 0, 1]]
    f = [[0, 11, 5], [0, 5, 1], [0, 1, 7], [0, 7, 10], [0, 10, 11], [1, 5, 9], [5, 11, 4], [11, 10, 2],
         [10, 7, 6], [7, 1, 8], [3, 9, 4], [3, 4, 2], [3, 2, 6], [3, 6, 8], [3, 8, 9], [4, 9, 5], [2, 4, 11],
         [6, 2, 10], [8, 6, 7], [9, 8, 1]]
    v = [np.array(x, float) / np.linalg.norm(x) for x in v]
    for _ in range(subdiv):
        cache, nf = {}, []
        def mid(a, b):
            k = (min(a, b), max(a, b))
            if k not in cache:
                m = v[a] + v[b]
                v.append(m / np.linalg.norm(m))
                cache[k] = len(v) - 1
            return cache[k]
        for a, b, c in f:
            ab, bc, ca = mid(a, b), mid(b, c), mid(c, a)
            nf += [[a, ab, ca], [b, bc, ab], [c, ca, bc], [ab, bc, ca]]
        f = nf
    return np.array(v), np.array(f)


def blob(rng, radius, axes, subdiv, rough):
    """A deformed icosphere: radial noise from random plane waves, scaled by axes, random yaw."""
    v, f = icosphere(subdiv)
    d = np.zeros(len(v))
    for _ in range(5):
        k = rng.normal(size=3) * rng.uniform(1.0, 3.0)
        d += np.sin(v @ k + rng.uniform(0, 2 * np.pi)) / 5
    v = v * (1 + rough * d)[:, None] * radius * np.asarray(axes)
    a = rng.uniform(0, 2 * np.pi)
    Rz = np.array([[math.cos(a), -math.sin(a), 0], [math.sin(a), math.cos(a), 0], [0, 0, 1]])
    return v @ Rz.T, f


def encode_temperature(t_k, emis):
    code = np.clip(np.round((np.asarray(t_k) - T_ENC_MIN) / T_ENC_SPAN * 65535), 0, 65535).astype(np.int64)
    return np.stack([code >> 8, code & 255, np.round(np.asarray(emis) * 255 + 0 * code)], -1).astype(np.uint8)


def decode_temperature(rgb):
    rgb = np.asarray(rgb, dtype=np.float64)
    return T_ENC_MIN + (rgb[..., 0] * 256 + rgb[..., 1]) / 65535 * T_ENC_SPAN, rgb[..., 2] / 255


def surface_temperature(cls, insolation, jitter):
    c = CLASSES[cls]
    return c["shade"] + (c["sun"] - c["shade"]) * insolation + jitter


def ember_rgb(t_c):
    """Display color of glowing char at t_c deg C: dull red at 600, orange-yellow at 900 (a few
    hand-chosen control points, not a measured blackbody color)."""
    x = np.clip((np.asarray(t_c, float) - 600) / 300, 0, 1)[..., None]
    return np.clip((1 - x) * np.array([190, 45, 12]) + x * np.array([255, 165, 40]), 0, 255)


# ------------------------------------------------------------------------------------------------
# world objects


@dataclass
class Boulder:
    center: np.ndarray        # m, ENU, the blob's center
    size: float               # m, largest horizontal extent
    height: float             # m, top above the local ground
    top: float                # m, z of the top
    verts: np.ndarray         # world vertices
    faces: np.ndarray
    wall: bool                # placed against a wall


@dataclass
class Firebrand:
    center: np.ndarray        # m, ENU on the ground
    radius: float             # m, radius of the ash bed (the fire's size)
    temp_c: float             # deg C, hottest ember
    hidden: bool              # placed behind a boulder as seen from the approach
    boulder: int              # index of the hiding boulder, -1 if in the open
    pieces: list = field(default_factory=list)   # (center, radius, temp_c) of each ember piece


# ------------------------------------------------------------------------------------------------
# the gorge


class Gorge:
    def __init__(self, seed=7):
        self.seed = seed
        rng = np.random.default_rng(seed)
        self.rng = rng
        self._axis(rng)
        self._terrain(rng)
        self.path = self.flight_path()
        self._client = p.connect(p.DIRECT)          # scratch client for ray tests during the build
        ASSETS.mkdir(parents=True, exist_ok=True)       # (large meshes load from a file only)
        self.terrain_obj = write_obj(ASSETS / f"terrain_s{seed}.obj", self.V, self.F, self.UV, self.normals.reshape(-1, 3))
        self.terrain_id = p.createMultiBody(0, p.createCollisionShape(
            p.GEOM_MESH, fileName=self.terrain_obj, flags=p.GEOM_FORCE_CONCAVE_TRIMESH,
            physicsClientId=self._client), physicsClientId=self._client)
        self._boulders(rng)
        self._textures(rng)
        self._firebrands(rng)

    # --- axis -----------------------------------------------------------------------------------
    def _axis(self, rng):
        y = np.arange(Y0, Y1 + 1e-9, ROW_DY)
        a1, l1, ph1 = 3.6, rng.uniform(55, 70), rng.uniform(0, 2 * np.pi)
        a2, l2, ph2 = 1.0, rng.uniform(24, 32), rng.uniform(0, 2 * np.pi)
        f = lambda yy: a1 * np.sin(2 * np.pi * yy / l1 + ph1) + a2 * np.sin(2 * np.pi * yy / l2 + ph2)
        fine = np.linspace(Y0, Y1, 4000)
        slope = np.abs(np.gradient(f(fine), fine)).max()
        k = min(1.0, math.tan(math.radians(MAX_HEADING_DEG)) / slope)
        self.xc_fn = lambda yy: k * (f(yy) - f(0.0))
        self.y = y
        self.xc = self.xc_fn(y)
        self.theta = np.arctan(np.gradient(self.xc, y))             # heading east of north (rad)
        # width: base 7 m with slow noise, two narrows
        yn = (rng.uniform(20, 28), rng.uniform(46, 56))
        w = 7.2 + 1.3 * noise1(rng, y, 30.0)
        for yc, wmin in zip(yn, (4.2, 4.6)):
            g = np.exp(-0.5 * ((y - yc) / 3.5) ** 2)
            w = w * (1 - g) + wmin * g
        self.width = np.clip(w, 4.0, 9.0)
        self.narrows = yn
        self.floor0 = 0.035 * y + 0.35 * noise1(rng, y, 18.0)
        self.floor0 -= np.interp(0.0, y, self.floor0)
        self.height = {s: np.clip(20 + 4.5 * noise1(rng, y, 40.0), 15.5, 24.5) for s in (-1, 1)}

    def floor_c(self, y):
        """Floor height on the centerline (z of the mesh's mid column, m)."""
        return np.interp(y, self.y, self.zc)

    def width_at(self, y):
        return np.interp(y, self.y, self.width)

    def axis_dir(self, y):
        th = np.interp(y, self.y, self.theta)
        return np.stack([np.sin(th), np.cos(th), np.zeros_like(th)], -1)

    def lateral(self, x, y):
        """Signed horizontal distance from the centerline (east positive), perpendicular to the axis."""
        return (np.asarray(x) - self.xc_fn(np.asarray(y))) * np.cos(np.interp(y, self.y, self.theta))

    # --- terrain ----------------------------------------------------------------------------------
    def _terrain(self, rng):
        y, NR = self.y, len(self.y)
        # strata: global horizontal layers
        z, layers = -8.0, []
        while z < 45:
            th = rng.uniform(0.8, 2.6)
            hard = rng.random() < 0.45
            layers.append(dict(z0=z, z1=z + th, hard=hard,
                               ang=rng.uniform(80, 88) if hard else rng.uniform(65, 74),
                               bench=rng.uniform(0.3, 1.2) if hard else 0.0,
                               color=rng.integers(0, 6)))
            z += th
        for a, b in zip(layers, layers[1:]):
            if not (a["hard"] and not b["hard"]):
                a["bench"] = 0.0
        self.layers = layers
        self.strata_z = np.array([L["z1"] for L in layers])
        self.n_floor = Field2(rng, (-40, Y0 - 5), (40, Y1 + 5), 0.25, 1.2)
        self.n_rough = {s: Field2(rng, (Y0 - 5, -10), (Y1 + 5, 50), 0.25, 0.6) for s in (-1, 1)}
        bench_var = {s: [0.5 + 0.9 * (noise1(rng, y, 15.0) * 0.5 + 0.5) for _ in layers] for s in (-1, 1)}
        ang_var = {s: [3.0 * noise1(rng, y, 20.0) for _ in layers] for s in (-1, 1)}

        # wall columns are height levels (every stratum top, every bench's outer edge, and steps of
        # at most 0.7 m within thick layers), so stratum boundaries follow mesh edges; a level below the
        # floor edge or above the rim of a row collapses onto the toe or the rim (degenerate faces dropped)
        zlo = self.floor0.min() - 0.5
        zhi = max((self.floor0 + self.height[s]).max() for s in (-1, 1)) + 0.5
        lv = []
        for L in layers:
            n = int(np.ceil((L["z1"] - L["z0"]) / 0.7))
            lv += list(L["z0"] + (L["z1"] - L["z0"]) * np.arange(1, n + 1) / n)
            if L["bench"]:
                lv.append(L["z1"] + 0.04)
        levels = np.array(sorted(z for z in lv if zlo < z < zhi))
        cols = ([(-1, "plat", d) for d in XI_PLATEAU[::-1]] + [(-1, "wall", z) for z in levels[::-1]] + [(-1, "toe", 0.0)]
                + [(0, "floor", e) for e in ETA_FLOOR]
                + [(1, "toe", 0.0)] + [(1, "wall", z) for z in levels] + [(1, "plat", d) for d in XI_PLATEAU])
        NC = len(cols)
        U, Z = np.zeros((NR, NC)), np.zeros((NR, NC))
        kind = np.array([{"floor": 0, "toe": 1, "wall": 1, "plat": 2}[c[1]] for c in cols])
        half = self.width / 2
        self.rim_xi, self.rim_z = {}, {}
        for i in range(NR):
            f0 = self.floor0[i]
            for j, (s, kd, c) in enumerate(cols):
                if kd == "floor":
                    U[i, j] = c * half[i]
                    Z[i, j] = f0 - 0.3 * (1 - c * c) + 0.12 * self.n_floor(np.array(c * half[i] + self.xc[i]), np.array(y[i]))
            for s in (-1, 1):
                edge = f0 + 0.12 * self.n_floor(np.array(s * half[i] + self.xc[i]), np.array(y[i]))
                rim = f0 + self.height[s][i]
                xs, zs = [0.0], [edge]
                for L, ly in enumerate(layers):
                    lo, hi = max(ly["z0"], zs[-1]), min(ly["z1"], rim)
                    if hi <= lo:
                        continue
                    ang = math.radians(ly["ang"] + ang_var[s][L][i])
                    xs.append(xs[-1] + max((hi - lo) / math.tan(ang), 0.02)); zs.append(hi)
                    if ly["bench"] and hi < rim - 0.5:
                        xs.append(xs[-1] + ly["bench"] * bench_var[s][L][i]); zs.append(hi + 0.04)
                xs, zs = np.array(xs), np.array(zs)
                self.rim_xi[(s, i)], self.rim_z[(s, i)] = xs[-1], zs[-1]
                for j, (ss, kd, c) in enumerate(cols):
                    if ss != s:
                        continue
                    if kd == "plat":
                        xi = xs[-1] + c - XI_PLATEAU[0] + 0.6
                        zz = rim + 0.04 * (xi - xs[-1]) + 0.35 * min(1.0, (xi - xs[-1]) / 3) * self.n_floor(
                            np.array(s * (half[i] + xi) + self.xc[i]), np.array(y[i]))
                    elif kd == "toe" or c <= edge:
                        xi, zz = 0.0, edge
                    elif c >= rim:
                        xi, zz = xs[-1], rim
                    else:
                        xi, zz = np.interp(c, zs, xs) + 0.08 * self.n_rough[s](np.array(y[i]), np.array(c)), c
                    U[i, j], Z[i, j] = s * (half[i] + xi), zz
        X = self.xc[:, None] + U / np.cos(self.theta)[:, None]
        Y = np.repeat(y[:, None], NC, 1)
        self.grid = np.stack([X, Y, Z], -1)            # NR x NC x 3
        self.cols, self.col_kind, self.U = cols, kind, U
        self.zc = Z[:, cols.index((0, "floor", ETA_FLOOR[len(ETA_FLOOR) // 2]))]
        self.wall_angle = {s: np.degrees(np.arctan2(self.height[s], np.array([self.rim_xi[(s, i)] for i in range(NR)])))
                           for s in (-1, 1)}
        # mesh: two triangles per grid quad, counterclockwise seen from above; zero-area faces dropped
        idx = np.arange(NR * NC).reshape(NR, NC)
        a, b, c_, d = idx[:-1, :-1], idx[:-1, 1:], idx[1:, :-1], idx[1:, 1:]
        F = np.concatenate([np.stack([a, b, d], -1).reshape(-1, 3), np.stack([a, d, c_], -1).reshape(-1, 3)])
        self.V = self.grid.reshape(-1, 3)
        fn = np.cross(self.V[F[:, 1]] - self.V[F[:, 0]], self.V[F[:, 2]] - self.V[F[:, 0]])
        area = np.linalg.norm(fn, axis=1) / 2
        self.F = F[area > 1e-5]
        ii, jj = np.meshgrid(np.arange(NR), np.arange(NC), indexing="ij")
        self.UV = np.stack([jj.ravel() / (NC - 1), ii.ravel() / (NR - 1)], -1)
        vn = np.zeros_like(self.V)
        for k in range(3):
            np.add.at(vn, F[:, k], fn)
        ln = np.linalg.norm(vn, axis=1, keepdims=True)
        vn = np.where(ln > 1e-9, vn / np.maximum(ln, 1e-12), [0, 0, 1.0])
        self.normals = vn.reshape(NR, NC, 3)

    # --- flight path -------------------------------------------------------------------------------
    def flight_path(self, height=FLIGHT_H, max_dev=0.35, max_leg=10.0):
        """Waypoints (ENU) along the centerline at `height` above the floor from y = 0 to Y_END: greedy,
        each leg as long as possible up to max_leg with the centerline within max_dev of the chord."""
        ys = np.linspace(0, Y_END, 721)
        pts = np.stack([self.xc_fn(ys), ys, self.floor_c(ys) + height], -1)
        out, k = [pts[0]], 0
        while k < len(pts) - 1:
            best = k + 1
            for m in range(k + 1, len(pts)):
                a, b = pts[k], pts[m]
                if np.linalg.norm(b - a) > max_leg:
                    break
                seg = pts[k:m + 1]
                t = np.clip((seg - a) @ (b - a) / ((b - a) @ (b - a)), 0, 1)
                if np.linalg.norm(seg - (a + t[:, None] * (b - a)), axis=1).max() <= max_dev:
                    best = m
            out.append(pts[best]); k = best
        return np.array(out)

    def path_points(self, step=0.1, path=None):
        path = self.path if path is None else path
        segs = [np.linspace(a, b, max(2, int(np.ceil(np.linalg.norm(b - a) / step)) + 1))[:-1] for a, b in zip(path, path[1:])]
        return np.concatenate(segs + [path[-1:]])

    # --- ray helpers (scratch client) --------------------------------------------------------------
    def rays(self, a, b):
        """Hit fraction and body of segments a -> b (N x 3) in the scratch client (terrain and boulders)."""
        a, b = np.asarray(a, float), np.asarray(b, float)
        frac, body = np.ones(len(a)), -np.ones(len(a), int)
        for k in range(0, len(a), 4000):
            res = p.rayTestBatch(a[k:k + 4000].tolist(), b[k:k + 4000].tolist(), physicsClientId=self._client)
            frac[k:k + 4000] = [r[2] if r[0] >= 0 else 1.0 for r in res]
            body[k:k + 4000] = [r[0] for r in res]
        return frac, body

    def ground_z(self, xy):
        xy = np.atleast_2d(xy)
        a = np.column_stack([xy, np.full(len(xy), 60.0)])
        b = np.column_stack([xy, np.full(len(xy), -30.0)])
        frac, _ = self.rays(a, b)
        return 60.0 - 90.0 * frac

    def sunlit(self, pts, normals, offset=0.08):
        a = pts + offset * normals
        frac, _ = self.rays(a, a + 120 * SUN)
        return (frac >= 1.0).astype(float)

    # --- boulders ------------------------------------------------------------------------------------
    def _boulders(self, rng):
        self.boulders = []
        pp = self.path_points(0.25)
        tries = 0
        n_target = int(rng.integers(20, 27))
        big = [9.0 + 8.5 * k for k in range(7)]        # large boulders first, spread along the axis
        while len(self.boulders) < n_target and tries < 4000:
            tries += 1
            if big and tries % 40 == 0:
                big.pop(0)                             # give up on a station that does not fit
            if big:
                yb, size = big[0] + rng.uniform(-2.5, 2.5), float(rng.uniform(1.7, 2.5))
            else:
                yb, size = rng.uniform(2.0, Y_END - 1), float(rng.uniform(0.5, 1.7))
            r = size / 2
            half = self.width_at(yb) / 2
            wall = rng.random() < 0.45
            side = rng.choice([-1, 1])
            u = side * (half - 0.35 * r) if wall else rng.uniform(-half + 0.6 * r, half - 0.6 * r)
            th = np.interp(yb, self.y, self.theta)
            xb = self.xc_fn(yb) + u / math.cos(th)
            v, f = blob(rng, r, (1.0, rng.uniform(0.7, 1.0), rng.uniform(0.65, 0.95)), 2, 0.22)
            ext = np.ptp(v[:, :2], axis=0).max()
            g = self.ground_z(np.array([[xb, yb]]) + v[:, :2] * 0.6).min()
            v = v + [xb, yb, g - v[:, 2].min() - 0.08 * (v[:, 2].max() - v[:, 2].min())]   # sunk by 8 %
            c = v.mean(axis=0)
            if any(np.linalg.norm(c[:2] - b.center[:2]) < (ext + b.size) / 2 + 0.3 for b in self.boulders):
                continue
            # corridor: lateral |d| <= CORRIDOR_HALF + 0.5 at height floor + 3 - 0.5 must stay free
            near = np.abs(pp[:, 1] - yb) < 4
            dxy = np.min(np.linalg.norm(v[:, None, :2] - pp[near][None, :, :2], axis=2), axis=1)
            low = pp[near][:, 2].min() - FLIGHT_H + CORRIDOR_Z[0] - 0.5
            if np.any((dxy < CORRIDOR_HALF + 0.5) & (v[:, 2] > low)):
                continue
            ground = self.ground_z(c[None, :2])[0]
            if big:
                big.pop(0)
            self.boulders.append(Boulder(center=c, size=float(ext), height=float(v[:, 2].max() - ground),
                                         top=float(v[:, 2].max()), verts=v, faces=f, wall=bool(wall)))
        self.boulder_ids = []
        for b in self.boulders:
            col = p.createCollisionShape(p.GEOM_MESH, vertices=b.verts.tolist(), physicsClientId=self._client)
            self.boulder_ids.append(p.createMultiBody(0, col, physicsClientId=self._client))

    # --- textures --------------------------------------------------------------------------------------
    def _texel_points(self):
        """3D point, normal, kind (0 floor, 1 wall, 2 plateau) and floor fraction eta of each texel,
        interpolated on the mesh's own triangles (a, b, d) and (a, d, c) of each grid quad."""
        NR, NC = self.grid.shape[:2]
        fi = ((np.arange(TEX_H) + 0.5) / TEX_H * (NR - 1))[:, None]
        fj = ((np.arange(TEX_W) + 0.5) / TEX_W * (NC - 1))[None, :]
        i0, j0 = np.minimum(fi.astype(int), NR - 2), np.minimum(fj.astype(int), NC - 2)
        ti, tj = np.broadcast_arrays(fi - i0, fj - j0)
        i0, j0 = np.broadcast_arrays(i0, j0)
        upper = (tj >= ti)[..., None]
        ti, tj = ti[..., None], tj[..., None]
        def tri(A):
            a, b, c, d = A[i0, j0], A[i0, j0 + 1], A[i0 + 1, j0], A[i0 + 1, j0 + 1]
            return np.where(upper, a + tj * (b - a) + ti * (d - b), a + ti * (c - a) + tj * (d - c))
        P, N = tri(self.grid), tri(self.normals)
        N /= np.linalg.norm(N, axis=-1, keepdims=True)
        toe = [j for j, c in enumerate(self.cols) if c[1] == "toe"]
        side = np.where(fj < toe[0], -1, 1).repeat(TEX_H, 0)
        rim = np.where(side < 0, np.interp(fi, np.arange(NR), [self.rim_z[(-1, i)] for i in range(NR)]),
                       np.interp(fi, np.arange(NR), [self.rim_z[(1, i)] for i in range(NR)]))
        floor = ((fj >= toe[0]) & (fj <= toe[1])).repeat(TEX_H, 0)
        colkind = self.col_kind[np.round(fj).astype(int)].repeat(TEX_H, 0)
        kind = np.where(floor, 0, np.where((colkind == 1) & (P[..., 2] < rim - 0.02), 1, 2))
        eta = np.clip((fj - toe[0]) / (toe[1] - toe[0]) * 2 - 1, -1, 1).repeat(TEX_H, 0)
        return P, N, kind, eta

    def _textures(self, rng):
        P, N, kind, eta = self._texel_points()
        x, y, z = P[..., 0], P[..., 1], P[..., 2]
        nveg = Field2(rng, (-40, Y0 - 5), (40, Y1 + 5), 0.2, 0.7)
        ncol = Field2(rng, (-40, Y0 - 5), (40, Y1 + 5), 0.1, 0.25)
        nstreak = Field2(rng, (-40, -12), (120, 60), 0.1, 0.5)      # (x + y, z / 6): vertical streaks
        fine = Field2(rng, (-40, Y0 - 5), (40, Y1 + 5), 0.05, 0.06)
        flat = N[..., 2]
        # classes
        veg_floor = (kind == 0) & (nveg(x, y) > 1.5 - 1.5 * np.abs(eta) ** 4)
        veg_bench = (kind == 1) & (flat > 0.8) & (nveg(x, y) > -0.5)
        veg_plat = (kind == 2) & (nveg(x, y) + 0.6 * ncol(x, y) > 1.3)
        veg = veg_floor | veg_bench | veg_plat
        cls = np.where(veg, CLASS_ID["veg"], np.where(kind == 0, CLASS_ID["floor"],
                                                      np.where(kind == 1, CLASS_ID["rock"], CLASS_ID["plateau"])))
        # floor patches below boulders are rock-colored gravel; fine as floor
        lit = self.sunlit(P.reshape(-1, 3), N.reshape(-1, 3)).reshape(P.shape[:2])
        cosi = np.clip(N @ SUN, 0, 1)
        self.texel_class = cls
        # visual colors
        palette = np.array([[178, 128, 86], [152, 90, 60], [199, 172, 132], [130, 112, 98], [170, 108, 68], [208, 192, 160]], float)
        layer = np.clip(np.searchsorted(self.strata_z, z), 0, len(self.layers) - 1)
        rock = palette[np.array([L["color"] for L in self.layers])[layer]]
        dz_top = self.strata_z[layer] - z
        rock *= (1 - 0.28 * (dz_top < 0.12))[..., None]                            # dark line under each layer top
        rock *= (1 + 0.07 * ncol(x, y) + 0.05 * fine(x, y))[..., None]
        rock *= (1 - 0.10 * np.clip(nstreak(x + y, z / 6), 0, None))[..., None]   # varnish streaks
        floor = np.array([160, 144, 118.0]) * (1 + 0.08 * ncol(x, y) + 0.08 * fine(x, y))[..., None]
        floor *= (1 - 0.12 * (1 - np.abs(eta)) ** 3)[..., None]                    # damper channel
        plat = np.array([164, 146, 98.0]) * (1 + 0.08 * ncol(x, y) + 0.05 * fine(x, y))[..., None]
        green = np.array([72, 108, 44.0]) + np.array([30, 28, 12.0]) * (0.5 + 0.5 * np.tanh(ncol(x, y)))[..., None]
        green *= (1 + 0.15 * fine(x, y))[..., None]
        col = np.where((cls == CLASS_ID["veg"])[..., None], green,
                       np.where((cls == CLASS_ID["floor"])[..., None], floor,
                                np.where((cls == CLASS_ID["rock"])[..., None], rock, plat)))
        col *= (0.62 + 0.38 * lit)[..., None]                                      # baked cast shadows
        self.tex_rgb = np.clip(col, 0, 255).astype(np.uint8)
        # thermal
        ins = cosi * lit
        tk = np.zeros(cls.shape)
        em = np.zeros(cls.shape)
        for name in ("floor", "rock", "veg", "plateau"):
            m = cls == CLASS_ID[name]
            tk[m] = surface_temperature(name, ins[m], 0.8 * fine(x[m], y[m]) + 0.6 * ncol(x[m], y[m])) + 273.15
            em[m] = CLASSES[name]["emis"]
        self.tex_thermal = encode_temperature(tk, em)
        self.texel_temp_k = tk
        # boulders: per-face colors and temperatures in a shared atlas
        nf = sum(len(b.faces) for b in self.boulders)
        aw = 128
        ah = int(np.ceil(nf / aw))
        rgb = np.zeros((ah * aw, 3)); th = np.zeros(ah * aw); k = 0
        self.boulder_texel0 = []
        for b in self.boulders:
            tri = b.verts[b.faces]
            cen = tri.mean(axis=1)
            n = np.cross(tri[:, 1] - tri[:, 0], tri[:, 2] - tri[:, 0])
            n /= np.linalg.norm(n, axis=1, keepdims=True)
            litb = self.sunlit(cen, n, 0.03)
            insb = np.clip(n @ SUN, 0, 1) * litb
            base = palette[[3, 0, 2][int(rng.integers(0, 3))]] * rng.uniform(0.8, 1.0)
            rgb[k:k + len(cen)] = base * (1 + 0.08 * rng.normal(size=(len(cen), 1))) * (0.62 + 0.38 * litb)[:, None]
            th[k:k + len(cen)] = surface_temperature("rock", insb, 0.5 * rng.normal(size=len(cen))) + 273.15
            self.boulder_texel0.append(k)
            k += len(cen)
        self.atlas = (aw, ah)
        self.tex_boulder_rgb = np.clip(rgb, 0, 255).reshape(ah, aw, 3).astype(np.uint8)
        self.tex_boulder_thermal = encode_temperature(th, np.full_like(th, CLASSES["rock"]["emis"])).reshape(ah, aw, 3)

    # --- firebrands -------------------------------------------------------------------------------------
    def _firebrands(self, rng, n_hidden=6, n_open=2):
        """Hidden fires: just behind a boulder (at least 1 m tall) on the line from an approach point
        D m back along the path, accepted if the hottest piece is out of sight from at least 80 % of
        the path points 3 to 20 m before it (ray tests against terrain and boulders). Open fires:
        on the floor, in sight from at least 80 % of the path points 3 to 25 m before."""
        self.firebrands = []
        pp = self.path_points(0.25)
        def before(c, d0, d1):
            dy = c[1] - pp[:, 1]
            return pp[(dy >= d0) & (dy <= d1)]
        def free(c, r):
            u = self.lateral(c[0], c[1])
            return (abs(u) <= self.width_at(c[1]) / 2 - 0.15
                    and all(np.linalg.norm(c[:2] - b.center[:2]) > b.size / 2 + r for b in self.boulders)
                    and all(abs(c[1] - f.center[1]) > 3 for f in self.firebrands))
        def seen(c, pts):
            frac, _ = self.rays(pts, np.repeat(c[None] + [0, 0, 0.05], len(pts), 0))
            return np.mean(frac >= 0.999)
        cand = [k for k, b in enumerate(self.boulders) if b.height >= 0.9 and 8 < b.center[1] < Y_END - 2]
        rng.shuffle(cand)
        for k in cand:
            if sum(f.hidden for f in self.firebrands) >= n_hidden:
                break
            b = self.boulders[k]
            r = float(rng.uniform(0.15, 0.35))
            for D in (8.0, 12.0, 16.0):
                a = pp[np.argmin(np.abs(pp[:, 1] - (b.center[1] - D)))]
                d = (b.center[:2] - a[:2]) / np.linalg.norm(b.center[:2] - a[:2])
                c = b.center[:2] + d * (((b.verts[:, :2] - b.center[:2]) @ d).max() + r + 0.1)
                c3 = np.array([c[0], c[1], self.ground_z(c[None])[0]])
                if free(c3, r) and seen(c3, before(c3, 3, 20)) <= 0.2:
                    self._add_fire(rng, c3, r, True, k)
                    break
        for _ in range(2000):
            if sum(not f.hidden for f in self.firebrands) >= n_open:
                break
            yy = rng.uniform(10, Y_END - 5)
            u = rng.uniform(-0.7, 0.7) * self.width_at(yy) / 2
            c = np.array([self.xc_fn(yy) + u / math.cos(np.interp(yy, self.y, self.theta)), yy])
            r = float(rng.uniform(0.15, 0.35))
            c3 = np.array([c[0], c[1], self.ground_z(c[None])[0]])
            if free(c3, r) and seen(c3, before(c3, 3, 25)) >= 0.8:
                self._add_fire(rng, c3, r, False, -1)
        self.firebrands.sort(key=lambda f: f.center[1])

    def _add_fire(self, rng, c, r, hidden, boulder):
        t = float(rng.uniform(600, 900))
        pieces = []
        for _ in range(int(rng.integers(7, 13))):
            for _ in range(50):
                q = c[:2] + rng.uniform(-r, r, 2) * 0.8
                if np.linalg.norm(q - c[:2]) <= 0.8 * r:
                    break
            pr = float(rng.uniform(0.025, 0.06))
            gz = self.ground_z(q[None])[0]
            pieces.append((np.array([q[0], q[1], gz + 0.35 * pr]), pr, float(t * rng.uniform(0.9, 1.0))))
        pieces[0] = (pieces[0][0], pieces[0][1], t)
        self.firebrands.append(Firebrand(center=c, radius=r, temp_c=t, hidden=hidden, boulder=boulder, pieces=pieces))

    # --- meshes of firebrands ---------------------------------------------------------------------------
    def fire_meshes(self, k):
        """(ash verts, faces), (ember verts, faces, piece index per face) of firebrand k."""
        fb = self.firebrands[k]
        rng = np.random.default_rng(self.seed * 1000 + k)
        ang = np.linspace(0, 2 * np.pi, 17)[:-1]
        rim = fb.center[:2] + fb.radius * np.stack([np.cos(ang), np.sin(ang)], -1) * rng.uniform(0.85, 1.1, (16, 1))
        rz = self.ground_z(rim) + 0.015
        av = np.vstack([[fb.center[0], fb.center[1], fb.center[2] + 0.02], np.column_stack([rim, rz])])
        af = np.array([[0, 1 + i, 1 + (i + 1) % 16] for i in range(16)])
        ev, ef, ep = [], [], []
        for i, (pc, pr, _) in enumerate(fb.pieces):
            v, f = blob(rng, pr, (1.0, rng.uniform(0.5, 1.0), rng.uniform(0.4, 0.7)), 1, 0.3)
            ef.append(f + sum(len(x) for x in ev)); ev.append(v + pc); ep += [i] * len(f)
        return (av, af), (np.vstack(ev), np.vstack(ef), np.array(ep))

    # --- assets -------------------------------------------------------------------------------------------
    def write_assets(self, out=ASSETS):
        out = Path(out)
        out.mkdir(parents=True, exist_ok=True)
        tag = f"s{self.seed}"
        files = {}
        files["terrain"] = write_obj(out / f"terrain_{tag}.obj", self.V, self.F, self.UV, self.normals.reshape(-1, 3))   # same as the build's
        save_png(np.flipud(self.tex_rgb), out / f"terrain_{tag}_rgb.png")
        save_png(np.flipud(self.tex_thermal), out / f"terrain_{tag}_thermal.png")
        save_png(np.flipud((self.texel_class * 60).astype(np.uint8)), out / f"terrain_{tag}_class.png")
        aw, ah = self.atlas
        save_png(np.flipud(self.tex_boulder_rgb), out / f"boulders_{tag}_rgb.png")
        save_png(np.flipud(self.tex_boulder_thermal), out / f"boulders_{tag}_thermal.png")
        for k, b in enumerate(self.boulders):
            tri = b.verts[b.faces].reshape(-1, 3)
            t = self.boulder_texel0[k] + np.repeat(np.arange(len(b.faces)), 3)
            uv = np.column_stack([(t % aw + 0.5) / aw, (t // aw + 0.5) / ah])
            files[f"boulder{k}"] = write_obj(out / f"boulder_{tag}_{k:02d}.obj", tri, np.arange(len(tri)).reshape(-1, 3), uv)
            write_obj(out / f"boulder_{tag}_{k:02d}_hull.obj", b.verts, b.faces)
        # firebrands: one 16 x 16 atlas row per firebrand: texel 0 ash, texel 1 + i ember piece i
        n = len(self.firebrands)
        frgb = np.zeros((n, 16, 3), np.uint8); fth = np.zeros((n, 16, 3), np.uint8)
        for k, fb in enumerate(self.firebrands):
            (av, af), (ev, ef, ep) = self.fire_meshes(k)
            frgb[k, 0] = (38, 34, 32)
            fth[k, 0] = encode_temperature(CLASSES["ash"]["shade"] + 273.15, CLASSES["ash"]["emis"])
            for i, (_, _, tc) in enumerate(fb.pieces):
                frgb[k, 1 + i] = ember_rgb(tc)
                fth[k, 1 + i] = encode_temperature(tc + 273.15, CLASSES["ember"]["emis"])
            uv_a = np.full((len(af) * 3, 2), [(0.5) / 16, (k + 0.5) / n])
            files[f"ash{k}"] = write_obj(out / f"fire_{tag}_{k}_ash.obj", av[af].reshape(-1, 3), np.arange(len(af) * 3).reshape(-1, 3), uv_a)
            uv_e = np.column_stack([(1.5 + np.repeat(ep, 3)) / 16, np.full(len(ep) * 3, (k + 0.5) / n)])
            files[f"ember{k}"] = write_obj(out / f"fire_{tag}_{k}_embers.obj", ev[ef].reshape(-1, 3), np.arange(len(ef) * 3).reshape(-1, 3), uv_e)
        save_png(np.flipud(frgb), out / f"fires_{tag}_rgb.png")
        save_png(np.flipud(fth), out / f"fires_{tag}_thermal.png")
        self.asset_dir, self.files = out, files
        return files

    # --- loading into a PyBullet client --------------------------------------------------------------------
    def load(self, client, kind):
        """Load the world into `client`. kind: "physics" (collision shapes only: concave terrain
        trimesh, convex boulders), "visual" (textured meshes, no collision) or "thermal" (the same
        meshes with the temperature-encoding textures). Returns {body id: (class, index)}."""
        if not hasattr(self, "files"):
            self.write_assets()
        out, tag, bodies = self.asset_dir, f"s{self.seed}", {}
        if kind == "physics":
            col = p.createCollisionShape(p.GEOM_MESH, fileName=self.files["terrain"], flags=p.GEOM_FORCE_CONCAVE_TRIMESH, physicsClientId=client)
            bodies[p.createMultiBody(0, col, physicsClientId=client)] = ("terrain", 0)
            for k, b in enumerate(self.boulders):
                col = p.createCollisionShape(p.GEOM_MESH, fileName=str(out / f"boulder_{tag}_{k:02d}_hull.obj"), physicsClientId=client)
                bodies[p.createMultiBody(0, col, physicsClientId=client)] = ("boulder", k)
            return bodies
        suffix = "rgb" if kind == "visual" else "thermal"
        tex = {name: p.loadTexture(str(out / f"{name}_{tag}_{suffix}.png"), physicsClientId=client)
               for name in ("terrain", "boulders", "fires")}
        def add(fname, texture, cls, k):
            vs = p.createVisualShape(p.GEOM_MESH, fileName=fname, rgbaColor=[1, 1, 1, 1], physicsClientId=client)
            b = p.createMultiBody(0, -1, vs, physicsClientId=client)
            p.changeVisualShape(b, -1, textureUniqueId=texture, rgbaColor=[1, 1, 1, 1], physicsClientId=client)
            bodies[b] = (cls, k)
        add(self.files["terrain"], tex["terrain"], "terrain", 0)
        for k in range(len(self.boulders)):
            add(self.files[f"boulder{k}"], tex["boulders"], "boulder", k)
        for k in range(len(self.firebrands)):
            add(self.files[f"ash{k}"], tex["fires"], "ash", k)
            add(self.files[f"ember{k}"], tex["fires"], "ember", k)
        return bodies

    # --- checks ----------------------------------------------------------------------------------------------
    def corridor_clearance(self, path=None):
        """Minimum distance from the corridor (|lateral| <= CORRIDOR_HALF around the path, height
        CORRIDOR_Z above the floor) to terrain and boulders, and from the path line itself, by
        closest-point queries of a 1 cm probe sphere in the scratch client (collision geometry)."""
        pts = self.path_points(0.25, path)
        probe = p.createMultiBody(0, p.createCollisionShape(p.GEOM_SPHERE, radius=0.01, physicsClientId=self._client),
                                  physicsClientId=self._client)
        statics = [self.terrain_id] + self.boulder_ids
        def clearance(q):
            p.resetBasePositionAndOrientation(probe, q.tolist(), [0, 0, 0, 1], physicsClientId=self._client)
            d = [c[8] for s in statics for c in p.getClosestPoints(probe, s, 6.0, physicsClientId=self._client)]
            return (min(d) if d else 6.0) + 0.01
        line = np.array([clearance(q) for q in pts])
        box = []
        for q in pts[::2]:
            th = np.interp(q[1], self.y, self.theta)
            nrm = np.array([math.cos(th), -math.sin(th), 0.0])
            for u in np.linspace(-CORRIDOR_HALF, CORRIDOR_HALF, 5):
                for h in CORRIDOR_Z:
                    box.append(clearance(q + u * nrm + [0, 0, h - FLIGHT_H]))
        p.removeBody(probe, physicsClientId=self._client)
        return line, np.array(box), pts

    def visibility(self, k, pts):
        """Line of sight (bool per path point) from pts to firebrand k's hottest ember piece."""
        c = max(self.firebrands[k].pieces, key=lambda q: q[2])[0] + [0, 0, 0.03]
        frac, _ = self.rays(pts, np.repeat(c[None], len(pts), 0))
        return frac >= 0.999

    def summary(self):
        fl = self.path_points(0.1)
        line, box, _ = self.corridor_clearance()
        print(f"seed {self.seed}: terrain {len(self.V)} vertices, {len(self.F)} triangles; "
              f"{len(self.boulders)} boulders ({sum(len(b.faces) for b in self.boulders)} triangles), "
              f"{len(self.firebrands)} firebrands")
        hd = np.degrees(np.abs(self.theta[(self.y >= 0) & (self.y <= Y_END)])).max()
        m = (self.y >= 0) & (self.y <= Y_END)
        print(f"  flight y 0..{Y_END} m, path length {np.sum(np.linalg.norm(np.diff(fl, axis=0), axis=1)):.1f} m, "
              f"max axis heading {hd:.1f} deg, floor width {self.width[m].min():.2f}..{self.width[m].max():.2f} m "
              f"(narrows at y = {self.narrows[0]:.1f}, {self.narrows[1]:.1f} m)")
        for s, name in ((-1, "west"), (1, "east")):
            print(f"  {name} wall height {self.height[s][m].min():.1f}..{self.height[s][m].max():.1f} m, mean angle toe to rim "
                  f"{self.wall_angle[s][m].min():.1f}..{self.wall_angle[s][m].max():.1f} deg")
        print(f"  floor rise {self.floor_c(Y_END) - self.floor_c(0):.2f} m over the flight; {len(self.path)} waypoints, legs "
              f"{np.linalg.norm(np.diff(self.path, axis=0), axis=1).min():.1f}..{np.linalg.norm(np.diff(self.path, axis=0), axis=1).max():.1f} m")
        print(f"  clearance: path line (3.5 m) min {line.min():.2f} m; corridor box (+-{CORRIDOR_HALF} m, {CORRIDOR_Z[0]}-{CORRIDOR_Z[1]} m) min {box.min():.2f} m")
        for k, f in enumerate(self.firebrands):
            print(f"  fire {k}: ({f.center[0]:.1f}, {f.center[1]:.1f}, {f.center[2]:.2f}) r {f.radius:.2f} m, {f.temp_c:.0f} C, "
                  f"{'behind boulder ' + str(f.boulder) if f.hidden else 'open'}, {len(f.pieces)} pieces")


def write_obj(path, v, f, uv=None, vn=None):
    lines = [f"# generated by gorge.py\n"]
    lines += [f"v {a:.5f} {b:.5f} {c:.5f}\n" for a, b, c in v]
    if uv is not None:
        lines += [f"vt {a:.6f} {b:.6f}\n" for a, b in uv]
    if vn is not None:
        lines += [f"vn {a:.5f} {b:.5f} {c:.5f}\n" for a, b, c in vn]
    def ref(i):
        i += 1
        return f"{i}/{i}/{i}" if vn is not None else (f"{i}/{i}" if uv is not None else f"{i}")
    lines += [f"f {ref(a)} {ref(b)} {ref(c)}\n" for a, b, c in f]
    tmp = Path(f"{path}.{os.getpid()}.tmp")
    tmp.write_text("".join(lines))
    os.replace(tmp, path)                      # atomic: parallel runs never read a partial file
    return str(path)


def save_png(a, path):
    tmp = Path(f"{path}.{os.getpid()}.tmp.png")
    Image.fromarray(a).save(tmp)
    os.replace(tmp, path)


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--seed", type=int, default=7)
    a = ap.parse_args()
    import time
    t0 = time.time()
    g = Gorge(a.seed)
    t1 = time.time()
    g.write_assets()
    print(f"built in {t1 - t0:.1f} s, assets in {time.time() - t1:.1f} s -> {ASSETS}")
    g.summary()
