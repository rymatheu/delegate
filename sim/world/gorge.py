"""A procedural basalt gorge with a dry wash, boulders, vegetation and small surface fires,
deterministic from a seed.

World frame: ENU (x east, y north, z up, meters), as PyBullet. The gorge axis runs north from the
origin with a gentle meander; the floor at the origin is at z ~ 0.

Construction (all generated here from the seed, nothing loaded from elsewhere):
- centerline x_c(y), two sines scaled so the axis stays within MAX_HEADING_DEG of north; floor (a dry
  wash) width W(y) 6.2 to 9.6 m with two narrows; floor height rising 3.5 % up the gorge;
- walls in the manner of a columnar basalt canyon, per side and row: a talus apron at the foot (angle
  of repose 31 to 39 deg, 0.3 to 3.6 m high, smaller in the narrows), a colonnade of near-vertical
  columns (84 to 88 deg), a ledge (0 to 0.9 m) and a blocky entablature (74 to 82 deg) up to the rim
  19 to 27 m above the floor, a rounded soil cap and a plateau 45 m wide. Columns: a 1D Voronoi
  pattern along the wall (0.5 to 1.1 m wide) with a ridge-shaped front (two facets per column), a
  per-column depth and cross joints at random heights, swaying slowly with height; entablature: a 2D
  Voronoi pattern of blocks with their own depths. The displacement moves the mesh (and, at texel
  scale, the baked shading normal); any overhang it would make is clipped to a vertical face;
- the terrain is one triangle mesh on a grid sheared to follow the centerline (rows at constant y,
  columns at fixed fractions of each profile segment), so the grid never folds;
- boulders: deformed icospheres with planar fracture faces (rounded to angular), partly buried,
  in clusters with smaller boulders, rock chips and cobbles around them;
- rocks: fallen column blocks (prisms) on the talus and at the wall foot, cobbles on the wash;
- vegetation as meshes: green shrubs (clusters of lumpy blobs), sagebrush, junipers and pines
  (trunk and crown), small broadleaf trees, grass tufts (two-sided blades);
- fires: small surface fires in litter and grass (a burned patch with char, ash and glowing embers,
  a ragged burning front, flame tongues 0.2 to 1.3 m), one burning shrub and one fire at the base
  of a small pine; 6 hidden behind a boulder as seen from the approach path, 2 in the open. Flames,
  smoke and the fire's light are drawn per frame in image space (fire.py) from the parameters here;
- textures: every texel's color is computed from the 3D point it covers, with the lighting baked in
  (sun with cast shadows from ray tests, sky light with ambient occlusion, a little bounce light), so
  the visual world is rendered ambient-only; a second texture with the same layout holds each
  texel's surface temperature and emissivity (sun-heated, shaded, transpiring, fire-heated) for the
  thermal camera (sensors.py). Objects use an atlas with one small square per triangle.

The build takes a minute; the result (meshes, textures, world data) is cached in assets/ under a key
made of the seed and this file's source, so later runs load it in about a second.

Run `python gorge.py [--seed N] [--rebuild]` to build, write the assets and print the world summary.
"""
import argparse
import fcntl
import hashlib
import math
import os
import pickle
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np
import pybullet as p
from PIL import Image
from scipy.ndimage import gaussian_filter, gaussian_filter1d, map_coordinates
from scipy.spatial import ConvexHull

HERE = Path(__file__).resolve().parent
ASSETS = HERE / "assets"
CACHE_VERSION = 4

# --- layout ------------------------------------------------------------------------------------
Y0, Y1, ROW_DY = -16.0, 100.0, 0.35        # terrain rows (m north); the flight is y in [0, Y_END]
Y_END = 72.0
MAX_HEADING_DEG = 22.0
FLIGHT_H = 3.5                             # m above the floor along the centerline
CORRIDOR_HALF, CORRIDOR_Z = 1.25, (3.0, 4.0)
KEEP_LOW, KEEP_R = 2.5, 3.6                # geometry higher than KEEP_LOW above the centerline floor stays
                                           # KEEP_R m (horizontally) from the flight path
KEEP_LOW_VEG, ROUTE_TOP = 1.6, 1.6         # the same for vegetation from 1.6 m; boulders within 2 m of the route
                                           # end at most ROUTE_TOP above the floor (1.5 m of clearance or more)
SITES = ((-4.0, 1.5), (Y_END - 1.0, 80.0)) # start and landing zones (north ranges): no rocks, shrubs or trees
NT, NV, NCOL, NENT, NCAP = 12, 6, 30, 16, 4   # mesh columns per wall segment: talus, vegetated slope, colonnade,
                                              # entablature, cap
XI_PLAT = np.array([0.8, 1.8, 3.2, 5.0, 7.5, 10.5, 14.0, 18.5, 24.0, 30.0, 37.0, 45.0])
ETA_FLOOR = np.linspace(-1, 1, 23)[1:-1]
TEX_SCALE = float(os.environ.get("GORGE_TEX_SCALE", "1.0"))   # < 1: smaller textures (development)
TEX_W, TEX_H = int(6144 * TEX_SCALE), int(4096 * TEX_SCALE)
ATLAS_W = 2048

# --- sun, air and surface temperatures -----------------------------------------------------------
LAT_DEG, DECL_DEG, HOUR_ANGLE_DEG = 39.0, 15.0, 29.0   # latitude, solar declination (mid May), hour angle now (about 14:00)


def sun_vector(hour_angle_deg):
    """Unit vector (ENU) toward the sun at a solar hour angle (deg, afternoon positive)."""
    h, la, de = (math.radians(a) for a in (hour_angle_deg, LAT_DEG, DECL_DEG))
    v = np.array([-math.cos(de) * math.sin(h), math.cos(la) * math.sin(de) - math.sin(la) * math.cos(de) * math.cos(h),
                  math.sin(la) * math.sin(de) + math.cos(la) * math.cos(de) * math.cos(h)])
    return v / np.linalg.norm(v)


SUN = sun_vector(HOUR_ANGLE_DEG)          # azimuth 235 deg (south-west), elevation 55 deg
SUN_AZ_DEG = (math.degrees(math.atan2(SUN[0], SUN[1])) + 360) % 360
SUN_EL_DEG = math.degrees(math.asin(SUN[2]))
# the sun's earlier positions (every 30 min back to 3 h) for the surfaces' thermal inertia
SUN_PAST = [(0.5 * k, sun_vector(HOUR_ANGLE_DEG - 7.5 * k)) for k in range(1, 7)]
# time constant (h) of each surface class's temperature response to insolation (thermal inertia)
TAU_H = dict(rock=2.5, soil=1.5, sand=1.0, drygrass=0.4, leaf=0.25, bark=0.8)
T_AIR_C = 30.0
# surface classes: temperature (deg C) in full shade and in full sun at normal incidence, emissivity
CLASSES = {
    "sand":     dict(shade=30.0, sun=52.0, emis=0.92),   # dry sand and gravel of the wash
    "rock":     dict(shade=29.0, sun=56.0, emis=0.94),   # dark basalt: walls, blocks, boulders
    "soil":     dict(shade=30.0, sun=50.0, emis=0.94),   # talus soil, ledges, plateau soil
    "drygrass": dict(shade=30.0, sun=46.0, emis=0.96),   # cured grass, low thermal mass
    "leaf":     dict(shade=28.0, sun=34.0, emis=0.97),   # green leaves, transpiring, near air temperature
    "bark":     dict(shade=29.0, sun=44.0, emis=0.95),
    "char":     dict(shade=None, sun=None, emis=0.95),   # burned ground: temperature from the fire model
    "ember":    dict(shade=None, sun=None, emis=0.90),   # glowing char, 600 to 900 C
}
T_ENC_MIN, T_ENC_SPAN = 200.0, 1100.0      # K: 16-bit temperature code in R (high) and G (low)
# fire heating of nearby surfaces (quasi-steady energy balance): dT = ETA_EXPO a q / (H_CONV + H_RAD)
H_CONV, H_RAD, ABSORB, ETA_EXPO = 12.0, 6.5, 0.9, 0.5
LIGHT = dict(sun=1.05, sky=0.55, reflect=0.45)
SKY_TINT, BOUNCE_TINT = np.array([0.90, 0.96, 1.10]), np.array([1.10, 1.0, 0.86])


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


class Tile:
    """A small periodic unit-variance noise tile (n x n cells, Gaussian-filtered white noise),
    sampled bilinearly at (u, v) / scale (meters per cell); used for texel-scale detail."""

    def __init__(self, rng, n=256, sigma=1.5):
        a = gaussian_filter(rng.normal(size=(n, n)), sigma, mode="wrap")
        self.a, self.n = (a / a.std()).astype(np.float32), n

    def __call__(self, u, v, scale):
        x = np.asarray(u, np.float64) / scale
        y = np.asarray(v, np.float64) / scale
        x0, y0 = np.floor(x), np.floor(y)
        fx, fy = (x - x0).astype(np.float32), (y - y0).astype(np.float32)
        i0, j0 = x0.astype(np.int64) % self.n, y0.astype(np.int64) % self.n
        i1, j1 = (i0 + 1) % self.n, (j0 + 1) % self.n
        a = self.a
        return ((a[j0, i0] * (1 - fx) + a[j0, i1] * fx) * (1 - fy) + (a[j1, i0] * (1 - fx) + a[j1, i1] * fx) * fy)


def fbm(tile, u, v, scale, octaves=3, gain=0.5):
    out, amp, s, norm = 0.0, 1.0, scale, 0.0
    for k in range(octaves):
        out = out + amp * tile(u + 17.3 * k, v - 9.1 * k, s)
        norm += amp
        amp *= gain
        s *= 0.5
    return out / norm


def noise1(rng, y, scale, n=6):
    """Smooth unit-amplitude 1D noise: a few sines with random phases, wavelengths around `scale`."""
    out = np.zeros_like(y, dtype=float)
    for k in range(n):
        lam = scale * rng.uniform(0.5, 1.5) / (1 + 0.5 * k)
        out += rng.uniform(0.5, 1.0) / (1 + k) * np.sin(2 * np.pi * y / lam + rng.uniform(0, 2 * np.pi))
    return out / np.abs(out).max()


def hash01(a, b, k):
    """Deterministic pseudo-random numbers in [0, 1) from integer arrays a, b and an integer k."""
    h = (np.asarray(a, np.int64) * 374761393 + np.asarray(b, np.int64) * 668265263 + int(k) * 1442695041) & 0xFFFFFFFF
    h = ((h ^ (h >> 13)) * 1274126177) & 0xFFFFFFFF
    h = h ^ (h >> 16)
    return (h & 0xFFFFFF).astype(np.float64) / float(0x1000000)


def voronoi2(u, v, k, jitter=0.85):
    """Cellular noise on the unit grid: distance to the nearest and second-nearest jittered cell
    point, the nearest cell's integer coordinates and the offset to its point."""
    u, v = np.asarray(u, np.float64), np.asarray(v, np.float64)
    iu, iv = np.floor(u).astype(np.int64), np.floor(v).astype(np.int64)
    f1 = np.full(u.shape, 9.0); f2 = np.full(u.shape, 9.0)
    cu, cv = np.zeros(u.shape, np.int64), np.zeros(u.shape, np.int64)
    du0, dv0 = np.zeros(u.shape), np.zeros(u.shape)
    for a in (-1, 0, 1):
        for b in (-1, 0, 1):
            gu, gv = iu + a, iv + b
            pu = gu + 0.5 + jitter * (hash01(gu, gv, k) - 0.5)
            pv = gv + 0.5 + jitter * (hash01(gu, gv, k + 7) - 0.5)
            du, dv = u - pu, v - pv
            d = np.sqrt(du * du + dv * dv)
            closer = d < f1
            f2 = np.where(closer, f1, np.minimum(f2, d))
            f1 = np.where(closer, d, f1)
            cu, cv = np.where(closer, gu, cu), np.where(closer, gv, cv)
            du0, dv0 = np.where(closer, du, du0), np.where(closer, dv, dv0)
    return f1, f2, cu, cv, du0, dv0


def smoothstep(a, b, x):
    t = np.clip((np.asarray(x) - a) / (b - a), 0, 1)
    return t * t * (3 - 2 * t)


def mix(a, b, t):
    """Linear blend of colors a and b (arrays ending in 3) by weight t (scalar or array without the
    color axis)."""
    t = np.asarray(t, float)
    if t.ndim and t.shape[-1] != 1:
        t = t[..., None]
    return a * (1 - t) + b * t


# ------------------------------------------------------------------------------------------------
# meshes

_ICO = {}


def icosphere(subdiv):
    if subdiv in _ICO:
        return _ICO[subdiv][0].copy(), _ICO[subdiv][1].copy()
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
    _ICO[subdiv] = (np.array(v), np.array(f))
    return _ICO[subdiv][0].copy(), _ICO[subdiv][1].copy()


OCTA_V = np.array([[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]], float)
OCTA_F = np.array([[0, 2, 4], [2, 1, 4], [1, 3, 4], [3, 0, 4], [2, 0, 5], [1, 2, 5], [3, 1, 5], [0, 3, 5]])


def rotation(yaw, tilt=0.0, tilt_dir=0.0):
    cz, sz = math.cos(yaw), math.sin(yaw)
    Rz = np.array([[cz, -sz, 0], [sz, cz, 0], [0, 0, 1.0]])
    if tilt == 0.0:
        return Rz
    ax = np.array([math.cos(tilt_dir), math.sin(tilt_dir), 0.0])
    K = np.array([[0, -ax[2], ax[1]], [ax[2], 0, -ax[0]], [-ax[1], ax[0], 0]])
    Rt = np.eye(3) + math.sin(tilt) * K + (1 - math.cos(tilt)) * K @ K
    return Rt @ Rz


def lumpy(rng, subdiv, rough, waves=5, kmin=1.0, kmax=3.0):
    """Unit icosphere with radial noise from random plane waves."""
    v, f = icosphere(subdiv)
    d = np.zeros(len(v))
    for _ in range(waves):
        k = rng.normal(size=3) * rng.uniform(kmin, kmax)
        d += np.sin(v @ k + rng.uniform(0, 2 * np.pi)) / waves
    return v * (1 + rough * d)[:, None], f


def boulder_shape(rng, size, flat, angular):
    """A boulder: lumpy icosphere (subdivision 3) cut by 4 to 13 fracture planes (each vertex beyond a
    random plane is moved onto it), scaled to `size` (m, largest horizontal extent) and flattened.
    Returns vertices, faces and per-face-corner normals: a face on a fracture plane is flat (the plane's
    normal), the rest smooth, so the facets read as sharp-edged breaks."""
    v, f = lumpy(rng, 3, 0.18, waves=7, kmin=0.8, kmax=3.2)
    plane = -np.ones(len(v), int)
    planes = []
    for k in range(int(round(6 + angular * 10))):
        n = rng.normal(size=3)
        n[2] *= 0.7
        n /= np.linalg.norm(n)
        o = rng.uniform(0.5, 0.82)
        s = v @ n - o
        cut = s > 0
        v = v - np.maximum(s, 0)[:, None] * n
        plane[cut] = len(planes)
        planes.append(n)
    ax = np.array([1.0, rng.uniform(0.68, 0.95), flat])
    v = v * ax
    sc = size / np.ptp(v[:, :2], axis=0).max()
    v = v * sc
    vn = vertex_normals(v, f)
    fn = vn[f].copy()
    flat_f = (plane[f[:, 0]] >= 0) & (plane[f[:, 0]] == plane[f[:, 1]]) & (plane[f[:, 1]] == plane[f[:, 2]])
    pn = np.cross(v[f[:, 1]] - v[f[:, 0]], v[f[:, 2]] - v[f[:, 0]])
    pn /= np.maximum(np.linalg.norm(pn, axis=1, keepdims=True), 1e-12)
    fn[flat_f] = pn[flat_f][:, None, :]
    return v, f, fn


def prism(rng, r, length, nside):
    """A fallen column block: an irregular n-gon prism along x, faces split (flat shading)."""
    ang = np.sort(rng.uniform(0, 2 * np.pi, nside)) if nside > 6 else (np.arange(nside) / nside * 2 * np.pi + rng.uniform(-0.25, 0.25, nside))
    rad = r * rng.uniform(0.82, 1.12, nside)
    yz = np.stack([rad * np.cos(ang), rad * np.sin(ang)], -1)
    x0, x1 = -length / 2 + rng.uniform(-0.06, 0.06, nside) * r, length / 2 + rng.uniform(-0.06, 0.06, nside) * r
    v = np.vstack([np.column_stack([x0, yz]), np.column_stack([x1, yz])])
    f = []
    for i in range(nside):
        j = (i + 1) % nside
        f += [[i, j, nside + j], [i, nside + j, nside + i]]
    for i in range(1, nside - 1):
        f += [[0, i + 1, i], [nside, nside + i, nside + i + 1]]
    return v, np.array(f)


def cylinder(r0, r1, h, nside, rng=None, bend=0.0):
    """Tapered, open-ended cylinder (trunk, branch, log) along z from 0 to h, with optional bend."""
    nring = 4
    ang = np.arange(nside) / nside * 2 * np.pi
    v = []
    for k in range(nring + 1):
        t = k / nring
        r = r0 + (r1 - r0) * t
        off = bend * np.array([math.sin(3.0 * t), math.cos(2.2 * t + 1)]) * t
        for a in ang:
            v.append([r * math.cos(a) + off[0], r * math.sin(a) + off[1], h * t])
    v = np.array(v)
    f = []
    for k in range(nring):
        for i in range(nside):
            j = (i + 1) % nside
            a, b, c, d = k * nside + i, k * nside + j, (k + 1) * nside + i, (k + 1) * nside + j
            f += [[a, b, d], [a, d, c]]
    top = len(v)
    v = np.vstack([v, [[*(v[-nside:, :2].mean(0)), h]]])
    for i in range(nside):
        f.append([nring * nside + i, nring * nside + (i + 1) % nside, top])
    return v, np.array(f)


def vertex_normals(v, f):
    fn = np.cross(v[f[:, 1]] - v[f[:, 0]], v[f[:, 2]] - v[f[:, 0]])
    vn = np.zeros_like(v)
    for k in range(3):
        np.add.at(vn, f[:, k], fn)
    ln = np.linalg.norm(vn, axis=1, keepdims=True)
    return np.where(ln > 1e-12, vn / np.maximum(ln, 1e-12), [0, 0, 1.0])


def split_faces(v, f):
    """Every face its own three vertices (flat shading)."""
    return v[f].reshape(-1, 3), np.arange(len(f) * 3).reshape(-1, 3)


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
    return np.clip((1 - x) * np.array([200, 50, 12]) + x * np.array([255, 170, 50]), 0, 255)


# ------------------------------------------------------------------------------------------------
# world objects


@dataclass
class Boulder:
    center: np.ndarray        # m, ENU, mean of the vertices
    size: float               # m, largest horizontal extent
    height: float             # m, top above the local ground
    top: float                # m, z of the top
    verts: np.ndarray         # world vertices
    faces: np.ndarray
    wall: bool                # on the talus or against the wall foot
    cluster: int = -1         # index of the boulder this one leans against (-1: none)


@dataclass
class Firebrand:
    center: np.ndarray        # m, ENU on the ground: the ignition point, center of the burned patch
    radius: float             # m, mean radius of the burned patch (the fire's size)
    temp_c: float             # deg C, hottest ember
    hidden: bool              # placed behind a boulder as seen from the approach
    boulder: int              # index of the hiding boulder, -1 if in the open
    pieces: list = field(default_factory=list)   # (center, radius, temp_c) of each ember piece
    kind: str = "litter"      # litter, grass, log, shrub, tree
    rim: np.ndarray = None    # radius of the burned patch at RIM_N angles (m)
    active: np.ndarray = None # flaming (1) or smoldering (0) at each rim angle
    tongues: np.ndarray = None   # flame tongues: x, y, z (base), width, height, phase, frequency, lean
    flame_h: float = 0.4      # m, nominal flame height
    power_w: float = 0.0      # W, radiated power (fire heating, glow)
    smoke: float = 1.0        # smoke production (relative)
    smoke_dark: float = 0.0   # 0 white-grey smoke ... 1 dark smoke
    extra: dict = field(default_factory=dict)  # kind-specific: log ends, shrub or tree position


RIM_N = 64


@dataclass
class Part:
    """One mesh of the objects atlas: world vertices, faces, vertex normals and its material."""
    verts: np.ndarray
    faces: np.ndarray
    normals: np.ndarray
    mat: str
    color: np.ndarray
    group: str                # boulder, rocks, veg, ember
    index: int = 0            # boulder index / fire index
    n: int = 4                # texels per triangle square side
    collide: bool = False     # in the group's collision hulls
    center: np.ndarray = None # blob or crown center (foliage lighting), base z (boulders)
    extra: float = 0.0        # material parameter (scorch, moss)
    fnorm: np.ndarray = None  # optional per-face-corner normals (F x 3 x 3): flat facets


# ------------------------------------------------------------------------------------------------
# the gorge


def source_key(seed):
    h = hashlib.sha1(Path(__file__).read_bytes())
    h.update(f"{seed} {TEX_W} {TEX_H} {CACHE_VERSION}".encode())
    return h.hexdigest()[:16]


class Gorge:
    PERSIST = ("seed", "_ax", "y", "xc", "theta", "width", "narrows", "floor0", "height", "talus_h", "col_top",
               "grid", "cols", "col_kind", "U", "zc", "V", "F", "UV", "normals", "rim_xi", "rim_z", "wall_angle",
               "path", "boulders", "firebrands", "rocks", "veg", "files", "asset_dir", "counts", "build_s", "mid", "ledge_w",
               "talus_ang", "fire_seen", "bake_times", "live_chunks")

    def __init__(self, seed=7, rebuild=False):
        self.seed = seed
        ASSETS.mkdir(parents=True, exist_ok=True)
        key = source_key(seed)
        cache = ASSETS / f"gorge_s{seed}.pkl"
        with open(ASSETS / f".build_s{seed}.lock", "w") as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)          # one build at a time; the others load its result
            state = None
            if cache.exists() and not rebuild:
                try:
                    with open(cache, "rb") as fh:
                        state = pickle.load(fh)
                    if state.get("_key") != key or not all(Path(f).exists() for f in state["files"].values()):
                        state = None
                except Exception:
                    state = None
            if state is None:
                t0 = time.time()
                self._build()
                self.build_s = time.time() - t0
                state = {k: getattr(self, k) for k in self.PERSIST}
                state["_key"] = key
                tmp = Path(f"{cache}.{os.getpid()}.tmp")
                with open(tmp, "wb") as fh:
                    pickle.dump(state, fh, protocol=pickle.HIGHEST_PROTOCOL)
                os.replace(tmp, cache)
                self.cached = False
            else:
                for k in self.PERSIST:
                    setattr(self, k, state[k])
                self.cached = True
        if self.cached:
            self._client = p.connect(p.DIRECT)
            self._scratch_bodies()

    # --- build ------------------------------------------------------------------------------------
    def _build(self):
        rng = np.random.default_rng(self.seed)
        self.asset_dir = ASSETS
        self.files = {}
        self._axis(rng)
        self._terrain(rng)
        self.path = self.flight_path()
        self._client = p.connect(p.DIRECT)
        tag = f"s{self.seed}"
        self.files["terrain"] = write_obj(ASSETS / f"terrain_{tag}.obj", self.V, self.F, self.UV, self.normals.reshape(-1, 3))
        self.terrain_id = p.createMultiBody(0, p.createCollisionShape(
            p.GEOM_MESH, fileName=self.files["terrain"], flags=p.GEOM_FORCE_CONCAVE_TRIMESH,
            physicsClientId=self._client), physicsClientId=self._client)
        self.parts = []
        self._boulders(rng)
        self._firebrands(rng)
        self._rocks(rng)
        self._vegetation(rng)
        self._fire_parts(rng)
        self._write_hulls()
        self._add_compounds()
        self._check_fires()
        self._bake_objects(rng)
        self._bake_terrain(rng)
        self._bake_fires(rng)
        self._write_meshes()
        self._live_lod(np.random.default_rng(self.seed * 7919 + 4243))
        self.counts = dict(live_triangles=self.live_counts, boulders=len(self.boulders), rocks=len(self.rocks), veg={k: sum(1 for v in self.veg if v["kind"] == k)
                                                                                    for k in sorted({v["kind"] for v in self.veg})},
                           triangles=dict(terrain=len(self.F), **{g: int(sum(len(q.faces) for q in self.parts if q.group == g))
                                                                    for g in ("boulder", "rocks", "veg", "ember")}))
        del self.parts

    def _scratch_bodies(self):
        """Collision bodies of the world in the scratch client (ray tests, clearance)."""
        c = self._client
        self.terrain_id = p.createMultiBody(0, p.createCollisionShape(p.GEOM_MESH, fileName=self.files["terrain"],
                                            flags=p.GEOM_FORCE_CONCAVE_TRIMESH, physicsClientId=c), physicsClientId=c)
        tag = f"s{self.seed}"
        self.boulder_ids = [p.createMultiBody(0, p.createCollisionShape(p.GEOM_MESH, fileName=str(self.asset_dir / f"boulder_{tag}_{k:02d}_hull.obj"),
                                                                        physicsClientId=c), physicsClientId=c)
                            for k in range(len(self.boulders))]
        self.compound_ids = [p.createMultiBody(0, p.createCollisionShape(p.GEOM_MESH, fileName=self.files[f"{g}_hull"], physicsClientId=c),
                                               physicsClientId=c) for g in ("rocks", "veg") if f"{g}_hull" in self.files]

    # --- axis -----------------------------------------------------------------------------------
    def _axis(self, rng):
        y = np.arange(Y0, Y1 + 1e-9, ROW_DY)
        a1, l1, ph1 = 3.6, rng.uniform(55, 70), rng.uniform(0, 2 * np.pi)
        a2, l2, ph2 = 1.0, rng.uniform(24, 32), rng.uniform(0, 2 * np.pi)
        f = lambda yy: a1 * np.sin(2 * np.pi * yy / l1 + ph1) + a2 * np.sin(2 * np.pi * yy / l2 + ph2)
        fine = np.linspace(Y0, Y1, 4000)
        slope = np.abs(np.gradient(f(fine), fine)).max()
        k = min(1.0, math.tan(math.radians(MAX_HEADING_DEG)) / slope)
        self._ax = (a1, l1, ph1, a2, l2, ph2, k, float(f(0.0)))
        self.y = y
        self.xc = self.xc_fn(y)
        self.theta = np.arctan(np.gradient(self.xc, y))             # heading east of north (rad)
        yn = (rng.uniform(20, 28), rng.uniform(46, 56))
        w = 7.7 + 1.2 * noise1(rng, y, 30.0)
        g_n = np.zeros_like(y)
        for yc, wmin in zip(yn, (6.3, 6.6)):
            g = np.exp(-0.5 * ((y - yc) / 3.5) ** 2)
            w = w * (1 - g) + wmin * g
            g_n = np.maximum(g_n, g)
        self.width = np.clip(w, 6.2, 9.6)
        self.narrows = yn
        self.floor0 = 0.035 * y + 0.35 * noise1(rng, y, 18.0)
        self.floor0 -= np.interp(0.0, y, self.floor0)
        self.height = {s: np.clip(23 + 4.5 * noise1(rng, y, 40.0), 19.0, 27.0) for s in (-1, 1)}
        # wall sections along each side: 0 a cliff down to a small talus, 1 a vegetated slope (a talus cone up
        # to 30-45 % of the wall, then a steep vegetated band with outcrops) with the cliff above it
        self.slope = {s: smoothstep(0.05, 0.4, noise1(rng, y, 20.0)) for s in (-1, 1)}
        th_cliff = {s: np.clip(1.6 + 0.9 * noise1(rng, y, 9.0), 0.6, 2.8) * (1 - 0.6 * g_n) for s in (-1, 1)}
        frac = {s: 0.3 + 0.07 * noise1(rng, y, 7.0) for s in (-1, 1)}
        self.talus_h = {s: th_cliff[s] * (1 - self.slope[s]) + frac[s] * self.height[s] * self.slope[s] for s in (-1, 1)}
        self.vband_h = {s: self.slope[s] * self.height[s] * (0.13 + 0.05 * noise1(rng, y, 6.0)) for s in (-1, 1)}
        self.vband_ang = {s: 52.0 + 5.0 * noise1(rng, y, 8.0) for s in (-1, 1)}
        self.talus_ang = {s: 38.0 + 2.5 * noise1(rng, y, 11.0) for s in (-1, 1)}
        self.col_frac = {s: 0.56 + 0.12 * noise1(rng, y, 25.0) for s in (-1, 1)}
        self.ledge_w = {s: np.clip(1.1 * noise1(rng, y, 9.0) - 0.05, 0.0, 1.0) for s in (-1, 1)}
        self.col_ang = {s: 86.0 + 2.0 * noise1(rng, y, 13.0) for s in (-1, 1)}
        self.ent_ang = {s: 78.0 + 4.0 * noise1(rng, y, 16.0) for s in (-1, 1)}
        self.cap_h = {s: 0.55 + 0.25 * noise1(rng, y, 12.0) for s in (-1, 1)}
        sm = 3.0 / ROW_DY                              # the wall profile changes smoothly along the gorge (3 m)
        for d in (self.height, self.talus_h, self.talus_ang, self.col_frac, self.ledge_w, self.col_ang, self.ent_ang, self.cap_h,
                  self.vband_h, self.vband_ang, self.slope):
            for s in (-1, 1):
                d[s] = gaussian_filter1d(d[s], sm, mode="nearest")

    def xc_fn(self, yy):
        a1, l1, ph1, a2, l2, ph2, k, f0 = self._ax
        yy = np.asarray(yy, float)
        return k * (a1 * np.sin(2 * np.pi * yy / l1 + ph1) + a2 * np.sin(2 * np.pi * yy / l2 + ph2) - f0)

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

    def at_lateral(self, y, u):
        """World x of the point at lateral offset u (m, east positive) on row y."""
        return self.xc_fn(y) + np.asarray(u) / np.cos(np.interp(y, self.y, self.theta))

    # --- wall features ----------------------------------------------------------------------------
    def _wall_features(self, rng):
        """Per side: the columns (centers along the wall, width 0.5 to 1.3 m, depth, facet ridge, tone,
        cross-joint spacing, top offset) and the entablature's irregular blocks (rows 0.22 to 0.65 m high,
        each with its own block widths 0.25 to 1.0 m)."""
        self.wf = {}
        for s in (-1, 1):
            n = 700
            c = np.cumsum(rng.uniform(0.5, 1.3, n)) + Y0 - 10
            yy = np.linspace(Y0 - 10, Y1 + 10, 600)
            nr, nb = 200, 320
            rz = np.cumsum(rng.uniform(0.22, 0.65, nr)) - 12.0
            bnd = np.cumsum(rng.uniform(0.25, 1.0, (nr, nb)), axis=1) + Y0 - 14 - rng.uniform(0, 1, (nr, 1))
            self.wf[s] = dict(
                c=c, dep=np.clip(rng.normal(0, 0.12, n), -0.3, 0.3), k=rng.uniform(0.3, 0.7, n),
                asym=rng.uniform(-0.25, 0.25, n), tone=rng.uniform(0, 1, n) ** 0.9, grey=rng.uniform(0, 1, n),
                jsp=rng.uniform(1.5, 5.5, n), jph=rng.uniform(0, 5, n), top=rng.normal(0, 0.9, n),
                pale=(rng.uniform(0, 1, n) < 0.1) * rng.uniform(0.4, 1.0, n),
                sway_lam=rng.uniform(9, 15), sway_ph=rng.uniform(0, 6.3), sway_a=rng.uniform(0.15, 0.3),
                tilt_y=yy, tilt=0.04 * noise1(rng, yy, 30.0), rz=rz, bnd=bnd,
                key=int(rng.integers(1, 1 << 30)))

    def column_d(self, s, y, z):
        """Columnar jointing: protrusion d (m, toward the gorge), distance to the nearest vertical joint
        (m), distance to the nearest cross joint (m), column index, slope of the facet (dd/du) and the
        protrusion step at the nearest cross joint (positive: the segment above sticks out)."""
        w = self.wf[s]
        u = y + w["sway_a"] * np.sin(2 * np.pi * z / w["sway_lam"] + w["sway_ph"]) + np.interp(y, w["tilt_y"], w["tilt"]) * z
        c = w["c"]
        i = np.clip(np.searchsorted(c, u), 1, len(c) - 2)
        left_closer = (u - c[i - 1]) < (c[i] - u)
        n = np.where(left_closer, i - 1, i)
        lo = (c[n] + c[np.maximum(n - 1, 0)]) / 2
        hi = (c[n] + c[np.minimum(n + 1, len(c) - 1)]) / 2
        jd = np.minimum(u - lo, hi - u)
        seg = np.floor((z - w["jph"][n]) / w["jsp"][n])
        zf = (z - w["jph"][n]) / w["jsp"][n] - seg
        cj = np.minimum(zf, 1 - zf) * w["jsp"][n]
        def off(sg):
            hs = hash01(n, sg.astype(np.int64), w["key"])
            return np.where(hs < 0.4, (hs - 0.2) * 0.6, 0.0)          # 40 % of the segments step in or out
        so = off(seg)
        step = np.where(zf > 0.5, off(seg + 1) - so, so - off(seg - 1)) * np.where(zf > 0.5, 1, -1)
        ridge = c[n] + w["asym"][n] * (hi - lo)
        slope = -w["k"][n] * np.sign(u - ridge)
        d = w["dep"][n] + so - w["k"][n] * np.abs(u - ridge)
        return d, jd, cj, n, slope, step

    def block_d(self, s, y, z):
        """Entablature: irregular blocks in wavy rows. Protrusion d, distance to the nearest block edge
        (m), block hash, distance below the row's top edge (m), and the protrusion of the block above
        at this point."""
        w = self.wf[s]
        zw = z + 0.12 * np.sin(y * 1.1 + 0.5 * np.sin(y * 0.37)) + 0.07 * np.sin(y * 2.9 + 1.3)
        yw = y + 0.08 * np.sin(z * 2.3)
        rz, bnd = w["rz"], w["bnd"]
        r = np.clip(np.searchsorted(rz, zw) - 1, 0, len(rz) - 3)

        def block(rr):
            b = np.zeros(rr.shape, np.int64)
            for k in np.unique(rr):
                m = rr == k
                b[m] = np.searchsorted(bnd[k], yw[m])
            b = np.clip(b - 1, 0, bnd.shape[1] - 2)
            h = hash01(rr, b, w["key"] + 5)
            h2 = hash01(rr, b, w["key"] + 9)
            return b, h, h2
        b, h, h2 = block(r)
        mid = (rz[r] + rz[r + 1]) / 2
        d = (h - 0.5) * 0.36 + (h2 - 0.5) * 0.5 * (zw - mid) - 0.06
        _, ha, h2a = block(r + 1)
        mida = (rz[r + 1] + rz[r + 2]) / 2
        d_above = (ha - 0.5) * 0.36 + (h2a - 0.5) * 0.5 * (rz[r + 1] - mida) - 0.06
        dy = np.minimum(yw - bnd[r, b], bnd[r, b + 1] - yw)
        top = rz[r + 1] - zw
        edge = np.minimum(dy, np.minimum(top, zw - rz[r]))
        return d, edge, h, top, d_above

    def col_top_at(self, s, y, z, zc):
        """Weight of the entablature (0 in the colonnade, 1 above it): each column ends at its own height."""
        n = self.column_d(s, y, z)[3]
        return smoothstep(-0.12, 0.12, z - (zc + self.wf[s]["top"][n]))

    def wall_d(self, s, y, z, zc, smooth=False):
        """Protrusion of the wall surface at (y, z) on side s; zc: top of the colonnade at that row. With
        smooth, averaged over +-0.25 m along the wall and +-0.2 m in height (the mesh's own resolution:
        the geometry gets the low-pass, the texture the detail, so the mesh shows no stair steps)."""
        if smooth:
            acc, wsum = 0.0, 0.0
            for dy_, wy in ((-0.24, 0.5), (-0.12, 0.85), (0.0, 1.0), (0.12, 0.85), (0.24, 0.5)):
                for dz_, wz in ((-0.2, 0.6), (0.0, 1.0), (0.2, 0.6)):
                    acc = acc + wy * wz * self.wall_d(s, y + dy_, z + dz_, zc)
                    wsum += wy * wz
            return acc / wsum
        d1 = self.column_d(s, y, z)[0]
        d2 = self.block_d(s, y, z)[0]
        t = self.col_top_at(s, y, z, zc)
        return d1 * (1 - t) + d2 * t

    # --- terrain ----------------------------------------------------------------------------------
    def _terrain(self, rng):
        self._wall_features(rng)
        y, NR = self.y, len(self.y)
        self.n_floor = Field2(rng, (-80, Y0 - 5), (80, Y1 + 5), 0.25, 1.2)
        self.n_bump = Field2(rng, (-80, Y0 - 5), (80, Y1 + 5), 0.2, 0.45)
        self.n_plat = Field2(rng, (-100, Y0 - 5), (100, Y1 + 5), 1.0, 7.0)
        self.n_talus = Field2(rng, (-80, Y0 - 5), (80, Y1 + 5), 0.3, 1.0)
        cols = []
        for s in (-1, 1):
            side = ([(s, "talus", f) for f in np.arange(1, NT + 1) / NT] + [(s, "vslope", f) for f in np.arange(1, NV + 1) / NV]
                    + [(s, "col", f) for f in np.arange(1, NCOL + 1) / NCOL]
                    + [(s, "ledge", k) for k in (0, 1)] + [(s, "ent", f) for f in np.arange(1, NENT + 1) / NENT]
                    + [(s, "cap", k) for k in range(NCAP)] + [(s, "plat", d) for d in XI_PLAT])
            if s < 0:
                cols = side[::-1] + [(-1, "toe", 0.0)] + [(0, "floor", e) for e in ETA_FLOOR]
            else:
                cols += [(1, "toe", 0.0)] + side
        NC = len(cols)
        kind_id = {"floor": 0, "toe": 0, "talus": 1, "col": 2, "ledge": 3, "ent": 4, "cap": 5, "plat": 6, "vslope": 7}
        kind = np.array([kind_id[c[1]] for c in cols])
        U, Z = np.zeros((NR, NC)), np.zeros((NR, NC))
        half = self.width / 2
        self.rim_xi, self.rim_z = {}, {}
        self.col_top = {s: np.zeros(NR) for s in (-1, 1)}
        self.talus_top = {s: np.zeros(NR) for s in (-1, 1)}
        for s in (-1, 1):
            order = [j for j in sorted((j for j, c in enumerate(cols) if c[0] == s), key=lambda j: (j if s > 0 else -j))]
            order = [j for j in order if cols[j][1] != "toe"]
            jt = cols.index((s, "toe", 0.0))
            XS, ZS, DISP = np.zeros((NR, len(order))), np.zeros((NR, len(order))), np.zeros((NR, len(order)), bool)
            edge_z = np.zeros(NR)
            for i in range(NR):
                f0, yy = self.floor0[i], y[i]
                edge = f0 + 0.1 * self.n_floor(np.array(s * half[i] + self.xc[i]), np.array(yy))
                edge_z[i] = edge
                ht = self.talus_h[s][i]
                xt = ht / math.tan(math.radians(self.talus_ang[s][i]))
                hv = self.vband_h[s][i]
                xv = xt + hv / math.tan(math.radians(self.vband_ang[s][i]))
                H = self.height[s][i]
                z_t, z_v = edge + ht, edge + ht + hv
                z_c = z_v + (f0 + H - z_v) * self.col_frac[s][i]
                self.col_top[s][i], self.talus_top[s][i] = z_c, z_t
                xc_ = xv + (z_c - z_v) / math.tan(math.radians(self.col_ang[s][i]))
                lw = self.ledge_w[s][i]
                z_l, z_r = z_c + 0.12, f0 + H
                xr = xc_ + lw + 0.03 + (z_r - z_l) / math.tan(math.radians(self.ent_ang[s][i]))
                ch = self.cap_h[s][i]
                for k, j in enumerate(order):
                    _, kd, c = cols[j]
                    if kd == "talus":
                        bump = float(self.n_talus(np.array(yy), np.array(s * 11 + c * xt))) if c < 1 else 0.0
                        xi, zz = c * xt, edge + ht * c ** 1.1 + 0.25 * min(1.0, ht / 3) * bump * math.sin(math.pi * c)
                    elif kd == "vslope":
                        bump = float(self.n_bump(np.array(yy), np.array(s * 23 + c * 4)))
                        xi, zz = xt + c * (xv - xt) + 0.15 * bump * (c < 1) * (hv > 0.3), z_t + c * hv
                    elif kd == "col":
                        zz = z_v + c * (z_c - z_v)
                        xi = xv + (zz - z_v) / math.tan(math.radians(self.col_ang[s][i]))
                        DISP[i, k] = True
                    elif kd == "ledge":
                        xi, zz = (xc_ + lw, z_c + 0.04) if c == 0 else (xc_ + lw + 0.03, z_l)
                        DISP[i, k] = c == 1
                    elif kd == "ent":
                        zz = z_l + c * (z_r - z_l)
                        xi = xc_ + lw + 0.03 + (zz - z_l) / math.tan(math.radians(self.ent_ang[s][i]))
                        DISP[i, k] = c < 1
                    elif kd == "cap":
                        t = (c + 1) / NCAP
                        xi, zz = xr + 1.4 * t, z_r + ch * (1 - (1 - t) ** 2)
                    else:
                        xi = xr + 1.4 + c
                        zz = z_r + ch + 0.015 * c + 0.7 * min(1.0, c / 8) * self.n_plat(np.array(s * (half[i] + xi) + self.xc[i]), np.array(yy))
                    XS[i, k], ZS[i, k] = xi, zz
                self.rim_xi[(s, i)], self.rim_z[(s, i)] = xr, z_r
            # the wall's relief, low-passed to the mesh resolution, all wall vertices at once
            ii, kk = np.nonzero(DISP)
            zc_rows = self.col_top[s][ii]
            XS[ii, kk] -= self.wall_d(s, y[ii], ZS[ii, kk], zc_rows, smooth=True)
            # outward monotonic (no overhang along a row)
            ramp = np.arange(XS.shape[1]) * 0.002
            XS = np.maximum.accumulate(XS + ramp, axis=1) - ramp
            XS = np.maximum(XS, 0.0)
            for k, j in enumerate(order):
                U[:, j], Z[:, j] = s * (half + XS[:, k]), ZS[:, k]
            U[:, jt], Z[:, jt] = s * half, edge_z
        for i in range(NR):
            f0 = self.floor0[i]
            # the start and landing zones are level: no floor noise there, the channel shallower
            site = max(float(smoothstep(a - 3.0, a, y[i]) * smoothstep(b + 3.0, b, y[i])) for a, b in SITES)
            for j, (s, kd, c) in enumerate(cols):
                if kd == "floor":
                    U[i, j] = c * half[i]
                    Z[i, j] = (f0 - 0.25 * (1 - 0.7 * site) * (1 - c * c)
                               + (1 - site) * (0.10 * self.n_floor(np.array(c * half[i] + self.xc[i]), np.array(y[i]))
                                               + 0.05 * self.n_bump(np.array(c * half[i] + self.xc[i]), np.array(y[i]))))
        X = self.xc[:, None] + U / np.cos(self.theta)[:, None]
        Y = np.repeat(y[:, None], NC, 1)
        self.grid = np.stack([X, Y, Z], -1)
        self.cols, self.col_kind, self.U = cols, kind, U
        self.mid = cols.index((0, "floor", ETA_FLOOR[len(ETA_FLOOR) // 2]))
        self.zc = Z[:, self.mid]
        self.wall_angle = {s: np.degrees(np.arctan2(self.height[s], np.array([self.rim_xi[(s, i)] for i in range(NR)])))
                           for s in (-1, 1)}
        idx = np.arange(NR * NC).reshape(NR, NC)
        a, b, c_, d = idx[:-1, :-1], idx[:-1, 1:], idx[1:, :-1], idx[1:, 1:]
        F = np.concatenate([np.stack([a, b, d], -1).reshape(-1, 3), np.stack([a, d, c_], -1).reshape(-1, 3)])
        self.V = self.grid.reshape(-1, 3)
        fn = np.cross(self.V[F[:, 1]] - self.V[F[:, 0]], self.V[F[:, 2]] - self.V[F[:, 0]])
        area = np.linalg.norm(fn, axis=1) / 2
        self.F = F[area > 1e-6]
        # texture columns: width proportional to the column's physical width (the plateau at half density)
        w = np.median(np.linalg.norm(np.diff(self.grid, axis=1), axis=-1), axis=0)
        wt = np.maximum(w, 0.02) * np.where((kind[1:] == 6) & (kind[:-1] == 6), 0.5, 1.0)
        self.ucol = np.concatenate([[0.0], np.cumsum(wt)]) / wt.sum()
        ii, jj = np.meshgrid(np.arange(NR), np.arange(NC), indexing="ij")
        self.UV = np.stack([self.ucol[jj.ravel()], ii.ravel() / (NR - 1)], -1)
        self.normals = vertex_normals(self.V, F).reshape(NR, NC, 3)

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

    def path_dist(self, xy):
        """Horizontal distance of points (N x 2) from the flight path line (extended 6 m beyond both ends)."""
        pp = self.path
        a = np.vstack([pp[0] - 6 * (pp[1] - pp[0]) / np.linalg.norm(pp[1] - pp[0]), pp,
                       pp[-1] + 8 * (pp[-1] - pp[-2]) / np.linalg.norm(pp[-1] - pp[-2])])[:, :2]
        xy = np.atleast_2d(xy)
        best = np.full(len(xy), np.inf)
        for p0, p1 in zip(a[:-1], a[1:]):
            d = p1 - p0
            t = np.clip((xy - p0) @ d / (d @ d), 0, 1)
            best = np.minimum(best, np.linalg.norm(xy - (p0 + t[:, None] * d), axis=1))
        return best

    def keep_ok(self, v, low=KEEP_LOW, r=KEEP_R):
        """The keep-out rule for any geometry: vertices higher than `low` above the centerline floor
        must be at least r m (horizontally) from the flight path; nothing in the start and landing zones."""
        v = np.atleast_2d(v)
        if any(np.any((v[:, 1] > a) & (v[:, 1] < b) & (np.abs(self.lateral(v[:, 0], v[:, 1])) < 3.2)) for a, b in SITES):
            return False
        hi = v[:, 2] - self.floor_c(v[:, 1]) > low
        return not hi.any() or self.path_dist(v[hi, :2]).min() >= r

    # --- ray helpers (scratch client) --------------------------------------------------------------
    def rays(self, a, b):
        """Hit fraction and body of segments a -> b (N x 3) in the scratch client (collision geometry)."""
        a, b = np.asarray(a, float), np.asarray(b, float)
        frac, body = np.ones(len(a)), -np.ones(len(a), int)
        B = 4000                                   # PyBullet's maximum batch is 2^14 rays
        for k in range(0, len(a), B):
            res = p.rayTestBatch(a[k:k + B].tolist(), b[k:k + B].tolist(), numThreads=4, physicsClientId=self._client)
            frac[k:k + B] = [r[2] if r[0] >= 0 else 1.0 for r in res]
            body[k:k + B] = [r[0] for r in res]
        return frac, body

    def ground_z(self, xy):
        xy = np.atleast_2d(xy)
        a = np.column_stack([xy, np.full(len(xy), 80.0)])
        b = np.column_stack([xy, np.full(len(xy), -30.0)])
        frac, _ = self.rays(a, b)
        return 80.0 - 110.0 * frac

    def terrain_z(self, xy):
        """Height of the terrain mesh alone (no objects) under xy: the topmost hit of a vertical ray in a
        scratch client that holds only the terrain."""
        xy = np.atleast_2d(xy)
        if getattr(self, "_tclient", None) is None:
            self._tclient = p.connect(p.DIRECT)
            p.createMultiBody(0, p.createCollisionShape(p.GEOM_MESH, fileName=self.files["terrain"], flags=p.GEOM_FORCE_CONCAVE_TRIMESH,
                                                        physicsClientId=self._tclient), physicsClientId=self._tclient)
        a = np.column_stack([xy, np.full(len(xy), 80.0)])
        b = np.column_stack([xy, np.full(len(xy), -30.0)])
        frac = np.ones(len(a))
        for k in range(0, len(a), 4000):
            res = p.rayTestBatch(a[k:k + 4000].tolist(), b[k:k + 4000].tolist(), physicsClientId=self._tclient)
            frac[k:k + 4000] = [r[2] if r[0] >= 0 else 1.0 for r in res]
        return 80.0 - 110.0 * frac

    def sunlit(self, pts, normals, offset=0.05):
        a = pts + offset * normals
        frac, _ = self.rays(a, a + 150 * SUN)
        return (frac >= 1.0).astype(float)

    def surface_point(self, y, s, kind, frac):
        """World point and normal on side s of row y in a wall segment (talus: frac 0 toe .. 1 top)."""
        i = int(np.clip(round((y - Y0) / ROW_DY), 0, len(self.y) - 1))
        js = [j for j, c in enumerate(self.cols) if c[0] == s and c[1] in (("toe", kind) if kind == "talus" else (kind,))]
        js = sorted(js, key=lambda j: abs(j - self.mid))
        k = frac * (len(js) - 1)
        k0 = int(min(k, len(js) - 2)); t = k - k0
        pt = self.grid[i, js[k0]] * (1 - t) + self.grid[i, js[k0 + 1]] * t
        n = self.normals[i, js[k0]] * (1 - t) + self.normals[i, js[k0 + 1]] * t
        return pt, n / np.linalg.norm(n)

    # --- boulders ------------------------------------------------------------------------------------
    def _place_boulder(self, rng, xy, size, flat, angular, sink, wall, cluster=-1, check=True):
        v, f, fn = boulder_shape(rng, size, flat, angular)
        R = rotation(rng.uniform(0, 2 * np.pi), rng.uniform(0, 0.25), rng.uniform(0, 2 * np.pi))
        v = v @ R.T
        fn = fn @ R.T
        foot = np.array(xy) + v[:, :2] * 0.7
        g = self.ground_z(foot)
        base = np.percentile(g, 35)
        h = np.ptp(v[:, 2])
        v = v + [xy[0], xy[1], base - v[:, 2].min() - sink * h]
        if check:
            if not self.keep_ok(v):
                return None
            for b in self.boulders:
                lim = (np.ptp(v[:, :2], axis=0).max() + b.size) / 2 * (0.72 if cluster >= 0 else 1.0) + (0.0 if cluster >= 0 else 0.25)
                if np.linalg.norm(v.mean(0)[:2] - b.center[:2]) < lim:
                    return None
        c = v.mean(axis=0)
        ground = float(self.ground_z(c[None, :2])[0])
        b = Boulder(center=c, size=float(np.ptp(v[:, :2], axis=0).max()), height=float(v[:, 2].max() - min(ground, base)),
                    top=float(v[:, 2].max()), verts=v, faces=f, wall=bool(wall), cluster=cluster)
        b.fnorm = fn
        return b

    def _add_boulder_body(self, b):
        col = p.createCollisionShape(p.GEOM_MESH, vertices=b.verts.tolist(), physicsClientId=self._client)
        self.boulder_ids.append(p.createMultiBody(0, col, physicsClientId=self._client))

    def _boulders(self, rng):
        """Large boulders first at stations along the gorge (the fires hide behind some of them), each
        with 1 to 3 smaller companions leaning on it; then scattered boulders on the wash and the talus."""
        self.boulders, self.boulder_ids = [], []
        stations = [6.5 + 6.9 * k for k in range(10)]
        for ys in stations:
            for _ in range(60):
                yb = ys + rng.uniform(-2.5, 2.5)
                half = self.width_at(yb) / 2
                side = rng.choice([-1, 1])
                u = side * rng.uniform(1.1, min(2.6, half - 0.6))
                size = float(rng.uniform(1.9, 2.7))
                b = self._place_boulder(rng, (float(self.at_lateral(yb, u)), yb), size, rng.uniform(0.7, 0.92),
                                        rng.uniform(0.3, 1.0), rng.uniform(0.1, 0.18), False)
                if b is None or b.top - self.floor_c(yb) > ROUTE_TOP or b.height < 1.15:
                    continue
                self.boulders.append(b); self._add_boulder_body(b)
                k0 = len(self.boulders) - 1
                for _ in range(int(rng.integers(1, 4))):
                    for _ in range(20):
                        a = rng.uniform(0, 2 * np.pi)
                        if abs(math.remainder(a - math.pi / 2, 2 * math.pi)) < 1.1:
                            continue                             # keep the downstream side free (fires hide there)
                        sz = float(rng.uniform(0.55, 1.2))
                        d = (b.size + sz) / 2 * rng.uniform(0.62, 0.8)
                        xy = b.center[:2] + d * np.array([math.cos(a), math.sin(a)])
                        c = self._place_boulder(rng, xy, sz, rng.uniform(0.6, 0.9), rng.uniform(0.2, 1.0), rng.uniform(0.1, 0.25),
                                                False, cluster=k0)
                        if c is not None:
                            self.boulders.append(c); self._add_boulder_body(c)
                            break
                break
        n_scatter = int(rng.integers(20, 26))
        tries = 0
        while n_scatter > 0 and tries < 3000:
            tries += 1
            yb = rng.uniform(-6, Y_END + 12)
            half = self.width_at(yb) / 2
            if rng.random() < 0.6:
                s = rng.choice([-1, 1])
                pt, _ = self.surface_point(yb, s, "talus", rng.uniform(0.05, 0.85))
                xy, wall = pt[:2], True
            else:
                xy, wall = (float(self.at_lateral(yb, rng.uniform(-half + 0.4, half - 0.4))), yb), False
            b = self._place_boulder(rng, xy, float(rng.uniform(0.6, 1.6)), rng.uniform(0.6, 0.9), rng.uniform(0.0, 1.0),
                                    rng.uniform(0.15, 0.3), wall)
            if b is not None and self.path_dist(b.verts[:, :2]).min() < 2.0 and b.top - self.floor_c(b.center[1]) > ROUTE_TOP:
                b = None                                          # under the route: low enough for 1.5 m of clearance
            if b is not None:
                self.boulders.append(b); self._add_boulder_body(b)
                n_scatter -= 1
        for k, b in enumerate(self.boulders):
            vn = vertex_normals(b.verts, b.faces)
            self.parts.append(Part(b.verts, b.faces, vn, "boulder", np.zeros(3), "boulder", k, 8 if b.size > 1.0 else 6,
                                   center=np.array([*b.center[:2], b.verts[:, 2].min()]), extra=float(rng.uniform(0, 1)),
                                   fnorm=b.fnorm))
            del b.fnorm

    # --- fires ----------------------------------------------------------------------------------------
    def _fire_points(self, fb):
        """Points whose line of sight decides whether a fire is seen: the patch center 0.1 m up, and the
        flaming rim points at half the flame height."""
        pts = [fb.center + [0, 0, 0.1]]
        ang = np.arange(RIM_N) / RIM_N * 2 * np.pi
        for k in range(0, RIM_N, 8):
            if fb.active[k]:
                q = fb.center[:2] + fb.rim[k] * np.array([math.cos(ang[k]), math.sin(ang[k])])
                pts.append(np.array([q[0], q[1], fb.center[2] + 0.5 * fb.flame_h]))
        return np.array(pts)

    def _seen(self, pts_fire, path_pts):
        """Fraction of path points from which any of the fire's points is in sight."""
        if len(path_pts) == 0:
            return 0.0
        any_seen = np.zeros(len(path_pts), bool)
        for q in pts_fire:
            frac, _ = self.rays(path_pts, np.repeat(q[None], len(path_pts), 0))
            any_seen |= frac >= 0.999
        return float(any_seen.mean())

    def _make_fire(self, rng, c, R, kind, hidden, boulder):
        """A fire at c: a burned patch of mean radius R with a ragged rim, flaming along most of it."""
        ang = np.arange(RIM_N) / RIM_N * 2 * np.pi
        rim = np.zeros(RIM_N)
        for k in range(1, 5):
            rim += rng.uniform(0.1, 0.22) / k * np.cos(k * ang + rng.uniform(0, 2 * np.pi))
        rim = R * (1 + rim + 0.07 * rng.normal(size=RIM_N))
        # the flaming front: an advancing edge on the downwind side (40 to 55 % of the rim, ragged), a few
        # short flaming stretches elsewhere; the rest smolders
        act_n = np.zeros(RIM_N)
        for k in range(2, 6):
            act_n += 0.35 * np.cos(k * ang + rng.uniform(0, 2 * np.pi)) / k
        wind = math.atan2(self.axis_dir(c[1])[1], self.axis_dir(c[1])[0]) + rng.uniform(-0.5, 0.5)
        act_n += np.cos(ang - wind)
        active = (act_n > np.percentile(act_n, rng.uniform(45, 60))).astype(float)
        for _ in range(int(rng.integers(1, 3))):
            k0 = int(rng.integers(0, RIM_N))
            active[(k0 + np.arange(int(rng.integers(2, 5)))) % RIM_N] = 1.0
        flame_h = {"litter": rng.uniform(0.25, 0.5), "grass": rng.uniform(0.35, 0.6), "log": rng.uniform(0.3, 0.55),
                   "shrub": rng.uniform(0.35, 0.55), "tree": rng.uniform(0.35, 0.6)}[kind]
        fb = Firebrand(center=np.array(c, float), radius=float(R), temp_c=0.0, hidden=hidden, boulder=boulder,
                       kind=kind, rim=rim, active=active, flame_h=float(flame_h))
        return fb

    def _finish_fire(self, rng, fb):
        """Flame tongues, ember pieces, radiated power and smoke of a placed fire. Tongues sit every 4 to
        7 cm along the flaming front and overlap (each 0.18 to 0.4 m wide), so they merge into one ragged
        sheet; heights are lognormal (a few licks two to three times the median) times a smooth variation
        along the front; column 8 of a tongue is its arc coordinate along the front (m), which fire.py
        uses for the height variation that travels along it in time."""
        c, R = fb.center, fb.radius
        ang = np.arange(RIM_N) / RIM_N * 2 * np.pi
        wind = self.axis_dir(c[1])
        wa = math.atan2(wind[1], wind[0])
        tongues = []
        L, s_arc = 0.0, 0.0
        along = 0.6 * noise1(rng, np.arange(RIM_N, dtype=float), 9.0)
        for k in range(RIM_N):
            seg = fb.rim[k] * 2 * np.pi / RIM_N
            if not fb.active[k]:
                s_arc += 0.5
                continue
            L += seg
            n = max(1, int(round(seg / rng.uniform(0.04, 0.07))))
            for m in range(n):
                a = ang[k] + (m + rng.uniform(0.1, 0.9)) / n * 2 * np.pi / RIM_N
                r = np.interp(a, np.append(ang, 2 * np.pi), np.append(fb.rim, fb.rim[0])) * rng.uniform(0.82, 1.02)
                q = c[:2] + r * np.array([math.cos(a), math.sin(a)])
                h = fb.flame_h * min(2.6, math.exp(rng.normal(0, 0.42) + 0.6 * along[k])) * (0.85 + 0.25 * max(0.0, math.cos(a - wa)))
                tongues.append([q[0], q[1], 0.0, rng.uniform(0.28, 0.5) * (0.6 + 0.5 * h), h, rng.uniform(0, 100), rng.uniform(1.6, 3.2),
                                rng.uniform(0.15, 0.45), s_arc + seg * m / n])
                if rng.random() < 0.3:                           # flames in the band just behind the front
                    q2 = c[:2] + r * rng.uniform(0.62, 0.85) * np.array([math.cos(a), math.sin(a)])
                    tongues.append([q2[0], q2[1], 0.0, rng.uniform(0.14, 0.26), h * rng.uniform(0.25, 0.5), rng.uniform(0, 100),
                                    rng.uniform(2.0, 3.6), 0.3, s_arc + seg * m / n + 0.13])
            s_arc += seg
        if fb.kind == "shrub":
            sc = fb.extra["shrub"]
            for i in range(18):
                q = sc[:2] + rng.normal(0, 0.22, 2)
                tongues.append([q[0], q[1], -1.0, rng.uniform(0.25, 0.45), fb.flame_h * math.exp(rng.normal(0.7, 0.35)), rng.uniform(0, 100),
                                rng.uniform(1.3, 2.4), 0.2, 50.0 + 0.1 * i])
            L += 1.5
        if fb.kind == "tree":
            tc = fb.extra["tree"]
            for i in range(11):
                a = i / 11 * 2 * np.pi
                q = tc[:2] + 0.18 * np.array([math.cos(a), math.sin(a)])
                tongues.append([q[0], q[1], -1.0, rng.uniform(0.15, 0.3), fb.flame_h * math.exp(rng.normal(0.4, 0.4)), rng.uniform(0, 100),
                                rng.uniform(1.8, 3.0), 0.15, 60.0 + 0.08 * i])
            L += 0.8
        if fb.kind == "log":
            a, b = fb.extra["log"]
            for i, t in enumerate(np.linspace(0.06, 0.94, 12)):
                q = a + t * (b - a)
                tongues.append([q[0], q[1], -1.0, rng.uniform(0.15, 0.3), fb.flame_h * math.exp(rng.normal(0.1, 0.4)), rng.uniform(0, 100),
                                rng.uniform(1.8, 3.0), 0.2, 70.0 + 0.08 * i])
            L += 0.6
        T = np.array(tongues)
        T[:, 2] = np.where(T[:, 2] < 0, self.ground_z(T[:, :2]) + 0.02, self.terrain_z(T[:, :2]) - 0.02)
        if fb.kind in ("shrub", "tree", "log"):
            key = {"shrub": "shrub_base", "tree": "tree_base", "log": "log_base"}[fb.kind]
            for i in np.nonzero(np.array(tongues)[:, 2] < 0)[0]:
                T[i, 2] = fb.extra.get(key, T[i, 2]) if np.isscalar(fb.extra.get(key, None)) else T[i, 2]
        fb.tongues = T
        intensity = {"litter": 45e3, "grass": 60e3, "log": 50e3, "shrub": 90e3, "tree": 80e3}[fb.kind]   # W per m of front
        fb.power_w = float(0.3 * intensity * L)                  # radiant fraction 0.3
        fb.smoke = float(0.6 + 0.5 * L)
        fb.smoke_dark = {"litter": 0.08, "grass": 0.04, "log": 0.15, "shrub": 0.3, "tree": 0.2}[fb.kind]
        # ember pieces: coals in the patch, mostly in the band behind the front
        t = float(rng.uniform(620, 900))
        pieces = []
        act_at = lambda a: np.interp(a, np.append(ang, 2 * np.pi), np.append(fb.active, fb.active[0]))
        for _ in range(int(rng.integers(10, 16))):
            for _ in range(20):
                a = rng.uniform(0, 2 * np.pi)
                if act_at(a) > 0.5 or rng.random() < 0.3:
                    break
            r = np.interp(a, np.append(ang, 2 * np.pi), np.append(fb.rim, fb.rim[0])) * (1 - abs(rng.normal(0, 0.2)))
            q = c[:2] + r * 0.82 * np.array([math.cos(a), math.sin(a)])
            pr = float(rng.uniform(0.02, 0.05))
            pieces.append((np.array([q[0], q[1], 0.0]), pr, float(t * rng.uniform(0.86, 1.0))))
        gz = self.terrain_z(np.array([q[0][:2] for q in pieces]))
        # resting on the burned patch (drawn 1.2 cm above the terrain), most of each piece above it
        pieces = [(np.array([q[0][0], q[0][1], z + 0.012 + 0.3 * q[1]]), q[1], q[2]) for q, z in zip(pieces, gz)]
        pieces[0] = (pieces[0][0], pieces[0][1], t)
        fb.pieces, fb.temp_c = pieces, t

    def front_points(self, f, n=10):
        """Points along fire f's flaming front (and its burning fuel), each with its share of the power."""
        ang = np.arange(RIM_N) / RIM_N * 2 * np.pi
        k = np.nonzero(f.active > 0.5)[0]
        sel = k[np.linspace(0, len(k) - 1, min(n, len(k))).astype(int)]
        pts = np.column_stack([f.center[0] + f.rim[sel] * np.cos(ang[sel]), f.center[1] + f.rim[sel] * np.sin(ang[sel]),
                               np.full(len(sel), f.center[2] + 0.35 * f.flame_h)])
        for key in ("shrub", "tree"):
            if key in f.extra:
                c = np.asarray(f.extra[key], float)
                pts = np.vstack([pts, [c[0], c[1], f.center[2] + 0.5]])
        return pts

    def _firebrands(self, rng, n_hidden=6, n_open=2):
        """Hidden fires: just behind a boulder at least 1.3 m tall, on the line from an approach point
        D m back along the path through the boulder, accepted if none of the fire's points (patch
        center, flaming rim at half the flame height) is in sight from at least 80 % of the path points
        3 to 20 m before it (ray tests against terrain and boulders). Open fires: on the wash 1.5 to 3 m
        from the path, the patch center in sight from at least 80 % of the path points 3 to 25 m before."""
        self.firebrands = []
        pp = self.path_points(0.25)

        def before(c, d0, d1):
            dy = c[1] - pp[:, 1]
            return pp[(dy >= d0) & (dy <= d1)]

        def free(c, r):
            u = self.lateral(c[0], c[1])
            return (abs(u) <= self.width_at(c[1]) / 2 - r - 0.1
                    and all(np.linalg.norm(c[:2] - b.center[:2]) > b.size / 2 + r + 0.05 for b in self.boulders)
                    and all(np.linalg.norm(c[:2] - f.center[:2]) > 5.0 for f in self.firebrands)
                    and not any(a - 2 < c[1] < b + 2 for a, b in SITES))
        def free_far(c, r):
            return (all(np.linalg.norm(c[:2] - b.center[:2]) > b.size / 2 + r + 0.05 for b in self.boulders)
                    and all(np.linalg.norm(c[:2] - f.center[:2]) > 5.0 for f in self.firebrands)
                    and not any(a - 2 < c[1] < b + 2 for a, b in SITES))
        hidden_kinds = ["litter", "grass", "log", "litter", "litter", "grass"]
        cand = [k for k, b in enumerate(self.boulders) if b.height >= 1.15 and 6 < b.center[1] < Y_END - 3 and not b.wall]
        rng.shuffle(cand)
        for k in cand:
            if sum(f.hidden for f in self.firebrands) >= n_hidden:
                break
            b = self.boulders[k]
            kind = hidden_kinds[sum(f.hidden for f in self.firebrands)]
            R0 = float(rng.uniform(0.38, 0.6))
            for D, phi, R in [(D, phi, R) for R in (R0, 0.8 * R0, 0.65 * R0) for D in (6.0, 9.0, 12.0, 16.0)
                              for phi in (0.0, 0.3, -0.3, 0.55, -0.55)]:
                a = pp[np.argmin(np.abs(pp[:, 1] - (b.center[1] - D)))]
                d = (b.center[:2] - a[:2]) / np.linalg.norm(b.center[:2] - a[:2])
                d = np.array([d[0] * math.cos(phi) - d[1] * math.sin(phi), d[0] * math.sin(phi) + d[1] * math.cos(phi)])
                c = b.center[:2] + d * (((b.verts[:, :2] - b.center[:2]) @ d).max() + R + 0.12)
                c3 = np.array([c[0], c[1], self.ground_z(c[None])[0]])
                if not free(c3, R):
                    continue
                fb = self._make_fire(rng, c3, R, kind, True, k)
                if kind == "log":
                    th = math.atan2(d[1], d[0]) + math.pi / 2 + rng.uniform(-0.4, 0.4)
                    e = np.array([math.cos(th), math.sin(th)]) * rng.uniform(0.45, 0.6)
                    fb.extra["log"] = (c - e, c + e)
                if self._seen(self._fire_points(fb), before(c3, 3, 20)) <= 0.2:
                    self.firebrands.append(fb)
                    break
        open_kinds = ["shrub", "tree"]
        for _ in range(3000):
            if sum(not f.hidden for f in self.firebrands) >= n_open:
                break
            kind = open_kinds[sum(not f.hidden for f in self.firebrands)]
            yy = rng.uniform(12, Y_END - 6)
            half = self.width_at(yy) / 2
            side = rng.choice([-1, 1])
            R = float(rng.uniform(0.6, 0.85))
            if kind == "tree":
                u = side * rng.uniform(half - 1.2, half + 0.2)
            else:
                u = side * rng.uniform(1.6, min(3.0, half - 0.9))
            c = np.array([self.at_lateral(yy, u), yy])
            c3 = np.array([c[0], c[1], self.ground_z(c[None])[0]])
            th_ = np.interp(yy, self.y, self.theta)
            tree_xy = c + np.array([math.cos(th_), -math.sin(th_)]) * side * (R + 0.12)
            if kind == "tree" and self.path_dist(tree_xy[None])[0] < KEEP_R + 0.8:
                continue
            if not (free(c3, R) if kind != "tree" else (abs(self.lateral(c3[0], c3[1])) <= half + 0.4 and free_far(c3, R))):
                continue
            fb = self._make_fire(rng, c3, R, kind, False, -1)
            lat = np.array([math.cos(np.interp(yy, self.y, self.theta)), -math.sin(np.interp(yy, self.y, self.theta))]) * side
            fb.extra[kind] = np.array([*(c + lat * (R * 0.8 if kind == 'shrub' else R + 0.12)), 0.0])
            if self._seen(np.array([c3 + [0, 0, 0.1]]), before(c3, 3, 25)) >= 0.8:
                self.firebrands.append(fb)
        self.firebrands.sort(key=lambda f: f.center[1])

    def in_fire_zone(self, xy, margin=0.0):
        """Whether points (N x 2) are inside a burned patch grown by `margin`."""
        xy = np.atleast_2d(xy)
        out = np.zeros(len(xy), bool)
        for f in self.firebrands:
            d = xy - f.center[:2]
            a = np.mod(np.arctan2(d[:, 1], d[:, 0]), 2 * np.pi)
            r = np.interp(a, np.append(np.arange(RIM_N) / RIM_N * 2 * np.pi, 2 * np.pi), np.append(f.rim, f.rim[0]))
            out |= np.linalg.norm(d, axis=1) < r + margin
        return out

    def _sightlines(self):
        """Segments from path points 3 to 25 m before each open fire to its center (keep them clear)."""
        if hasattr(self, "_sl"):
            return self._sl
        pp = self.path_points(1.0)
        segs = []
        for f in self.firebrands:
            if f.hidden:
                continue
            dy = f.center[1] - pp[:, 1]
            for q in pp[(dy >= 3) & (dy <= 25)]:
                segs.append((q, f.center + [0, 0, 0.1]))
        self._sl = (np.array([s[0] for s in segs]).reshape(-1, 3), np.array([s[1] for s in segs]).reshape(-1, 3))
        return self._sl

    def blocks_sight(self, center, radius):
        a, b = self._sightlines()
        if len(a) == 0:
            return False
        d = b - a
        t = np.clip(((center - a) * d).sum(1) / (d * d).sum(1), 0, 1)
        return bool((np.linalg.norm(a + t[:, None] * d - center, axis=1) < radius + 0.05).any())

    # --- placement on the terrain ----------------------------------------------------------------------
    def ground_at(self, xy, tol=0.03):
        """Terrain height under each point and whether the point is free (no boulder, rock or plant hull
        above the terrain there): small objects are put on the terrain, never on top of a boulder."""
        xy = np.atleast_2d(xy)
        tz = self.terrain_z(xy)
        gz = self.ground_z(xy)
        return tz, gz <= tz + tol

    # --- rocks -----------------------------------------------------------------------------------------
    def _rock_ok(self, v, center, r):
        return (self.keep_ok(v) and not self.in_fire_zone(center[None, :2], r + 0.15)[0] and not self.blocks_sight(center, r)
                and all(np.linalg.norm(center[:2] - b.center[:2]) > b.size / 2 * 0.8 + r * 0.5 for b in self.boulders))

    def _block(self, rng, pt, r, sink=0.45):
        """A fallen column fragment (prism) at pt, its edges knocked off, tilted at random, partly sunk."""
        length = float(rng.uniform(1.2, 3.0) * r)
        v, f = prism(rng, r, length, int(rng.choice([5, 5, 6, 4])))
        v = v * (1 + 0.12 * rng.uniform(-1, 1, (len(v), 1)))
        R = rotation(rng.uniform(0, 2 * np.pi), rng.uniform(0, 0.6), rng.uniform(0, 2 * np.pi))
        v = v @ R.T + pt - [0, 0, sink * r]
        return v, f, length

    def _rocks(self, rng):
        """Rubble of fallen column fragments in clusters on the talus (denser and coarser toward the cliff
        foot), scattered blocks, cobbles on the wash; chips and cobbles at the foot of the boulders. Every
        piece sits on the terrain (never on a boulder)."""
        self.rocks = []
        basalt = [np.array(c, float) for c in ((70, 64, 58), (92, 84, 74), (80, 76, 72), (62, 58, 56), (108, 96, 82))]

        def add_block(pt, r):
            v, f, L = self._block(rng, pt, r)
            if not self._rock_ok(v, pt, L / 2):
                return False
            v, f = split_faces(v, f)
            self.rocks.append(dict(kind="block", center=pt, r=max(r, L / 2), collide=r >= 0.1))
            self.parts.append(Part(v, f, vertex_normals(v, f), "basalt", basalt[int(rng.integers(0, 5))] * rng.uniform(0.85, 1.12),
                                   "rocks", len(self.rocks) - 1, 4, collide=r >= 0.1, center=pt))
            return True
        # rubble clusters on the talus
        n_cl, tries = 0, 0
        while n_cl < 320 and tries < 5000:
            tries += 1
            yb = rng.uniform(Y0 + 2, Y1 - 2)
            s = rng.choice([-1, 1])
            fr = rng.beta(2.0, 1.3)
            c0, _ = self.surface_point(yb, s, "talus", fr)
            n_cl += 1
            for _ in range(int(rng.integers(6, 16))):
                q = c0[:2] + rng.normal(0, 0.7, 2)
                tz, free = self.ground_at(q[None])
                if not free[0]:
                    continue
                r = float(np.clip(rng.lognormal(math.log(0.22), 0.45), 0.08, 0.6))
                add_block(np.array([q[0], q[1], tz[0]]), r)
        # scattered blocks
        tries = 0
        while sum(1 for r in self.rocks if r["kind"] == "block") < 1100 and tries < 4000:
            tries += 1
            yb = rng.uniform(Y0 + 2, Y1 - 2)
            s = rng.choice([-1, 1])
            pt, _ = self.surface_point(yb, s, rng.choice(["talus", "talus", "vslope"]), rng.uniform(0, 1))
            tz, free = self.ground_at(pt[None, :2])
            if free[0]:
                add_block(np.array([pt[0], pt[1], tz[0]]), float(rng.uniform(0.08, 0.3)))
        # cobbles on the wash
        tries = 0
        n_cob = 0
        while n_cob < 650 and tries < 8000:
            tries += 1
            yb = rng.uniform(Y0 + 2, Y1 - 2)
            half = self.width_at(yb) / 2
            e = np.clip(rng.normal(0, 0.55), -1, 1)
            if abs(e) < 0.4 and rng.random() < 0.6:
                continue
            xy = np.array([self.at_lateral(yb, e * half), yb])
            tz, free = self.ground_at(xy[None])
            if not free[0]:
                continue
            r = float(np.clip(rng.lognormal(math.log(0.07), 0.45), 0.035, 0.24))
            v, f = lumpy(rng, 1, 0.25)
            v = v * [r, r * rng.uniform(0.7, 1.0), r * rng.uniform(0.45, 0.75)]
            v = v @ rotation(rng.uniform(0, 2 * np.pi)).T
            ctr = np.array([xy[0], xy[1], tz[0]])
            v = v + ctr + [0, 0, 0.25 * r]
            if not self._rock_ok(v, ctr, r):
                continue
            n_cob += 1
            col = np.array([(140, 132, 122), (118, 110, 100), (150, 132, 106), (96, 90, 84), (164, 156, 140)][int(rng.integers(0, 5))], float)
            self.rocks.append(dict(kind="cobble", center=ctr, r=r, collide=r >= 0.12))
            self.parts.append(Part(v, f, vertex_normals(v, f), "cobble", col * rng.uniform(0.85, 1.1), "rocks", len(self.rocks) - 1, 4,
                                   collide=r >= 0.12, center=ctr))
        # chips and cobbles at the foot of the boulders (on the terrain around them)
        for b in self.boulders:
            if b.size < 0.9:
                continue
            for _ in range(int(rng.integers(5, 12))):
                a = rng.uniform(0, 2 * np.pi)
                d = b.size / 2 * rng.uniform(0.85, 1.4)
                xy = b.center[:2] + d * np.array([math.cos(a), math.sin(a)])
                tz, free = self.ground_at(xy[None])
                if not free[0]:
                    continue
                r = float(rng.uniform(0.04, 0.18))
                if rng.random() < 0.6:
                    v, f = prism(rng, r * 0.6, r * rng.uniform(1.5, 3.0), 4)
                    v, f = split_faces(v @ rotation(rng.uniform(0, 6.3), rng.uniform(0, 0.4), rng.uniform(0, 6.3)).T, f)
                    mat = "chip"
                else:
                    v, f = lumpy(rng, 1, 0.3)
                    v = v * [r, r * 0.8, r * 0.6]
                    mat = "cobble"
                ctr = np.array([xy[0], xy[1], tz[0]])
                v = v + ctr
                if not (self.keep_ok(v) and not self.in_fire_zone(xy[None], r + 0.1)[0] and not self.blocks_sight(ctr, r)):
                    continue
                self.rocks.append(dict(kind=mat, center=ctr, r=r, collide=r >= 0.12))
                self.parts.append(Part(v, f, vertex_normals(v, f), mat, basalt[int(rng.integers(0, 5))] * rng.uniform(0.9, 1.15), "rocks",
                                       len(self.rocks) - 1, 4, collide=r >= 0.12, center=ctr))

    # --- vegetation -------------------------------------------------------------------------------------
    def _blobs(self, rng, centers, radii, center, subdiv=1, rough=0.32, squash=0.85):
        """Foliage: lumpy icospheres at `centers`; vertex normals point mostly away from the plant's
        `center`, so the crown shades as one volume."""
        V, F, N = [], [], []
        n0 = 0
        for c, r in zip(centers, radii):
            v, f = lumpy(rng, subdiv, rough, waves=6, kmin=1.5, kmax=4.0)
            v = v * [r, r * rng.uniform(0.85, 1.0), r * squash]
            v = v @ rotation(rng.uniform(0, 6.3)).T
            own = v / np.maximum(np.linalg.norm(v, axis=1, keepdims=True), 1e-9)
            v = v + c
            glob = v - center
            glob /= np.maximum(np.linalg.norm(glob, axis=1, keepdims=True), 1e-9)
            nn = 0.8 * glob + 0.2 * own
            N.append(nn / np.linalg.norm(nn, axis=1, keepdims=True))
            V.append(v); F.append(f + n0)
            n0 += len(v)
        return np.vstack(V), np.vstack(F), np.vstack(N)

    def _shrub(self, rng, base, height, width, mat, scorch=0.0, scorch_dir=None, subdiv=1, n_tex=4):
        """A shrub: a few large lumpy foliage blobs forming a dome."""
        n = int(np.clip(round(width * 8), 3, 12))
        a = rng.uniform(0, 2 * np.pi, n)
        rr = rng.uniform(0.0, 0.4, n) * width
        zz = height * rng.uniform(0.3, 0.62, n)
        cen = base + np.column_stack([rr * np.cos(a) * rng.uniform(0.8, 1.2), rr * np.sin(a), zz])
        radii = width * rng.uniform(0.18, 0.34, n) * np.clip(1.15 - rr / width, 0.6, 1.1)
        center = base + [0, 0, height * 0.42]
        v, f, vn = self._blobs(rng, cen, radii, center, subdiv, 0.34, height / width * 1.1)
        v[:, 2] = np.maximum(v[:, 2], base[2] + 0.01)
        q = Part(v, f, vn, mat, np.zeros(3), "veg", 0, n_tex, collide=True, center=center, extra=scorch)
        return [q], cen

    def _tree(self, rng, base, height, kind, scorch=0.0):
        """A tree. Pine: bare lower trunk and 8 to 12 overlapping drooping cones narrowing upward (a narrow
        conical crown); juniper: an irregular column of foliage blobs from near the ground; broadleaf:
        trunk, branches and a rounded canopy of a few large blobs."""
        parts = []
        r_tr = 0.03 + 0.022 * height
        lean = rng.normal(0, 0.035, 2)
        tv, tf = cylinder(r_tr, r_tr * 0.35, height * (0.97 if kind != "broadleaf" else 0.75), 7, bend=0.03 * height)
        tv[:, :2] += tv[:, 2:3] * lean
        tv = tv + base - [0, 0, 0.05]
        parts.append(Part(tv, tf, vertex_normals(tv, tf), "bark", np.zeros(3), "veg", 0, 4, collide=True, center=base.copy(), extra=scorch))
        if kind == "pine":
            lo = height * rng.uniform(0.22, 0.38)
            nt = int(rng.integers(8, 13))
            rb = height * rng.uniform(0.2, 0.26)
            V, F, N, n0 = [], [], [], 0
            center = base + [lean[0] * height * 0.6, lean[1] * height * 0.6, (lo + height) / 2]
            m = 14
            for k in range(nt):
                t = k / (nt - 1)
                z0 = lo + (height - lo) * t * 0.88
                r = rb * (1 - 0.82 * t) * rng.uniform(0.85, 1.12) + 0.05
                th = r * rng.uniform(1.1, 1.5)
                ang = np.arange(m) / m * 2 * np.pi + rng.uniform(0, 1)
                rad = r * rng.uniform(0.7, 1.15, m)
                droop = rng.uniform(0.05, 0.25, m) * r
                c = base + [lean[0] * z0, lean[1] * z0, z0]
                ring = np.column_stack([rad * np.cos(ang), rad * np.sin(ang), -droop]) + c
                mid = np.column_stack([0.55 * rad * np.cos(ang + 0.2), 0.55 * rad * np.sin(ang + 0.2), 0.45 * th + rng.uniform(-0.05, 0.05, m) * r]) + c
                apex = c + [0, 0, th]
                under = c + [0, 0, -0.1 * r]
                v = np.vstack([ring, mid, [apex], [under]])
                ia, iu = 2 * m, 2 * m + 1
                f = []
                for i in range(m):
                    j = (i + 1) % m
                    f += [[i, j, m + j], [i, m + j, m + i], [m + i, m + j, ia], [j, i, iu]]
                nn = v - center; nn[:, 2] += 0.4 * np.linalg.norm(nn[:, :2], axis=1)
                nn /= np.maximum(np.linalg.norm(nn, axis=1, keepdims=True), 1e-9)
                V.append(v); F.append(np.array(f) + n0); N.append(nn); n0 += len(v)
            parts.append(Part(np.vstack(V), np.vstack(F), np.vstack(N), "conifer", np.zeros(3), "veg", 0, 4, collide=True,
                              center=center, extra=scorch * 0.5))
        elif kind == "juniper":
            n = int(np.clip(height * 6, 10, 24))
            z = rng.uniform(0.1, 0.92, n) * height
            prof = (0.24 + 0.1 * height) * np.sqrt(np.clip(1 - (z / height - 0.38) ** 2 / 0.42, 0.1, 1))
            a = rng.uniform(0, 2 * np.pi, n)
            rr = prof * rng.uniform(0.2, 0.75, n)
            cen = base + np.column_stack([rr * np.cos(a) + lean[0] * z, rr * np.sin(a) + lean[1] * z, z])
            center = base + [0, 0, height * 0.5]
            v, f, vn = self._blobs(rng, cen, prof * rng.uniform(0.45, 0.7, n), center, 1, 0.4, 1.1)
            parts.append(Part(v, f, vn, "juniper", np.zeros(3), "veg", 0, 4, collide=True, center=center, extra=scorch))
        else:
            for k in range(int(rng.integers(3, 6))):
                a = rng.uniform(0, 2 * np.pi)
                z0 = height * rng.uniform(0.4, 0.6)
                bv, bf = cylinder(r_tr * 0.5, r_tr * 0.2, height * 0.3, 5)
                Rb = rotation(a, rng.uniform(0.5, 0.9), a + math.pi / 2)
                bv = bv @ Rb.T + base + [lean[0] * z0, lean[1] * z0, z0]
                parts.append(Part(bv, bf, vertex_normals(bv, bf), "bark", np.zeros(3), "veg", 0, 4, collide=False, center=base.copy()))
            n = int(rng.integers(4, 8))
            R = height * 0.3
            center = base + [lean[0] * height * 0.7, lean[1] * height * 0.7, height * 0.7]
            u = rng.normal(size=(n, 3)); u /= np.linalg.norm(u, axis=1, keepdims=True)
            cen = center + u * np.array([R, R, R * 0.55]) * rng.uniform(0.3, 0.75, (n, 1))
            v, f, vn = self._blobs(rng, cen, R * rng.uniform(0.5, 0.75, n), center, 2, 0.32, 0.85)
            parts.append(Part(v, f, vn, "leaf", np.zeros(3), "veg", 0, 3, collide=True, center=center, extra=scorch))
        return parts

    def _twigs(self, rng, base, height, width):
        """The woody skeleton of a shrub: stems from the base branching upward and outward (charred)."""
        parts = []
        for k in range(int(rng.integers(9, 15))):
            a = rng.uniform(0, 2 * np.pi)
            tilt = rng.uniform(0.2, 0.9)
            L = height * rng.uniform(0.6, 1.1)
            v, f = cylinder(rng.uniform(0.008, 0.016), 0.004, L, 4, bend=0.08)
            R = rotation(a, tilt, a + math.pi / 2)
            v = v @ R.T + base + [rng.normal(0, 0.05), rng.normal(0, 0.05), 0.0]
            parts.append(Part(v, f, vertex_normals(v, f), "log", np.zeros(3), "veg", 0, 2, collide=False, center=base.copy(), extra=1.0))
        return parts

    def _grass(self, rng, base, height, dry, nblade=None):
        """A grass tuft: blades as thin triangles leaning outward, both sides."""
        n = nblade or int(rng.integers(6, 11))
        v, f = [], []
        for k in range(n):
            a = rng.uniform(0, 2 * np.pi)
            h = height * rng.uniform(0.6, 1.0)
            lean = rng.uniform(0.15, 0.6)
            w = rng.uniform(0.012, 0.022)
            d = np.array([math.cos(a), math.sin(a), 0.0])
            side = np.array([-math.sin(a), math.cos(a), 0.0]) * w
            b0 = base + d * rng.uniform(0, 0.05)
            tip = b0 + d * lean * h + [0, 0, h * (1 - 0.3 * lean)]
            i = len(v)
            v += [b0 - side, b0 + side, tip]
            f += [[i, i + 1, i + 2], [i, i + 2, i + 1]]
        v, f = np.array(v), np.array(f)
        vn = np.tile([0.0, 0.0, 1.0], (len(v), 1))
        return Part(v, f, vn, "grass", np.array([dry, height, 0.0]), "veg", 0, 2, collide=False, center=base.copy())

    def _veg_ok(self, v, center, r, near_fire_ok=False):
        if not self.keep_ok(v, low=KEEP_LOW_VEG):
            return False
        if not near_fire_ok and self.in_fire_zone(center[None, :2], r + 0.25)[0]:
            return False
        if self.blocks_sight(center + [0, 0, r * 0.5], r):
            return False
        for b in self.boulders:
            if np.linalg.norm(center[:2] - b.center[:2]) < b.size / 2 + 0.6 * r:
                return False
        return True

    def _add_veg(self, parts, kind, center, r):
        k = len(self.veg)
        for q in parts:
            q.index = k
        self.parts += parts
        self.veg.append(dict(kind=kind, center=np.asarray(center, float), r=float(r)))

    def _plateau_point(self, rng, yb, s, d):
        i = int(np.clip(round((yb - Y0) / ROW_DY), 0, len(self.y) - 1))
        u = s * (self.width[i] / 2 + self.rim_xi[(s, i)] + 1.4 + d)
        xy = np.array([self.at_lateral(yb, u), yb])
        return np.array([xy[0], xy[1], self.terrain_z(xy[None])[0]])

    def _vegetation(self, rng):
        self.veg = []
        dens = Field2(rng, (-80, Y0 - 5), (80, Y1 + 5), 0.5, 4.0)
        # green shrubs: clustered on the talus, the vegetated slopes and the wash edges
        n, tries, cluster = 0, 0, None
        while n < 560 and tries < 14000:
            tries += 1
            if cluster is None or cluster[1] <= 0:              # shrubs grow in clusters of 2 to 8 that merge
                yb = rng.uniform(Y0 + 1, Y1 - 1)
                s = rng.choice([-1, 1])
                i = int(np.clip(round((yb - Y0) / ROW_DY), 0, len(self.y) - 1))
                r = rng.random()
                if r < 0.15:
                    half = self.width_at(yb) / 2
                    c0 = np.array([self.at_lateral(yb, s * (half - rng.uniform(0, 0.9))), yb, 0.0])
                elif r < 0.45 and self.vband_h[s][i] > 0.8:
                    c0, _ = self.surface_point(yb, s, "vslope", rng.uniform(0.0, 0.95))
                else:
                    c0, _ = self.surface_point(yb, s, "talus", rng.beta(1.3, 1.6))
                if dens(c0[0], c0[1]) < -0.3 - 0.4 * self.slope[s][i]:
                    continue
                cluster = [c0, int(rng.integers(2, 9)), "leaf" if rng.random() < 0.7 else ("leafdark" if rng.random() < 0.6 else "sage")]
            cluster[1] -= 1
            pt = cluster[0] + np.array([*rng.normal(0, 0.8, 2), 0.0])
            tz, free = self.ground_at(pt[None, :2])
            if not free[0]:
                continue
            pt = np.array([pt[0], pt[1], tz[0]])
            h = float(rng.lognormal(math.log(0.75), 0.35))
            w = h * rng.uniform(1.1, 2.0)
            parts, _ = self._shrub(rng, pt, h, w, cluster[2])
            v = np.vstack([q.verts for q in parts])
            if not self._veg_ok(v, pt, w / 2):
                continue
            self._add_veg(parts, "shrub", pt, w / 2)
            n += 1
        # shrubs on the ledges between colonnade and entablature
        n, tries = 0, 0
        while n < 90 and tries < 4000:
            tries += 1
            yb = rng.uniform(Y0 + 1, Y1 - 1)
            s = rng.choice([-1, 1])
            i = int(np.clip(round((yb - Y0) / ROW_DY), 0, len(self.y) - 1))
            if self.ledge_w[s][i] < 0.3:
                continue
            pt, _ = self.surface_point(yb, s, "ledge", 0.5)
            h = float(rng.uniform(0.3, 0.8))
            parts, _ = self._shrub(rng, pt - [0, 0, 0.03], h, min(h * 1.3, self.ledge_w[s][i] * 1.4), "leaf" if rng.random() < 0.6 else "sage")
            v = np.vstack([q.verts for q in parts])
            if not self.keep_ok(v, low=KEEP_LOW_VEG):
                continue
            self._add_veg(parts, "ledge shrub", pt, h * 0.65)
            n += 1
        # the plateau: junipers and pines along the rim and scattered, sagebrush (light meshes) everywhere
        n_sage, n_tree, tries = 0, 0, 0
        while (n_sage < 900 or n_tree < 190) and tries < 20000:
            tries += 1
            yb = rng.uniform(Y0 + 1, Y1 - 1)
            s = rng.choice([-1, 1])
            if n_tree < 190 and rng.random() < 0.3:
                d = float(rng.exponential(6.0) + 0.6) if rng.random() < 0.7 else rng.uniform(1, 43)
                if d > 43:
                    continue
                pt = self._plateau_point(rng, yb, s, d)
                kind = "pine" if rng.random() < 0.45 else "juniper"
                h = float(rng.uniform(3.0, 8.0) if kind == "pine" else rng.uniform(1.8, 4.2))
                self._add_veg(self._tree(rng, pt, h, kind), kind, pt, h * 0.25)
                n_tree += 1
            elif n_sage < 900:
                pt = self._plateau_point(rng, yb, s, rng.uniform(0.6, 40.0))
                h = float(rng.uniform(0.3, 0.8))
                parts, _ = self._shrub(rng, pt, h, h * rng.uniform(1.1, 1.6), "sage", subdiv=0, n_tex=3)
                self._add_veg(parts, "sage", pt, h * 0.7)
                n_sage += 1
        # small trees on the talus, the vegetated slopes and the wall foot (the keep-out rule keeps them off the route)
        n, tries = 0, 0
        while n < 60 and tries < 6000:
            tries += 1
            yb = rng.uniform(Y0 + 1, Y1 - 1)
            s = rng.choice([-1, 1])
            i = int(np.clip(round((yb - Y0) / ROW_DY), 0, len(self.y) - 1))
            seg = "vslope" if (self.vband_h[s][i] > 0.8 and rng.random() < 0.5) else "talus"
            pt, _ = self.surface_point(yb, s, seg, rng.uniform(0.1, 0.95))
            tz, free = self.ground_at(pt[None, :2])
            if not free[0]:
                continue
            pt = np.array([pt[0], pt[1], tz[0]])
            kind = ("pine", "broadleaf", "juniper", "juniper", "juniper", "pine")[int(rng.integers(0, 6))]
            h = float(rng.uniform(2.2, 5.5))
            parts = self._tree(rng, pt, h, kind)
            v = np.vstack([q.verts for q in parts])
            if not self._veg_ok(v, pt, h * 0.25):
                continue
            self._add_veg(parts, kind, pt, h * 0.25)
            n += 1
        # grass tufts: wash (more toward the edges and around boulders), talus, vegetated slopes, plateau bunchgrass
        tufts = []
        for _ in range(9000):
            yb = rng.uniform(Y0 + 1, Y1 - 1)
            r = rng.random()
            s = rng.choice([-1, 1])
            if r < 0.3:
                half = self.width_at(yb) / 2
                e = np.clip(rng.normal(0, 0.6), -1.05, 1.05)
                xy = np.array([self.at_lateral(yb, e * half), yb])
                dry = 0.55 + 0.4 * rng.random()
            elif r < 0.55:
                pt, _ = self.surface_point(yb, s, "talus", rng.uniform(0, 1))
                xy, dry = pt[:2], 0.25 + 0.5 * rng.random()
            elif r < 0.62:
                pt, _ = self.surface_point(yb, s, "vslope", rng.uniform(0, 1))
                xy, dry = pt[:2], 0.2 + 0.4 * rng.random()
            else:
                xy, dry = self._plateau_point(rng, yb, s, rng.uniform(0.3, 25))[:2], 0.65 + 0.35 * rng.random()
            tufts.append((xy, dry))
        for b in self.boulders:                                  # plants at the foot of the boulders
            for _ in range(int(rng.integers(4, 10))):
                a = rng.uniform(0, 2 * np.pi)
                xy = b.center[:2] + (b.size / 2 + rng.uniform(0.0, 0.4)) * np.array([math.cos(a), math.sin(a)])
                tufts.append((xy, 0.2 + 0.4 * rng.random()))
        for f in self.firebrands:                                # fuel around the fires: grass just outside the patch
            for _ in range(22):
                a = rng.uniform(0, 2 * np.pi)
                xy = f.center[:2] + (f.rim.max() * 1.1 + rng.uniform(0.05, 0.7)) * np.array([math.cos(a), math.sin(a)])
                tufts.append((xy, 0.6 + 0.3 * rng.random()))
        xy = np.array([t[0] for t in tufts])
        tz, free = self.ground_at(xy)
        burned = self.in_fire_zone(xy, 0.08)
        for (q, dry), z, ok, bu in zip(tufts, tz, free, burned):
            if bu or not ok:
                continue
            pt = np.array([q[0], q[1], z - 0.01])
            h = float(rng.uniform(0.15, 0.5))
            part = self._grass(rng, pt, h, dry)
            if not self.keep_ok(part.verts):
                continue
            near = [f for f in self.firebrands if np.linalg.norm(f.center[:2] - q) < f.radius + 0.9]
            if near:
                part.extra = float(np.clip(1.2 - (np.linalg.norm(near[0].center[:2] - q) - near[0].radius) / 0.7, 0, 1))
            self._add_veg([part], "grass", pt, 0.05)

    def _fire_parts(self, rng):
        """Fuel that belongs to a fire: the burning shrub, the small pine at a fire, the log; scorched
        shrubs next to some fires."""
        for k, f in enumerate(self.firebrands):
            if f.kind == "shrub":
                c = f.extra["shrub"]
                c = np.array([c[0], c[1], self.ground_z(c[None, :2])[0]])
                parts = self._twigs(rng, c, 1.0, 1.1)                         # its foliage has burned
                self._add_veg(parts, "burning shrub", c, 0.55)
                f.extra["shrub"] = c
                f.extra["shrub_base"] = float(c[2] + 0.05)
            elif f.kind == "tree":
                c = f.extra["tree"]
                c = np.array([c[0], c[1], self.ground_z(c[None, :2])[0]])
                h = float(rng.uniform(2.3, 2.9))
                parts = self._tree(rng, c, h, "pine", scorch=1.0)
                self._add_veg(parts, "tree at fire", c, 0.4)
                f.extra["tree"] = c
                f.extra["tree_base"] = float(c[2] + 0.03)
            elif f.kind == "log":
                a, b = f.extra["log"]
                za, zb = self.ground_z(np.array([a, b]))
                L = float(np.linalg.norm(b - a))
                r = float(rng.uniform(0.07, 0.11))
                v, fc = cylinder(r, r * 0.8, L, 8, bend=0.02)
                d = np.array([b[0] - a[0], b[1] - a[1], zb - za]) / L
                zax = np.array([0, 0, 1.0])
                ax = np.cross(zax, d); s_ = np.linalg.norm(ax); c_ = zax @ d
                K = np.array([[0, -ax[2], ax[1]], [ax[2], 0, -ax[0]], [-ax[1], ax[0], 0]])
                Rm = np.eye(3) + K + K @ K * ((1 - c_) / (s_ ** 2))
                v = v @ Rm.T + [a[0], a[1], za + r * 0.6]
                self._add_veg([Part(v, fc, vertex_normals(v, fc), "log", np.zeros(3), "veg", 0, 4, collide=True,
                                    center=np.array([*(a + b) / 2, za]), extra=1.0)], "burning log", np.array([*(a + b) / 2, za]), L / 2)
                f.extra["log_base"] = float((za + zb) / 2 + r)
            # scorched shrub at the edge of some fires
            if f.hidden and rng.random() < 0.5:
                for _ in range(10):
                    a = rng.uniform(0, 2 * np.pi)
                    q = f.center[:2] + (f.radius + 0.35) * np.array([math.cos(a), math.sin(a)])
                    tz, free = self.ground_at(q[None])
                    if not free[0]:
                        continue
                    c = np.array([q[0], q[1], tz[0]])
                    parts, _ = self._shrub(rng, c, 0.5, 0.6, "leaf", scorch=0.6, scorch_dir=f.center)
                    v = np.vstack([q_.verts for q_ in parts])
                    if self.keep_ok(v, low=KEEP_LOW_VEG) and all(np.linalg.norm(c[:2] - b.center[:2]) > b.size / 2 + 0.2 for b in self.boulders):
                        self._add_veg(parts, "scorched shrub", c, 0.3)
                        break
        for f in self.firebrands:
            self._finish_fire(rng, f)

    # --- collision hulls ------------------------------------------------------------------------------
    def _write_hulls(self):
        """One OBJ per group with each colliding part as its own object: PyBullet makes a compound of
        their convex hulls (rocks: blocks and cobbles of at least 0.1 / 0.12 m; vegetation: trunks,
        foliage blobs, logs; grass, small branches and smaller stones have no collision)."""
        tag = f"s{self.seed}"
        for g in ("rocks", "veg"):
            lines, n = ["# generated by gorge.py: convex parts (one object each)\n"], 0
            for k, q in enumerate(q for q in self.parts if q.group == g and q.collide):
                h = ConvexHull(q.verts)                    # PyBullet takes each object's convex hull: write just that
                v, f = q.verts[h.vertices], np.searchsorted(h.vertices, h.simplices)
                lines.append(f"o part{k}\n")
                lines += [f"v {a:.4f} {b:.4f} {c:.4f}\n" for a, b, c in v]
                lines += [f"f {a + 1 + n} {b + 1 + n} {c + 1 + n}\n" for a, b, c in f]
                n += len(v)
            path = ASSETS / f"{g}_{tag}_hull.obj"
            tmp = Path(f"{path}.{os.getpid()}.tmp")
            tmp.write_text("".join(lines))
            os.replace(tmp, path)
            self.files[f"{g}_hull"] = str(path)
        for k, b in enumerate(self.boulders):
            write_obj(ASSETS / f"boulder_{tag}_{k:02d}_hull.obj", b.verts, b.faces)

    def _add_compounds(self):
        self.compound_ids = [p.createMultiBody(0, p.createCollisionShape(p.GEOM_MESH, fileName=self.files[f"{g}_hull"],
                                                                         physicsClientId=self._client), physicsClientId=self._client)
                             for g in ("rocks", "veg")]

    def _check_fires(self):
        """The fires' visibility with every collision body in place (vegetation and rocks only add
        occlusion; they were kept off the open fires' sight lines)."""
        pp = self.path_points(0.25)
        self.fire_seen = []
        for f in self.firebrands:
            dy = f.center[1] - pp[:, 1]
            pts = pp[(dy >= 3) & (dy <= (20 if f.hidden else 25))]
            self.fire_seen.append(self._seen(self._fire_points(f) if f.hidden else np.array([f.center + [0, 0, 0.1]]), pts))

    # --- fire heating -----------------------------------------------------------------------------------
    def fire_heating(self, pts, normals, vis=True):
        """Temperature rise (K) of surfaces at pts with normals from the fires' radiation: the radiated
        power of each fire split over points along its flaming front (front_points, at a third of the
        flame height), flux q = P_i cos / (4 pi d^2) from each point in sight, dT = ETA_EXPO ABSORB q /
        (H_CONV + H_RAD) (quasi-steady balance; ETA_EXPO accounts for the ground not having reached
        equilibrium). The ground ahead of the front is heated most, the burned interior behind it less."""
        pts = np.atleast_2d(pts)
        out = np.zeros(len(pts))
        for f in self.firebrands:
            near = np.linalg.norm(pts - f.center, axis=1) < 7.0
            if not near.any():
                continue
            src = self.front_points(f)
            P_i = f.power_w / len(src)
            pn, nn = pts[near], normals[near]
            acc = np.zeros(len(pn))
            for s in src:
                dv = s - pn
                d = np.linalg.norm(dv, axis=1)
                l = dv / np.maximum(d[:, None], 1e-6)
                cos = np.clip((nn * l).sum(1), 0, 1) * 0.8 + 0.2
                q = P_i * cos / (4 * np.pi * np.maximum(d, 0.25) ** 2)
                if vis:
                    a = pn + 0.04 * nn
                    frac, _ = self.rays(a, np.repeat(s[None], len(a), 0))
                    q = q * np.where(frac >= 0.97, 1.0, 0.15)
                acc += q
            out[near] += ETA_EXPO * ABSORB * acc / (H_CONV + H_RAD)
        return np.minimum(out, 250.0)

    # --- the live level of detail (onboard cameras) -------------------------------------------------------
    LIVE_FIRE_KINDS = ("burning shrub", "tree at fire", "burning log", "scorched shrub")
    LIVE_CHUNK = 24                                  # terrain rows per chunk of the live world (8.4 m)

    def _live_lod(self, rng):
        """A decimated visual world for the onboard cameras' live streams (Gorge.load(..., lod=2)): the
        same terrain and fires; each boulder from its icosphere's subdivision-2 vertices (320 faces, the
        same shape); rocks under about 0.12 m left out, cobbles as octahedra, column fragments as they are;
        each plant as one or two low-poly crowns (pines: a trunk and three cones), the fires' own fuel as
        it is; no grass. The parts are baked into their own atlas with the same materials (colors,
        lighting, temperatures). Collision is unchanged (this is visual only)."""
        live = []
        n2 = 162                                     # vertices of an icosphere of subdivision 2
        _, f2 = icosphere(2)
        for k, b in enumerate(self.boulders):
            q0 = [q for q in self.parts if q.group == "boulder" and q.index == k][0]
            v = b.verts[:n2]
            live.append(Part(v, f2, vertex_normals(v, f2), "boulder", np.zeros(3), "lboulder", k, 6, center=q0.center, extra=q0.extra))
        for q in self.parts:
            if q.group != "rocks":
                continue
            ext = np.ptp(q.verts, axis=0)
            if q.mat == "basalt" and ext.max() >= 0.25 or q.mat == "chip" and ext.max() >= 0.16:
                live.append(Part(q.verts, q.faces, q.normals, q.mat, q.color, "lrocks", q.index, 4, center=q.center))
            elif q.mat == "cobble" and ext.max() >= 0.12:
                c = (q.verts.max(0) + q.verts.min(0)) / 2
                v = OCTA_V * (ext / 2) + c
                live.append(Part(v, OCTA_F, vertex_normals(v, OCTA_F), "cobble", q.color, "lrocks", q.index, 4, center=q.center))
        by = {}
        for q in self.parts:
            if q.group == "veg" and q.mat != "grass":
                by.setdefault(q.index, []).append(q)
        for k, ps in by.items():
            kind = self.veg[k]["kind"]
            if kind in self.LIVE_FIRE_KINDS:
                live += [Part(q.verts, q.faces, q.normals, q.mat, q.color, "lveg", k, q.n, center=q.center, extra=q.extra, fnorm=q.fnorm)
                         for q in ps]
                continue
            fol = [q for q in ps if q.mat not in ("bark", "log")]
            if not fol:
                continue
            V = np.vstack([q.verts for q in fol])
            lo, hi = V.min(0), V.max(0)
            mat, scorch = fol[0].mat, fol[0].extra
            base = np.array([*((lo[:2] + hi[:2]) / 2), min(lo[2], np.vstack([q.verts for q in ps])[:, 2].min())])
            if kind in ("pine", "broadleaf"):
                trunk = [q for q in ps if q.mat == "bark"][0]
                top = hi[2]
                tv, tf = cylinder(np.ptp(trunk.verts[:, 0]) / 2 * 0.9, 0.02, (top - base[2]) * (0.97 if kind == "pine" else 0.75), 5)
                tv = tv[np.r_[0:5, 20:26]]                  # one segment: bottom ring, top ring and cap
                tv[5:10, 2] = tv[10, 2]
                tf = np.array([[a, b, b + 5] for a, b in zip(range(5), [1, 2, 3, 4, 0])] + [[a, b + 5, a + 5] for a, b in zip(range(5), [1, 2, 3, 4, 0])]
                              + [[5 + i, 5 + (i + 1) % 5, 10] for i in range(5)])
                tv = tv + base
                live.append(Part(tv, tf, vertex_normals(tv, tf), "bark", np.zeros(3), "lveg", k, 4, center=base.copy(), extra=trunk.extra))
            if kind == "pine":
                R = max(np.ptp(V[:, 0]), np.ptp(V[:, 1])) / 2
                z0, z1 = lo[2], hi[2]
                cv, cf, n0 = [], [], 0
                for i, (a, b_, rr) in enumerate(((0.0, 0.55, 1.0), (0.3, 0.8, 0.72), (0.58, 1.0, 0.45))):
                    za, zb = z0 + a * (z1 - z0), z0 + b_ * (z1 - z0)
                    ang = np.arange(8) / 8 * 2 * np.pi + rng.uniform(0, 1)
                    ring = np.column_stack([R * rr * np.cos(ang), R * rr * np.sin(ang), np.full(8, za)]) + [base[0], base[1], 0]
                    v = np.vstack([ring, [[base[0], base[1], zb]], [[base[0], base[1], za + 0.05]]])
                    f = [[j, (j + 1) % 8, 8] for j in range(8)] + [[(j + 1) % 8, j, 9] for j in range(8)]
                    cv.append(v); cf.append(np.array(f) + n0); n0 += len(v)
                v, f = np.vstack(cv), np.vstack(cf)
                center = np.array([base[0], base[1], (z0 + z1) / 2])
                nn = v - center; nn[:, 2] += 0.4 * np.linalg.norm(nn[:, :2], axis=1)
                nn /= np.maximum(np.linalg.norm(nn, axis=1, keepdims=True), 1e-9)
                live.append(Part(v, f, nn, mat, np.zeros(3), "lveg", k, 4, center=center, extra=scorch))
                continue
            ext = hi - lo
            center = (lo + hi) / 2
            if kind == "broadleaf":
                cen, rad, sub = [center], [ext / 2], 1
            elif kind == "juniper":
                cen, rad, sub = [center], [ext * [0.5, 0.5, 0.5]], 1
            elif kind == "sage":
                cen, rad, sub = [center], [ext / 2], 0
            else:                                         # shrubs: one rounded blob
                cen, rad, sub = [center], [ext / 2], 1
            vs, fs, ns, n0 = [], [], [], 0
            for c_, r_ in zip(cen, rad):
                v, f = lumpy(rng, sub, 0.25, waves=5, kmin=1.5, kmax=3.5)
                v = v * r_ + c_
                v[:, 2] = np.maximum(v[:, 2], base[2] + 0.01)
                nn = 0.8 * (v - center) / np.maximum(np.linalg.norm(v - center, axis=1, keepdims=True), 1e-9) + 0.2 * (v - c_) / np.maximum(
                    np.linalg.norm(v - c_, axis=1, keepdims=True), 1e-9)
                vs.append(v); fs.append(f + n0); ns.append(nn / np.linalg.norm(nn, axis=1, keepdims=True)); n0 += len(v)
            live.append(Part(np.vstack(vs), np.vstack(fs), np.vstack(ns), mat, np.zeros(3), "lveg", k, 4, center=center, extra=scorch))
        rgb, thm, AH = self._bake_objects(rng, live)
        tag, out = f"s{self.seed}", ASSETS
        save_png(np.flipud(rgb), out / f"objectslive_{tag}_rgb.png")
        save_png(np.flipud(thm), out / f"objectslive_{tag}_thermal.png")
        # chunks along the gorge (LIVE_CHUNK rows of the terrain each), so that the cameras can leave out
        # what is outside their view: per chunk the terrain's faces and the objects whose center is in it
        NR, NC = self.grid.shape[:2]
        edges = list(range(0, NR - 1, self.LIVE_CHUNK)) + [NR - 1]
        frow = self.F.min(axis=1) // NC
        self.live_chunks, self.live_counts = [], dict(terrain=int(len(self.F)), boulders_live=0, rocks_live=0, veg_live=0)
        vn = self.normals.reshape(-1, 3)
        for c, (r0, r1) in enumerate(zip(edges[:-1], edges[1:])):
            f = self.F[(frow >= r0) & (frow < r1)]
            used = np.unique(f)
            remap = -np.ones(len(self.V), int); remap[used] = np.arange(len(used))
            key = f"live_terrain_{c}"
            self.files[key] = write_obj(out / f"terrainlive_{tag}_{c:02d}.obj", self.V[used], remap[f], self.UV[used], vn[used])
            self.live_chunks.append((key, "terrain", 0, self.V[used].min(0), self.V[used].max(0)))
            y0, y1 = self.y[r0] - (1e9 if c == 0 else 0), self.y[r1] + (1e9 if c == len(edges) - 2 else 0)
            for g, cls, cnt in (("lboulder", "boulder", "boulders_live"), ("lrocks", "rocks", "rocks_live"), ("lveg", "veg", "veg_live")):
                ps = [q for q in live if q.group == g and y0 <= q.center[1] < y1]
                if not ps:
                    continue
                off = np.cumsum([0] + [len(q.verts) for q in ps])[:-1]
                v = np.vstack([q.verts for q in ps])
                fc = np.vstack([q.faces + o for q, o in zip(ps, off)])
                uv = np.vstack([q.uv.reshape(-1, 2) for q in ps])
                key = f"live_{g}_{c}"
                self.files[key] = write_obj(out / f"{g}live_{tag}_{c:02d}.obj", v, fc, uv, uv_faces=np.arange(len(uv)).reshape(-1, 3))
                self.live_chunks.append((key, cls, -1, v.min(0), v.max(0)))
                self.live_counts[cnt] += int(len(fc))

    # --- texture of the objects (atlas, one square per triangle) ----------------------------------------
    ROCKY = ("boulder", "basalt", "cobble", "chip")

    def _bake_objects(self, rng, parts=None):
        """The objects atlas: every triangle of every part gets a square of n x n texels; each texel is
        colored from the 3D point it covers (material noise in world coordinates, baked lighting with
        the vertex shadow term interpolated) and gets a temperature. Rocky parts respond to the
        insolation of the last 3 h (thermal inertia, TAU_H["rock"]), plants to the present sun."""
        tl = Tile(rng, 256, 1.2)
        tl2 = Tile(rng, 256, 3.0)
        store = parts is None
        parts = self.parts if parts is None else parts
        allv = np.vstack([q.verts for q in parts])
        alln = np.vstack([q.normals for q in parts])
        lit = self.sunlit(allv, alln, 0.04)
        heat = self.fire_heating(allv, alln)
        rocky = np.concatenate([np.full(len(q.verts), q.mat in self.ROCKY) for q in parts])
        ins_eff = np.clip(alln @ SUN, 0, 1) * lit
        if rocky.any():
            rv, rn = allv[rocky], alln[rocky]
            acc, wsum = ins_eff[rocky].copy(), 1.0
            for age, S in SUN_PAST:
                frac, _ = self.rays(rv + 0.04 * rn, rv + 0.04 * rn + 150 * S)
                wk = math.exp(-age / TAU_H["rock"])
                acc += wk * np.clip(rn @ S, 0, 1) * (frac >= 1.0)
                wsum += wk
            ins_eff[rocky] = acc / wsum
        k = 0
        for q in parts:
            n = len(q.verts)
            q.lit, q.heat, q.ins = lit[k:k + n], heat[k:k + n], ins_eff[k:k + n]
            k += n
        sizes = sorted({q.n for q in parts}, reverse=True)
        y0, place = 0, {}
        for sz in sizes:
            nf = sum(len(q.faces) for q in parts if q.n == sz)
            per_row = ATLAS_W // sz
            place[sz] = (y0, per_row)
            y0 += int(np.ceil(nf / per_row)) * sz
        AH = int(np.ceil(y0 / 16) * 16)
        rgb = np.zeros((AH, ATLAS_W, 3), np.uint8)
        thm = np.zeros((AH, ATLAS_W, 3), np.uint8)
        counters = {sz: 0 for sz in sizes}
        batches = {}
        for q in parts:
            sz = q.n
            ybase, per_row = place[sz]
            nf = len(q.faces)
            idx = counters[sz] + np.arange(nf)
            counters[sz] += nf
            ox, oy = (idx % per_row) * sz, ybase + (idx // per_row) * sz
            e = 0.02
            uv = np.stack([np.stack([ox + e, oy + e], -1), np.stack([ox + sz - e, oy + e], -1), np.stack([ox + e, oy + sz - e], -1)], 1)
            q.uv = uv / [ATLAS_W, AH]
            batches.setdefault((q.mat, sz), []).append((q, ox, oy))
        for (mat, sz), items in batches.items():
            f = lambda get: np.concatenate([get(q) for q, _, _ in items])
            V = f(lambda q: q.verts[q.faces])                       # F x 3 x 3
            NV = f(lambda q: q.fnorm if q.fnorm is not None else q.normals[q.faces])
            LV = f(lambda q: q.lit[q.faces])
            HV = f(lambda q: q.heat[q.faces])
            IV = f(lambda q: q.ins[q.faces])
            C = f(lambda q: np.repeat(q.center[None], len(q.faces), 0))[:, None, :]
            CL = f(lambda q: np.repeat(np.asarray(q.color, float)[None], len(q.faces), 0))[:, None, :]
            E = f(lambda q: np.full(len(q.faces), q.extra))[:, None]
            ox = np.concatenate([o for _, o, _ in items]); oy = np.concatenate([o for _, _, o in items])
            jj, ii = np.meshgrid(np.arange(sz), np.arange(sz))
            a = ((jj + 0.5) / sz).ravel(); b = ((ii + 0.5) / sz).ravel()
            s_ = a + b
            a, b = np.where(s_ > 1, a / s_, a), np.where(s_ > 1, b / s_, b)
            w0 = (1 - a - b)[None, :, None]; w1 = a[None, :, None]; w2 = b[None, :, None]
            P = w0 * V[:, None, 0] + w1 * V[:, None, 1] + w2 * V[:, None, 2]
            N = w0 * NV[:, None, 0] + w1 * NV[:, None, 1] + w2 * NV[:, None, 2]
            N /= np.maximum(np.linalg.norm(N, axis=-1, keepdims=True), 1e-9)
            L = w0[..., 0] * LV[:, None, 0] + w1[..., 0] * LV[:, None, 1] + w2[..., 0] * LV[:, None, 2]
            Ht = w0[..., 0] * HV[:, None, 0] + w1[..., 0] * HV[:, None, 1] + w2[..., 0] * HV[:, None, 2]
            Ins = w0[..., 0] * IV[:, None, 0] + w1[..., 0] * IV[:, None, 1] + w2[..., 0] * IV[:, None, 2]
            col, tk, em = self._material(mat, P, N, L, Ht, Ins, C, CL, E, tl, tl2)
            tk = tk + 1.0 * fbm(tl2, P[..., 0] * 3 + P[..., 2], P[..., 1] * 3, 0.15, 2)
            rr = (oy[:, None] + ii.ravel()[None, :]).ravel()
            cc = (ox[:, None] + jj.ravel()[None, :]).ravel()
            rgb[rr, cc] = np.clip(col.reshape(-1, 3), 0, 255).astype(np.uint8)
            thm[rr, cc] = encode_temperature(tk.ravel(), em.ravel())
        if store:
            self.atlas_rgb, self.atlas_thermal, self.atlas_h = rgb, thm, AH
        return rgb, thm, AH

    def _light(self, N, lit, ao, wrap=0.0):
        """Baked lighting factor (RGB): sun (Lambert, or wrapped for foliage) with the cast-shadow term;
        sky light through the unoccluded part of the hemisphere (ao); light reflected by the terrain
        that occludes the rest (1 - ao), warm (sunlit rock and sand)."""
        ndl = (N @ SUN + wrap) / (1 + wrap)
        sun = LIGHT["sun"] * np.clip(ndl, 0, 1) * lit
        sky = LIGHT["sky"] * ao * (0.6 + 0.4 * N[..., 2])
        refl = LIGHT["reflect"] * (1 - ao) * (0.75 - 0.25 * N[..., 2])
        return sun[..., None] + sky[..., None] * SKY_TINT + refl[..., None] * BOUNCE_TINT

    def _material(self, m, P, N, lit, heat, ins_eff, C, CL, E, tl, tl2):
        """Color (baked lighting), temperature (K) and emissivity of texels (F x n^2) of material m;
        C: part center (F x 1 x 3), CL: part color or parameters, E: part parameter (scorch, moss)."""
        x, y, z = P[..., 0], P[..., 1], P[..., 2]
        jit = 0.5 * tl(x + z, y, 0.3)
        ins = np.clip(N @ SUN, 0, 1) * lit
        if m == "boulder":
            # the wall's basalt: grey-brown to buff, mottled, pale grey-green and a little orange lichen on
            # the upper faces, dark and damp underneath, moss at the base
            hz = z - C[..., 2]
            n1 = 0.5 * fbm(tl, x + 0.6 * z, y - 0.4 * z, 0.12, 3) + 0.5 * fbm(tl, y + 0.5 * z + 7, x - 0.7 * z, 0.12, 3)
            n2 = 0.5 * fbm(tl2, x - z * 0.5, y + z * 0.3, 0.05, 2) + 0.5 * fbm(tl2, z + y * 0.3 + 3, x * 0.6 - y, 0.05, 2)
            base = mix(np.array([78, 72, 66.0]), np.array([128, 116, 98.0]), np.clip(E * 1.3 - 0.15, 0, 1)[..., None])
            col = base * (1 + 0.16 * n1[..., None]) * (1 + 0.08 * n2[..., None])
            up = smoothstep(-0.1, 0.5, N[..., 2])
            lich = smoothstep(0.35, 1.1, 0.5 * fbm(tl2, x * 1.4 + 31, y * 1.4 + z, 0.05, 3) + 0.5 * fbm(tl2, z * 1.4, x + y * 1.4, 0.05, 3)) * up
            col = mix(col, np.array([168, 170, 146.0]) * (1 + 0.1 * n2[..., None]), 0.65 * lich)
            orng = smoothstep(1.3, 1.9, fbm(tl, x * 2.1 + 5, y * 2.1 - z, 0.025, 2)) * up
            col = mix(col, np.array([176, 120, 58.0]), 0.5 * orng)
            col = col * (1 - 0.15 * smoothstep(0.5, 1.4, 0.5 * tl(x + z, y, 0.025) + 0.5 * tl(z + 3, x + y, 0.025)))[..., None]
            under = smoothstep(0.1, -0.6, N[..., 2])
            moss = smoothstep(0.3, 0.05, hz + 0.08 * tl(x, y, 0.05)) * smoothstep(-0.4, 0.3, N[..., 2] + 0.3 * tl2(x, y, 0.08)) * (E > 0.35)
            col = mix(col, np.array([66, 82, 42.0]) * (1 + 0.15 * n2[..., None]), 0.75 * moss)
            ao = np.clip(0.4 + 1.2 * hz, 0.4, 1.0) * (1 - 0.45 * under)
            col = col * self._light(N, lit, ao)
            tk = surface_temperature("rock", ins_eff, jit) + 273.15 + heat
            return col, tk, np.full(tk.shape, CLASSES["rock"]["emis"])
        if m in ("basalt", "cobble", "chip"):
            n1 = fbm(tl, x + z, y - z, 0.06, 2)
            col = CL * (1 + 0.14 * n1[..., None]) * (1 + 0.08 * tl(x * 2 + z, y, 0.012))[..., None]
            lich = smoothstep(0.6, 1.4, tl2(x * 1.4 + 5, y + z, 0.05)) * smoothstep(0.0, 0.5, N[..., 2])
            col = mix(col, np.array([160, 160, 136.0]), 0.5 * lich)
            ao = np.clip(0.5 + 2.0 * (z - C[..., 2]), 0.45, 1.0) * (1 - 0.35 * smoothstep(0.1, -0.6, N[..., 2]))
            col = col * self._light(N, lit, ao)
            tk = surface_temperature("rock", ins_eff, jit) + 273.15 + heat
            return col, tk, np.full(tk.shape, CLASSES["rock"]["emis"])
        if m in ("leaf", "leafdark", "sage", "conifer", "juniper"):
            # olive and sage greens (sunlit about (95, 110, 70) after lighting, shade about (55, 65, 45))
            base = np.array({"leaf": (66, 76, 46), "leafdark": (52, 62, 40), "sage": (100, 104, 88), "conifer": (46, 58, 40),
                             "juniper": (58, 70, 48)}[m], float)
            base = base * (1 + 0.1 * tl2(C[..., 0], C[..., 1], 1.0))[..., None]
            leafn = fbm(tl, x * 1.3 + z, y * 1.3 - z, 0.06, 2)
            col = base * (1 + 0.14 * leafn[..., None])
            col = col * (1 - 0.25 * smoothstep(0.4, 1.4, -leafn))[..., None]       # gaps between leaf masses
            if m in ("leaf", "leafdark"):
                col = mix(col, np.array([112, 118, 64.0]), 0.25 * smoothstep(0.6, 1.4, tl2(x, y + z, 0.06)))
            sc = np.clip(E * smoothstep(-0.5, 0.8, tl(x, y + z, 0.08) + E), 0, 1) * (E > 0)
            col = mix(col, np.array([96, 62, 30.0]), sc)
            col = mix(col, np.array([30, 24, 20.0]), np.clip(sc - 0.5, 0, 1))
            rel = P - C
            depth = np.clip(rel[..., 2] / np.maximum(np.linalg.norm(rel, axis=-1), 1e-3), -1, 1)
            ao = np.clip(0.42 + 0.55 * depth, 0.18, 1.0)
            col = col * self._light(N, lit, ao, wrap=0.25)
            tk = surface_temperature("leaf", ins, jit) + 273.15 + heat * 0.6 + 25 * E * (E > 0.9)
            return col, tk, np.full(tk.shape, CLASSES["leaf"]["emis"])
        if m in ("bark", "log"):
            st = tl(x * 6 + y * 6, z * 0.6, 0.05)
            col = np.array([86, 74, 62.0]) * (1 + 0.18 * st[..., None])
            hz = z - C[..., 2]
            crack = smoothstep(1.0, 1.5, tl(x * 3, y * 3 + z, 0.03))
            if m == "bark":
                char = np.clip(E * smoothstep(0.9, 0.2, hz + 0.15 * tl2(x, y, 0.05)), 0, 1)
            else:
                char = np.clip(E + 0 * hz, 0, 1)
            col = mix(col, np.array([26, 22, 20.0]) * (1 + 0.3 * st[..., None]), char)
            col = col * self._light(N, lit, np.full(z.shape, 0.9))
            tk = surface_temperature("bark", ins, jit) + 273.15 + heat
            if m == "log":
                col = col + np.array([210, 70, 12.0]) * (crack * E)[..., None]
                tk = tk + (180 + 300 * crack) * E
            else:
                tk = tk + 120 * char
            return col, tk, np.full(tk.shape, CLASSES["bark"]["emis"])
        if m == "grass":
            dry = CL[..., 0]
            h = np.clip((z - C[..., 2]) / np.maximum(CL[..., 1], 0.05), 0, 1)
            green, straw = np.array([86, 104, 54.0]), np.array([176, 154, 98.0])
            col = mix(green, straw, np.clip(dry + 0.25 * tl(x, y, 0.4), 0, 1))
            col = col * (0.55 + 0.45 * h)[..., None]
            col = mix(col, np.array([40, 30, 22.0]), np.clip(E * (1.2 - h), 0, 1))
            col = col * self._light(N, lit, 0.8 + 0.2 * h)
            tk_d = surface_temperature("drygrass", ins, jit)
            tk_g = surface_temperature("leaf", ins, jit)
            tk = np.where(dry > 0.5, tk_d, tk_g) + 273.15 + heat
            em = np.where(dry > 0.5, CLASSES["drygrass"]["emis"], CLASSES["leaf"]["emis"]) + 0 * tk
            return col, tk, em
        raise ValueError(m)

    # --- terrain texture -------------------------------------------------------------------------------
    def _texel_map(self, ti, tj):
        """Fractional grid row and column of texel centers (row ti, column tj of the texture)."""
        NR, NC = self.grid.shape[:2]
        fi = (np.asarray(ti) + 0.5) / TEX_H * (NR - 1)
        fj = np.interp((np.asarray(tj) + 0.5) / TEX_W, self.ucol, np.arange(NC))
        return fi, fj

    def _interp_grid(self, fi, fj):
        """3D point and normal on the mesh's own triangles at fractional (row, column)."""
        NR, NC = self.grid.shape[:2]
        i0, j0 = np.minimum(fi.astype(int), NR - 2), np.minimum(fj.astype(int), NC - 2)
        ti, tj = fi - i0, fj - j0
        upper = (tj >= ti)[..., None]
        ti, tj = ti[..., None], tj[..., None]

        def tri(A):
            a, b, c, d = A[i0, j0], A[i0, j0 + 1], A[i0 + 1, j0], A[i0 + 1, j0 + 1]
            return np.where(upper, a + tj * (b - a) + ti * (d - b), a + ti * (c - a) + tj * (d - c))
        P, N = tri(self.grid), tri(self.normals)
        N /= np.maximum(np.linalg.norm(N, axis=-1, keepdims=True), 1e-9)
        return P, N

    def _quad_kind(self, fj):
        j = np.clip(np.floor(fj).astype(int), 0, len(self.cols) - 2)
        outer = np.where(j < self.mid, j, j + 1)
        return self.col_kind[outer], np.where(j < self.mid, -1, 1)

    def _coarse(self, step):
        ti = np.arange(step // 2, TEX_H, step)
        tj = np.arange(step // 2, TEX_W, step)
        fi, fj = self._texel_map(ti[:, None], tj[None, :])
        fi, fj = np.broadcast_arrays(fi, fj)
        P, N = self._interp_grid(fi, fj)
        return ti, tj, P, N

    @staticmethod
    def _up(a, ti_c, tj_c, ti, tj):
        ci = np.interp(ti, ti_c, np.arange(len(ti_c)))
        cj = np.interp(tj, tj_c, np.arange(len(tj_c)))
        ci, cj = np.broadcast_arrays(ci[:, None], cj[None, :])
        return map_coordinates(a, [ci, cj], order=1, mode="nearest")

    def _bake_terrain(self, rng):
        """Terrain color (baked lighting) and thermal texture.
        Coarse passes (ray tests): sun shadow now (every 3rd texel), at the sun's six earlier positions
        (every 6th), sky visibility (every 8th, 12 rays), fire heating near the fires. Then, in bands of
        rows, each texel's material, color and lighting; the surface class parameters (shade and sun
        temperature, emissivity, time constant) are blurred over about 25 cm so that material boundaries
        blend; the temperature is the class's response to the insolation of the last 3 h weighted by
        exp(-age / tau). The color texture is finally prefiltered (Gaussian, 0.6 texel) so that no single
        texel stands out when TinyRenderer magnifies it."""
        tl, tl2, tl3 = Tile(rng, 256, 1.0), Tile(rng, 256, 2.5), Tile(rng, 512, 1.2)
        t0 = time.time()
        ti3, tj3, P3, N3 = self._coarse(3)
        sh = self.sunlit(P3.reshape(-1, 3), N3.reshape(-1, 3), 0.06).reshape(P3.shape[:2])
        heat3 = self.fire_heating(P3.reshape(-1, 3), N3.reshape(-1, 3)).reshape(P3.shape[:2])
        ti6, tj6, P6, N6 = self._coarse(6)
        past = []
        for age, S in SUN_PAST:
            a = P6.reshape(-1, 3) + 0.08 * N6.reshape(-1, 3)
            frac, _ = self.rays(a, a + 150 * S)
            past.append((age, (np.clip(N6 @ S, 0, 1) * (frac >= 1.0).reshape(P6.shape[:2])).astype(np.float32)))
        ti8, tj8, P8, N8 = self._coarse(8)
        dirs = []
        for k in range(12):
            u1, u2 = (k + 0.5) / 12, ((k * 0.618) % 1)
            r, ph = math.sqrt(u1), 2 * math.pi * u2
            dirs.append((r * math.cos(ph), r * math.sin(ph), math.sqrt(max(0.0, 1 - u1))))
        Pf, Nf = P8.reshape(-1, 3), N8.reshape(-1, 3)
        t1 = np.cross(Nf, [0.31, 0.53, 0.79]); t1 /= np.maximum(np.linalg.norm(t1, axis=1, keepdims=True), 1e-9)
        t2 = np.cross(Nf, t1)
        vis = np.zeros(len(Pf))
        for d in dirs:
            w = d[0] * t1 + d[1] * t2 + d[2] * Nf
            frac, _ = self.rays(Pf + 0.08 * Nf, Pf + 0.08 * Nf + 45 * w)
            vis += frac >= 1.0
        ao8 = (vis / len(dirs)).reshape(P8.shape[:2])
        self.bake_times = dict(rays=time.time() - t0)
        foot = self._boulder_footprints()
        H2, W2 = (TEX_H + 1) // 2, (TEX_W + 1) // 2
        cls_half = np.zeros((H2, W2), np.int8)
        rgb = np.zeros((TEX_H, TEX_W, 3), np.uint8)
        keep = []                                          # per band: what the thermal pass needs
        tj = np.arange(TEX_W)
        band = 128
        for r0 in range(0, TEX_H, band):
            ti = np.arange(r0, min(TEX_H, r0 + band))
            fi, fj = self._texel_map(ti[:, None], tj[None, :])
            fi, fj = np.broadcast_arrays(fi, fj)
            P, N = self._interp_grid(fi, fj)
            kind, side = self._quad_kind(fj)
            lit = self._up(sh, ti3, tj3, ti, tj)
            ao = self._up(ao8, ti8, tj8, ti, tj)
            col, Nn, cav, cls, burn = self._terrain_material(P, N, fi, kind, side, tl, tl2, tl3)
            contact = self._contact(P, foot)
            light = self._light(Nn, lit, np.clip(ao, 0.12, 1) * cav * contact)
            rgb[r0:r0 + len(ti)] = np.clip(col * light, 0, 255).astype(np.uint8)
            cls_half[r0 // 2:(r0 + len(ti) + 1) // 2] = cls[::2, ::2]
            ins_now = (np.clip(Nn @ SUN, 0, 1) * lit).astype(np.float32)
            keep.append((r0, ti, ins_now, burn.astype(np.float32), N[..., 2].astype(np.float32), P[..., 0].astype(np.float32),
                         P[..., 1].astype(np.float32), P[..., 2].astype(np.float32)))
        # prefilter the color texture
        for c in range(3):
            rgb[..., c] = np.clip(gaussian_filter(rgb[..., c].astype(np.float32), 0.6) + 0.5, 0, 255).astype(np.uint8)
        self.tex_rgb = rgb
        # thermal: class parameters at half resolution, blurred over about 25 cm (8 half-texels)
        names = ("rock", "soil", "sand", "drygrass", "leaf")
        par = {key: np.zeros((H2, W2), np.float32) for key in ("shade", "sun", "emis", "tau")}
        for ci, nm in enumerate(names):
            m = cls_half == ci
            par["shade"][m] = CLASSES[nm]["shade"]; par["sun"][m] = CLASSES[nm]["sun"]
            par["emis"][m] = CLASSES[nm]["emis"]; par["tau"][m] = TAU_H[nm]
        for key in par:
            par[key] = gaussian_filter(par[key], 8.0, mode="nearest")
        thm = np.zeros((TEX_H, TEX_W, 3), np.uint8)
        ti_h, tj_h = np.arange(0, TEX_H, 2) + 0.5, np.arange(0, TEX_W, 2) + 0.5
        for r0, ti, ins_now, burn, nz, x, y, z in keep:
            pp = {key: self._up(v, ti_h, tj_h, ti, tj) for key, v in par.items()}
            tau = np.maximum(pp["tau"], 0.1)
            wsum = np.ones_like(tau)
            ins = ins_now.copy()
            for age, pk in past:
                wk = np.exp(-age / tau)
                ins += wk * self._up(pk, ti6, tj6, ti, tj)
                wsum += wk
            ins /= wsum
            noise = 1.2 * fbm(tl2, x * 1.7, y * 1.7, 0.3, 3) + 0.8 * fbm(tl, x * 2.3 + 9, y * 2.3, 0.06, 2)
            heat = self._up(heat3, ti3, tj3, ti, tj)
            tk = pp["shade"] + (pp["sun"] - pp["shade"]) * ins + noise + 273.15 + heat
            tk = tk + (180 + 150 * smoothstep(-1, 1, tl(x * 3, y * 3, 0.04))) * burn ** 1.5
            em = np.clip(pp["emis"] + 0.012 * tl(x * 3 + 4, y * 3, 0.15), 0.85, 0.99)
            thm[r0:r0 + len(ti)] = encode_temperature(tk, em)
        self.tex_thermal = thm
        self.bake_times["terrain"] = time.time() - t0

    def _boulder_footprints(self):
        """Per boulder: center (xy) and the radius of its ground contact by angle (32 bins)."""
        out = []
        for b in self.boulders:
            gz = self.terrain_z(b.center[None, :2])[0]
            v = b.verts[b.verts[:, 2] < gz + 0.25]
            if len(v) < 3:
                v = b.verts
            d = v[:, :2] - b.center[:2]
            a = np.mod(np.arctan2(d[:, 1], d[:, 0]), 2 * np.pi)
            r = np.linalg.norm(d, axis=1)
            bins = np.zeros(32)
            np.maximum.at(bins, (a / (2 * np.pi) * 32).astype(int) % 32, r)
            bins = np.maximum(bins, gaussian_filter1d(bins, 1.0, mode="wrap") * 0.9)
            out.append((b.center[:2].copy(), bins, float(b.size)))
        return out

    def _contact(self, P, foot):
        """Contact darkening around boulders: 1 - 0.5 exp(-d / 0.12 m) at a distance d outside the footprint."""
        x, y = P[..., 0], P[..., 1]
        out = np.ones(x.shape, np.float32)
        for c, bins, size in foot:
            dx, dy = x - c[0], y - c[1]
            near = (np.abs(dx) < size) & (np.abs(dy) < size)
            if not near.any():
                continue
            a = np.mod(np.arctan2(dy[near], dx[near]), 2 * np.pi)
            rr = np.interp(a, np.arange(33) / 32 * 2 * np.pi, np.append(bins, bins[0]))
            d = np.maximum(np.hypot(dx[near], dy[near]) - rr, 0)
            out[near] *= (1 - 0.5 * np.exp(-d / 0.12)).astype(np.float32)
        return out

    def _terrain_material(self, P, N, fi, kind, side, tl, tl2, tl3):
        """Albedo, shading normal, cavity term, surface class (0 rock, 1 soil, 2 sand, 3 dry grass, 4 leaf)
        and burn amount of terrain texels."""
        x, y, z = P[..., 0], P[..., 1], P[..., 2]
        shp = z.shape
        col = np.zeros(shp + (3,))
        cav = np.ones(shp)
        Nn = N.copy()
        cls = np.zeros(shp, np.int8)
        rows = np.clip(np.round(fi).astype(int), 0, len(self.y) - 1)
        # --- walls: colonnade, ledge, entablature ------------------------------------------------------
        wall = (kind >= 2) & (kind <= 4)
        for s in (-1, 1):
            m = wall & (side == s)
            if not m.any():
                continue
            ym, zm = y[m], z[m]
            zc = self.col_top[s][rows[m]]
            dcol, jd, cj, ci, slope, step = self.column_d(s, ym, zm)
            dbl, bedge, hb, btop, dab = self.block_d(s, ym, zm)
            t = self.col_top_at(s, ym, zm, zc)
            w = self.wf[s]
            n0 = N[m]
            ey = np.array([0.0, 1.0, 0.0]) - n0[:, 1:2] * n0
            ey /= np.maximum(np.linalg.norm(ey, axis=1, keepdims=True), 1e-9)
            ez = np.cross(n0, ey) * (-s)
            ez = np.where(ez[:, 2:3] < 0, -ez, ez)
            # shading normal: the column's facet, or the block's own tilt
            hb2 = hash01(np.floor(ym * 3).astype(np.int64), np.floor(zm * 3).astype(np.int64), 3)
            gy = (1 - t) * slope + t * (hb - 0.5) * 0.9
            gz = t * ((hash01(np.round(hb * 1e6).astype(np.int64), 1, 7) - 0.5) * 0.9 - 0.25)
            nn = n0 - (gy * s)[:, None] * ey - gz[:, None] * ez
            Nn[m] = nn / np.linalg.norm(nn, axis=1, keepdims=True)
            # albedo: per column between dark grey-brown and buff (+-25 %), greyer columns, per block likewise
            dark, buff, grey = np.array([74, 66, 58.0]), np.array([158, 136, 106.0]), np.array([112, 108, 102.0])
            ct = mix(dark, buff, w["tone"][ci]) * 1.0
            ct = mix(ct, grey, 0.45 * (w["grey"][ci] > 0.7))
            cb = mix(dark * 0.95, buff * 0.92, hb)
            cb = mix(cb, grey * 0.9, 0.4 * (hash01(np.round(hb * 1e6).astype(np.int64), 2, 11) > 0.7))
            c = mix(ct, cb, t)
            c = c * (1 + 0.08 * fbm(tl, ym * 1.3, zm, 0.1, 3) + 0.06 * fbm(tl2, ym * 0.4, zm * 0.25, 0.6, 2))[:, None]
            # recesses: 40-60 % darker within 4-8 cm of a column's edges, the joint itself darkest; cross
            # joints only where the column steps, with the shadow below a protruding segment
            jdn = jd + 0.01 * tl(ym * 3, zm * 3, 0.03)
            rec = (1 - 0.45 * smoothstep(0.16, 0.02, jdn)) * (1 - 0.3 * smoothstep(0.04, 0.0, jdn))
            stepj = 0.6 * smoothstep(0.04, 0.008, cj) * smoothstep(0.02, 0.08, np.abs(step))
            shad = (step > 0.03) * smoothstep(0.0, 0.06, cj) * smoothstep(1.4 * step + 0.02, 1.4 * step - 0.02, cj) * (cj > 0)
            colr = rec * (1 - 0.5 * stepj) * (1 - 0.45 * shad)
            ben = bedge + 0.01 * tl(ym * 3, zm * 3, 0.03)
            brec = (1 - 0.4 * smoothstep(0.12, 0.02, ben)) * (1 - 0.25 * smoothstep(0.035, 0.0, ben))
            bshad = smoothstep(1.4 * np.maximum(dab - dbl, 0) + 0.01, 1.4 * np.maximum(dab - dbl, 0) - 0.03, btop) * (dab > dbl + 0.03)
            blr = brec * (1 - 0.5 * bshad)
            cav_m = (1 - t) * colr + t * blr
            # weathering: dark vertical varnish streaks, white mineral streaks on a few columns, lichen
            streak = fbm(tl3, ym * 4.0 + 50 * s, zm * 0.1, 0.35, 2)
            c = c * (1 - 0.3 * smoothstep(0.2, 1.4, streak))[:, None]
            pale = w["pale"][ci] * smoothstep(0.6, 1.6, tl3(ym * 6.0 - 30 * s, zm * 0.12 + 11, 0.3)) * (1 - t)
            c = mix(c, np.array([210, 206, 196.0]), 0.6 * pale)
            lich = smoothstep(0.9, 1.6, fbm(tl2, ym * 1.5 + 9, zm * 1.5, 0.06, 2))
            c = mix(c, np.array([150, 152, 124.0]), 0.3 * lich)
            orange = smoothstep(1.3, 2.0, fbm(tl2, ym * 0.9, zm * 0.9 + 4, 0.12, 2)) * smoothstep(1.1, 1.8, tl(ym * 1.7, zm * 1.7 + 4, 0.03))
            c = mix(c, np.array([166, 118, 62.0]), 0.3 * orange)
            hrel = np.clip((zm - self.floor0[rows[m]]) / 24.0, 0, 1)
            c = c * (0.85 + 0.2 * hrel)[:, None]
            # ledge: soil and plants on its flat top only
            led = (kind[m] == 3) & (n0[:, 2] > 0.55)
            soil = mix(np.array([112, 98, 80.0]), np.array([96, 90, 82.0]), smoothstep(-0.5, 0.5, tl(ym * 3, zm, 0.05)))
            green = smoothstep(0.3, 1.1, tl2(ym * 0.7, zm, 0.2))
            soil = mix(soil, np.array([74, 88, 50.0]), 0.75 * green)
            c = np.where(led[:, None], soil, c)
            c = c * np.where(led, 1.0, cav_m)[:, None]
            col[m], cav[m] = c, np.where(led, 0.9, 0.6 + 0.4 * cav_m)
            cls[m] = np.where(led & (green > 0.5), 4, np.where(led, 1, 0))
        # --- talus: dark grey angular blocks with plants between --------------------------------------------
        m = kind == 1
        if m.any():
            xm, ym = x[m], y[m]
            sc_ = 0.22 + 0.16 * smoothstep(-1, 1, tl2(xm * 0.5, ym * 0.5, 0.5))
            f1, f2, cu, cv, du, dv = voronoi2(xm / sc_ + 0.3 * tl(xm, ym, 0.2), ym / sc_, 77, jitter=0.95)
            hb = hash01(cu, cv, 78)
            gap = smoothstep(0.02, 0.1, (f2 - f1) * sc_)                  # 1 in a block, 0 in the gap between blocks
            stone = hb > 0.25
            nb = np.stack([du * (hash01(cu, cv, 79) - 0.5) * 1.6, dv * (hash01(cu, cv, 80) - 0.5) * 1.6, np.zeros_like(du)], -1)
            nn = N[m] + nb * (stone * gap)[:, None]
            Nn[m] = nn / np.linalg.norm(nn, axis=1, keepdims=True)
            rock = mix(np.array([70, 66, 62.0]), np.array([112, 102, 90.0]), hb) * (1 + 0.1 * tl(xm * 3, ym * 3, 0.03))[:, None]
            soil = np.array([84, 76, 64.0]) * (1 + 0.1 * fbm(tl, xm, ym, 0.15, 2))[:, None]
            gr = smoothstep(0.0, 0.8, fbm(tl2, xm * 0.7, ym * 0.7, 0.5, 3) + 0.4 * tl(xm, ym, 0.06) - 0.2 * self.talus_frac(xm, ym))
            g_col = mix(np.array([70, 84, 46.0]), np.array([104, 108, 64.0]), smoothstep(-1, 1, tl(xm + 7, ym, 0.12)))
            g_col = g_col * (0.75 + 0.3 * smoothstep(-1.2, 1.2, tl(xm * 2, ym * 2, 0.02)))[:, None]
            c = np.where((stone & (gap > 0.3))[:, None], rock, soil)
            c = mix(c, g_col, 0.9 * gr * (1 - 0.7 * (stone & (gap > 0.5))))
            c = c * (0.72 + 0.28 * np.maximum(gap, 1 - stone))[:, None]
            col[m], cav[m] = c, 0.8 + 0.2 * gap
            cls[m] = np.where(gr > 0.55, 4, np.where(stone, 0, 1))
        # --- vegetated slope band: soil, grass, shrubs' shade, rock outcrops ---------------------------------
        m = kind == 7
        if m.any():
            xm, ym, zm = x[m], y[m], z[m]
            f1, f2, cu, cv, du, dv = voronoi2(ym / 0.7, zm / 0.5, 41, jitter=0.8)
            hb = hash01(cu, cv, 42)
            outc = (hb > 0.72) & (f1 < 0.45)
            soil = np.array([110, 96, 76.0]) * (1 + 0.1 * fbm(tl, ym, zm, 0.1, 2))[:, None]
            g = smoothstep(-0.6, 0.6, fbm(tl2, xm + ym, zm * 1.3, 0.4, 3))
            gcol = mix(np.array([64, 80, 42.0]), np.array([120, 116, 70.0]), smoothstep(-1, 1, tl(ym * 2, zm * 2, 0.08)))
            c = mix(soil, gcol * (0.75 + 0.3 * smoothstep(-1, 1, tl(ym * 4, zm * 4, 0.015)))[:, None], 0.85 * g)
            rock = mix(np.array([90, 82, 74.0]), np.array([140, 126, 104.0]), hb)
            c = np.where(outc[:, None], rock, c)
            col[m], cav[m] = c, np.where(outc, 1.0, 0.85)
            cls[m] = np.where(outc, 0, np.where(g > 0.5, 4, 1))
        # --- floor: the dry wash (no single-texel features: the smallest pebbles span 3 texels) -------------
        m = kind == 0
        if m.any():
            xm, ym = x[m], y[m]
            lat = self.lateral(xm, ym)
            e = np.abs(lat) / (self.width_at(ym) / 2)
            f1, f2, cu, cv, du, dv = voronoi2(xm / 0.09, ym / 0.09, 91)
            hb = hash01(cu, cv, 92)
            gravel_amt = smoothstep(0.15, 0.9, e + 0.35 * fbm(tl2, xm * 0.3, ym * 0.3, 0.5, 2))
            peb = smoothstep(0.5, 0.36, f1) * (hb < 0.2 + 0.6 * gravel_amt)
            nb = np.stack([du, dv, np.zeros_like(du)], -1) * (peb * 0.7)[:, None]
            nn = N[m] + nb
            Nn[m] = nn / np.linalg.norm(nn, axis=1, keepdims=True)
            sand = np.array([178, 162, 134.0]) * (1 + 0.05 * fbm(tl, xm * 2, ym * 2, 0.08, 2))[:, None]
            sand = mix(sand, np.array([192, 178, 150.0]), 0.5 * smoothstep(0.4, 0.0, e) * smoothstep(-0.5, 0.8, tl2(xm, ym * 0.3, 0.5)))
            h1 = hb[:, None]
            pc = np.select([h1 < 0.12, h1 < 0.3, h1 < 0.5, h1 < 0.75], [np.array([110, 102, 94.0]), np.array([150, 132, 104.0]),
                                                                       np.array([168, 162, 152.0]), np.array([132, 124, 112.0])],
                           np.array([120, 108, 92.0]))
            c = mix(sand, pc, peb)
            gp = smoothstep(0.35, 1.0, fbm(tl2, xm * 0.8 + 40, ym * 0.8, 0.7, 3) + 1.2 * e - 0.5)
            gcol = mix(np.array([86, 96, 54.0]), np.array([150, 136, 88.0]), smoothstep(-1.0, 1.0, tl(xm, ym, 0.15)))
            gcol = gcol * (0.7 + 0.35 * smoothstep(-1.2, 1.2, tl(xm * 3, ym * 3, 0.03)))[:, None]
            c = mix(c, gcol, 0.65 * gp)
            col[m], cav[m] = c, 1 - 0.12 * (1 - peb) * gravel_amt
            cls[m] = np.where(gp > 0.5, 3, 2)
        # --- cap and plateau: golden and olive grass, sage-grey patches, soil ----------------------------------
        m = (kind == 5) | (kind == 6)
        if m.any():
            xm, ym = x[m], y[m]
            g = fbm(tl2, xm * 0.5, ym * 0.5, 0.8, 3)
            straw = mix(np.array([164, 142, 94.0]), np.array([118, 114, 74.0]), smoothstep(-1, 1, g))
            straw = straw * (0.82 + 0.3 * smoothstep(-1.4, 1.4, tl(xm * 2 + ym, ym * 2 - xm, 0.03)))[:, None]
            sage = mix(np.array([112, 118, 98.0]), np.array([86, 94, 74.0]), smoothstep(-1, 1, tl(xm, ym, 0.1)))
            c = mix(straw, sage, 0.6 * smoothstep(0.3, 1.1, fbm(tl, xm + 70, ym, 0.25, 2)))
            soil = np.array([124, 106, 82.0]) * (1 + 0.1 * tl(xm, ym, 0.05))[:, None]
            c = mix(c, soil, 0.6 * smoothstep(0.9, 1.5, tl3(xm, ym, 0.3)))
            capm = kind[m] == 5
            rk = smoothstep(0.3, 1.0, tl2(xm * 2, ym * 2, 0.2)) * capm
            c = mix(c, np.array([104, 94, 82.0]), rk)
            col[m], cav[m] = c, 0.85 + 0.15 * smoothstep(-1, 1, tl(xm * 3, ym * 3, 0.03))
            cls[m] = np.where(rk > 0.5, 0, 3)
        # --- fires: the burned patch baked in (char inside the rim, a noisy feathered edge) ------------------------
        burn = np.zeros(shp)
        for f in self.firebrands:
            d = np.stack([x - f.center[0], y - f.center[1]], -1)
            r = np.linalg.norm(d, axis=-1)
            near = r < f.rim.max() * 1.3 + 0.6
            if not near.any():
                continue
            a = np.mod(np.arctan2(d[..., 1], d[..., 0]), 2 * np.pi)
            rim = np.interp(a, np.append(np.arange(RIM_N) / RIM_N * 2 * np.pi, 2 * np.pi), np.append(f.rim, f.rim[0]))
            q = (r - rim) / 0.25 + 0.6 * fbm(tl, x * 2, y * 2, 0.06, 2)
            burn = np.maximum(burn, smoothstep(0.9, -0.6, q) * near)
        ash = smoothstep(0.4, 1.2, fbm(tl, x * 1.3 + 3, y * 1.3, 0.08, 2))
        charc = mix(np.array([28, 24, 21.0]), np.array([86, 84, 80.0]), 0.5 * ash * (burn > 0.9))
        scorch = mix(np.array([84, 64, 44.0]), charc, smoothstep(0.3, 0.8, burn))
        col = mix(col, scorch, np.clip(burn * 1.3, 0, 1))
        return col, Nn, cav, cls, burn

    def talus_frac(self, x, y):
        """0 at the talus toe .. 1 at its top (approximate, from the row's talus height)."""
        u = np.abs(self.lateral(x, y)) - self.width_at(y) / 2
        s = np.where(self.lateral(x, y) < 0, -1, 1)
        th = np.where(s < 0, np.interp(y, self.y, self.talus_h[-1]), np.interp(y, self.y, self.talus_h[1]))
        return np.clip(u * 0.7 / np.maximum(th, 0.3), 0, 1)

    # --- fires: burned patches and their texture -------------------------------------------------------------
    def fire_meshes(self, k):
        """(burned patch verts, faces), (ember verts, faces, piece index per face) of firebrand k."""
        fb = self.firebrands[k]
        rng = np.random.default_rng(self.seed * 1000 + k)
        ang = np.arange(RIM_N) / RIM_N * 2 * np.pi
        rings = np.array([0.0, 0.25, 0.5, 0.7, 0.82, 0.88])     # inside the char baked into the terrain
        pts = [fb.center[:2]]
        for r in rings[1:]:
            for a, rr in zip(ang, fb.rim):
                pts.append(fb.center[:2] + r * rr * np.array([math.cos(a), math.sin(a)]))
        pts = np.array(pts)
        z = self.terrain_z(pts) + 0.012
        av = np.column_stack([pts, z])
        af = [[0, 1 + i, 1 + (i + 1) % RIM_N] for i in range(RIM_N)]
        for r in range(len(rings) - 2):
            o0, o1 = 1 + r * RIM_N, 1 + (r + 1) * RIM_N
            for i in range(RIM_N):
                j = (i + 1) % RIM_N
                af += [[o0 + i, o1 + i, o1 + j], [o0 + i, o1 + j, o0 + j]]
        ev, ef, ep = [], [], []
        for i, (pc, pr, _) in enumerate(fb.pieces):
            v, f = lumpy(rng, 1, 0.45, waves=6, kmin=2, kmax=5)
            v = v * [pr, pr * rng.uniform(0.5, 1.0), pr * rng.uniform(0.35, 0.6)]
            v = v @ rotation(rng.uniform(0, 6.3)).T + pc
            ef.append(f + sum(len(x) for x in ev)); ev.append(v); ep += [i] * len(f)
        return (av, np.array(af)), (np.vstack(ev), np.vstack(ef), np.array(ep))

    FIRE_TEX = 256
    COAL_TEX = 16

    def _bake_fires(self, rng):
        """Per fire a FIRE_TEX x FIRE_TEX top-down texture of the burned patch (char and ash; glowing
        cracks and small coals in the band behind the flaming front, dull embers behind) and its
        temperature (150 to 350 C, hotter toward the front, hot specks); below it, per ember piece a
        COAL_TEX square: dark char with a network of glowing cracks."""
        n, S, CT = len(self.firebrands), self.FIRE_TEX, self.COAL_TEX
        tl = Tile(rng, 256, 1.0)
        rgb = np.zeros((S + CT, S * n, 3), np.uint8)
        thm = np.zeros((S + CT, S * n, 3), np.uint8)
        ang = np.arange(RIM_N) / RIM_N * 2 * np.pi
        self.fire_tex_extent = []
        for k, f in enumerate(self.firebrands):
            Rm = float(f.rim.max()) * 1.05
            self.fire_tex_extent.append(Rm)
            jj, ii = np.meshgrid(np.arange(S), np.arange(S))
            x = f.center[0] + ((jj + 0.5) / S * 2 - 1) * Rm
            y = f.center[1] + ((ii + 0.5) / S * 2 - 1) * Rm
            d = np.stack([x - f.center[0], y - f.center[1]], -1)
            r = np.linalg.norm(d, axis=-1)
            a = np.mod(np.arctan2(d[..., 1], d[..., 0]), 2 * np.pi)
            rim = np.interp(a, np.append(ang, 2 * np.pi), np.append(f.rim, f.rim[0]))
            act = np.interp(a, np.append(ang, 2 * np.pi), np.append(gaussian_filter1d(f.active, 1.5, mode="wrap"), f.active[0]))
            q = r / np.maximum(rim, 1e-3)                       # 0 center .. 1 rim
            n1 = tl(x, y, 0.03)
            n2 = fbm(tl, x * 0.7 + 5, y * 0.7, 0.1, 3)
            char = np.array([26, 22, 20.0]) * (1 + 0.35 * n1)[..., None]
            ash = smoothstep(0.4, 1.2, fbm(tl, x * 1.3 + 3, y * 1.3, 0.08, 2))      # the terrain bake's own ash pattern
            c = mix(char, np.array([86, 84, 80.0]) * (1 + 0.2 * n1)[..., None], 0.5 * ash)
            c = mix(c, np.array([150, 148, 142.0]), 0.5 * smoothstep(0.8, 1.5, n2 + 0.3 * n1) * ash * (q < 0.7))
            # glowing cracks (Voronoi edges) and small coals, densest just behind the active front
            f1, f2, *_ = voronoi2(x / 0.035, y / 0.035, 300 + k)
            crack = smoothstep(0.12, 0.0, f2 - f1)
            band = smoothstep(0.35, 0.8, q) * (0.25 + 0.75 * act)
            coal = smoothstep(1.2, 1.8, tl(x * 2.3, y * 2.3, 0.01)) * smoothstep(0.2, 0.7, q)
            glow = np.clip(crack * band * smoothstep(-0.6, 0.6, n1) + coal * 0.8, 0, 1)
            emit = mix(np.array([150, 30, 6.0]), np.array([255, 150, 40.0]), np.clip(glow * 1.3 - 0.3, 0, 1))
            col = mix(c, emit, np.clip(glow * 1.1, 0, 1))
            t_c = 150 + 120 * smoothstep(0.2, 0.9, q) * (1 + 0.3 * n2) + 80 * band * smoothstep(-1, 1, n1)
            t_c = np.maximum(t_c, 350 + 400 * glow) * (glow > 0.15) + t_c * (glow <= 0.15)
            rgb[:S, k * S:(k + 1) * S] = np.clip(col, 0, 255).astype(np.uint8)
            thm[:S, k * S:(k + 1) * S] = encode_temperature(t_c + 273.15, np.full(t_c.shape, CLASSES["char"]["emis"]))
            for i, (_, _, tc) in enumerate(f.pieces):
                cj, ci = np.meshgrid(np.arange(CT), np.arange(CT))
                g1, g2, *_ = voronoi2(cj / 4.0 + 13 * i, ci / 4.0 + 7 * k, 500 + i)
                cr = smoothstep(0.18, 0.0, g2 - g1)
                cc = mix(np.array([34, 26, 22.0]), ember_rgb(tc), cr)
                rgb[S:, k * S + i * CT:k * S + (i + 1) * CT] = np.clip(cc, 0, 255).astype(np.uint8)
                thm[S:, k * S + i * CT:k * S + (i + 1) * CT] = encode_temperature(tc * (0.55 + 0.45 * cr) + 273.15,
                                                                                  np.full(cr.shape, CLASSES["ember"]["emis"]))
        self.fire_rgb, self.fire_thermal = rgb, thm

    # --- assets -------------------------------------------------------------------------------------------
    def _write_meshes(self):
        out, tag = ASSETS, f"s{self.seed}"
        files = self.files
        save_png(np.flipud(self.tex_rgb), out / f"terrain_{tag}_rgb.png")
        save_png(np.flipud(self.tex_thermal), out / f"terrain_{tag}_thermal.png")
        save_png(np.flipud(self.atlas_rgb), out / f"objects_{tag}_rgb.png")
        save_png(np.flipud(self.atlas_thermal), out / f"objects_{tag}_thermal.png")
        save_png(np.flipud(self.fire_rgb), out / f"fires_{tag}_rgb.png")
        save_png(np.flipud(self.fire_thermal), out / f"fires_{tag}_thermal.png")
        for g, sel in (("rocks", lambda q: q.group == "rocks"), ("veg", lambda q: q.group == "veg" and q.mat != "grass"),
                       ("grass", lambda q: q.group == "veg" and q.mat == "grass")):
            ps = [q for q in self.parts if sel(q)]
            off = np.cumsum([0] + [len(q.verts) for q in ps])[:-1]
            v = np.vstack([q.verts for q in ps])
            f = np.vstack([q.faces + o for q, o in zip(ps, off)])
            uv = np.vstack([q.uv.reshape(-1, 2) for q in ps])
            files[g] = write_obj(out / f"{g}_{tag}.obj", v, f, uv, uv_faces=np.arange(len(uv)).reshape(-1, 3))
        for k, b in enumerate(self.boulders):
            q = [q for q in self.parts if q.group == "boulder" and q.index == k][0]
            files[f"boulder{k}"] = write_obj(out / f"boulder_{tag}_{k:02d}.obj", q.verts, q.faces, q.uv.reshape(-1, 2),
                                             uv_faces=np.arange(len(q.faces) * 3).reshape(-1, 3))
        S, n = self.FIRE_TEX, len(self.firebrands)
        for k, fb in enumerate(self.firebrands):
            (av, af), (ev, ef, ep) = self.fire_meshes(k)
            Rm = self.fire_tex_extent[k]
            u = (k * S + ((av[:, 0] - fb.center[0]) / Rm + 1) / 2 * S) / (S * n)
            v = ((av[:, 1] - fb.center[1]) / Rm + 1) / 2 * S / (S + self.COAL_TEX)
            uva = np.column_stack([u, v])
            files[f"ash{k}"] = write_obj(out / f"fire_{tag}_{k}_ash.obj", av[af].reshape(-1, 3), np.arange(len(af) * 3).reshape(-1, 3),
                                         uva[af].reshape(-1, 2))
            CT = self.COAL_TEX
            corners = ev[ef].reshape(-1, 3)
            pc = np.array([fb.pieces[i][0] for i in np.repeat(ep, 3)])
            pr = np.array([fb.pieces[i][1] for i in np.repeat(ep, 3)])
            lx = np.clip((corners[:, 0] - pc[:, 0]) / (2.2 * pr) + 0.5, 0.05, 0.95)
            ly = np.clip((corners[:, 1] - pc[:, 1]) / (2.2 * pr) + 0.5, 0.05, 0.95)
            uv_e = np.column_stack([(k * S + (np.repeat(ep, 3) + lx) * CT) / (S * n), (S + ly * CT) / (S + CT)])
            files[f"ember{k}"] = write_obj(out / f"fire_{tag}_{k}_embers.obj", corners, np.arange(len(ef) * 3).reshape(-1, 3), uv_e)
        for k in range(len(self.boulders)):
            files[f"boulder{k}_hull"] = str(out / f"boulder_{tag}_{k:02d}_hull.obj")
        keep = {Path(x).name for x in files.values()} | {f"{n}_{tag}_{s}.png" for n in ("terrain", "objects", "fires", "objectslive")
                                                         for s in ("rgb", "thermal")}
        keep |= {f.name for f in out.glob(f"*live_{tag}_*.obj")}
        for old in out.glob(f"*_{tag}*"):                 # files of an earlier build of this seed that this one does not write
            if old.name not in keep and not old.name.startswith(f"gorge_{tag}") and not old.name.endswith(".tmp"):
                old.unlink()

    def write_assets(self, out=ASSETS):
        """The assets are written by the build (and cached); this returns their files."""
        return self.files

    # --- loading into a PyBullet client --------------------------------------------------------------------
    def load(self, client, kind, lod=0):
        """Load the world into `client`. kind: "physics" (collision shapes only: concave terrain
        trimesh, convex boulders, compounds of convex hulls for rocks and vegetation), "visual"
        (textured meshes, no collision) or "thermal" (the same meshes with the temperature-encoding
        textures). lod 1 leaves out the grass tufts (they have no collision); lod 2 is the live level of
        detail of the onboard cameras (Gorge._live_lod: decimated boulders, rocks and plants, no grass;
        the same terrain and fires). Returns {body id: (class,
        index)}; classes terrain, boulder, rocks, veg (0: shrubs and trees, 1: grass), ash, ember."""
        out, tag, bodies = self.asset_dir, f"s{self.seed}", {}
        if kind == "physics":
            col = p.createCollisionShape(p.GEOM_MESH, fileName=self.files["terrain"], flags=p.GEOM_FORCE_CONCAVE_TRIMESH, physicsClientId=client)
            bodies[p.createMultiBody(0, col, physicsClientId=client)] = ("terrain", 0)
            for k, b in enumerate(self.boulders):
                col = p.createCollisionShape(p.GEOM_MESH, fileName=self.files[f"boulder{k}_hull"], physicsClientId=client)
                bodies[p.createMultiBody(0, col, physicsClientId=client)] = ("boulder", k)
            for g in ("rocks", "veg"):
                col = p.createCollisionShape(p.GEOM_MESH, fileName=self.files[f"{g}_hull"], physicsClientId=client)
                bodies[p.createMultiBody(0, col, physicsClientId=client)] = (g, 0)
            return bodies
        suffix = "rgb" if kind == "visual" else "thermal"
        tex = {name: p.loadTexture(str(out / f"{name}_{tag}_{suffix}.png"), physicsClientId=client)
               for name in (("terrain", "objectslive", "fires") if lod >= 2 else ("terrain", "objects", "fires"))}

        def add(fname, texture, cls, k):
            vs = p.createVisualShape(p.GEOM_MESH, fileName=fname, rgbaColor=[1, 1, 1, 1], physicsClientId=client)
            b = p.createMultiBody(0, -1, vs, physicsClientId=client)
            p.changeVisualShape(b, -1, textureUniqueId=texture, rgbaColor=[1, 1, 1, 1], physicsClientId=client)
            bodies[b] = (cls, k)
        if lod >= 2:                                     # the live level of detail (Gorge._live_lod), in chunks
            self.live_aabb = getattr(self, "live_aabb", {})
            for key, cls, k, lo, hi in self.live_chunks:
                add(self.files[key], tex["terrain" if cls == "terrain" else "objectslive"], cls, k)
                self.live_aabb[(client, max(bodies))] = (lo, hi)
        else:
            add(self.files["terrain"], tex["terrain"], "terrain", 0)
            for k in range(len(self.boulders)):
                add(self.files[f"boulder{k}"], tex["objects"], "boulder", k)
            add(self.files["rocks"], tex["objects"], "rocks", 0)
            add(self.files["veg"], tex["objects"], "veg", 0)
            if lod < 1:
                add(self.files["grass"], tex["objects"], "veg", 1)
        for k in range(len(self.firebrands)):
            add(self.files[f"ash{k}"], tex["fires"], "ash", k)
            add(self.files[f"ember{k}"], tex["fires"], "ember", k)
        return bodies

    # --- checks ----------------------------------------------------------------------------------------------
    def statics(self):
        return [self.terrain_id] + list(self.boulder_ids) + list(self.compound_ids)

    def corridor_clearance(self, path=None):
        """Minimum distance from the corridor (|lateral| <= CORRIDOR_HALF around the path, height
        CORRIDOR_Z above the floor) to all collision geometry, and from the path line itself, by
        closest-point queries of a 1 cm probe sphere in the scratch client."""
        pts = self.path_points(0.25, path)
        probe = p.createMultiBody(0, p.createCollisionShape(p.GEOM_SPHERE, radius=0.01, physicsClientId=self._client),
                                  physicsClientId=self._client)
        statics = self.statics()

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

    def free_width(self, height=FLIGHT_H, step=0.25):
        """Free width (m) across the axis at `height` above the centerline floor along the route: rays
        from the path point to both sides against all collision geometry."""
        pts = self.path_points(step)
        pts = np.column_stack([pts[:, :2], self.floor_c(pts[:, 1]) + height])
        th = np.interp(pts[:, 1], self.y, self.theta)
        nrm = np.column_stack([np.cos(th), -np.sin(th), np.zeros_like(th)])
        f1, _ = self.rays(pts, pts + 20 * nrm)
        f2, _ = self.rays(pts, pts - 20 * nrm)
        return 20 * (f1 + f2), pts

    def visibility(self, k, pts):
        """Line of sight (bool per path point) from pts to firebrand k (its patch center, 0.15 m up)."""
        c = self.firebrands[k].center + [0, 0, 0.15]
        frac, _ = self.rays(pts, np.repeat(c[None], len(pts), 0))
        return frac >= 0.999

    def summary(self):
        fl = self.path_points(0.1)
        line, box, _ = self.corridor_clearance()
        fw, _ = self.free_width()
        c = self.counts
        print(f"seed {self.seed}: terrain {len(self.V)} vertices, {len(self.F)} triangles; {len(self.boulders)} boulders, "
              f"{len(self.rocks)} rocks, vegetation {c['veg']}; triangles {c['triangles']}; {len(self.firebrands)} fires "
              f"(build {getattr(self, 'build_s', 0):.0f} s{', cached' if getattr(self, 'cached', False) else ''})")
        hd = np.degrees(np.abs(self.theta[(self.y >= 0) & (self.y <= Y_END)])).max()
        m = (self.y >= 0) & (self.y <= Y_END)
        print(f"  flight y 0..{Y_END} m, path length {np.sum(np.linalg.norm(np.diff(fl, axis=0), axis=1)):.1f} m, "
              f"max axis heading {hd:.1f} deg, wash (floor) width {self.width[m].min():.2f}..{self.width[m].max():.2f} m "
              f"(narrows at y = {self.narrows[0]:.1f}, {self.narrows[1]:.1f} m); free width at {FLIGHT_H} m above the floor "
              f"{fw.min():.2f}..{fw.max():.2f} m (median {np.median(fw):.2f})")
        for s, name in ((-1, "west"), (1, "east")):
            print(f"  {name} wall height {self.height[s][m].min():.1f}..{self.height[s][m].max():.1f} m, talus "
                  f"{self.talus_h[s][m].min():.1f}..{self.talus_h[s][m].max():.1f} m high, mean angle toe to rim "
                  f"{self.wall_angle[s][m].min():.1f}..{self.wall_angle[s][m].max():.1f} deg")
        print(f"  floor rise {self.floor_c(Y_END) - self.floor_c(0):.2f} m over the flight; {len(self.path)} waypoints, legs "
              f"{np.linalg.norm(np.diff(self.path, axis=0), axis=1).min():.1f}..{np.linalg.norm(np.diff(self.path, axis=0), axis=1).max():.1f} m")
        print(f"  clearance: path line (3.5 m) min {line.min():.2f} m; corridor box (+-{CORRIDOR_HALF} m, {CORRIDOR_Z[0]}-{CORRIDOR_Z[1]} m) min {box.min():.2f} m")
        pp = self.path_points(0.25)
        for k, f in enumerate(self.firebrands):
            dy = f.center[1] - pp[:, 1]
            pts = pp[(dy >= 3) & (dy <= (20 if f.hidden else 25))]
            seen = self._seen(self._fire_points(f) if f.hidden else np.array([f.center + [0, 0, 0.1]]), pts)
            print(f"  fire {k}: ({f.center[0]:.1f}, {f.center[1]:.1f}, {f.center[2]:.2f}) {f.kind}, patch r {f.radius:.2f} m, flames "
                  f"{f.flame_h:.2f} m ({len(f.tongues)} tongues), {f.power_w / 1000:.1f} kW radiated, embers {f.temp_c:.0f} C, "
                  f"{'behind boulder ' + str(f.boulder) if f.hidden else 'open'}, in sight from {seen * 100:.0f} % of the approach")


def write_obj(path, v, f, uv=None, vn=None, uv_faces=None):
    """A Wavefront OBJ: vertices, optional texture coordinates (indexed like the vertices, or by
    uv_faces) and normals."""
    v = np.asarray(v, float)
    parts = ["# generated by gorge.py\n"]
    parts.append("".join("v %.4f %.4f %.4f\n" % tuple(r) for r in v))
    if uv is not None:
        parts.append("".join("vt %.6f %.6f\n" % tuple(r) for r in np.asarray(uv)))
    if vn is not None:
        parts.append("".join("vn %.4f %.4f %.4f\n" % tuple(r) for r in np.asarray(vn)))
    f1 = np.asarray(f) + 1
    if uv_faces is not None:
        t1 = np.asarray(uv_faces) + 1
        parts.append("".join("f %d/%d %d/%d %d/%d\n" % (a, ta, b, tb, c, tc) for (a, b, c), (ta, tb, tc) in zip(f1, t1)))
    elif vn is not None:
        parts.append("".join("f %d/%d/%d %d/%d/%d %d/%d/%d\n" % (a, a, a, b, b, b, c, c, c) for a, b, c in f1))
    elif uv is not None:
        parts.append("".join("f %d/%d %d/%d %d/%d\n" % (a, a, b, b, c, c) for a, b, c in f1))
    else:
        parts.append("".join("f %d %d %d\n" % (a, b, c) for a, b, c in f1))
    tmp = Path(f"{path}.{os.getpid()}.tmp")
    tmp.write_text("".join(parts))
    os.replace(tmp, path)                      # atomic: parallel runs never read a partial file
    return str(path)


def save_png(a, path):
    tmp = Path(f"{path}.{os.getpid()}.tmp.png")
    Image.fromarray(a).save(tmp, compress_level=6)
    os.replace(tmp, path)


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--rebuild", action="store_true", help="ignore the cache")
    a = ap.parse_args()
    t0 = time.time()
    g = Gorge(a.seed, rebuild=a.rebuild)
    print(f"world ready in {time.time() - t0:.1f} s -> {ASSETS}")
    g.summary()
