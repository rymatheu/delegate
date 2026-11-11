"""Onboard imaging for the gorge world: an RGB camera (with depth and segmentation) and an uncooled
LWIR microbolometer in the class of a FLIR Lepton 3.5, both rendered with PyBullet's TinyRenderer
from the vehicle's true pose and a camera mount in the body frame; and hot-spot detection.

Frames: world ENU, body FLU (PyBullet's). A mount is a position in the body frame and a
depression `pitch_deg` below the body x axis (and an optional yaw): FORWARD looks forward and 30 deg
down from the nose, DOWN straight down (image top = body forward).

Thermal rendering. The thermal camera renders a twin of the world (gorge.Gorge.load(..., "thermal"))
in its own PyBullet client, whose textures hold each surface element's temperature (16 bits in R
and G) and emissivity (B), with lighting reduced to the ambient term at 1 (TinyRenderer then returns
the texel exactly; checked by `selftest`). Per frame:
1. render the twin at SS x the sensor resolution: temperature T, emissivity e, segmentation, depth;
   pixels with no surface (segmentation -1) are sky, with brightness temperature T_SKY(elevation);
2. band radiance of each sample, Planck's law integrated over 8-14 um (table, `band_radiance`),
   through the atmosphere: L = tau(r) [e L(T) + (1 - e) L(T_air)] + (1 - tau(r)) L(T_air),
   tau(r) = exp(-ALPHA r) with r the range along the ray;
3. optics and detector: mean of the SS x SS samples of each pixel (so a sub-pixel ember raises its
   pixel by its fill fraction only), a Gaussian point spread of PSF_SIGMA_PX, white noise of
   NETD (as radiance at 30 deg C), clipping at the radiance of T_MAX_C (low-gain saturation);
4. apparent temperature = inverse of the band radiance (emissivity 1, no atmosphere correction:
   what a radiometric camera with default settings reports).
"""
import math
import time
from dataclasses import dataclass

import numpy as np
import pybullet as p
from PIL import Image
from scipy.ndimage import gaussian_filter, label

import gorge as G

# --- mounts --------------------------------------------------------------------------------------


@dataclass
class Mount:
    pos: tuple = (0.20, 0.0, -0.03)   # m, body FLU
    pitch_deg: float = 30.0           # depression below the body x axis
    yaw_deg: float = 0.0              # left positive

    def axes(self):
        """Camera forward and up vectors in the body frame."""
        a, b = math.radians(self.pitch_deg), math.radians(self.yaw_deg)
        Ry = np.array([[math.cos(a), 0, math.sin(a)], [0, 1, 0], [-math.sin(a), 0, math.cos(a)]])
        Rz = np.array([[math.cos(b), -math.sin(b), 0], [math.sin(b), math.cos(b), 0], [0, 0, 1]])
        R = Rz @ Ry
        return R @ [1.0, 0, 0], R @ [0, 0, 1.0]


FORWARD = Mount()
DOWN = Mount(pos=(0.0, 0.0, -0.10), pitch_deg=90.0)


def camera_pose(R_wb, p_wb, mount):
    """Eye, forward, up and right (world) of a camera on a body at (R_wb, p_wb)."""
    f, u = mount.axes()
    eye = np.asarray(p_wb) + R_wb @ np.asarray(mount.pos)
    fwd, up = R_wb @ f, R_wb @ u
    return eye, fwd, up, np.cross(fwd, up)


def matrices(eye, fwd, up, hfov_deg, w, h, near, far, client):
    vfov = 2 * math.degrees(math.atan(math.tan(math.radians(hfov_deg) / 2) * h / w))
    view = p.computeViewMatrix(eye.tolist(), (eye + fwd).tolist(), up.tolist(), physicsClientId=client)
    proj = p.computeProjectionMatrixFOV(vfov, w / h, near, far, physicsClientId=client)
    return view, proj


def ray_dirs(w, h, hfov_deg, fwd, up, right):
    """Unit world direction of each pixel center (h x w x 3) and its length factor |d| / d.fwd."""
    tx = math.tan(math.radians(hfov_deg) / 2)
    ty = tx * h / w
    xs = ((np.arange(w) + 0.5) / w * 2 - 1) * tx
    ys = (1 - (np.arange(h) + 0.5) / h * 2) * ty
    d = xs[None, :, None] * right + ys[:, None, None] * up + fwd
    n = np.linalg.norm(d, axis=-1, keepdims=True)
    return d / n, n[..., 0]


def linear_depth(buf, near, far):
    return far * near / (far - (far - near) * np.asarray(buf))


# --- RGB camera -------------------------------------------------------------------------------------

SKY_HORIZON, SKY_ZENITH = np.array([206, 220, 232.0]), np.array([112, 152, 210.0])


def sky_rgb(dirs):
    s = np.clip(dirs[..., 2], 0, 1)[..., None] ** 0.6
    return (1 - s) * SKY_HORIZON + s * SKY_ZENITH


def glow(img, seg, ember_colors, sigma, gain=1.6):
    """Draw glowing embers: every pixel of an ember body gets its emission color (unlit), and a
    Gaussian bloom of the ember pixels (sigma px, weight gain) is added. ember_colors: {body id: RGB}."""
    out = img.astype(float)
    em = np.zeros_like(out)
    for bid, col in ember_colors.items():
        m = seg == bid
        if m.any():
            out[m] = col
            em[m] = col
    if em.any():
        bloom = np.stack([gaussian_filter(em[..., c], sigma) for c in range(3)], -1)
        out = out + gain * bloom
    return np.clip(out, 0, 255)


class RGBCamera:
    def __init__(self, client, bodies, mount=FORWARD, width=320, height=240, hfov_deg=90.0, rate_hz=10.0,
                 near=0.05, far=200.0, gorge=None):
        self.c, self.mount, self.w, self.h, self.hfov, self.rate = client, mount, width, height, hfov_deg, rate_hz
        self.near, self.far = near, far
        self.ember_colors = {b: G.ember_rgb(gorge.firebrands[k].temp_c) for b, (cls, k) in bodies.items() if cls == "ember"}

    def capture(self, R_wb, p_wb):
        eye, fwd, up, right = camera_pose(R_wb, p_wb, self.mount)
        view, proj = matrices(eye, fwd, up, self.hfov, self.w, self.h, self.near, self.far, self.c)
        _, _, rgb, dep, seg = p.getCameraImage(self.w, self.h, view, proj, renderer=p.ER_TINY_RENDERER, shadow=0,
                                               lightDirection=G.SUN.tolist(), physicsClientId=self.c)
        rgb = np.reshape(rgb, (self.h, self.w, 4))[..., :3].astype(float)
        seg = np.reshape(seg, (self.h, self.w))
        dirs, k = ray_dirs(self.w, self.h, self.hfov, fwd, up, right)
        sky = seg < 0
        rgb[sky] = sky_rgb(dirs)[sky]
        rgb = glow(rgb, seg, self.ember_colors, max(1.0, self.w / 320))
        z = linear_depth(np.reshape(dep, (self.h, self.w)), self.near, self.far)
        return dict(rgb=rgb.astype(np.uint8), depth=np.where(sky, np.inf, z), seg=seg)


# --- radiometry -------------------------------------------------------------------------------------

H_PLANCK, C_LIGHT, K_BOLTZ = 6.62607015e-34, 2.99792458e8, 1.380649e-23
BAND_UM = (8.0, 14.0)
_TT = np.arange(150.0, 1800.0, 0.05)


def planck_band(t_k, band=BAND_UM, n=600):
    """Band radiance (W m^-2 sr^-1) of a blackbody at t_k: Planck's law integrated over the band."""
    lam = np.linspace(band[0], band[1], n) * 1e-6
    t = np.atleast_1d(np.asarray(t_k, float))[:, None]
    spec = 2 * H_PLANCK * C_LIGHT ** 2 / lam ** 5 / np.expm1(H_PLANCK * C_LIGHT / (lam * K_BOLTZ * t))
    return np.trapezoid(spec, lam, axis=1)


_LT = planck_band(_TT)


def band_radiance(t_k):
    return np.interp(t_k, _TT, _LT)


def band_temperature(L):
    return np.interp(L, _LT, _TT)


def T_SKY(elev):
    """Clear-sky LWIR brightness temperature (K) by elevation: air temperature at the horizon,
    50 K colder at the zenith (an assumption in the range of measured clear-sky values)."""
    return G.T_AIR_C + 273.15 - 50.0 * np.clip(np.sin(elev), 0, 1)


ALPHA_PER_M = 4.0e-4    # 8-14 um extinction of humid near-surface air: tau(100 m) = 0.96 (assumption)


@dataclass
class Lepton:
    """FLIR Lepton 3.5 class (FLIR Lepton 3.5 datasheet): 160 x 120, 57 deg HFOV, < 9 Hz (8.7 Hz),
    NETD < 50 mK, low-gain scene range up to 400 deg C (typical 450). PSF: diffraction core of an
    f/1.1 lens at 10 um, sigma = 0.42 lambda N = 4.6 um = 0.39 px at 12 um pitch, rounded up to 0.5 px
    for aberrations (assumption). SS: supersampling per axis of the radiometric render."""
    width: int = 160
    height: int = 120
    hfov_deg: float = 57.0
    rate_hz: float = 8.7
    netd_k: float = 0.050
    t_max_c: float = 400.0
    psf_sigma_px: float = 0.5
    ss: int = 4


class ThermalCamera:
    def __init__(self, client, bodies, mount=FORWARD, spec=Lepton(), seed=0, near=0.05, far=300.0):
        self.c, self.mount, self.s, self.near, self.far = client, mount, spec, near, far
        self.rng = np.random.default_rng(seed)
        self.rate = spec.rate_hz
        self.ember_of = {b: k for b, (cls, k) in bodies.items() if cls == "ember"}
        self.fire_of = {b: k for b, (cls, k) in bodies.items() if cls in ("ember", "ash")}
        self.L_air = band_radiance(G.T_AIR_C + 273.15)
        self.L_max = band_radiance(spec.t_max_c + 273.15)
        self.sigma_L = spec.netd_k * (band_radiance(303.15 + 0.5) - band_radiance(303.15 - 0.5))

    def capture(self, R_wb, p_wb):
        s, ss = self.s, self.s.ss
        W, H = s.width * ss, s.height * ss
        eye, fwd, up, right = camera_pose(R_wb, p_wb, self.mount)
        view, proj = matrices(eye, fwd, up, s.hfov_deg, W, H, self.near, self.far, self.c)
        _, _, rgb, dep, seg = p.getCameraImage(W, H, view, proj, renderer=p.ER_TINY_RENDERER, shadow=0,
                                               lightAmbientCoeff=1.0, lightDiffuseCoeff=0.0, lightSpecularCoeff=0.0,
                                               physicsClientId=self.c)
        rgb = np.reshape(rgb, (H, W, 4))[..., :3]
        seg = np.reshape(seg, (H, W))
        dirs, kz = ray_dirs(W, H, s.hfov_deg, fwd, up, right)
        rng_m = linear_depth(np.reshape(dep, (H, W)), self.near, self.far) * kz
        t_k, emis = G.decode_temperature(rgb)
        sky = seg < 0
        t_k = np.where(sky, T_SKY(np.arcsin(np.clip(dirs[..., 2], -1, 1))), t_k)
        emis = np.where(sky, 1.0, emis)
        tau = np.where(sky, 1.0, np.exp(-ALPHA_PER_M * rng_m))
        L = tau * (emis * band_radiance(t_k) + (1 - emis) * self.L_air) + (1 - tau) * self.L_air
        blk = lambda a: a.reshape(s.height, ss, s.width, ss).mean(axis=(1, 3))
        Lp = gaussian_filter(blk(L), s.psf_sigma_px, mode="nearest")
        Lp = np.clip(Lp + self.rng.normal(0, self.sigma_L, Lp.shape), band_radiance(150.0), self.L_max)
        temp_c = band_temperature(Lp) - 273.15
        fill = {}                                   # firebrand -> (ember fill, any-part fill) per pixel
        for k in set(self.fire_of.values()):
            ids = [b for b, kk in self.fire_of.items() if kk == k]
            m = np.isin(seg, ids)
            if m.any():
                fill[k] = (blk(np.isin(seg, [b for b in ids if b in self.ember_of]).astype(float)), blk(m.astype(float)))
        # per pixel: range and segment of the sample with the highest radiance (for detection)
        Lb = L.reshape(s.height, ss, s.width, ss).transpose(0, 2, 1, 3).reshape(s.height, s.width, -1)
        arg = Lb.argmax(axis=-1)
        pick = lambda a: np.take_along_axis(a.reshape(s.height, ss, s.width, ss).transpose(0, 2, 1, 3).reshape(s.height, s.width, -1),
                                            arg[..., None], -1)[..., 0]
        return dict(temp_c=temp_c.astype(np.float32), fill=fill,
                    range=np.where(pick(sky.astype(float)) > 0, np.inf, pick(rng_m)), seg=pick(seg),
                    eye=eye, fwd=fwd, up=up, right=right)


# --- display -------------------------------------------------------------------------------------------

# an ironbow-like false-color palette, written as a few control points (position, RGB)
PALETTE = [(0.00, (0, 0, 10)), (0.15, (40, 0, 95)), (0.35, (135, 0, 140)), (0.55, (205, 45, 60)),
           (0.72, (240, 120, 10)), (0.88, (255, 205, 40)), (1.00, (255, 255, 225))]


def false_color(x):
    """Map x in [0, 1] (array) to RGB uint8 with PALETTE."""
    pos = np.array([q[0] for q in PALETTE])
    cols = np.array([q[1] for q in PALETTE], float)
    x = np.clip(np.asarray(x, float), 0, 1)
    return np.stack([np.interp(x, pos, cols[:, c]) for c in range(3)], -1).astype(np.uint8)


def fixed_scale(temp_c, lo=20.0, hi=120.0):
    return false_color((temp_c - lo) / (hi - lo))


def agc(temp_c):
    """Automatic gain: histogram equalization of the frame (as the sensor's AGC modes do)."""
    t = temp_c.ravel()
    order = np.sort(t)
    ranks = np.searchsorted(order, t, side="right") / t.size
    return false_color(ranks.reshape(temp_c.shape))


# --- detection --------------------------------------------------------------------------------------------

DETECT_DELTA_K = 40.0     # hot pixel: apparent temperature above the frame median by this much
MATCH_RADIUS_M = 1.5


def detect(frame, spec=Lepton()):
    """Hot-spot detections in one thermal frame: connected hot pixels -> peak temperature, pixel
    count, bearing (azimuth right of the optical axis, elevation up from it, deg), range (m, from
    the depth of the hottest sample) and world position."""
    t = frame["temp_c"]
    hot = t > np.median(t) + DETECT_DELTA_K
    lab, n = label(hot)
    out = []
    tx = math.tan(math.radians(spec.hfov_deg) / 2)
    ty = tx * spec.height / spec.width
    for k in range(1, n + 1):
        m = lab == k
        i, j = np.unravel_index(np.argmax(np.where(m, t, -np.inf)), t.shape)
        x = ((j + 0.5) / spec.width * 2 - 1) * tx
        y = (1 - (i + 0.5) / spec.height * 2) * ty
        d = x * frame["right"] + y * frame["up"] + frame["fwd"]
        d /= np.linalg.norm(d)
        r = float(frame["range"][i, j])
        out.append(dict(peak_c=float(t[i, j]), n_pix=int(m.sum()), az_deg=math.degrees(math.atan(x)),
                        el_deg=math.degrees(math.atan(y)), range=r,
                        pos=(frame["eye"] + r * d) if np.isfinite(r) else None, pixel=(int(i), int(j))))
    return out


def match(dets, firebrands):
    """Index of the true firebrand within MATCH_RADIUS_M of each detection's position, or -1."""
    res = []
    for d in dets:
        if d["pos"] is None:
            res.append(-1); continue
        dist = [np.linalg.norm(d["pos"] - f.center) for f in firebrands]
        k = int(np.argmin(dist))
        res.append(k if dist[k] <= MATCH_RADIUS_M else -1)
    return res


# --- self-test ----------------------------------------------------------------------------------------------


def selftest(seed=7):
    """Texel pass-through of the thermal twin, band-radiance numbers and per-frame rendering cost."""
    g = G.Gorge(seed)
    g.write_assets()
    vis, th = p.connect(p.DIRECT), p.connect(p.DIRECT)
    bv, bt = g.load(vis, "visual"), g.load(th, "thermal")
    pts = g.path_points(1.0)
    R = np.eye(3)                                # level, nose east; turn to north
    Rn = np.array([[0, -1, 0], [1, 0, 0], [0, 0, 1.0]])
    cams = dict(rgb_fwd=RGBCamera(vis, bv, FORWARD, gorge=g), rgb_down=RGBCamera(vis, bv, DOWN, gorge=g),
                thermal=ThermalCamera(th, bt, FORWARD, seed=0))
    for name, cam in cams.items():
        ts = []
        for q in pts[::6]:
            t0 = time.perf_counter(); cam.capture(Rn @ R, q); ts.append(time.perf_counter() - t0)
        print(f"{name}: {np.mean(ts) * 1000:.1f} ms per frame (mean of {len(ts)}, max {np.max(ts) * 1000:.1f})")
    # thermal twin pass-through: every rendered (R, G, B) must be a texel of some texture
    s = Lepton()
    eye, fwd, up, right = camera_pose(Rn, pts[20], FORWARD)
    view, proj = matrices(eye, fwd, up, s.hfov_deg, 640, 480, 0.05, 300, th)
    _, _, rgb, _, seg = p.getCameraImage(640, 480, view, proj, renderer=p.ER_TINY_RENDERER, shadow=0, lightAmbientCoeff=1.0,
                                         lightDiffuseCoeff=0.0, lightSpecularCoeff=0.0, physicsClientId=th)
    rgb = np.reshape(rgb, (480, 640, 4))[..., :3].reshape(-1, 3)[np.reshape(seg, -1) >= 0]
    fires = np.asarray(Image.open(g.asset_dir / f"fires_s{g.seed}_thermal.png"))[..., :3]
    texels = np.concatenate([g.tex_thermal.reshape(-1, 3), g.tex_boulder_thermal.reshape(-1, 3), fires.reshape(-1, 3)])
    key = lambda a: (a[:, 0].astype(np.int64) << 16) | (a[:, 1].astype(np.int64) << 8) | a[:, 2]
    ok = np.isin(key(rgb), key(texels))
    print(f"thermal twin: {ok.mean() * 100:.3f} % of {len(rgb)} surface samples are exact texels")
    for tc in (30.0, 50.0, 150.0, 400.0, 600.0, 900.0):
        t = tc + 273.15
        frac = planck_band(t)[0] / (5.670374419e-8 * t ** 4 / math.pi)
        print(f"  {tc:5.0f} C: band radiance {planck_band(t)[0]:8.2f} W/m2/sr, {frac * 100:5.1f} % of sigma T^4 / pi")
    L30 = planck_band(303.15)[0]
    for tc in (600.0, 900.0):
        r_band = planck_band(tc + 273.15)[0] / L30
        r_t4 = ((tc + 273.15) / 303.15) ** 4
        print(f"  contrast {tc:.0f} C vs 30 C: band {r_band:.1f}x, T^4 {r_t4:.1f}x (T^4 overstates by {r_t4 / r_band:.1f}x)")
        f = (planck_band(303.15 + DETECT_DELTA_K)[0] - L30) / (planck_band(tc + 273.15)[0] - L30)
        print(f"    ember fill fraction that lifts a 30 C pixel by the detection margin {DETECT_DELTA_K:g} K: {f * 100:.2f} %")

if __name__ == "__main__":
    selftest()
