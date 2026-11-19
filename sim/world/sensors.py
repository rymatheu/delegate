"""Onboard imaging for the gorge world: an RGB camera (with depth and segmentation) and an uncooled
LWIR microbolometer camera in the class of a 640 x 512 drone thermal core, both rendered with
PyBullet's TinyRenderer from the vehicle's true pose and a camera mount in the body frame; the
fires' flames, smoke and light are composited per frame in image space (fire.py); hot-spot
detection.

Frames: world ENU, body FLU (PyBullet's). A mount is a position in the body frame and a
depression `pitch_deg` below the body x axis (and an optional yaw): FORWARD looks forward and 30 deg
down from the nose, DOWN straight down (image top = body forward).

RGB. The world's textures carry their lighting (gorge.py bakes sun, cast shadows, sky light and
ambient occlusion), so the scene is rendered ambient-only; then: a depth-aware softening of magnified
texels with world-anchored fine detail (`soften`); sky (gradient by elevation, a glow around the sun,
procedural clouds) where there is no surface; the fires (firelight on the scene, flames, smoke, glare;
fire.py); aerial perspective (haze over the range); automatic exposure; a mild tone curve.

Thermal camera: what is modeled (ThermalSpec holds the numbers).
1. Scene: the thermal twin of the world (gorge.Gorge.load(..., "thermal")) in its own PyBullet
   client, whose textures hold each surface element's temperature (16 bits in R and G) and
   emissivity (B), rendered with lighting reduced to the ambient term at 1 (TinyRenderer then returns
   the texel exactly; checked by `selftest`), at ss x ss samples per pixel. The temperatures come from
   gorge.py: sunlit rock and sand hot, shade near air, leaves near air (transpiration), dry grass in
   between, fire-heated surfaces by a radiative energy balance around each fire, burned ground and
   embers from the fire model. Sky: clear-sky brightness temperature by elevation.
2. Radiometry: band radiance of each sample, Planck's law integrated over 8 to 14 um (tabulated,
   `band_radiance`); emissivity with the reflected sky/surroundings at air temperature; atmosphere
   L = tau [e L(T) + (1 - e) L(T_air)] + (1 - tau) L(T_air), tau = exp(-ALPHA r).
3. Fires (fire.py): flames composited in radiance by their emissivity (soot absorption over the path
   through the flame) and gas temperature; smoke nearly transparent.
4. Optics: pixel average of the samples (sub-pixel fill), a Gaussian core PSF (diffraction of an
   f/1.0 lens at 10 um plus aberrations) and two wide halo terms (scatter in the germanium optics and
   the window: a fraction of the energy spread over tens of pixels; this is what puts a soft glow
   around saturated flames in real images).
5. Detector: microbolometer signal proportional to absorbed band radiance; residual non-uniformity
   after the factory and shutter corrections (fixed per camera from its seed: per-pixel gain spread,
   per-pixel, per-column and per-row offsets), temporal noise of NETD (white, plus a little row noise),
   two gain states as such cores have (high gain: scene up to 150 C, low NETD; low gain: up to 550 C)
   with automatic switching when a fire fills part of the image (with hysteresis), saturation at the
   top of the range, 14-bit quantization.
6. Output: apparent (brightness) temperature for emissivity 1 without atmospheric correction, as a
   radiometric core reports by default.
Display: false color through PALETTE, my own control points (deep blue, indigo, purple, magenta, red,
orange, yellow, near white; no vendor table): `fixed_scale` maps a fixed temperature span, `AGC`
does what core AGCs do: a histogram of the counts with a plateau (no single level gets more than a
share of the output range, so a uniform background does not take it all and a small fire does not
compress the rest to black), tails rejected, blended with a linear map and smoothed over frames.
Not modeled: the microbolometer's thermal time constant (motion smear), shutter (FFC) events and
offset drift between them, lens vignetting and narcissus, detector nonlinearity.
"""
import math
import time
from dataclasses import dataclass

import numpy as np
import pybullet as p
from PIL import Image
from scipy.ndimage import gaussian_filter, label, zoom

import fire as FI
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


def look_at(eye, target, up=(0, 0, 1)):
    """Eye, forward, up, right of a camera at eye looking at target."""
    eye = np.asarray(eye, float)
    fwd = np.asarray(target, float) - eye
    fwd /= np.linalg.norm(fwd)
    right = np.cross(fwd, up)
    right /= np.linalg.norm(right)
    return eye, fwd, np.cross(right, fwd), right


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


_KZ = {}


def range_factor(w, h, hfov_deg):
    """|d| / d.fwd of each pixel (range = z-depth times this); depends on the image geometry only."""
    key = (w, h, round(hfov_deg, 6))
    if key not in _KZ:
        tx = math.tan(math.radians(hfov_deg) / 2)
        ty = tx * h / w
        xs = ((np.arange(w) + 0.5) / w * 2 - 1) * tx
        ys = (1 - (np.arange(h) + 0.5) / h * 2) * ty
        _KZ[key] = np.sqrt(1 + xs[None, :] ** 2 + ys[:, None] ** 2).astype(np.float32)
    return _KZ[key]


def linear_depth(buf, near, far):
    return far * near / (far - (far - near) * np.asarray(buf))


def tiny(client, W, H, view, proj, seg=False):
    """TinyRenderer, ambient light only (the textures carry their lighting or temperature):
    RGB (H x W x 3 uint8), depth buffer, segmentation (or None)."""
    flags = 0 if seg else p.ER_NO_SEGMENTATION_MASK
    _, _, rgb, dep, sg = p.getCameraImage(W, H, view, proj, renderer=p.ER_TINY_RENDERER, shadow=0, flags=flags,
                                          lightAmbientCoeff=1.0, lightDiffuseCoeff=0.0, lightSpecularCoeff=0.0,
                                          physicsClientId=client)
    rgb = np.fromiter(rgb, np.uint8, count=W * H * 4).reshape(H, W, 4)[..., :3]
    dep = np.fromiter(dep, np.float32, count=W * H).reshape(H, W)
    return rgb, dep, (np.asarray(sg).reshape(H, W) if seg else None)


# --- RGB camera -------------------------------------------------------------------------------------

SKY_HORIZON, SKY_ZENITH = np.array([204, 216, 228.0]), np.array([92, 136, 204.0])
HAZE, HAZE_M = np.array([196, 206, 216.0]), 900.0
_CLOUD = FI.NoiseTile(424242, 256)


def sky_rgb(dirs):
    """Sky color by direction: gradient by elevation, glow around the sun, soft cumulus from a noise
    tile projected on a cloud deck."""
    el = np.clip(dirs[..., 2], -0.2, 1)
    s = np.clip(el, 0, 1)[..., None] ** 0.55
    col = (1 - s) * SKY_HORIZON + s * SKY_ZENITH
    cs = np.clip(dirs @ G.SUN, -1, 1)
    col = col + (np.clip(cs, 0, 1) ** 24 * 60)[..., None] * np.array([1.0, 0.95, 0.85])
    up = np.maximum(dirs[..., 2], 0.03)
    u, v = dirs[..., 0] / up * 3.0, dirs[..., 1] / up * 3.0
    c = _CLOUD(u + 50, v) * 0.7 + 0.3 * _CLOUD(u * 2.3 + 11, v * 2.3)
    cov = np.clip((c - 0.35) * 1.4, 0, 1) * np.clip(dirs[..., 2] * 6, 0, 1)
    cloud = np.array([238, 240, 244.0]) * (0.86 + 0.14 * np.clip(c, -1, 1))[..., None]
    return col * (1 - cov[..., None]) + cloud * cov[..., None]


_TONE_X = np.arange(0, 2048) / 4.0                       # input 0 .. 512 in quarter steps
_TONE = (0.03 + 0.97 * np.clip(_TONE_X / 255.0 / (1 + 0.18 * _TONE_X / 255.0) * 1.18, 0, 1) ** 1.04) * 255


def tone(img):
    """A mild tone curve (lifted toe, soft shoulder; a table) per channel, then 8 % more saturation."""
    y = _TONE.astype(np.float32)[np.clip(img * 4, 0, 2047).astype(np.int32)]
    m = y.mean(-1, keepdims=True)
    return np.clip(m + (y - m) * 1.08, 0, 255)


_DETAIL = FI.NoiseTile(31337, 256)
TEXEL_M = 0.028                      # typical texel size of the world's textures (m)


def soften(img, z, eye, fwd, up, right, hfov, fine=True):
    """Hide texture magnification: where a texel covers more than a pixel (TinyRenderer samples the
    nearest texel, so magnified texels show as squares), blend toward a blurred image by the
    magnification, except across depth edges (silhouettes stay sharp); then add a fine detail noise
    anchored in world coordinates (1 to 2 cm), so that close surfaces keep a texture of their own."""
    H, W = z.shape
    tx = math.tan(math.radians(hfov) / 2)
    mag = TEXEL_M * W / (2 * tx * np.where(np.isfinite(z), z, 1e9))
    if mag.max() < 1.3:
        return img
    zz = np.where(np.isfinite(z), z, 1e4).astype(np.float32)
    gz = np.abs(np.gradient(zz, axis=0)) + np.abs(np.gradient(zz, axis=1))
    edge = gaussian_filter((gz / zz > 0.04).astype(np.float32), 1.2)
    w1 = np.clip((mag - 1.2) / 1.5, 0, 1) * np.clip(1 - 3 * edge, 0, 1)
    w2 = 0.65 * np.clip((mag - 3.0) / 3.0, 0, 1) * np.clip(1 - 3 * edge, 0, 1)
    rows = np.nonzero((w1 > 0.01).any(axis=1))[0]
    r0 = max(0, int(rows.min()) - 4) if len(rows) else H
    if r0 >= H:
        return img
    full = img
    img = img[r0:]
    z, zz, mag, edge, w1, w2 = (a[r0:] for a in (z, zz, mag, edge, w1, w2))
    H = H - r0
    b1 = np.stack([gaussian_filter(img[..., c], 0.9) for c in range(3)], -1)
    h2, w2_ = H // 2 * 2, W // 2 * 2
    small = img[:h2, :w2_].reshape(H // 2, 2, W // 2, 2, 3).mean(axis=(1, 3))
    b2 = np.stack([gaussian_filter(small[..., c], 1.1) for c in range(3)], -1)
    b2 = np.repeat(np.repeat(b2, 2, 0), 2, 1)
    b2 = np.pad(b2, ((0, H - h2), (0, W - w2_), (0, 0)), mode="edge")
    out = img * (1 - w1)[..., None] + b1 * w1[..., None]
    out = out * (1 - w2)[..., None] + b2 * w2[..., None]
    sel = w1 > 0.02
    if sel.any():
        ii, jj = np.nonzero(sel)
        ty = tx * full.shape[0] / W
        ii = ii + r0
        k = (((jj + 0.5) / W * 2 - 1) * tx)[:, None] * right + ((1 - (ii + 0.5) / full.shape[0] * 2) * ty)[:, None] * up + fwd
        P = eye + zz[ii - r0, jj][:, None] * k
        u_, v_ = P[:, 0] + P[:, 1], P[:, 2] + 0.5 * (P[:, 1] - P[:, 0])       # varies on floors and on walls of any facing
        dn = 0.6 * _DETAIL(u_ / 0.012, v_ / 0.012) + 0.4 * _DETAIL(v_ / 0.025 + 50, u_ / 0.025)
        dn2 = _DETAIL(u_ / 0.006 + 99, v_ / 0.006 - 31) if fine else 0.0
        out[ii - r0, jj] *= (1 + w1[ii - r0, jj] * (0.07 * dn + 0.06 * w2[ii - r0, jj] / 0.65 * dn2))[:, None]
    res = full.copy()
    res[r0:] = out
    return res.astype(np.float32)


def soften_live(img, z, eye, fwd, up, right, hfov):
    """`soften` for the live cameras, computed at half resolution: the same magnification weight and
    blur toward a smoothed image, with one octave of the world-anchored detail."""
    H, W = z.shape
    h2, w2 = H // 2, W // 2
    tx = math.tan(math.radians(hfov) / 2)
    zs = z[:2 * h2:2, :2 * w2:2]
    mag = TEXEL_M * W / (2 * tx * np.where(np.isfinite(zs), zs, 1e9))
    if mag.max() < 1.3:
        return img
    zz = np.where(np.isfinite(zs), zs, 1e4).astype(np.float32)
    gz = np.abs(np.gradient(zz, axis=0)) + np.abs(np.gradient(zz, axis=1))
    edge = gaussian_filter((gz / zz > 0.06).astype(np.float32), 0.8)
    wgt = np.clip((mag - 1.2) / 1.5, 0, 1) * np.clip(1 - 3 * edge, 0, 1)
    rows = np.nonzero((wgt > 0.01).any(axis=1))[0]
    if not len(rows):
        return img
    r0 = max(0, int(rows.min()) - 2)
    small = img[2 * r0:2 * h2, :2 * w2].reshape(h2 - r0, 2, w2, 2, 3).mean(axis=(1, 3))
    blur = np.stack([gaussian_filter(small[..., c], 0.7) for c in range(3)], -1)
    ii, jj = np.mgrid[r0:h2, 0:w2]
    ty = tx * H / W
    k = (((2 * jj + 1) / W * 2 - 1) * tx)[..., None] * right + ((1 - (2 * ii + 1) / H * 2) * ty)[..., None] * up + fwd
    P = eye + zz[r0:, :, None] * k
    u_, v_ = P[..., 0] + P[..., 1], P[..., 2] + 0.5 * (P[..., 1] - P[..., 0])
    dn = _DETAIL(u_ / 0.012, v_ / 0.012)
    w_ = wgt[r0:]
    target = blur * (1 + 0.07 * w_ * dn)[..., None]
    up2 = lambda a: np.repeat(np.repeat(a, 2, 0), 2, 1)
    out = img.copy()
    sl = (slice(2 * r0, 2 * h2), slice(0, 2 * w2))
    wf = up2(w_)[..., None]
    out[sl] = img[sl] * (1 - wf) + up2(target) * wf
    return out


def render_rgb(client, eye, fwd, up, right, hfov, W, H, near=0.05, far=300.0, t=0.0, fires=None, seg=False, haze=True, exposure=1.0,
               detail=True):
    """A frame of the visual world: TinyRenderer, sky, fires, haze, exposure, tone. exposure: a gain, or
    an AutoExposure. Returns (rgb uint8, z-depth along fwd (inf for sky), segmentation or None)."""
    view, proj = matrices(eye, fwd, up, hfov, W, H, near, far, client)
    rgb, dep, sg = tiny(client, W, H, view, proj, seg)
    img = rgb.astype(np.float32)
    sky = dep >= 0.99999
    z = np.where(sky, np.inf, linear_depth(dep, near, far)).astype(np.float32)
    kz = range_factor(W, H, hfov)
    if detail:
        if fires is not None and fires.live:
            img = soften_live(img, z, eye, fwd, up, right, hfov)
        else:
            img = soften(img, z, eye, fwd, up, right, hfov, fine=fires is None or fires.flame_scale == 1)
    if sky.any():
        ii, jj = np.nonzero(sky)
        tx = math.tan(math.radians(hfov) / 2)
        ty = tx * H / W
        d = (((jj + 0.5) / W * 2 - 1) * tx)[:, None] * right + ((1 - (ii + 0.5) / H * 2) * ty)[:, None] * up + fwd
        img[sky] = sky_rgb(d / np.linalg.norm(d, axis=1, keepdims=True))
    if fires is not None:
        img = fires.render_rgb(img, z, FI.Camera(eye, fwd, up, right, hfov, W, H, near), t)
    if haze:
        rng_m = np.where(sky, 0.0, z * kz)
        T = np.exp(-rng_m / HAZE_M)[..., None]
        img = img * T + HAZE * (1 - T)
    gain = exposure(img) if callable(exposure) else exposure
    if gain != 1.0:
        img = img * np.float32(gain)
    return tone(img).astype(np.uint8), z, sg


class AutoExposure:
    """A camera's automatic exposure: the gain that brings the frame's mean luminance (sky counted at
    a third) to TARGET, within GAIN, approached by DAMP per frame."""
    TARGET, GAIN, DAMP = 118.0, (0.85, 1.7), 0.5

    def __init__(self):
        self.g = None

    def __call__(self, img):
        lum = img[::4, ::4] @ np.array([0.3, 0.55, 0.15], np.float32)
        m = float(np.mean(np.minimum(lum, 255)))
        g = float(np.clip(self.TARGET / max(m, 1.0), *self.GAIN))
        self.g = g if self.g is None else self.g + self.DAMP * (g - self.g)
        return self.g


_CULL_STATE = {}


class Culler:
    """Frustum culling of the live world's chunks (Gorge.load(..., lod=2)): before a frame, every chunk
    whose bounding box lies entirely outside the view (1 m margin) or behind the camera is hidden
    (alpha 0: TinyRenderer then skips it), the others shown."""

    def __init__(self, gorge, client):
        aabb = getattr(gorge, "live_aabb", {}) if gorge is not None else {}
        self.c = client
        self.items = []
        for (cl, bid), (lo, hi) in aabb.items():
            if cl == client:
                C = np.array([[x, y, z] for x in (lo[0], hi[0]) for y in (lo[1], hi[1]) for z in (lo[2], hi[2])])
                self.items.append((bid, C))
        self.state = _CULL_STATE.setdefault(client, {})     # shared by every camera on this client

    def __call__(self, eye, fwd, up, right, hfov, W, H, far):
        if not self.items:
            return
        tx = math.tan(math.radians(hfov) / 2)
        ty = tx * H / W
        for bid, C in self.items:
            r = C - eye
            z, x, y = r @ fwd, r @ right, r @ up
            vis = not ((z < 0.05).all() or (z > far).all() or (x > z * tx + 1).all() or (x < -z * tx - 1).all()
                       or (y > z * ty + 1).all() or (y < -z * ty - 1).all())
            if self.state.get(bid) != vis:
                p.changeVisualShape(bid, -1, rgbaColor=[1, 1, 1, 1.0 if vis else 0.0], physicsClientId=self.c)
                self.state[bid] = vis


class RGBCamera:
    def __init__(self, client, bodies, mount=FORWARD, width=320, height=240, hfov_deg=90.0, rate_hz=10.0,
                 near=0.05, far=200.0, gorge=None, fires=True, seg=False, fire_quality="live", exposure="auto"):
        self.c, self.mount, self.w, self.h, self.hfov, self.rate = client, mount, width, height, hfov_deg, rate_hz
        self.near, self.far, self.seg = near, far, seg
        self.exposure = AutoExposure() if exposure == "auto" else exposure
        self.cull = Culler(gorge, client)
        self.fires = FI.Fires(gorge, fire_quality) if (gorge is not None and fires) else None

    def capture(self, R_wb, p_wb, t=0.0):
        eye, fwd, up, right = camera_pose(R_wb, p_wb, self.mount)
        self.cull(eye, fwd, up, right, self.hfov, self.w, self.h, self.far)
        rgb, z, sg = render_rgb(self.c, eye, fwd, up, right, self.hfov, self.w, self.h, self.near, self.far, t, self.fires, self.seg,
                                exposure=self.exposure)
        return dict(rgb=rgb, depth=z, seg=sg)


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
_LT32 = _LT.astype(np.float32)
_LOGL = np.linspace(np.log(_LT[0]), np.log(_LT[-1]), 1 << 17)            # inverse table on a uniform log L grid
_TINV = np.interp(np.exp(_LOGL), _LT, _TT).astype(np.float32)


def band_radiance(t_k):
    """Band radiance by linear interpolation in the table (uniform 0.05 K grid, direct indexing)."""
    x = (np.asarray(t_k, np.float32) - np.float32(_TT[0])) * np.float32(20.0)
    x = np.clip(x, 0, len(_TT) - 1.001)
    i = x.astype(np.int32)
    f = x - i
    return _LT32[i] + (_LT32[i + 1] - _LT32[i]) * f


def band_temperature(L):
    """Inverse of band_radiance (table on a uniform grid of log radiance)."""
    x = (np.log(np.maximum(np.asarray(L, np.float32), np.float32(_LT[0]))) - np.float32(_LOGL[0])) / np.float32(_LOGL[1] - _LOGL[0])
    x = np.clip(x, 0, len(_LOGL) - 1.001)
    i = x.astype(np.int32)
    f = x - i
    return _TINV[i] + (_TINV[i + 1] - _TINV[i]) * f


def T_SKY(elev):
    """Clear-sky LWIR brightness temperature (K) by elevation: air temperature at the horizon,
    50 K colder at the zenith (an assumption in the range of measured clear-sky values)."""
    return G.T_AIR_C + 273.15 - 50.0 * np.clip(np.sin(elev), 0, 1)


ALPHA_PER_M = 4.0e-4    # 8-14 um extinction of humid near-surface air: tau(100 m) = 0.96 (assumption)


@dataclass
class ThermalSpec:
    """An uncooled VOx microbolometer core of the 640 x 512, 12 um class used on drones, with an
    7.5 mm f/1.0 lens: HFOV 2 atan(3.84 / 7.5) = 54.2 deg, VFOV 44.6 deg; 8.7 Hz output (the
    export-limited rate below 9 Hz). NETD 40 mK in high gain (scene -25 to 150 C), 100 mK in low gain
    (up to 550 C); residual non-uniformity after correction and the halo of the optics are assumptions
    of typical size. ss: samples per pixel and axis of the radiometric render (1 for live video)."""
    width: int = 640
    height: int = 512
    pitch_um: float = 12.0
    focal_mm: float = 7.5
    rate_hz: float = 8.7
    netd_k: float = 0.040
    netd_low_k: float = 0.100
    t_max_c: float = 150.0          # high gain saturation
    t_max_low_c: float = 550.0      # low gain saturation
    t_min_c: float = -40.0
    psf_sigma_px: float = 0.55
    halo: tuple = ((0.025, 5.0), (0.012, 26.0))     # (energy fraction, Gaussian sigma in px)
    fpn_gain: float = 0.004         # rms relative gain residual per pixel
    fpn_pix_k: float = 0.030        # rms offset residual per pixel, per column, per row (K at 30 C): below NETD
    fpn_col_k: float = 0.015
    fpn_row_k: float = 0.010
    row_noise_k: float = 0.012
    adc_bits: int = 14
    ss: int = 1

    @property
    def hfov_deg(self):
        return 2 * math.degrees(math.atan(self.width * self.pitch_um * 1e-3 / 2 / self.focal_mm))


Lepton = ThermalSpec            # the name the scripts used for the earlier 160 x 120 model


class ThermalCamera:
    def __init__(self, client, bodies, mount=FORWARD, spec=None, seed=0, near=0.05, far=300.0, gorge=None, fill=False,
                 fire_quality="live"):
        self.s = spec or ThermalSpec()
        self.c, self.mount, self.near, self.far = client, mount, near, far
        self.rng = np.random.default_rng(seed)
        self.rate = self.s.rate_hz
        self.fire_of = {b: k for b, (cls, k) in bodies.items() if cls in ("ember", "ash")}
        self.ember_of = {b: k for b, (cls, k) in bodies.items() if cls == "ember"}
        self.fires = FI.Fires(gorge, fire_quality) if gorge is not None else None
        self.want_fill = fill
        self.cull = Culler(gorge, client)
        self.L_air = band_radiance(G.T_AIR_C + 273.15)
        s = self.s
        dL = band_radiance(303.15 + 0.5) - band_radiance(303.15 - 0.5)       # radiance per K at 30 C
        self.dL = dL
        frng = np.random.default_rng(10007 + seed)                            # the camera's own non-uniformity
        self.fpn_gain = 1 + s.fpn_gain * frng.normal(size=(s.height, s.width))
        self.fpn_off = dL * (s.fpn_pix_k * frng.normal(size=(s.height, s.width)) + s.fpn_col_k * frng.normal(size=(1, s.width))
                             + s.fpn_row_k * frng.normal(size=(s.height, 1)))
        self.gain_high = True
        self.L_min = band_radiance(s.t_min_c + 273.15)

    def capture(self, R_wb, p_wb, t=0.0):
        s, ss = self.s, self.s.ss
        W, H = s.width * ss, s.height * ss
        eye, fwd, up, right = camera_pose(R_wb, p_wb, self.mount)
        view, proj = matrices(eye, fwd, up, s.hfov_deg, W, H, self.near, self.far, self.c)
        self.cull(eye, fwd, up, right, s.hfov_deg, W, H, self.far)
        rgb, dep, seg = tiny(self.c, W, H, view, proj, seg=self.want_fill)
        kz = range_factor(W, H, s.hfov_deg)
        sky = dep >= 0.99999
        z = np.where(sky, np.inf, linear_depth(dep, self.near, self.far)).astype(np.float32)
        rng_m = np.where(sky, np.inf, z * kz)
        rgbf = rgb.astype(np.float32)
        t_k = np.float32(G.T_ENC_MIN) + (rgbf[..., 0] * 256 + rgbf[..., 1]) * np.float32(G.T_ENC_SPAN / 65535)
        emis = rgbf[..., 2] / 255
        tau = np.exp(-ALPHA_PER_M * np.where(sky, 0, rng_m)).astype(np.float32)
        L = tau * (emis * band_radiance(t_k) + (1 - emis) * self.L_air) + (1 - tau) * self.L_air
        if sky.any():
            ii, jj = np.nonzero(sky)
            tx = math.tan(math.radians(s.hfov_deg) / 2)
            ty = tx * H / W
            d = (((jj + 0.5) / W * 2 - 1) * tx)[:, None] * right + ((1 - (ii + 0.5) / H * 2) * ty)[:, None] * up + fwd
            L[sky] = band_radiance(T_SKY(np.arcsin(np.clip(d[:, 2] / np.linalg.norm(d, axis=1), -1, 1))))
        fire_rho, zf = {}, None
        if self.fires is not None:
            L, zf, fire_rho = self.fires.render_thermal(L, z, FI.Camera(eye, fwd, up, right, s.hfov_deg, W, H, self.near), t,
                                                        band_radiance, G.T_AIR_C + 273.15, per_fire=self.want_fill)
        blk = (lambda a: a.reshape(s.height, ss, s.width, ss).mean(axis=(1, 3))) if ss > 1 else (lambda a: a)
        Lp = blk(L)
        # optics: core PSF and halo (wide terms on a 4x coarser grid)
        core = gaussian_filter(Lp, s.psf_sigma_px, mode="nearest")
        frac = sum(b for b, _ in s.halo)
        small = Lp.reshape(s.height // 4, 4, s.width // 4, 4).mean(axis=(1, 3))
        halo = sum(b * gaussian_filter(small, sg / 4, mode="nearest") for b, sg in s.halo)
        Lo = (1 - frac) * core + zoom(halo, 4, order=1)
        # detector: gain state, non-uniformity, noise, saturation, quantization
        L_hi = band_radiance(s.t_max_c + 273.15)
        hot = float((Lo > 0.9 * L_hi).mean())
        if self.gain_high and hot > 0.002:
            self.gain_high = False
        elif not self.gain_high and float((Lo > band_radiance(s.t_max_c - 20 + 273.15)).mean()) < 0.0005:
            self.gain_high = True
        L_max = L_hi if self.gain_high else band_radiance(s.t_max_low_c + 273.15)
        netd = s.netd_k if self.gain_high else s.netd_low_k
        sig = Lo * self.fpn_gain + self.fpn_off * (1.0 if self.gain_high else 2.0)
        sig = sig + self.dL * (netd * self.rng.normal(size=sig.shape) + s.row_noise_k * self.rng.normal(size=(s.height, 1)))
        sig = np.clip(sig, self.L_min, L_max)
        q = (L_max - self.L_min) / (2 ** s.adc_bits - 1)
        counts = np.round((sig - self.L_min) / q)
        Lq = self.L_min + counts * q
        temp_c = band_temperature(Lq) - 273.15
        out = dict(temp_c=temp_c.astype(np.float32), counts=counts.astype(np.uint16), gain="high" if self.gain_high else "low",
                   eye=eye, fwd=fwd, up=up, right=right, spec=s, t=t)
        # range of each pixel (the flame's where a flame is in front): the nearest sample
        rr = rng_m if zf is None else np.minimum(rng_m, np.where(np.isfinite(zf), zf * kz, np.inf))
        out["range"] = rr.reshape(s.height, ss, s.width, ss).min(axis=(1, 3)) if ss > 1 else rr
        if self.want_fill:
            fill = {}
            for k in set(self.fire_of.values()):
                ids = [b for b, kk in self.fire_of.items() if kk == k]
                part = np.isin(seg, ids).astype(float)
                emb = np.isin(seg, [b for b in ids if b in self.ember_of]).astype(float)
                fl = fire_rho.get(k)
                hot_ = np.maximum(emb, fl) if fl is not None else emb
                anyp = np.maximum(part, fl) if fl is not None else part
                if anyp.any():
                    fill[k] = (blk(hot_), blk(anyp))
            out["fill"] = fill
            out["seg"] = seg[::ss, ::ss] if ss > 1 else seg
        return out


# --- display -------------------------------------------------------------------------------------------

# an ironbow-like false-color palette, written as control points (position, RGB): deep blue, indigo,
# purple, magenta, red, orange, yellow, near white
PALETTE = [(0.00, (8, 6, 40)), (0.06, (28, 10, 96)), (0.16, (70, 12, 138)), (0.30, (122, 18, 150)),
           (0.44, (170, 34, 132)), (0.57, (212, 62, 84)), (0.70, (240, 112, 32)), (0.82, (252, 172, 36)),
           (0.92, (255, 226, 110)), (1.00, (255, 255, 230))]


def false_color(x):
    """Map x in [0, 1] (array) to RGB uint8 with PALETTE."""
    pos = np.array([q[0] for q in PALETTE])
    cols = np.array([q[1] for q in PALETTE], float)
    x = np.clip(np.asarray(x, float), 0, 1)
    return np.stack([np.interp(x, pos, cols[:, c]) for c in range(3)], -1).astype(np.uint8)


def fixed_scale(temp_c, lo=20.0, hi=120.0):
    return false_color((np.asarray(temp_c) - lo) / (hi - lo))


class AGC:
    """Automatic gain of the display, on the signal (band radiance).
    Without a fire in view: histogram equalization with a plateau (each level's count capped at a
    multiple of the mean count), as core AGCs do, blended from a high plateau (PLATEAUS[0]: the
    background keeps most of the range and its structure), a low one (PLATEAUS[1]) and a linear map
    (weights WEIGHTS); tails rejected (TAIL).
    With a fire in view (more than FIRE_FRAC of the pixels above FIRE_C, hotter than any natural
    surface here): two parts. The pixels below FIRE_C are equalized as above into [0, SPLIT[0]] of the
    palette (deep blue to magenta), the hotter ones mapped linearly in log radiance from FIRE_C to the
    frame maximum onto [SPLIT[1], 1] (red, orange, yellow, white): sunlit sand stays purple, only the
    fire and the ground it heats are orange to white. The lookup is smoothed over frames (DAMP)."""
    BINS, PLATEAUS, WEIGHTS, TAIL, DAMP = 1024, (60.0, 3.0), (0.55, 0.2, 0.25), 0.002, 0.35
    FIRE_C, FIRE_FRAC, SPLIT = 72.0, 0.0002, (0.45, 0.52)

    def __init__(self):
        self.lut = None

    def _equalize(self, L, lo, top):
        edges = np.linspace(lo, top, self.BINS + 1)
        h0, _ = np.histogram(np.clip(L, lo, top), edges)
        lut = self.WEIGHTS[-1] * np.clip((edges - lo) / max(top - lo, 1e-9), 0, 1)
        for pl, wgt in zip(self.PLATEAUS, self.WEIGHTS):
            h = np.minimum(h0, pl * L.size / self.BINS).astype(float)
            cdf = np.concatenate([[0.0], np.cumsum(h)])
            lut = lut + wgt * cdf / max(cdf[-1], 1e-9)
        return edges, lut

    def __call__(self, temp_c):
        L = band_radiance(np.asarray(temp_c, float) + 273.15)
        lo = float(np.quantile(L, self.TAIL))
        top = float(L.max())
        Lf = float(band_radiance(self.FIRE_C + 273.15))
        fire = float((L > Lf).mean()) > self.FIRE_FRAC
        if fire:
            bg = L[L <= Lf]
            hi = max(float(np.quantile(bg, 1 - self.TAIL)), lo + 1.0)
            e1, l1 = self._equalize(bg, lo, hi)
            e2 = np.exp(np.linspace(np.log(Lf), np.log(max(top, Lf * 1.01)), 64))
            l2 = self.SPLIT[1] + (1 - self.SPLIT[1]) * (np.log(e2) - np.log(Lf)) / max(np.log(e2[-1]) - np.log(Lf), 1e-9)
            edges = np.concatenate([e1, [Lf * 0.9999], e2])
            lut = np.concatenate([l1 * self.SPLIT[0], [self.SPLIT[0]], l2])
        else:
            hi = max(float(np.quantile(L, 1 - self.TAIL)), lo + band_radiance(303.15 + 3) - band_radiance(303.15))
            edges, lut = self._equalize(L, lo, max(top, hi))
        if self.lut is not None:
            e0, l0 = self.lut
            grid = np.union1d(e0, edges)
            lut = (1 - self.DAMP) * np.interp(grid, e0, l0) + self.DAMP * np.interp(grid, edges, lut)
            edges = grid
            if len(edges) > 4096:
                sel = np.linspace(0, len(edges) - 1, 4096).astype(int)
                edges, lut = edges[sel], lut[sel]
        self.lut = (edges, lut)
        return false_color(np.interp(L, edges, lut))


def agc(temp_c):
    """One-frame automatic gain (no smoothing over frames)."""
    return AGC()(temp_c)


def colorbar(h, w=18):
    """A vertical PALETTE bar (hot at the top), h x w x 3."""
    return false_color(np.linspace(1, 0, h)[:, None].repeat(w, 1))


# --- detection --------------------------------------------------------------------------------------------

DETECT_DELTA_K = 40.0     # hot pixel: apparent temperature above the frame median by this much
MATCH_RADIUS_M = 2.0      # beyond the burned patch: the ground the fire heats belongs to its thermal footprint


def detect(frame, spec=None):
    """Hot-spot detections in one thermal frame: connected hot pixels -> peak temperature, pixel
    count, bearing (azimuth right of the optical axis, elevation up from it, deg), range (m, of the
    hottest pixel's nearest sample) and world position."""
    spec = spec or frame.get("spec") or ThermalSpec()
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
    """Index of the true fire within MATCH_RADIUS_M of each detection's position, or -1. The distance
    is to the fire's extent: horizontally beyond its burned patch, vertically beyond 1.5 m of flame.
    (With 1.5 m the main flight had 127 unmatched detections, all 1.5 to 3.1 m beyond a burned patch:
    ground heated by the fire, split off from the fire's own blob.)"""
    res = []
    for d in dets:
        if d["pos"] is None:
            res.append(-1); continue
        dist = []
        for f in firebrands:
            dxy = max(0.0, float(np.linalg.norm(d["pos"][:2] - f.center[:2])) - f.radius)
            dz = d["pos"][2] - f.center[2]
            dz = max(0.0, -dz, dz - 1.5)
            dist.append(math.hypot(dxy, dz))
        k = int(np.argmin(dist))
        res.append(k if dist[k] <= MATCH_RADIUS_M else -1)
    return res


# --- self-test ----------------------------------------------------------------------------------------------


def selftest(seed=7):
    """Texel pass-through of the thermal twin, band-radiance numbers and per-frame rendering cost."""
    g = G.Gorge(seed)
    vis, th = p.connect(p.DIRECT), p.connect(p.DIRECT)
    bv, bt = g.load(vis, "visual"), g.load(th, "thermal")
    pts = g.path_points(1.0)
    Rn = np.array([[0, -1, 0], [1, 0, 0], [0, 0, 1.0]])           # level, nose north
    cams = dict(rgb_fwd_640x480=RGBCamera(vis, bv, FORWARD, 640, 480, gorge=g), rgb_down_320x240=RGBCamera(vis, bv, DOWN, gorge=g),
                thermal_640x512=ThermalCamera(th, bt, FORWARD, seed=0, gorge=g))
    for name, cam in cams.items():
        ts = []
        for i, q in enumerate(pts[::6]):
            t0 = time.perf_counter(); cam.capture(Rn, q, 0.1 * i); ts.append(time.perf_counter() - t0)
        print(f"{name}: {np.mean(ts[1:]) * 1000:.1f} ms per frame (mean of {len(ts) - 1}, max {np.max(ts[1:]) * 1000:.1f})")
    # thermal twin pass-through: every rendered (R, G, B) must be a texel of some texture
    s = ThermalSpec()
    eye, fwd, up, right = camera_pose(Rn, pts[20], FORWARD)
    view, proj = matrices(eye, fwd, up, s.hfov_deg, 640, 480, 0.05, 300, th)
    rgb, dep, seg = tiny(th, 640, 480, view, proj, seg=True)
    rgb = rgb.reshape(-1, 3)[np.reshape(seg, -1) >= 0]
    tex = [np.asarray(Image.open(g.asset_dir / f"{n}_s{g.seed}_thermal.png"))[..., :3].reshape(-1, 3) for n in ("terrain", "objects", "fires")]
    key = lambda a: (a[:, 0].astype(np.int64) << 16) | (a[:, 1].astype(np.int64) << 8) | a[:, 2]
    ok = np.isin(key(rgb), key(np.concatenate(tex)))
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
    for chord in (0.05, 0.15, 0.3):
        e = 1 - math.exp(-FI.KAPPA * chord)
        for tg in (900.0, 1250.0):
            Lf = (1 - e) * L30 + e * planck_band(tg)[0]
            print(f"  flame chord {chord:.2f} m (emissivity {e:.2f}), gas {tg:.0f} K over a 30 C scene: apparent "
                  f"{band_temperature(Lf) - 273.15:.0f} C")
    hf = ThermalSpec()
    print(f"  {hf.width} x {hf.height}, HFOV {hf.hfov_deg:.1f} deg, IFOV {hf.pitch_um / hf.focal_mm:.2f} mrad: "
          f"a pixel is {hf.pitch_um / hf.focal_mm * 10:.1f} mm at 10 m")


if __name__ == "__main__":
    selftest()
