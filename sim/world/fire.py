"""Flames, smoke and firelight of the gorge's surface fires, drawn per frame in image space with the
depth buffer (PyBullet's TinyRenderer has no transparency), for the RGB and the thermal camera.

Everything is deterministic in the gorge seed and the simulation time t (seconds).

Flames. Each fire (gorge.Firebrand) has flame tongues every 4 to 7 cm along the flaming part of its
front (and on a burning shrub, log or tree base): base point, base width w (0.18 to 0.4 m, so that
neighbors overlap and merge into one sheet), height h (lognormal: a few licks two to three times the
median), phase, frequency f, lean and the arc coordinate s along the front (gorge.py). A tongue is drawn
on a billboard through its base, along its axis (vertical, leaning downwind) and turned toward the
camera. Its height varies with a noise in (s, t) that travels along the front (neighbors rise and
fall together) and flickers (puffing frequencies of small litter fires, 1.5 to 3 Hz). In billboard
coordinates (s across in units of w, v up in units of the current height) its half-width is
0.5 (1 - v)^0.6 (1 + 0.4 v), wide at the base; three octaves of a noise tile scrolled upward bend its
sides and tear its top (tips detach). Each pixel gets a density rho, a heat index (high in the lower
core, falling toward the edges and the tips) and the flame's depth; the depth test is soft over 8 cm.
- RGB: color by heat index through control points from dark red to orange to a capped yellow
  (255, 215, 120); composited over the scene with opacity 0.85 rho (translucent edges), so the flame
  is orange-dominant; sooty dark-red tips darken what is behind them; glare around the brightest parts.
- thermal: gas temperature 700 K + 550 K x heat, modulated by filaments (streaks scrolling upward);
  emissivity 1 - exp(-KAPPA chord) with the chord through a round tongue (KAPPA = 1.2 per m, an
  assumption in the range reported for vegetation flames, 0.5 to 3 per m), the chord modulated by the
  same filaments; composited in band radiance: L = (1 - e) L_scene + e B(T).
Smoke. Per fire SMOKE_N puffs, each living SMOKE_LIFE s and reborn with new random offsets (hash of
fire, slot and generation): a buoyant rise (1.2 m/s decaying in 1.2 s, then 0.12 m/s) bent over by
the up-gorge wind (drift 0.6 to 1.0 m/s), growing, stretched along the wind and flattened with age into
a thin haze drifting along the gorge. Each puff is a soft ellipsoid with noise (opacity at most
0.12), transparent while young (no dark smudge at the base), faded near the camera, depth-tested softly
against the scene, shaded by the sun (bright on the sun side, blue-grey in its own shadow), drawn at
reduced resolution. Thermal: smoke is nearly transparent in 8 to 14 um (emissivity 0.02 x opacity)
and only slightly above the air temperature: 5 K x (height above the flames / 0.1 m)^(-5/3), under
0.1 K a meter up (a plume's centerline excess temperature falls as height^(-5/3)).
Firelight (RGB). Each fire is a point light of its radiated power, flickering, at 0.35 m above its
center; scene pixels within 4 m get irradiance / d^2 times max(0, n . l) (normal from the depth
buffer) as a warm tint proportional to their own color, plus a little additive glow.
Quality: "still" draws the flames at full and the smoke at half resolution, "live" (the onboard
cameras) the flames at half and the smoke at a quarter (puffs fainter than 1.2 % and fires farther
than 45 m left out).
"""
import math

import numpy as np
from scipy.ndimage import gaussian_filter, zoom

KAPPA = 1.2                    # 1/m, flame absorption coefficient in 8 to 14 um (assumption)
SMOKE_N, SMOKE_LIFE = 20, 14.0
PUFF_ALPHA = 0.12              # opacity cap of a smoke puff
SUN_DIR = None                 # set from gorge.SUN by Fires
FLAME_RAMP = [(0.00, (100, 18, 4)), (0.22, (190, 46, 8)), (0.48, (240, 104, 18)), (0.74, (254, 164, 50)),
              (1.00, (255, 215, 120))]


def _ramp(x, pts):
    pos = np.array([q[0] for q in pts])
    col = np.array([q[1] for q in pts], np.float32)
    x = np.clip(x, 0, 1)
    return np.stack([np.interp(x, pos, col[:, c]) for c in range(3)], -1).astype(np.float32)


class NoiseTile:
    """A periodic fBm tile (3 octaves of Gaussian-filtered white noise, unit variance), sampled
    bilinearly with wrap-around at (u, v) in tile cells."""

    def __init__(self, seed, n=256):
        rng = np.random.default_rng(seed)
        a = sum(gaussian_filter(rng.normal(size=(n, n)), s, mode="wrap") * w for s, w in ((6.0, 1.0), (3.0, 0.5), (1.5, 0.25)))
        self.a, self.n = (a / a.std()).astype(np.float32), n
        self.flat = np.pad(self.a, ((0, 1), (0, 1)), mode="wrap").ravel()     # (n + 1)^2, wrap built in

    def __call__(self, u, v):
        u = np.asarray(u, np.float32); v = np.asarray(v, np.float32)
        x0, y0 = np.floor(u), np.floor(v)
        fx, fy = u - x0, v - y0
        i0 = x0.astype(np.int32) & (self.n - 1)
        j0 = y0.astype(np.int32) & (self.n - 1)
        idx = j0 * (self.n + 1) + i0
        f = self.flat
        a00, a01 = f.take(idx), f.take(idx + 1)
        a10, a11 = f.take(idx + self.n + 1), f.take(idx + self.n + 2)
        return (a00 + (a01 - a00) * fx) * (1 - fy) + (a10 + (a11 - a10) * fx) * fy


def flicker(t, phase):
    """Smooth noise in time, about [-1, 1]: three incommensurate sines."""
    return (0.5 * np.sin(2 * np.pi * t + phase) + 0.3 * np.sin(2 * np.pi * 2.31 * t + 1.7 * phase + 1.1)
            + 0.2 * np.sin(2 * np.pi * 4.07 * t + 0.6 * phase + 2.3))


def _hash(a, b, c):
    h = (np.int64(a) * 374761393 + np.int64(b) * 668265263 + np.int64(c) * 1442695041) & 0xFFFFFFFF
    h = ((h ^ (h >> 13)) * 1274126177) & 0xFFFFFFFF
    return float((h ^ (h >> 16)) & 0xFFFFFF) / 0x1000000


class Camera:
    """What the fire layer needs of a pinhole camera: eye, unit forward/up/right, tan of the half
    fields of view and the image size; the scene's z-depth buffer is along `fwd`."""

    def __init__(self, eye, fwd, up, right, hfov_deg, W, H, near=0.05):
        self.eye, self.fwd, self.up, self.right = (np.asarray(a, np.float64) for a in (eye, fwd, up, right))
        self.tx = math.tan(math.radians(hfov_deg) / 2)
        self.ty = self.tx * H / W
        self.W, self.H, self.near = W, H, near

    def project(self, X):
        """Pixel coordinates (x right, y down; pixel centers at integers) and z-depth of points X (N x 3)."""
        r = np.atleast_2d(X) - self.eye
        z = r @ self.fwd
        zs = np.where(z > 1e-6, z, 1e-6)
        xn = (r @ self.right) / (zs * self.tx)
        yn = (r @ self.up) / (zs * self.ty)
        return (xn + 1) / 2 * self.W - 0.5, (1 - yn) / 2 * self.H - 0.5, z

    def rays(self, x0, x1, y0, y1, step=1):
        """Ray directions k (k . fwd = 1) of the pixel block [y0:y1, x0:x1] (every `step` pixels)."""
        xs = ((np.arange(x0, x1, step) + 0.5 * step) / self.W * 2 - 1) * self.tx
        ys = (1 - (np.arange(y0, y1, step) + 0.5 * step) / self.H * 2) * self.ty
        return xs[None, :, None] * self.right + ys[:, None, None] * self.up + self.fwd


def _up2(a):
    """Bilinear 2x upsampling (pixel centers), separable, edges clamped."""
    def ax(a, k):
        a = np.moveaxis(a, k, 0)
        nxt = np.concatenate([a[1:], a[-1:]])
        prv = np.concatenate([a[:1], a[:-1]])
        out = np.empty((2 * a.shape[0],) + a.shape[1:], a.dtype)
        out[0::2] = 0.75 * a + 0.25 * prv
        out[1::2] = 0.75 * a + 0.25 * nxt
        return np.moveaxis(out, 0, k)
    return ax(ax(a, 0), 1)


class Upsampler:
    """Bilinear upsampling by an integer factor of only the block of a low-resolution image where
    `mask` is set (one pixel of margin); elsewhere the fill value."""

    def __init__(self, mask, sc, H, W):
        self.sc, self.H, self.W = sc, H, W
        ys, xs = np.nonzero(mask)
        if len(ys):
            h, w = mask.shape
            self.b = (max(0, ys.min() - 1), min(h, ys.max() + 2), max(0, xs.min() - 1), min(w, xs.max() + 2))
        else:
            self.b = None

    def __call__(self, a, fill=0.0, order=1):
        out = np.full((self.H, self.W), fill, np.float32)
        if self.b is None:
            return out
        y0, y1, x0, x1 = self.b
        a = a[y0:y1, x0:x1].astype(np.float32)
        if order == 0:
            blk = np.repeat(np.repeat(a, self.sc, 0), self.sc, 1)
        else:
            blk = a
            for _ in range({2: 1, 4: 2}.get(self.sc, 0)):
                blk = _up2(blk)
            if self.sc not in (2, 4):
                blk = zoom(a, self.sc, order=1, grid_mode=False)
        Y0, X0 = y0 * self.sc, x0 * self.sc
        hh, ww = min(blk.shape[0], self.H - Y0), min(blk.shape[1], self.W - X0)
        out[Y0:Y0 + hh, X0:X0 + ww] = blk[:hh, :ww]
        return out


class Fires:
    def __init__(self, gorge, quality="still"):
        """quality "still": flames at full and smoke at half resolution; "live": flames at half and
        smoke at a third (the live camera workers)."""
        self.g = gorge
        self.flame_scale, self.smoke_scale, self.octaves = (1, 2, 3) if quality == "still" else (2, 4, 2)
        self.smoke_reach = 80.0 if quality == "still" else 45.0
        self.live = quality != "still"
        self.step = 1
        self.fires = gorge.firebrands
        self.noise = NoiseTile(gorge.seed * 7919 + 13)
        self.wdir = [gorge.axis_dir(f.center[1]) for f in self.fires]
        import gorge as G
        self.sun = np.asarray(G.SUN, float)

    # --- culling ------------------------------------------------------------------------------------
    def near(self, cam, reach=60.0):
        """Fires within `reach` m and not entirely behind the camera."""
        out = []
        for k, f in enumerate(self.fires):
            r = f.center - cam.eye
            if np.linalg.norm(r) < reach and (r @ cam.fwd > -6.0):
                out.append(k)
        return out

    def _box(self, cam, lo, hi):
        """Pixel bounding box (x0, x1, y0, y1) and nearest z-depth of the world box lo..hi, or None
        when it is outside the image or behind the camera."""
        c = np.array([[x, y, z] for x in (lo[0], hi[0]) for y in (lo[1], hi[1]) for z in (lo[2], hi[2])])
        px, py, pz = cam.project(c)
        if (pz < cam.near).all():
            return None
        if (pz < cam.near).any():
            return 0, cam.W, 0, cam.H, max(float(pz.min()), cam.near)
        x0, x1 = int(max(0, np.floor(px.min()) - 2)), int(min(cam.W, np.ceil(px.max()) + 3))
        y0, y1 = int(max(0, np.floor(py.min()) - 2)), int(min(cam.H, np.ceil(py.max()) + 3))
        if x1 <= x0 or y1 <= y0:
            return None
        return x0, x1, y0, y1, float(pz.min())

    def in_view(self, cam, zbuf, reach=60.0):
        """Fires whose flames can be in the image: the box around the patch and its flames projects
        into the image and is not entirely behind nearer surfaces (z-buffer)."""
        out = []
        for k in self.near(cam, reach):
            f = self.fires[k]
            ext = float(f.rim.max()) + 0.5
            hz = float(f.tongues[:, 2].max() - f.center[2] + f.tongues[:, 4].max() * 1.4)
            b = self._box(cam, f.center - [ext, ext, 0.2], f.center + [ext, ext, hz + 0.1])
            if b is None:
                continue
            x0, x1, y0, y1, zmin = b
            if np.nanmax(np.where(np.isfinite(zbuf[y0:y1, x0:x1]), zbuf[y0:y1, x0:x1], 1e9)) < zmin - 0.2:
                continue                                  # everything in its box is in front of the fire
            if not self._samples_visible(cam, zbuf, f, hz):
                continue
            out.append(k)
        return out

    def _samples_visible(self, cam, zbuf, f, hz):
        """Whether any of the fire's sample points (the tongues' bases and tops, the patch center) is in
        front of the scene at its pixel (3 x 3 pixel neighborhood, 0.3 m margin)."""
        T = f.tongues[::4]
        P = np.vstack([T[:, :3] + [0, 0, 0.05], T[:, :3] + np.column_stack([np.zeros((len(T), 2)), T[:, 4] * 0.8]),
                       T[:, :3] + np.column_stack([np.zeros((len(T), 2)), T[:, 4] * 1.6]), [f.center + [0, 0, 0.1]]])
        px, py, pz = cam.project(P)
        ok = (pz > cam.near) & (px >= -1) & (px <= cam.W) & (py >= -1) & (py <= cam.H)
        if not ok.any():
            return False
        H, W = zbuf.shape
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                xi = np.clip(np.round(px[ok]).astype(int) + dx, 0, W - 1)
                yi = np.clip(np.round(py[ok]).astype(int) + dy, 0, H - 1)
                if (zbuf[yi, xi] >= pz[ok] - 0.3).any():
                    return True
        return False

    # --- flames ---------------------------------------------------------------------------------------
    def _tongues(self, cam, zbuf, T, t, wd, perp, k):
        """All tongues T (n x 9) of a fire, each rasterized in its own pixel box; the boxes are padded
        to a common size and done in one batch. Returns a list of (box, rho, heat, chord, z-depth, tip)."""
        n = len(T)
        bx, by, bz, w, h, ph, fq, lean, sa = (T[:, i] for i in range(9))
        tt = t * fq + ph
        travel = self.noise(sa * 2.2 + 17.0 * k, np.full(n, t * 0.9, np.float32))      # along the front, in time
        ht = h * (0.82 + 0.18 * flicker(tt * 0.6, ph)) * np.exp(0.28 * np.clip(travel, -1.5, 1.5))
        U = np.zeros((n, 3)); U[:, 2] = 1.0
        U = U + wd * lean[:, None] + perp * (0.12 * flicker(tt * 0.45, ph + 3.0))[:, None]
        U /= np.linalg.norm(U, axis=1, keepdims=True)
        B = np.stack([bx, by, bz], -1)
        V = B + U * (ht * 0.5)[:, None] - cam.eye
        Rb = np.cross(U, V)
        Rb /= np.maximum(np.linalg.norm(Rb, axis=1, keepdims=True), 1e-9)
        Nb = np.cross(Rb, U)
        cs = np.stack([B + s * Rb * (w * 1.5)[:, None] + u * U * (ht * 1.45)[:, None] for s in (-1, 1) for u in (-0.12, 1.0)], 1)
        px, py, pz = cam.project(cs.reshape(-1, 3))
        px, py, pz = px.reshape(n, 4), py.reshape(n, 4), pz.reshape(n, 4)
        ok = (pz > cam.near).all(1)
        x0 = np.clip(np.floor(px.min(1)) - 1, 0, cam.W).astype(int)
        x1 = np.clip(np.ceil(px.max(1)) + 2, 0, cam.W).astype(int)
        y0 = np.clip(np.floor(py.min(1)) - 1, 0, cam.H).astype(int)
        y1 = np.clip(np.ceil(py.max(1)) + 2, 0, cam.H).astype(int)
        ok &= (x1 > x0) & (y1 > y0)
        if not ok.any():
            return []
        sel = np.nonzero(ok)[0]
        bw, bh = int((x1 - x0)[sel].max()), int((y1 - y0)[sel].max())
        X = x0[sel, None] + np.arange(bw)[None]
        Y = y0[sel, None] + np.arange(bh)[None]
        kx = ((X + 0.5) / cam.W * 2 - 1) * cam.tx
        ky = (1 - (Y + 0.5) / cam.H * 2) * cam.ty

        def dot(A):
            a = A[sel]
            return (kx[:, None, :] * (a @ cam.right)[:, None, None] + ky[:, :, None] * (a @ cam.up)[:, None, None]
                    + (a @ cam.fwd)[:, None, None]).astype(np.float32)
        kN, kR, kU = dot(Nb), dot(Rb), dot(U)
        D = B[sel] - cam.eye
        lam = ((D * Nb[sel]).sum(1)[:, None, None] / np.where(np.abs(kN) > 1e-9, kN, 1e-9)).astype(np.float32)
        wq, hq = w[sel][:, None, None], ht[sel][:, None, None]
        s = (lam * kR - (D * Rb[sel]).sum(1)[:, None, None]) / wq
        v = (lam * kU - (D * U[sel]).sum(1)[:, None, None]) / hq
        p_, t_ = ph[sel][:, None, None], tt[sel][:, None, None]
        n1 = self.noise(s * 1.3 + p_ * 7.0, v * 2.0 - t_ * 1.6)
        n2 = self.noise(s * 2.9 + p_ * 3.0 + 40.0, v * 4.2 - t_ * 3.1)
        n3 = self.noise(s * 6.1 + p_ * 5.0 + 90.0, v * 8.5 - t_ * 5.3) if self.octaves > 2 else 0.0
        sd = s + 0.75 * v * n1 + 0.16 * n2 + 0.06 * n3
        vd = v + 0.18 * n2 * v + 0.06 * n3
        hw = 0.5 * np.clip(1 - vd, 0, 1) ** 0.38 * (1 + 0.3 * vd) * np.clip((vd + 0.15) / 0.15, 0, 1)
        r = np.clip((hw - np.abs(sd)) / (0.35 * hw + 0.04), 0, 1)
        r *= np.clip(1.25 - 1.1 * vd + 0.95 * n1 * vd + 0.55 * n2 + 0.25 * n3, 0, 1)
        Yc, Xc = np.minimum(Y, cam.H - 1), np.minimum(X, cam.W - 1)
        zb = zbuf[Yc[:, :, None], Xc[:, None, :]]
        inside = (Y < cam.H)[:, :, None] & (X < cam.W)[:, None, :]
        r *= np.clip((zb - lam) / 0.08 + 0.5, 0, 1) * (lam > cam.near) * inside
        core = np.clip(1.3 - 1.05 * vd - 0.8 * np.abs(sd) / np.maximum(hw, 0.05) + 0.1 * n3, 0, 1)
        hh = r * core
        fil = 0.55 + 0.45 * np.clip(self.noise(s * 5.0 + p_ * 11.0, v * 1.4 - t_ * 2.6), -1, 1)
        c = 2 * wq * np.sqrt(np.clip(hw * hw - sd * sd, 0, None)) * r * fil
        tip = r * np.clip(1 - core * 1.6, 0, 1) * np.clip((vd - 0.45) / 0.3, 0, 1)
        out = []
        for i, j in enumerate(sel):
            hb_, wb_ = y1[j] - y0[j], x1[j] - x0[j]
            ri = r[i, :hb_, :wb_]
            if ri.any():
                out.append(((y0[j], y1[j], x0[j], x1[j]), ri, hh[i, :hb_, :wb_], c[i, :hb_, :wb_], lam[i, :hb_, :wb_], tip[i, :hb_, :wb_]))
        return out

    def flames(self, cam, zbuf, t, per_fire=False, ks=None):
        """rho, heat, chord (m), flame z-depth and soot-tip weight per pixel; with per_fire, also each
        fire's rho; computed at 1/flame_scale resolution and resized."""
        sc = self.flame_scale
        if ks is None:
            ks = self.in_view(cam, zbuf)
        if sc == 1 or not ks:
            return self._flames(cam, zbuf, t, per_fire, ks)
        W, H = cam.W // sc, cam.H // sc
        zs = zbuf[:H * sc, :W * sc].reshape(H, sc, W, sc).min(axis=(1, 3))
        c2 = Camera(cam.eye, cam.fwd, cam.up, cam.right, math.degrees(2 * math.atan(cam.tx)), W, H, cam.near)
        rho, heat, chord, zf, tip, fr = self._flames(c2, zs, t, per_fire, ks)
        up = Upsampler(rho > 0, sc, cam.H, cam.W)
        zfu = up(np.where(np.isfinite(zf), zf, 1e6), 1e6, order=0)           # depths are not blended
        zfu[zfu > 1e5] = np.inf
        return up(rho), up(heat), up(chord), zfu.astype(np.float32), up(tip), {k: up(v) for k, v in fr.items()}

    def _flames(self, cam, zbuf, t, per_fire, ks):
        H, W = cam.H, cam.W
        rho_t = np.zeros((H, W), np.float32)
        heat = np.zeros((H, W), np.float32)
        chord = np.zeros((H, W), np.float32)
        tip = np.zeros((H, W), np.float32)
        zf = np.full((H, W), np.inf, np.float32)
        fire_rho = {}
        for k in ks:
            f = self.fires[k]
            wd = self.wdir[k]
            perp = np.array([-wd[1], wd[0], 0.0])
            fr = np.zeros((H, W), np.float32) if per_fire else None
            T = f.tongues
            if self.live and np.linalg.norm(f.center - cam.eye) > 12.0:
                T = T[::2].copy()
                T[:, 3] *= 1.5
            for (y0, y1, x0, x1), r, hh, c, lam, tp in self._tongues(cam, zbuf, T, t, wd, perp, k):
                blk = (slice(y0, y1), slice(x0, x1))
                rho_t[blk] = 1 - (1 - rho_t[blk]) * (1 - 0.85 * r)
                heat[blk] = np.maximum(heat[blk], hh)
                chord[blk] += c
                tip[blk] = np.maximum(tip[blk], tp)
                zf[blk] = np.where(r > 0.05, np.minimum(zf[blk], lam), zf[blk])
                if fr is not None:
                    fr[blk] = np.maximum(fr[blk], r)
            if fr is not None:
                fire_rho[k] = fr
        return rho_t, heat, chord, zf, tip, fire_rho

    # --- smoke ----------------------------------------------------------------------------------------
    def puffs(self, k, t):
        """Center, radii (along the wind, across, up), opacity, age fraction, noise seed and height above
        the flames of fire k's smoke puffs at time t."""
        f = self.fires[k]
        wd = self.wdir[k]
        perp = np.array([-wd[1], wd[0], 0.0])
        src = f.center + [0, 0, 0.25 + (0.6 if f.kind in ("shrub", "tree") else 0.0)]
        out = []
        for i in range(SMOKE_N):
            u = t + i * SMOKE_LIFE / SMOKE_N + 3.7 * k
            gen = int(math.floor(u / SMOKE_LIFE))
            age = u - gen * SMOKE_LIFE
            h1, h2, h3 = (_hash(k + 1, i, gen * 3 + q) for q in range(3))
            rise = 1.2 * 1.2 * (1 - math.exp(-age / 1.2)) + 0.12 * age
            drift = (0.6 + 0.4 * min(1.0, age / 4)) * age * (0.8 + 0.4 * h1)
            P = src + wd * drift + perp * ((h2 - 0.5) * 0.3 * age) + np.array([0, 0, rise * (0.8 + 0.4 * h3)])
            af = age / SMOKE_LIFE
            r = f.radius * 0.45 + 0.3 * age ** 0.8 * (0.8 + 0.4 * h3)
            radii = (r * (1 + 1.2 * af), r, r * max(0.35, 1 - 0.75 * af))
            a = PUFF_ALPHA * min(1.0, 0.75 * f.smoke) * (1 - af) ** 1.1 * float(np.clip((age - 0.15) / 0.6, 0, 1))
            out.append((P, radii, a, af, h1, rise))
        return out

    def smoke(self, cam, zbuf, t, scale=2):
        """Smoke opacity, darkness (0 light .. 1 dark), warmth (0..1, flame-lit), sun shading (0..1) and
        excess temperature (K) per pixel, drawn at 1/scale resolution and resized."""
        W, H = cam.W // scale, cam.H // scale
        zs = zbuf[:H * scale, :W * scale].reshape(H, scale, W, scale).min(axis=(1, 3))
        sc = Camera(cam.eye, cam.fwd, cam.up, cam.right, math.degrees(2 * math.atan(cam.tx)), W, H, cam.near)
        acc = np.ones((H, W), np.float32)
        maps = {key: np.zeros((H, W), np.float32) for key in ("dark", "warm", "lit", "hot", "w")}
        any_ = False
        for k in self.near(cam, self.smoke_reach):
            f = self.fires[k]
            wd = self.wdir[k]
            perp = np.array([-wd[1], wd[0], 0.0])
            lo = np.minimum(f.center, f.center + wd * 12) - [3.5, 3.5, 0.0]
            hi = np.maximum(f.center, f.center + wd * 12) + [3.5, 3.5, 5.0]
            if self._box(cam, lo, hi) is None:
                continue
            E = np.stack([wd, perp, np.array([0, 0, 1.0])])
            puffs = self.puffs(k, t)
            if self.live:
                puffs = [(P, tuple(1.15 * np.array(r_)), min(1.6 * a, 0.18), af, h1, rise) for P, r_, a, af, h1, rise in puffs[::2]]
            for P, radii, a, af, h1, rise in puffs:
                if a < (0.003 if self.smoke_scale < 4 else 0.012):
                    continue
                rmax = max(radii)
                rel = P - cam.eye
                if np.all(np.abs(E @ rel) < np.array(radii) * 1.2):
                    continue                                   # the camera is inside this puff
                px, py, pz = sc.project(P[None])
                pz = float(pz[0])
                if pz < cam.near + rmax * 0.3:
                    continue
                rs = rmax / (pz * sc.tx) * W / 2
                x0, x1 = int(max(0, px[0] - 1.7 * rs)), int(min(W, px[0] + 1.7 * rs + 1))
                y0, y1 = int(max(0, py[0] - 1.7 * rs)), int(min(H, py[0] + 1.7 * rs + 1))
                if x1 <= x0 or y1 <= y0:
                    continue
                k_ = sc.rays(x0, x1, y0, y1)                    # k . fwd = 1
                ra = np.array(radii)
                o = (E @ (cam.eye - P)) / ra                     # ray in the puff's scaled frame
                d = (k_ @ E.T) / ra
                dd = (d * d).sum(-1)
                tc = -(d @ o) / dd
                q = o + tc[..., None] * d
                d2 = (q * q).sum(-1)
                dens = np.exp(-2.0 * d2)
                if self.live:
                    al = a * dens * 0.75
                else:
                    xx, yy = np.meshgrid(np.arange(x0, x1), np.arange(y0, y1))
                    nz = self.noise((xx - px[0]) / max(rs, 1e-3) * 7 + h1 * 97, (yy - py[0]) / max(rs, 1e-3) * 7 + af * 30 - t * 0.3)
                    al = a * dens * np.clip(0.45 + 0.65 * nz, 0, 1)
                al *= np.clip((zs[y0:y1, x0:x1] - (tc - rmax * 0.5)) / rmax, 0, 1)
                al *= float(np.clip((pz - 0.8) / 2.0, 0, 1))      # fade near the camera
                al = al.astype(np.float32)
                if not al.any():
                    continue
                nw = (q / ra) @ E                                # outward normal at the closest approach
                nw /= np.maximum(np.linalg.norm(nw, axis=-1, keepdims=True), 1e-9)
                lit = np.clip(0.5 + 0.5 * (nw @ self.sun), 0, 1)
                any_ = True
                blk = (slice(y0, y1), slice(x0, x1))
                acc[blk] *= 1 - al
                maps["dark"][blk] += al * f.smoke_dark * (1 - af) ** 2
                maps["warm"][blk] += al * max(0.0, 1 - af * 8)
                maps["lit"][blk] += al * lit
                maps["hot"][blk] += al * 5.0 * (max(rise, 0.1) / 0.1) ** (-5 / 3)
                maps["w"][blk] += al
        if not any_:
            return None
        alpha = 1 - acc
        wn = np.maximum(maps["w"], 1e-6)
        up = Upsampler(alpha > 0.002, scale, cam.H, cam.W)
        return [up(alpha), up(maps["dark"] / wn), up(maps["warm"] / wn), up(maps["lit"] / wn), up(maps["hot"] / wn)]

    # --- firelight -------------------------------------------------------------------------------------
    def lights(self, t):
        out = []
        for k, f in enumerate(self.fires):
            pw = f.power_w * (0.82 + 0.18 * flicker(t * 2.2 + k, 1.3 * k))
            pos = f.center + [0, 0, 0.35 + (0.4 if f.kind in ("shrub", "tree") else 0.0)]
            out.append((pos, pw))
        return out

    # --- the RGB layer -----------------------------------------------------------------------------------
    def render_rgb(self, img, zbuf, cam, t):
        """Firelight, flames, smoke and glare onto img (H x W x 3 float, 0..255), in place; returns img."""
        ks = self.in_view(cam, zbuf)
        H, W = cam.H, cam.W
        boxes = {}
        for k in ks:
            f = self.fires[k]
            b = self._box(cam, f.center - [4.0, 4.0, 1.0], f.center + [4.0, 4.0, 3.0])
            if b is not None:
                boxes[k] = b
        if boxes:
            st = 4 if self.live else 2
            x0 = min(b[0] for b in boxes.values()) // st * st; x1 = max(b[1] for b in boxes.values())
            y0 = min(b[2] for b in boxes.values()) // st * st; y1 = max(b[3] for b in boxes.values())
            k_ = cam.rays(x0, x1, y0, y1, st)
            zb = zbuf[y0:y1:st, x0:x1:st][:k_.shape[0], :k_.shape[1]]
            Pw = cam.eye + np.where(np.isfinite(zb), zb, 1e4)[..., None] * k_
            gx = np.gradient(Pw, axis=1)
            gy = np.gradient(Pw, axis=0)
            n = np.cross(gy, gx)
            n /= np.maximum(np.linalg.norm(n, axis=-1, keepdims=True), 1e-9)
            n = np.where(((n * k_).sum(-1) > 0)[..., None], -n, n)
            lightsum = np.zeros(zb.shape, np.float32)
            lights = self.lights(t)
            for k in boxes:
                pos, pw = lights[k]
                d = Pw - pos
                d2 = (d * d).sum(-1)
                m = d2 < 16.0
                if not m.any():
                    continue
                l = -d[m] / np.sqrt(d2[m])[:, None]
                ndl = np.clip((n[m] * l).sum(-1), 0, 1)
                lightsum[m] += (pw / 30000.0) * 0.04 * ndl / (d2[m] + 0.04) * np.clip((16.0 - d2[m]) / 6.0, 0, 1)
            if lightsum.any():
                ls = np.repeat(np.repeat(np.clip(lightsum, 0, 2.5), st, 0), st, 1)[:y1 - y0, :x1 - x0][..., None]
                sub = img[y0:y1, x0:x1]
                img[y0:y1, x0:x1] = sub + sub * ls * np.array([1.0, 0.5, 0.18], np.float32) + 30 * np.clip(ls, 0, 1) * np.array([1.0, 0.42, 0.1], np.float32)
        # flames: translucent, orange-dominant, sooty tips
        rho, heat, chord, zf, tip, _ = self.flames(cam, zbuf, t, ks=ks)
        emis = np.zeros((H, W, 3), np.float32)
        if rho.any():
            ys, xs = np.nonzero(rho > 0)
            sl = (slice(ys.min(), ys.max() + 1), slice(xs.min(), xs.max() + 1))
            r_, h_, tp = rho[sl], heat[sl], tip[sl]
            hn = h_ / np.maximum(r_, 1e-3)
            col = _ramp(hn, FLAME_RAMP)
            a = np.clip(0.85 * r_ * (0.45 + 0.55 * np.sqrt(np.clip(hn, 0, 1))), 0, 0.95)[..., None]
            soot = (0.4 * tp)[..., None]
            img[sl] = img[sl] * (1 - soot) + np.array([90, 20, 6], np.float32) * soot * 0.5
            img[sl] = img[sl] * (1 - a) + col * a
            emis[sl] = col * a
        # smoke (over the flames: it rises above them)
        sm = self.smoke(cam, zbuf, t, self.smoke_scale)
        if sm is not None:
            alpha, dark, warm, lit, _ = sm
            ys, xs = np.nonzero(alpha > 0.002)
            if len(ys):
                sl = (slice(ys.min(), ys.max() + 1), slice(xs.min(), xs.max() + 1))
                a_, d_, w_, l_ = alpha[sl], dark[sl], warm[sl], lit[sl]
                sunc, shadec = np.array([236, 234, 228], np.float32), np.array([146, 156, 172], np.float32)
                scol = shadec + (sunc - shadec) * l_[..., None]
                scol = scol * (1 - 0.6 * d_)[..., None] + np.array([255, 150, 60], np.float32) * (0.3 * w_)[..., None]
                img[sl] = img[sl] * (1 - a_)[..., None] + scol * a_[..., None]
        # glare of the brightest parts of the flames (lens scatter)
        ys, xs = np.nonzero(rho > 0.01)
        if len(ys):
            s1, s2 = max(1.0, W / 200), max(2.0, W / 45)
            m = int(3 * s2) + 2
            y0, y1, x0, x1 = max(0, ys.min() - m), min(H, ys.max() + m + 1), max(0, xs.min() - m), min(W, xs.max() + m + 1)
            e = emis[y0:y1, x0:x1].mean(-1)
            h2, w2 = e.shape[0] // 2 * 2, e.shape[1] // 2 * 2
            e2 = e[:h2, :w2].reshape(h2 // 2, 2, w2 // 2, 2).mean(axis=(1, 3))
            gl = gaussian_filter(np.clip(e2 - 150, 0, None), s1 / 2) * 0.45 + gaussian_filter(e2, s2 / 2) * 0.16
            gl = np.repeat(np.repeat(gl, 2, 0), 2, 1)
            img[y0:y0 + h2, x0:x0 + w2] += gl[..., None] * np.array([1.0, 0.68, 0.36], np.float32)
        return img

    # --- the thermal layer --------------------------------------------------------------------------------
    def render_thermal(self, L, zbuf, cam, t, planck, t_air_k, per_fire=False):
        """Flames and smoke composited over the scene's band radiance L (H x W), in place of it.
        Returns (L, flame z-depth, {fire: rho} if per_fire)."""
        ks = self.in_view(cam, zbuf)
        rho, heat, chord, zf, tip, fr = self.flames(cam, zbuf, t, per_fire, ks=ks)
        if rho.any():
            hn = heat / np.maximum(rho, 1e-3)
            fil = np.clip(chord / np.maximum(rho, 1e-3) / 0.25, 0, 1)
            Tg = 700.0 + 550.0 * hn * (0.75 + 0.25 * fil)
            e = (1 - np.exp(-KAPPA * chord)) * np.clip(rho * 1.2, 0, 1)
            L = L * (1 - e) + e * planck(Tg)
        sm = self.smoke(cam, zbuf, t, self.smoke_scale)
        if sm is not None:
            alpha, _, _, _, hot = sm
            es = 0.02 * alpha
            L = L * (1 - es) + es * planck(t_air_k + hot)
        return L, (zf if rho.any() else None), fr
