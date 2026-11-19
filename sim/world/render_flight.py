"""The vehicle as the gorge renderers draw it: the render model (`model_path`: the X500 from PX4's Gazebo meshes without
propellers, x500/x500_render_noprops.urdf) and the propellers, which are not meshes: each is drawn as the motion blur of a
two-blade propeller at its true speed (`prop_state`, `draw_props`), composited onto the rendered image. Rendering only.

Frames: PyBullet is ENU / FLU; `body_rotation` turns an FRD-body-to-NED quaternion (w, x, y, z) into the FLU-body-to-ENU
rotation, R_enu_flu = T R_ned_frd D.
"""
from pathlib import Path

import numpy as np

T = np.array([[0, 1, 0], [1, 0, 0], [0, 0, -1.0]])
D = np.diag([1, -1, -1.0])

# X500 rotors in the FLU body frame, in motor order m1..m4 (PX4 rotor_0..3): hub position (m),
# spin (+1 CCW seen from above), blade color. Propeller plane 0.05 m above the body origin.
HUBS = np.array([[0.174, -0.174, 0.05], [-0.174, 0.174, 0.05], [0.174, 0.174, 0.05], [-0.174, -0.174, 0.05]])
SPIN = np.array([1, 1, -1, -1.0])
BLADE_RGB = np.array([[217, 56, 31], [30, 30, 33], [217, 56, 31], [30, 30, 33]], dtype=float)   # front red, rear dark
PROP_RADIUS = 0.14        # m: the 13 inch propeller of the model scaled by 0.846
MAX_RAD_S = 1000.0        # rad/s at command 1 (PX4 model maxRotVelocity)
SHUTTER_S = 1.0 / 1000    # exposure time of the virtual camera


def rot(q):
    w, x, y, z = q
    return np.array([[1 - 2 * (y * y + z * z), 2 * (x * y - w * z), 2 * (x * z + w * y)],
                     [2 * (x * y + w * z), 1 - 2 * (x * x + z * z), 2 * (y * z - w * x)],
                     [2 * (x * z - w * y), 2 * (y * z + w * x), 1 - 2 * (x * x + y * y)]])


def quat_xyzw(R):
    t = np.trace(R)
    if t > 0:
        s = np.sqrt(1 + t) * 2
        q = [(R[2, 1] - R[1, 2]) / s, (R[0, 2] - R[2, 0]) / s, (R[1, 0] - R[0, 1]) / s, s / 4]
    else:
        i = int(np.argmax(np.diag(R))); j, k = (i + 1) % 3, (i + 2) % 3
        s = np.sqrt(1 + R[i, i] - R[j, j] - R[k, k]) * 2
        q = [0, 0, 0, (R[k, j] - R[j, k]) / s]
        q[i], q[j], q[k] = s / 4, (R[j, i] + R[i, j]) / s, (R[k, i] + R[i, k]) / s
    return q


def body_rotation(q_ned_frd):
    """FLU body to ENU world rotation from the CSV's FRD body to NED quaternion (w, x, y, z)."""
    return T @ rot(q_ned_frd) @ D


def model_path():
    """Render model: the X500 from PX4's meshes without propellers."""
    return str(Path(__file__).parent / "x500" / "x500_render_noprops.urdf")


def prop_state(d, hz=400.0):
    """Per tick and motor: the propeller's true angle (rad, signed by its spin) and speed (rad/s).
    Speed is MAX_RAD_S·sqrt(m): thrust ∝ speed² and the command m is the thrust fraction."""
    m = np.column_stack([d["m1"], d["m2"], d["m3"], d["m4"]]).clip(0, 1)
    speed = MAX_RAD_S * np.sqrt(m)
    return np.cumsum(speed / hz, axis=0) * SPIN, speed


def chord(x):
    """Blade chord (m) at radius fraction x: widest near 40% radius, narrow at root and tip."""
    return 0.006 + 0.026 * np.sin(np.pi * np.clip(0.12 + 0.86 * x, 0, 1)) ** 1.3


def draw_props(img, view, proj, pos, R, angle, speed):
    """Composite the four propellers of one vehicle onto the float image `img` (H×W×3) as exact
    angular motion blur. A blade of angular width w(r) = chord(r)/r turning through Δ = speed ×
    SHUTTER_S during the exposure covers the direction ψ (measured from the middle of the sweep)
    for the fraction |[ψ − w/2, ψ + w/2] ∩ [−Δ/2, Δ/2]| / Δ of the exposure. That fraction is the
    opacity: 1 near the hub, where the blade is wider than its sweep, and falling toward the tip,
    where the same sweep is a long arc. Each pixel is mapped to its point on the rotor plane by
    intersecting its camera ray with that plane (hub position, normal = body z)."""
    h, w_img = img.shape[:2]
    V, P = np.array(view).reshape(4, 4).T, np.array(proj).reshape(4, 4).T
    PV, inv = P @ V, np.linalg.inv(P @ V)
    e1, e2, n = R[:, 0], R[:, 1], R[:, 2]
    turn = np.linspace(0, 2 * np.pi, 24)
    for i in range(4):
        c = pos + R @ HUBS[i]
        # bounding box of the disc in the image
        ring = c + PROP_RADIUS * 1.05 * (np.outer(np.cos(turn), e1) + np.outer(np.sin(turn), e2))
        clip = (PV @ np.column_stack([ring, np.ones(len(ring))]).T).T
        if np.any(clip[:, 3] <= 0.05):
            continue
        ndc = clip[:, :2] / clip[:, 3:4]
        u0, u1 = int(np.floor((ndc[:, 0].min() + 1) / 2 * w_img)), int(np.ceil((ndc[:, 0].max() + 1) / 2 * w_img))
        v0, v1 = int(np.floor((1 - ndc[:, 1].max()) / 2 * h)), int(np.ceil((1 - ndc[:, 1].min()) / 2 * h))
        u0, u1, v0, v1 = max(u0, 0), min(u1, w_img), max(v0, 0), min(v1, h)
        if u1 <= u0 or v1 <= v0:
            continue
        # 2×2 supersampled pixel rays → points on the rotor plane
        us, vs = np.meshgrid(np.arange(u0, u1, 0.5) + 0.25, np.arange(v0, v1, 0.5) + 0.25)
        x, y = 2 * us / w_img - 1, 1 - 2 * vs / h
        def unproject(z):
            q = np.stack([x, y, np.full_like(x, z), np.ones_like(x)], axis=-1) @ inv.T
            return q[..., :3] / q[..., 3:4]
        o, far = unproject(-1.0), unproject(1.0)
        dvec = far - o
        tpar = ((c - o) @ n) / (dvec @ n)
        q = o + tpar[..., None] * dvec - c
        a, b = q @ e1, q @ e2
        r = np.sqrt(a * a + b * b)
        xr = r / PROP_RADIUS
        delta = max(speed[i] * SHUTTER_S, 1e-3)                    # sweep during the exposure
        wid = np.minimum(chord(xr) / np.maximum(r, 1e-4), np.pi)   # blade angular width
        mid = angle[i] + SPIN[i] * delta / 2
        psi = np.arctan2(b, a) - mid
        psi = (psi + np.pi / 2) % np.pi - np.pi / 2                # two blades: fold by half a turn
        cover = np.clip(np.minimum(psi + wid / 2, delta / 2) - np.maximum(psi - wid / 2, -delta / 2), 0, None) / delta
        cover = np.minimum(cover, 1.0) * (xr <= 1.0) * np.clip((1.0 - xr) / 0.04, 0, 1) ** 0.5   # soft tip
        alpha = cover.reshape(v1 - v0, 2, u1 - u0, 2).mean(axis=(1, 3))[..., None]
        img[v0:v1, u0:u1] = img[v0:v1, u0:u1] * (1 - alpha) + BLADE_RGB[i] * alpha
