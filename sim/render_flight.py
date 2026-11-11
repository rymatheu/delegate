"""Render a recorded leanfc flight in PyBullet: the vehicle drawn at successive instants along the
flown path (strobe), from the CSV written by run_leanfc.py. Rendering only: the physics already
ran (headless) and its states are in the CSV; this replays them in the same engine's renderer.

Usage: render_flight.py run.csv out.png [--every SECONDS] [--from SECONDS] [--until SECONDS]
                                         [--title TEXT] [--yaw DEG] [--pitch DEG] [--dist M]
The X500 is drawn with the meshes of PX4's Gazebo model (sim/assets/x500_render_noprops.urdf,
written by sim/assets/make_x500_render_urdf.py). The propellers are not meshes: each is drawn as
the motion blur of a two-blade propeller at its true speed (`draw_props`).
Frames: the CSV is NED / FRD; PyBullet is ENU / FLU: p_enu = (e, n, −d), R_enu_flu = T R_ned_frd D.
"""
import json
import sys
from pathlib import Path

import numpy as np
import pybullet as p
from PIL import Image, ImageDraw, ImageFont

W, H = 1800, 1100
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


def model_path(vehicle):
    """Render model: the X500 from PX4's meshes without propellers; the CF2X from the package."""
    if vehicle == "cf2x":
        import gym_pybullet_drones
        return str(Path(gym_pybullet_drones.__file__).parent / "assets" / "cf2x.urdf")
    return str(Path(__file__).parent / "assets" / "x500_render_noprops.urdf")


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


def render(width, height, view, proj, vehicles):
    """One image of the current scene plus the propeller blur of each (pos, R, angle, speed)."""
    _, _, rgb, _, _ = p.getCameraImage(width, height, view, proj, shadow=1, lightDirection=[2, -3, 6], renderer=p.ER_TINY_RENDERER)
    img = np.reshape(rgb, (height, width, 4))[:, :, :3].astype(float)
    cam = np.linalg.inv(np.array(view).reshape(4, 4).T)[:3, 3]
    for pos, R, angle, speed in sorted(vehicles, key=lambda v: -np.linalg.norm(v[0] - cam)):   # far to near
        draw_props(img, view, proj, pos, R, angle, speed)
    return Image.fromarray(img.astype(np.uint8))


def load(csv):
    d = np.genfromtxt(csv, delimiter=",", names=True)
    side = Path(csv).with_suffix(".json")
    meta = json.loads(side.read_text()) if side.exists() else {}
    wps = np.array(meta.get("waypoints", []), dtype=float).reshape(-1, 3)
    pos = np.column_stack([d["p_e"], d["p_n"], -d["p_d"]])           # ENU
    sp = np.column_stack([d["sp_e"], d["sp_n"], -d["sp_d"]])
    quat = np.column_stack([d["q_w"], d["q_x"], d["q_y"], d["q_z"]])
    return d, meta, wps, pos, sp, quat


def font(size):
    """DejaVu Sans as shipped with Matplotlib (free license); no system fonts."""
    from matplotlib import font_manager
    return ImageFont.truetype(font_manager.findfont("DejaVu Sans"), size)


def ground(size=60.0, cell=1.0):
    """A flat checkered ground generated here (no bundled assets): one box with a generated texture."""
    n = 4 * int(size / cell)        # PyBullet maps the texture across a quarter of the box face
    tex = Path(__file__).parent / "assets" / "generated" / "checker.png"
    if not tex.exists():
        tex.parent.mkdir(parents=True, exist_ok=True)
        i, j = np.indices((n, n))
        img = np.where(((i + j) % 2 == 0)[..., None], [222, 222, 222], [150, 172, 208]).astype(np.uint8)
        Image.fromarray(img).resize((n * 8, n * 8), Image.NEAREST).save(tex)
    vis = p.createVisualShape(p.GEOM_BOX, halfExtents=[size / 2, size / 2, 0.01])
    body = p.createMultiBody(0, baseVisualShapeIndex=vis, basePosition=[0, 0, -0.01])
    p.changeVisualShape(body, -1, textureUniqueId=p.loadTexture(str(tex)), rgbaColor=[1, 1, 1, 1])


def scene(wps, radius=0.06):
    p.connect(p.DIRECT)
    ground()
    for w in wps:                                                     # waypoint markers and poles
        e = [w[1], w[0], -w[2]]
        p.createMultiBody(0, baseVisualShapeIndex=p.createVisualShape(p.GEOM_SPHERE, radius=radius, rgbaColor=[0.1, 0.35, 0.8, 1]), basePosition=e)
        p.createMultiBody(0, baseVisualShapeIndex=p.createVisualShape(p.GEOM_CYLINDER, radius=radius / 7, length=e[2], rgbaColor=[0.1, 0.35, 0.8, 1]),
                          basePosition=[e[0], e[1], e[2] / 2])


def main():
    csv, out = sys.argv[1], sys.argv[2]
    arg = lambda k, dflt: type(dflt)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else dflt
    every, until, title, t_from = arg("--every", 0.75), arg("--until", 14.0), arg("--title", ""), arg("--from", 0.0)
    d, meta, wps, pos, sp, quat = load(csv)
    t = d["t"]
    angle, speed = prop_state(d)
    scene(wps)
    urdf, is_x500 = model_path(meta.get("vehicle", "x500")), meta.get("vehicle", "x500") != "cf2x"
    keep, vehicles = (t >= t_from) & (t <= until), []
    for tk in np.arange(t_from, until + 1e-9, every):
        k = int(np.argmin(np.abs(t - tk)))
        R = body_rotation(quat[k])
        p.loadURDF(urdf, pos[k].tolist(), quat_xyzw(R), useFixedBase=True, flags=p.URDF_ENABLE_CACHED_GRAPHICS_SHAPES)
        if is_x500:
            vehicles.append((pos[k], R, angle[k], speed[k]))

    ctr = (pos[keep].min(axis=0) + pos[keep].max(axis=0)) / 2
    span = float(np.linalg.norm(pos[keep].max(axis=0) - pos[keep].min(axis=0)))
    view = p.computeViewMatrixFromYawPitchRoll(ctr.tolist(), distance=arg("--dist", 1.25 * span + 1.5), yaw=arg("--yaw", 32.0), pitch=arg("--pitch", -24.0), roll=0, upAxisIndex=2)
    proj = p.computeProjectionMatrixFOV(fov=42, aspect=W / H, nearVal=0.1, farVal=100)
    img = render(W, H, view, proj, vehicles)

    V, P = np.array(view).reshape(4, 4).T, np.array(proj).reshape(4, 4).T
    def px(pts):
        c = (P @ V @ np.column_stack([pts, np.ones(len(pts))]).T).T
        ndc = c[:, :3] / c[:, 3:4]
        return np.column_stack([(ndc[:, 0] + 1) / 2 * W, (1 - ndc[:, 1]) / 2 * H])
    dr = ImageDraw.Draw(img, "RGBA")
    ground = pos[keep].copy(); ground[:, 2] = 0.002
    dr.line([tuple(a) for a in px(ground)], fill=(60, 60, 60, 110), width=3)             # ground track
    dr.line([tuple(a) for a in px(sp[keep])], fill=(20, 80, 200, 200), width=2)          # navigator target
    dr.line([tuple(a) for a in px(pos[keep])], fill=(210, 60, 30, 230), width=3)         # flown path
    big, small = font(28), font(22)
    for i, w in enumerate(wps):
        a = px(np.array([[w[1], w[0], -w[2] + 0.22]]))[0]
        dr.text((a[0] + 8, a[1] - 14), f"w{i+1}  ({w[0]:g}, {w[1]:g}) m, {-w[2]:g} m up", fill=(20, 60, 160, 255), font=small)
    if t_from == 0:
        a = px(pos[:1] + [0, 0, -0.45])[0]; dr.text((a[0] - 30, a[1]), "start", fill=(0, 0, 0, 255), font=small)
    if title:
        dr.rectangle([0, 0, W, 54], fill=(255, 255, 255, 215)); dr.text((18, 10), title, fill=(0, 0, 0, 255), font=big)
    dr.rectangle([0, H - 44, W, H], fill=(255, 255, 255, 215))
    dr.text((18, H - 38), f"vehicle every {every:g} s  ·  red: flown path  ·  blue: navigator target  ·  grey: ground track  ·  front propellers red", fill=(0, 0, 0, 255), font=small)
    img.save(out); print("wrote", out, img.size)


if __name__ == "__main__":
    main()
