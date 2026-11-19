#!/usr/bin/env python3
"""Numerical checks of the X500 plant model of Plant/Model/Field.lean (constants of Constants.lean).

The 17-state field is written out below exactly as in Field.lean: NED world, FRD body, state
x = (p 0..2, v 3..5, q = (q1, q2, q3, q4) 6..9 body to NED with q1 scalar, body rates w 10..12, normalized propeller
thrusts f 13..16 in ArduPilot motor-slot order), commands u held over the period h = 1/400 s and clipped to [0, 1].
It is integrated with RK4 at a fine step (h/2000 in part (a), h/1000 in part (b)).

(a) Model-only checks, on 20 random states (unit quaternion, rates up to 3 rad/s, thrusts in [0, 1]) and commands in
    [-0.2, 1.2]^4. `CHECKS` is a list of named check functions, each printing one line `OK name ...` or
    `FAIL name ... witness`; append new checks there. Checked: the motor block's closed form
    f(t) = c + (f0 - c) e^{-t/tau(c, f0)} on [0, h] and its equality with three simulator updates
    f <- f + (c - f)(1 - e^{-hPhys/tau}); thrusts in [0, 1] moving monotonically toward the command; |q|^2 constant;
    command sensitivity |f_u(h) - f_w(h)| <= (1 - e^{-h/tauUp}) |clip u - clip w|; start-thrust sensitivity
    <= e^{-h/tauDown} |df|; hover at rest stays put.
(b) Model versus simulator: the X500 environment of sim/ (sim/world/airframes.py AirframeAviary, Physics.PYB at
    1200 Hz, gravity set as sim/harness/simulator.py _aviary, PyBullet damping removed as its reset_env), in free
    flight 20 m up, three 1/1200 s substeps per control period with the propeller speeds of
    sim/harness/motors.actuators_to_rpm; the true state is read from PyBullet, converted to NED/FRD with
    sim/harness/simulator.py's functions, and compared with the ODE from the same initial state under the same held commands. Scenarios: hover;
    roll, yaw and pitch command steps of +-0.05 from hover; a general state; a torque-free tumble at hover thrust.
    The differences (simulator - ODE) after 1..8 periods (and 40 periods for the general state and the tumble) are printed: this is the
    modeling gap, reported, not tested against a bound. Two diagnostics locate it: the starred columns compare the
    simulator with a "substep model" (the same field, but with the thrust held over each substep at its lagged
    end-of-substep value, as sim/world/airframes.py applies it), and the gap after 40 periods is recomputed with a
    2400 Hz physics rate (it must halve: the gap is the simulator's first-order time discretization). Also checked:
    the frame conversions round-trip, the lagged thrusts agree (both are the exact step response), and the
    environment writes no files (record=False; its output_folder, under the system temp directory, is never created).

    python3 tests/plant/numcheck.py            (from any directory; part (b) needs the simulator's Python with
    python3 tests/plant/numcheck.py --model    gym-pybullet-drones, .venv/bin/python; --model: part (a) only).
                                               Exit status 1 on a FAIL. About 5 s.
"""
from __future__ import annotations

import contextlib
import ctypes
import io
import math
import os
import random
import sys
import tempfile
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
PLANT = REPO
SIM = REPO.parent / "sim"            # the repository's shared simulator (sim/harness/X there is sim/gorgesim/X)

# Constants.lean, in floating point
mass = 2.0643076923076924
Jx = Jy = 0.02166666666666667
Jz = 0.04000000000000001
lever = 0.174
kf = 9.37456697678494e-08
km = 1.4999307162855904e-09
t2w = 1.689113625148385
grav = 9.80665
h = 1 / 400
hPhys = 1 / 1200
tauUp, tauDown = 0.0125, 0.025
maxRPM = math.sqrt(t2w * grav * mass / (4 * kf))
fmax = kf * maxRPM ** 2
kmkf = km / kf
hover = 1 / t2w
SLOT_TO_SIM = [0, 2, 3, 1]   # sim/harness/motors.py:16


# ----------------------------------------------------------------------------------------------------------------
# The field of Field.lean


def clip01(a):
    return max(0.0, min(1.0, a))


def lag_tau(c, f):
    return tauUp if c > f else tauDown


def vf(x, c):
    """The field at x for the clipped commands c."""
    q1, q2, q3, q4 = x[6:10]
    wx, wy, wz = x[10:13]
    F = [fmax * clip01(a) for a in x[13:17]]
    a = (F[0] + F[1] + F[2] + F[3]) / mass
    tx = lever * (-F[0] + F[1] + F[2] - F[3])
    ty = lever * (F[0] - F[1] + F[2] - F[3])
    tz = km * maxRPM ** 2 * (clip01(x[13]) + clip01(x[14]) - clip01(x[15]) - clip01(x[16]))
    return [x[3], x[4], x[5],
            -a * 2 * (q2 * q4 + q1 * q3), -a * 2 * (q3 * q4 - q1 * q2), grav - a * (q1 * q1 - q2 * q2 - q3 * q3 + q4 * q4),
            (-q2 * wx - q3 * wy - q4 * wz) / 2, (q1 * wx + q3 * wz - q4 * wy) / 2,
            (q1 * wy - q2 * wz + q4 * wx) / 2, (q1 * wz + q2 * wy - q3 * wx) / 2,
            (tx - (wy * (Jz * wz) - wz * (Jy * wy))) / Jx, (ty - (wz * (Jx * wx) - wx * (Jz * wz))) / Jy,
            (tz - (wx * (Jy * wy) - wy * (Jx * wx))) / Jz,
            (c[0] - x[13]) / lag_tau(c[0], x[13]), (c[1] - x[14]) / lag_tau(c[1], x[14]),
            (c[2] - x[15]) / lag_tau(c[2], x[15]), (c[3] - x[16]) / lag_tau(c[3], x[16])]


def rk4(x, u, t, n):
    """RK4 of the field over time t in n steps, commands u held (clipped)."""
    c = [clip01(a) for a in u]
    dt = t / n
    for _ in range(n):
        k1 = vf(x, c)
        k2 = vf([a + dt / 2 * b for a, b in zip(x, k1)], c)
        k3 = vf([a + dt / 2 * b for a, b in zip(x, k2)], c)
        k4 = vf([a + dt * b for a, b in zip(x, k3)], c)
        x = [a + dt / 6 * (b + 2 * p + 2 * q + e) for a, b, p, q, e in zip(x, k1, k2, k3, k4)]
    return x


def trajectory(x, u, chunks=20, n=100):
    """The states at t = k h / chunks, k = 0..chunks (RK4 at h / (chunks n))."""
    out = [x]
    for _ in range(chunks):
        out.append(rk4(out[-1], u, h / chunks, n))
    return out


def lag_closed(c, f0, t):
    return c + (f0 - c) * math.exp(-t / lag_tau(c, f0))


def lag_sim(c, f0, substeps=3):
    """sim/world/airframes.py:65-66, once per physics substep."""
    f = f0
    for _ in range(substeps):
        f = f + (c - f) * (1 - math.exp(-hPhys / lag_tau(c, f)))
    return f


def qmul(a, b):
    return (a[0] * b[0] - a[1] * b[1] - a[2] * b[2] - a[3] * b[3], a[0] * b[1] + a[1] * b[0] + a[2] * b[3] - a[3] * b[2],
            a[0] * b[2] - a[1] * b[3] + a[2] * b[0] + a[3] * b[1], a[0] * b[3] + a[1] * b[2] - a[2] * b[1] + a[3] * b[0])


def qconj(a):
    return (a[0], -a[1], -a[2], -a[3])


def qrot(q, v):
    """R(q) v for a unit q."""
    return qmul(qmul(q, (0.0, *v)), qconj(q))[1:]


def quat_angle(a, b):
    """Rotation angle between two unit quaternions."""
    r = qmul(qconj(a), b)
    return 2 * math.atan2(math.sqrt(r[1] ** 2 + r[2] ** 2 + r[3] ** 2), abs(r[0]))


def from_euler(roll, pitch, yaw):
    """ArduPilot's Quaternion::from_euler (ZYX)."""
    cr, sr, cp, sp = math.cos(roll / 2), math.sin(roll / 2), math.cos(pitch / 2), math.sin(pitch / 2)
    cy, sy = math.cos(yaw / 2), math.sin(yaw / 2)
    return (cr * cp * cy + sr * sp * sy, sr * cp * cy - cr * sp * sy, cr * sp * cy + sr * cp * sy,
            cr * cp * sy - sr * sp * cy)


def state(p, v, q, w, f):
    return [*p, *v, *q, *w, *f]


# ----------------------------------------------------------------------------------------------------------------
# (a) model-only checks

random.seed(17)
SAMPLES = []
for _ in range(20):
    q = [random.gauss(0, 1) for _ in range(4)]
    nq = math.sqrt(sum(a * a for a in q))
    x = state([random.uniform(-5, 5) for _ in range(3)], [random.uniform(-3, 3) for _ in range(3)], [a / nq for a in q],
              [random.uniform(-3, 3) for _ in range(3)], [random.uniform(0, 1) for _ in range(4)])
    SAMPLES.append(dict(x=x, u=[random.uniform(-0.2, 1.2) for _ in range(4)],
                        w=[random.uniform(-0.2, 1.2) for _ in range(4)], f1=[random.uniform(0, 1) for _ in range(4)]))
_cache = {}


def traj(k, which="u"):
    """Cached trajectories of sample k: under u, under w, and under u from the start thrusts f1."""
    if (k, which) not in _cache:
        s = SAMPLES[k]
        x = s["x"] if which != "f1" else s["x"][:13] + s["f1"]
        _cache[k, which] = trajectory(x, s["w"] if which == "w" else s["u"])
    return _cache[k, which]


def check_motor_closed_form():
    e_cf = e_sim = 0.0
    for k, s in enumerate(SAMPLES):
        tr = traj(k)
        for j, y in enumerate(tr):
            for i in range(4):
                e_cf = max(e_cf, abs(y[13 + i] - lag_closed(clip01(s["u"][i]), s["x"][13 + i], j * h / 20)))
        for i in range(4):
            c, f0 = clip01(s["u"][i]), s["x"][13 + i]
            e_sim = max(e_sim, abs(lag_sim(c, f0) - lag_closed(c, f0, h)), abs(lag_sim(c, f0) - tr[-1][13 + i]))
    return e_cf < 1e-9 and e_sim < 1e-9, f"max |RK4 - closed form| {e_cf:.1e} on [0, h]; max |3 sim updates - closed" \
                                         f" form or RK4| {e_sim:.1e} at h"


def check_thrust_range_monotone():
    for k, s in enumerate(SAMPLES):
        tr = traj(k)
        for i in range(4):
            c = clip01(s["u"][i])
            fs = [y[13 + i] for y in tr]
            if not all(-1e-15 <= f <= 1 + 1e-15 for f in fs):
                return False, f"sample {k} motor {i}: thrust leaves [0, 1]: {min(fs)}, {max(fs)}"
            d = [f - c for f in fs]
            if not all(d[j] * d[0] >= 0 and abs(d[j + 1]) <= abs(d[j]) + 1e-15 for j in range(len(d) - 1)):
                return False, f"sample {k} motor {i}: not monotone toward c = {c}: {fs}"
    return True, "f in [0, 1] and |f - c| nonincreasing without overshoot at 21 times on [0, h], 80 motors"


def check_quat_norm():
    e = max(abs(sum(a * a for a in y[6:10]) - sum(a * a for a in traj(k)[0][6:10]))
            for k in range(len(SAMPLES)) for y in traj(k))
    return e < 1e-12, f"max | |q(t)|^2 - |q(0)|^2 | {e:.1e} on [0, h]"


def check_command_sensitivity():
    L = 1 - math.exp(-h / tauUp)
    worst = 0.0
    for k, s in enumerate(SAMPLES):
        for i in range(4):
            d = abs(traj(k)[-1][13 + i] - traj(k, "w")[-1][13 + i])
            dc = abs(clip01(s["u"][i]) - clip01(s["w"][i]))
            if d > L * dc + 1e-12:
                return False, f"sample {k} motor {i}: |df(h)| {d} > {L} |dc| = {L * dc}"
            worst = max(worst, d / dc if dc > 1e-9 else 0.0)
    return True, f"|f_u(h) - f_w(h)| <= (1 - e^(-h/tauUp)) |clip u - clip w|: largest ratio {worst:.6f} <= {L:.6f}"


def check_start_sensitivity():
    L = math.exp(-h / tauDown)
    worst = 0.0
    for k, s in enumerate(SAMPLES):
        for i in range(4):
            d = abs(traj(k)[-1][13 + i] - traj(k, "f1")[-1][13 + i])
            d0 = abs(s["x"][13 + i] - s["f1"][i])
            if d > L * d0 + 1e-12:
                return False, f"sample {k} motor {i}: |df(h)| {d} > {L} |df(0)| = {L * d0}"
            worst = max(worst, d / d0 if d0 > 1e-9 else 0.0)
    return True, f"|f(h) - f'(h)| <= e^(-h/tauDown) |f(0) - f'(0)|: largest ratio {worst:.6f} <= {L:.6f}"


def check_hover():
    e = 0.0
    for yaw in (0.0, 0.7, -2.5):
        x = state([1.0, -2.0, -20.0], [0, 0, 0], from_euler(0, 0, yaw), [0, 0, 0], [hover] * 4)
        y = rk4(x, [hover] * 4, h, 2000)
        e = max(e, max(abs(a - b) for a, b in zip(x, y)), max(abs(a) for a in vf(x, [hover] * 4)))
    return e < 1e-12, f"level at rest, f = u = 1/thrust2weight, three yaws: max |x(h) - x(0)|, |F(x)| {e:.1e}"


# The integrals of the lag (Plant/Lib/Gronwall.lean, Plant/Field/Motor.lean) and the derived bounds of
# Plant/Step/{Sharp,InputSens}.lean.
amax = t2w * grav
alphaMax = 2 * lever * fmax / Jx
gyro = (Jz - Jx) / Jx
ctau = 2 * (2 * lever * fmax) ** 2 / Jx + (2 * kmkf * fmax) ** 2 / Jz


def lagM(n, tau, t):
    mu = 1 - math.exp(-t / tau)
    return [mu, t - tau * mu, t * t / 2 - tau * t + tau ** 2 * mu,
            t ** 3 / 6 - tau * t * t / 2 + tau ** 2 * t - tau ** 3 * mu][n]


def lagK(n, c, f, t):
    tau = lag_tau(c, f)
    M1, M2, M3 = lagM(1, tau, t), lagM(2, tau, t), lagM(3, tau, t)
    return [None, f * t + (c - f) * M1, f * t * t / 2 + (c - f) * (t * M1 - M2), f * t * t / 2 + (c - f) * M2,
            f * t ** 3 / 6 + (c - f) * (t * M2 - 2 * M3)][n]


def accK(n, x, u, t):
    return amax / 4 * sum(lagK(n, clip01(u[i]), x[13 + i], t) for i in range(4))


def wTA(W, A):
    wB = math.sqrt(((2 * Jx + Jz) * W * W + ctau * h * h) * math.e / Jx)
    return W + h * (A + gyro * wB ** 2)


def sens_bounds(Om, d, t):
    Kq = (1.5 + 2 * gyro) * Om
    return dict(f=d * lagM(0, tauUp, t), w=2 * alphaMax * d * lagM(1, tauUp, t) * math.exp(2 * gyro * Om * t),
                q=3 * alphaMax * d * lagM(2, tauUp, t) * math.exp(Kq * t),
                v=amax * d * (lagM(1, tauUp, t) + 24 * alphaMax * lagM(3, tauUp, t) * math.exp(Kq * t)),
                p=amax * d * (lagM(2, tauUp, t) + 24 * alphaMax * t * lagM(3, tauUp, t) * math.exp(Kq * t)))


def block_diffs(a, b):
    return dict(f=max(abs(a[i] - b[i]) for i in range(13, 17)), w=max(abs(a[i] - b[i]) for i in range(10, 13)),
                q=max(abs(a[i] - b[i]) for i in range(6, 10)), v=max(abs(a[i] - b[i]) for i in range(3, 6)),
                p=max(abs(a[i] - b[i]) for i in range(0, 3)))


def check_input_sensitivity():
    """Step/InputSens.lean traj_input_sens at t = h, k h / 20: every block within its bound; also a roll step."""
    worst = {b: 0.0 for b in "fwqvp"}
    for k, s in enumerate(SAMPLES):
        x = s["x"]
        W = max(abs(a) for a in x[10:13])
        Om = wTA(W, alphaMax)
        d = max(abs(a - b) for a, b in zip(s["u"], s["w"]))
        for j in range(1, 21):
            B = sens_bounds(Om, d, j * h / 20)
            D = block_diffs(traj(k)[j], traj(k, "w")[j])
            for b in "fwqvp":
                if D[b] > B[b] * (1 + 1e-9) + 1e-15:
                    return False, f"sample {k} t = {j}h/20 block {b}: {D[b]:.3e} > bound {B[b]:.3e}"
                worst[b] = max(worst[b], D[b] / B[b] if B[b] > 0 else 0.0)
    # sharpness: from hover, a roll step of 0.05 on one axis
    x0 = state([0, 0, -20], [0, 0, 0], (1, 0, 0, 0), [0, 0, 0], [hover] * 4)
    u, w = [hover] * 4, [hover - 0.05, hover + 0.05, hover + 0.05, hover - 0.05]
    a, b = rk4(x0, u, h, 2000), rk4(x0, w, h, 2000)
    B, D = sens_bounds(wTA(0, alphaMax), 0.05, h), block_diffs(a, b)
    ratios = " ".join(f"{k} {D[k] / B[k]:.3f}" for k in "fwq")
    return True, ("largest ratio actual/bound over 20 samples x 20 times: " +
                  " ".join(f"{b} {worst[b]:.3f}" for b in "fwqvp") + f"; roll step 0.05 from hover: {ratios}")


def check_pv_sharp():
    """Step/Sharp.lean traj_pv_sharp at t = h: the expansion with accK1..4 within amax Cd h^3/6, amax Cd h^4/24."""
    worst_v = worst_p = 0.0
    for k, s in enumerate(SAMPLES):
        x, u = s["x"], s["u"]
        W = max(abs(a) for a in x[10:13])
        Om = wTA(W, alphaMax)
        Cd = math.sqrt(2 * (alphaMax + Jz / Jx * Om * Om) ** 2 + 4 * Om ** 4)
        q1, q2, q3, q4 = x[6:10]
        wx, wy = x[10], x[11]
        dn = [2 * (q2 * q4 + q1 * q3), 2 * (q3 * q4 - q1 * q2), q1 * q1 - q2 * q2 - q3 * q3 + q4 * q4]
        c0 = [q1 * q1 + q2 * q2 - q3 * q3 - q4 * q4, 2 * (q2 * q3 + q1 * q4), 2 * (q2 * q4 - q1 * q3)]
        c1 = [2 * (q2 * q3 - q1 * q4), q1 * q1 - q2 * q2 + q3 * q3 - q4 * q4, 2 * (q3 * q4 + q1 * q2)]
        dd = [c0[j] * wy - c1[j] * wx for j in range(3)]
        y = traj(k)[-1]
        K1, K2, K3, K4 = (accK(n, x, u, h) for n in (1, 2, 3, 4))
        for j in range(3):
            ez = 1.0 if j == 2 else 0.0
            rv = y[3 + j] - (x[3 + j] + h * grav * ez - K1 * dn[j] - K2 * dd[j])
            rp = y[j] - (x[j] + h * x[3 + j] + h * h / 2 * grav * ez - K3 * dn[j] - K4 * dd[j])
            bv, bp = amax * Cd * h ** 3 / 6, amax * Cd * h ** 4 / 24
            if abs(rv) > bv or abs(rp) > bp:
                return False, f"sample {k} row {j}: |r_v| {abs(rv):.2e} (bound {bv:.2e}), |r_p| {abs(rp):.2e} ({bp:.2e})"
            worst_v, worst_p = max(worst_v, abs(rv) / bv), max(worst_p, abs(rp) / bp)
    return True, f"largest |r_v| / bound {worst_v:.3f}, |r_p| / bound {worst_p:.3f}"


def check_level_flight():
    """Step/Multi.lean stepN_level_vz, stepN_level_pz: 40 periods of level flight, equal thrusts and commands."""
    e = 0.0
    for f0, c in ((0.2, 0.9), (0.8, 0.1), (hover, hover), (0.5, 0.5 + 1e-3)):
        x = state([0, 0, -20], [0.3, -0.2, 0.5], from_euler(0, 0, 0.4), [0, 0, 0], [f0] * 4)
        y, n = x, 40
        for _ in range(n):
            y = rk4(y, [c] * 4, h, 400)
        T = n * h
        vz = x[5] + T * grav - amax * lagK(1, c, f0, T)
        pz = x[2] + T * x[5] + T * T / 2 * grav - amax * lagK(3, c, f0, T)
        e = max(e, abs(y[5] - vz), abs(y[2] - pz), abs(y[13] - lag_closed(c, f0, T)))
    return e < 1e-9, f"max deviation from the closed forms after 40 periods {e:.1e}"


def check_spin():
    """Step/Exact.lean step_spin: paired thrusts and commands, yaw-only attitude, zero roll and pitch rates."""
    e = 0.0
    kappa = 2 * kmkf * fmax / Jz
    for f0, f2, c0, c2, r in ((0.5, 0.6, 0.7, 0.4, 0.3), (0.9, 0.1, 0.2, 1.0, -1.0)):
        x = state([1, 2, -20], [0.5, 0.1, -0.2], (math.cos(0.3), 0, 0, math.sin(0.3)), [0, 0, r], [f0, f0, f2, f2])
        u = [c0, c0, c2, c2]
        y = rk4(x, u, h, 2000)
        rate = r + kappa * (lagK(1, c0, f0, h) - lagK(1, c2, f2, h))
        th = r * h + kappa * (lagK(3, c0, f0, h) - lagK(3, c2, f2, h))
        qs = x[6] ** 2 + x[9] ** 2
        exp = [x[0] + h * x[3], x[1] + h * x[4], x[2] + h * x[5] + h * h / 2 * grav - qs * accK(3, x, u, h),
               x[3], x[4], x[5] + h * grav - qs * accK(1, x, u, h),
               x[6] * math.cos(th / 2) - x[9] * math.sin(th / 2), 0, 0, x[6] * math.sin(th / 2) + x[9] * math.cos(th / 2),
               0, 0, rate] + [lag_closed(u[i], x[13 + i], h) for i in range(4)]
        e = max(e, max(abs(a - b) for a, b in zip(y, exp)))
    return e < 1e-9, f"max |RK4 - spinSol| {e:.1e}"


def check_period_dev():
    """Step/Period.lean step_v_dev_le, step_p_dev_le: deviation from free fall within accK1, accK3 times |q|^2."""
    worst = 0.0
    for k, s in enumerate(SAMPLES):
        x, y = s["x"], traj(k)[-1]
        ev = math.sqrt(sum((y[3 + j] - x[3 + j] - h * grav * (j == 2)) ** 2 for j in range(3)))
        ep = math.sqrt(sum((y[j] - x[j] - h * x[3 + j] - h * h / 2 * grav * (j == 2)) ** 2 for j in range(3)))
        bv, bp = accK(1, x, s["u"], h), accK(3, x, s["u"], h)
        if ev > bv * (1 + 1e-9) or ep > bp * (1 + 1e-9):
            return False, f"sample {k}: {ev} > {bv} or {ep} > {bp}"
        worst = max(worst, ev / bv, ep / bp)
    return True, f"largest deviation / bound {worst:.6f}"


def check_numbers():
    """Step/Numbers.lean: the evaluated constants."""
    Om = wTA(1, alphaMax)
    B = sens_bounds(137 / 100, 1.0, h)
    vals = dict(alphaMax=alphaMax, amax=amax, wTA_1=Om, mu_h=lagM(0, tauUp, h), sensW=B["w"], sensQ=B["q"],
                sensV=B["v"], sensP=B["p"])
    ok = (137.30 <= alphaMax <= 137.31 and amax <= 16.5646 and Om <= 1.37 and 0.1812 <= vals["mu_h"] <= 0.1815
          and B["w"] <= 0.0650 and B["q"] <= 8.7e-5 and B["v"] <= 3.91e-3 and B["p"] <= 3.48e-6)
    return ok, " ".join(f"{k} {v:.6g}" for k, v in vals.items())


CHECKS = [
    ("motor_closed_form", check_motor_closed_form),
    ("thrust_range_monotone", check_thrust_range_monotone),
    ("quat_norm_constant", check_quat_norm),
    ("thrust_command_sensitivity", check_command_sensitivity),
    ("thrust_start_sensitivity", check_start_sensitivity),
    ("hover_rest", check_hover),
    ("input_sensitivity_blocks", check_input_sensitivity),
    ("pv_sharp", check_pv_sharp),
    ("level_flight_40", check_level_flight),
    ("spin_closed_form", check_spin),
    ("period_deviation", check_period_dev),
    ("numbers", check_numbers),
]


# ----------------------------------------------------------------------------------------------------------------
# (b) model versus simulator


@contextlib.contextmanager
def quiet():
    """Silence stdout and stderr, also at the file-descriptor level (pybullet's C banner); exceptions still
    propagate and are printed afterward."""
    sys.stdout.flush()
    sys.stderr.flush()
    saved = [os.dup(1), os.dup(2)]
    null = os.open(os.devnull, os.O_WRONLY)
    os.dup2(null, 1)
    os.dup2(null, 2)
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            yield
    finally:
        sys.stdout.flush()
        sys.stderr.flush()
        ctypes.CDLL(None).fflush(None)   # the C library's buffers, before the descriptors are restored
        for fd, old in zip((1, 2), saved):
            os.dup2(old, fd)
            os.close(old)
        os.close(null)


class Sim:
    """The X500 environment of sim/, stepped one control period (three substeps) at a time."""

    def __init__(self, out, pyb_hz=1200):
        sys.path[:0] = [str(SIM / "world"), str(SIM)]
        with quiet():
            import numpy as np
            import pybullet as pb
            from gorgesim import motors, simulator as sm
            from airframes import AIRFRAMES, LAG, AirframeAviary
            from gym_pybullet_drones.utils.enums import DroneModel, Physics
            # drone_model: the enum's first member, the one sim/harness/simulator.py:131 passes. With Physics.PYB it only
            # names the package's own URDF, which AirframeAviary replaces with the X500's (and it is not RACE, whose
            # yaw torques the package negates).
            model = list(DroneModel)[0]
            assert model is not DroneModel.RACE
            env = AirframeAviary(urdf=AIRFRAMES["x500"]["urdf"], lag=LAG, drone_model=model, num_drones=1,
                                 physics=Physics.PYB, pyb_freq=pyb_hz, ctrl_freq=pyb_hz, gui=False, record=False,
                                 obstacles=False, user_debug_gui=False, output_folder=str(out))
        # sim/harness/simulator.py _aviary, lines 136-140
        env.G = sm.GRAVITY_MSS
        env.GRAVITY = env.G * env.M
        env.HOVER_RPM = np.sqrt(env.GRAVITY / (4 * env.KF))
        env.MAX_RPM = np.sqrt((env.THRUST2WEIGHT_RATIO * env.GRAVITY) / (4 * env.KF))
        env.MAX_THRUST = 4 * env.KF * env.MAX_RPM ** 2
        self.np, self.pb, self.sm, self.motors, self.env = np, pb, sm, motors, env
        self.fmax = env.KF * env.MAX_RPM ** 2
        self.substeps = pyb_hz // 400   # sim/fly_gorge.py:144
        self.T = sm.ENU_TO_NED

    def to_enu(self, x):
        """A NED/FRD state as PyBullet's ENU position and velocity, (x, y, z, w) FLU-to-ENU quaternion and
        world-frame angular velocity: the inverse of the simulator's conversions."""
        T = self.T
        q = x[6:10]
        qe = qmul(qmul(qconj(self.sm.Q_ENU_TO_NED), q), qconj(self.sm.Q_FRD_TO_FLU))
        return (T @ x[0:3], T @ x[3:6], (qe[1], qe[2], qe[3], qe[0]), T @ self.np.array(qrot(q, x[10:13])))

    def put(self, x):
        """Reset, remove damping (sim/harness/simulator.py:184), and set the state x (NED/FRD, normalized thrusts)."""
        env, pb = self.env, self.pb
        with quiet():
            env.reset()
        i, c = env.DRONE_IDS[0], env.CLIENT
        pb.changeDynamics(i, -1, linearDamping=0.0, angularDamping=0.0, physicsClientId=c)
        p, v, q, w = self.to_enu(x)
        pb.resetBasePositionAndOrientation(i, p.tolist(), q, physicsClientId=c)
        pb.resetBaseVelocity(i, v.tolist(), w.tolist(), physicsClientId=c)
        lag = self.np.zeros(4)
        for s in range(4):
            lag[SLOT_TO_SIM[s]] = self.fmax * x[13 + s]
        env.lag_thrust = lag

    def read(self):
        """The true state, NED/FRD with the simulator's conversions, thrusts normalized in slot order."""
        env, pb, sm = self.env, self.pb, self.sm
        pos, quat = pb.getBasePositionAndOrientation(env.DRONE_IDS[0], physicsClientId=env.CLIENT)
        vel, angv = pb.getBaseVelocity(env.DRONE_IDS[0], physicsClientId=env.CLIENT)
        p, v, _, w = sm.enu_state_to_ned(pos, quat, vel, angv)
        f = [env.lag_thrust[SLOT_TO_SIM[s]] / self.fmax for s in range(4)]
        return state(p, v, sm.quat_ned_frd(quat), w, f)

    def period(self, u):
        rpm = self.motors.actuators_to_rpm(self.env, u)
        for _ in range(self.substeps):
            self.env.step(rpm.reshape(1, 4))


def frame_roundtrip(sim):
    """Set states, read them back without stepping; and check the simulator's matrices against the quaternion."""
    np, sm = sim.np, sim.sm
    e_rt = e_mat = 0.0
    random.seed(5)
    for _ in range(10):
        q = [random.gauss(0, 1) for _ in range(4)]
        nq = math.sqrt(sum(a * a for a in q))
        q = [a / nq * (1 if q[0] >= 0 else -1) for a in q]
        x = state([random.uniform(-5, 5), random.uniform(-5, 5), -20.0], [random.uniform(-3, 3) for _ in range(3)], q,
                  [random.uniform(-3, 3) for _ in range(3)], [random.uniform(0, 1) for _ in range(4)])
        sim.put(x)
        y = sim.read()
        e_rt = max(e_rt, max(abs(a - b) for a, b in zip(x, y)))
        _, _, quat, _ = sim.to_enu(x)
        R = sm.ENU_TO_NED @ sm.quat_to_matrix(quat) @ sm.FRD_TO_FLU     # enu_state_to_ned's R_ned_frd
        Rq = np.array([qrot(q, e) for e in np.eye(3)]).T
        d = (2 * (q[1] * q[3] + q[0] * q[2]), 2 * (q[2] * q[3] - q[0] * q[1]), q[0] ** 2 - q[1] ** 2 - q[2] ** 2 + q[3] ** 2)
        e_mat = max(e_mat, np.abs(R - Rq).max(), np.abs(sm.ap_quat_to_matrix(q) - Rq).max(), np.abs(R[:, 2] - d).max())
    return e_rt < 1e-9 and e_mat < 1e-12, (f"10 random states set and read back: max error {e_rt:.1e}; R_ned_frd of"
                                           f" simulator.py = R(q) = ap_quat_to_matrix(q), third column = downAxis(q):"
                                           f" {e_mat:.1e}")


def substep_model(x, u):
    """One control period of the field with the simulator's time discretization of the thrust: before each of the
    three substeps the thrusts jump to their lagged value at the end of the substep (sim/world/airframes.py:65-66),
    which is then held while the rest of the state follows the field exactly (RK4, h/900)."""
    c = [clip01(a) for a in u]
    for _ in range(3):
        f = [lag_sim(c[i], x[13 + i], 1) for i in range(4)]
        x = rk4(x[:13] + f, f, hPhys, 300)   # command = thrust: the motor block stands still
    return x


def gap_row(xs, xo):
    qs, qo = xs[6:10], xo[6:10]
    if sum(a * b for a, b in zip(qs, qo)) < 0:
        qo = [-a for a in qo]
    return (max(abs(xs[j] - xo[j]) for j in range(3)), max(abs(xs[j] - xo[j]) for j in range(3, 6)),
            quat_angle(qs, qo), max(abs(a - b) for a, b in zip(qs, qo)), max(abs(xs[j] - xo[j]) for j in range(10, 13)),
            max(abs(xs[j] - xo[j]) for j in range(13, 17)))


def scenarios():
    lev = from_euler(0, 0, 0)
    up = [0.0, 0.0, -20.0]
    hv = [hover] * 4
    return [
        ("(i) hover", state(up, [0, 0, 0], lev, [0, 0, 0], hv), hv, 8),
        ("(ii) roll step +-0.05 (-,+,+,-)", state(up, [0, 0, 0], lev, [0, 0, 0], hv),
         [hover + 0.05 * s for s in (-1, 1, 1, -1)], 8),
        ("(iii) general state", state(up, [2.0, -1.0, 0.5], from_euler(math.radians(10), math.radians(-5),
                                                                       math.radians(30)),
                                      [0.5, -0.3, 0.2], [0.55, 0.6, 0.62, 0.58]), [0.7, 0.5, 0.65, 0.55], 40),
        ("(iv) yaw step +-0.05 (+,+,-,-)", state(up, [0, 0, 0], lev, [0, 0, 0], hv),
         [hover + 0.05 * s for s in (1, 1, -1, -1)], 8),
        ("(v) pitch step +-0.05 (+,-,+,-)", state(up, [0, 0, 0], lev, [0, 0, 0], hv),
         [hover + 0.05 * s for s in (1, -1, 1, -1)], 8),
        ("(vi) torque-free tumble, f = u = hover", state(up, [1.0, 0.0, 0.0], from_euler(0.3, 0.2, -1.0),
                                                         [1.0, -0.5, 2.0], hv), hv, 40),
    ]


def sim_compare():
    out = Path(tempfile.gettempdir()) / f"plant-numcheck-pyb-{os.getpid()}"   # never created with record=False
    t0 = time.time()
    try:
        sim = Sim(out)
    except ImportError as e:
        print(f"FAIL sim_import {e} (run with the simulator's Python, or pass --model)")
        return False
    good = True
    ok, info = frame_roundtrip(sim)
    good &= ok
    print(f"{'OK' if ok else 'FAIL'} frame_roundtrip {info}")
    f_gap = 0.0
    ends = {}
    print("(b) simulator - ODE after N control periods (h = 2.5 ms; max over components; angle = rotation between"
          " the attitudes);\n    starred: simulator - substep model (the field with the thrust held per substep at its"
          " lagged end value)")
    for name, x0, u, nmax in scenarios():
        sim.put(x0)
        xo = xd = x0
        print(f"  {name}: u = ({', '.join(f'{a:.4f}' for a in u)})")
        print(f"  {'N':>4s} {'|dp| m':>9s} {'|dv| m/s':>9s} {'angle rad':>9s} {'|dq_i|':>9s} {'|dw| rad/s':>10s}"
              f" {'|df|':>9s} | {'|dv|*':>9s} {'angle*':>9s} {'|dw|*':>9s}")
        for n in range(1, nmax + 1):
            sim.period(u)
            xo = rk4(xo, u, h, 1000)
            xd = substep_model(xd, u)
            xs = sim.read()
            row, rd = gap_row(xs, xo), gap_row(xs, xd)
            f_gap = max(f_gap, row[5])
            if n <= 8 or n == nmax:
                print(f"  {n:4d} " + " ".join(f"{a:9.2e}" if j != 4 else f"{a:10.2e}" for j, a in enumerate(row)) +
                      f" | {rd[1]:9.2e} {rd[2]:9.2e} {rd[4]:9.2e}")
        ends[name] = (x0, u, nmax, row)
        print(f"       ODE change over {nmax} periods: |v - v0| {max(abs(xo[j] - x0[j]) for j in range(3, 6)):.2e} m/s,"
              f" angle {quat_angle(x0[6:10], xo[6:10]):.2e} rad, |w - w0| "
              f"{max(abs(xo[j] - x0[j]) for j in range(10, 13)):.2e} rad/s")
    ok = f_gap < 1e-9
    good &= ok
    print(f"{'OK' if ok else 'FAIL'} sim_lag_thrust max |f_sim - f_ODE| {f_gap:.1e} over all periods (both exact)")
    sim.env.close()
    # the gap is the simulator's time discretization: it halves when the physics rate doubles
    sim2 = Sim(out, 2400)
    worst = (0.0, "")
    for name, (x0, u, nmax, row) in ends.items():
        if nmax < 40:
            continue
        sim2.put(x0)
        for _ in range(nmax):
            sim2.period(u)
        xo = rk4(x0, u, nmax * h, nmax * 1000)
        row2 = gap_row(sim2.read(), xo)
        ratios = [a / b for a, b in zip(row[1:5], row2[1:5])]
        print(f"     {name.split()[0]} after {nmax} periods, 1200 Hz / 2400 Hz physics: |dv| {row[1]:.2e} / {row2[1]:.2e},"
              f" angle {row[2]:.2e} / {row2[2]:.2e}, |dw| {row[4]:.2e} / {row2[4]:.2e}; ratios (dv, angle, dq, dw) "
              f"{', '.join(f'{r:.3f}' for r in ratios)}")
        worst = max(worst, (max(abs(r - 2) for r in ratios), name.split()[0]))
    sim2.env.close()
    ok = worst[0] < 0.2
    good &= ok
    print(f"{'OK' if ok else 'FAIL'} gap_first_order the gap halves with the physics substep (|ratio - 2| <= "
          f"{worst[0]:.3f} {worst[1]}): it is the simulator's O(hPhys) discretization of the ODE")
    ok = not out.exists()
    good &= ok
    print(f"{'OK' if ok else 'FAIL'} no_files the environment's output_folder {out} was {'not ' if ok else ''}created")
    print(f"(b) {time.time() - t0:.1f} s")
    return good


def main() -> int:
    t0 = time.time()
    fails = 0
    print("(a) model-only checks, 20 random states, RK4 at h/2000")
    for name, fn in CHECKS:
        ok, info = fn()
        fails += not ok
        print(f"{'OK' if ok else 'FAIL'} {name} {info}")
    print(f"(a) {time.time() - t0:.1f} s")
    if "--model" not in sys.argv[1:]:
        fails += not sim_compare()
    print("numcheck: all checks pass" if fails == 0 else f"numcheck: {fails} part(s) FAILED")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
