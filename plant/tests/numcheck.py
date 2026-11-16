#!/usr/bin/env python3
"""Numerical sanity check of the phase-3 statements of the plant library (plant/PLAN.md, rule 5).

Integrates the CF2X field of plant/Plant/Model/Field.lean (constants of Constants.lean) with RK4 at h/400 per
substep and checks, on random states and commands, the statements of Field/Actuators.lean, Flow/Sensitivity.lean,
Step/Exact.lean, Step/Symmetry.lean, Step/Period.lean and Step/Multi.lean (up to the RK4 error, tolerance 1e-9
relative where an identity is claimed). Plain Python, a few seconds.

    python3 plant/tests/numcheck.py
"""
import math
import random

mass, Jx, Jy, Jz, lever, kf, km, t2w, g = 0.027, 1.4e-5, 1.4e-5, 2.17e-5, 0.028, 3.16e-10, 7.94e-12, 2.25, 9.80665
h = 1 / 400
fmax = t2w * g * mass / 4
kmkf = km / kf
amax = t2w * g
alphaMax = 2 * lever * fmax / Jx


def clip(a):
    return max(0.0, min(1.0, a))


def wrench(u):
    c = [clip(a) for a in u]
    return [fmax * sum(c), lever * fmax * (-c[0] + c[1] + c[2] - c[3]), lever * fmax * (c[0] - c[1] + c[2] - c[3]),
            kmkf * fmax * (c[0] + c[1] - c[2] - c[3])]


def unmix(w):
    a, b, c, d = w[0] / fmax, w[1] / (lever * fmax), w[2] / (lever * fmax), w[3] / (kmkf * fmax)
    return [(a - b + c + d) / 4, (a + b - c + d) / 4, (a + b + c - d) / 4, (a - b - c - d) / 4]


def vf(x, u):
    T, tx, ty, tz = wrench(u)
    a = T / mass
    q1, q2, q3, q4 = x[6:10]
    wx, wy, wz = x[10:13]
    d = (2 * (q2 * q4 + q1 * q3), 2 * (q3 * q4 - q1 * q2), q1 * q1 - q2 * q2 - q3 * q3 + q4 * q4)
    return [x[3], x[4], x[5], -a * d[0], -a * d[1], g - a * d[2],
            (-q2 * wx - q3 * wy - q4 * wz) / 2, (q1 * wx + q3 * wz - q4 * wy) / 2,
            (q1 * wy - q2 * wz + q4 * wx) / 2, (q1 * wz + q2 * wy - q3 * wx) / 2,
            (tx - (wy * Jz * wz - wz * Jy * wy)) / Jx, (ty - (wz * Jx * wx - wx * Jz * wz)) / Jy,
            (tz - (wx * Jy * wy - wy * Jx * wx)) / Jz]


def step(x, u, t=h, n=400):
    dt = t / n
    for _ in range(n):
        k1 = vf(x, u)
        k2 = vf([a + dt / 2 * b for a, b in zip(x, k1)], u)
        k3 = vf([a + dt / 2 * b for a, b in zip(x, k2)], u)
        k4 = vf([a + dt * b for a, b in zip(x, k3)], u)
        x = [a + dt / 6 * (b + 2 * c + 2 * d + e) for a, b, c, d, e in zip(x, k1, k2, k3, k4)]
    return x


def rand_state(W=10.0, unit=True):
    q = [random.gauss(0, 1) for _ in range(4)]
    n = math.sqrt(sum(c * c for c in q)) if unit else 1.0
    return ([random.uniform(-5, 5) for _ in range(3)] + [random.uniform(-3, 3) for _ in range(3)] +
            [c / n for c in q] + [random.uniform(-W, W) for _ in range(3)])


def yawRot(c, s, x):
    C, S = c * c - s * s, 2 * c * s
    return [C * x[0] - S * x[1], S * x[0] + C * x[1], x[2], C * x[3] - S * x[4], S * x[3] + C * x[4], x[5],
            c * x[6] - s * x[9], c * x[7] - s * x[8], c * x[8] + s * x[7], c * x[9] + s * x[6], x[10], x[11], x[12]]


fails = []


def check(name, ok, info=""):
    if not ok:
        fails.append(f"{name}: {info}")


random.seed(1)
for trial in range(40):
    x = rand_state()
    u = [random.uniform(-0.2, 1.2) for _ in range(4)]
    w = [random.uniform(-0.2, 1.2) for _ in range(4)]
    # Actuators: unmix (wrench u) = clip u
    check("unmix_wrench", max(abs(a - clip(b)) for a, b in zip(unmix(wrench(u)), u)) < 1e-12)
    # Actuators: field Lipschitz in the input, Kin Q
    Q = sum(c * c for c in x[6:10])
    Kin = max(amax * Q, 2 * alphaMax)
    du = max(abs(a - b) for a, b in zip(u, w))
    dv = max(abs(a - b) for a, b in zip(vf(x, u), vf(x, w)))
    check("norm_vf_sub_input_le", dv <= Kin * du + 1e-9, f"{dv} > {Kin * du}")
    xs = step(x, u)
    a = wrench(u)[0] / mass
    # Period: velocity and position against free fall
    dvv = [xs[3] - x[3], xs[4] - x[4], xs[5] - x[5] - h * g]
    dpp = [xs[0] - x[0] - h * x[3], xs[1] - x[1] - h * x[4], xs[2] - x[2] - h * x[5] - h * h / 2 * g]
    check("step_v_dev_le", sum(c * c for c in dvv) <= (a * Q * h) ** 2 * (1 + 1e-9) + 1e-24, f"{dvv} vs {a * Q * h}")
    check("step_p_dev_le", sum(c * c for c in dpp) <= (a * Q * h * h / 2) ** 2 * (1 + 1e-9) + 1e-24)
    check("step_v_sub_le", all(abs(xs[3 + j] - x[3 + j]) <= (g + amax) * h + 1e-12 for j in range(3)))
    # Symmetry: yaw rotation equivariance of the field and the step
    psi = random.uniform(-math.pi, math.pi)
    c, s = math.cos(psi / 2), math.sin(psi / 2)
    e1 = max(abs(p - q) for p, q in zip(vf(yawRot(c, s, x), u), yawRot(c, s, vf(x, u))))
    check("vf_yawRot", e1 < 1e-9 * (1 + max(abs(v) for v in vf(x, u))), str(e1))
    e2 = max(abs(p - q) for p, q in zip(step(yawRot(c, s, x), u), yawRot(c, s, xs)))
    check("step_yawRot", e2 < 1e-9, str(e2))
    # Sensitivity: input error to state error, ‖step x u - step x w‖ ≤ Kin h e^{Kh} ‖u - w‖ (crude, K ≥ 0)
    ds = max(abs(p - q) for p, q in zip(xs, step(x, w)))
    check("norm_step_sub_input_le_mul (K = 0 lower bound)", ds <= Kin * h * math.exp(0) * du * 1.6,
          f"{ds} vs {Kin * h * du}")

# Exact: spin closed form
for trial in range(20):
    psi0 = random.uniform(-3, 3)
    x = [random.uniform(-1, 1) for _ in range(6)] + [math.cos(psi0 / 2), 0, 0, math.sin(psi0 / 2), 0, 0,
                                                      random.uniform(-5, 5)]
    c0 = random.uniform(0, 1)
    dz = random.uniform(-0.3, 0.3)
    u = [c0 + dz, c0 + dz, c0 - dz, c0 - dz]   # τx = τy = 0, τz ≠ 0 (clipped equally in pairs)
    T, tx, ty, tz = wrench(u)
    if abs(tx) > 1e-15 or abs(ty) > 1e-15:
        continue
    a = T / mass
    az = g - a * (x[6] ** 2 + x[9] ** 2)
    th = x[12] * h + tz / Jz * h * h / 2
    cf = [x[0] + h * x[3], x[1] + h * x[4], x[2] + h * x[5] + h * h / 2 * az, x[3], x[4], x[5] + h * az,
          x[6] * math.cos(th / 2) - x[9] * math.sin(th / 2), 0, 0, x[6] * math.sin(th / 2) + x[9] * math.cos(th / 2),
          0, 0, x[12] + h * tz / Jz]
    e = max(abs(p - q) for p, q in zip(step(x, u), cf))
    check("step_spin", e < 1e-10, str(e))

# Multi: level flight over n periods
x = [0, 0, -1, 0.2, -0.1, 0.3, 1, 0, 0, 0, 0, 0, 0]
cc = 0.4
y = x
for n in range(1, 41):
    y = step(y, [cc] * 4, n=40)
    vz = x[5] + n * h * (g - amax * cc)
    pz = x[2] + n * h * x[5] + (n * h) ** 2 / 2 * (g - amax * cc)
    check("stepN_level_vz", abs(y[5] - vz) < 1e-10, f"n={n} {y[5]} {vz}")
    check("stepN_level_pz", abs(y[2] - pz) < 1e-10, f"n={n} {y[2]} {pz}")

print("numcheck:", "all statements hold on the samples" if not fails else f"{len(fails)} failures")
for f in fails[:20]:
    print("  FAIL", f)
