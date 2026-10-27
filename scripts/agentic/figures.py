"""Figures for the agentic contract-delegation run (docs/figs/agentic/fig_shapes.pdf, fig_regions.pdf, fig_sweep.pdf).

Every shaded region is computed by evaluating a proposal's own functions (A1, G1, G2) on floats over a grid; the
targets come from the controller of scripts/vcore.py run on floats. Parameters are listed in notes/agentic-run/figures.md.

    .venv/bin/python scripts/agentic/figures.py
"""
import os, sys, importlib.util
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, os.path.join(ROOT, 'scripts', 'agentic'))
sys.path.insert(0, os.path.join(ROOT, 'scripts'))
from proposal import U, W, E, Ticks           # noqa: E402
from vcore import controller, Num, CTRL       # noqa: E402

FIG = os.path.join(ROOT, 'docs', 'figs', 'agentic')
os.environ.setdefault('B_RHO_NUM', '5'); os.environ.setdefault('B_RHO_DEN', '4')   # proposer B as kept: rho = 5/4

PROPS = [  # label, file, fence margin on (w1, w2) as written in its G1
    ('algorithm, $\\rho=1$', 'scripts/agentic/example_proposal.py', ('1', '1')),
    ('proposer A', 'notes/agentic-run/proposer-A/propA_r2.py', ('0', '1')),
    ('proposer B, $\\rho=5/4$', 'notes/agentic-run/proposer-B/propB.py', ('5/4', '5/4')),
    ('proposer C', 'notes/agentic-run/proposer-C/proposal_C1.py', ('0', '1')),
]


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, path))
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m


MODS = [load(p, 'prop%d' % i) for i, (_, p, _) in enumerate(PROPS)]


def setup_mpl():   # the style of docs/figs/validation (scripts/validate.py, setup_mpl)
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family': 'serif', 'font.serif': ['DejaVu Serif', 'Times New Roman', 'Times'],
                         'font.size': 8, 'axes.labelsize': 8, 'legend.fontsize': 7, 'xtick.labelsize': 7,
                         'ytick.labelsize': 7, 'axes.titlesize': 8,
                         'axes.prop_cycle': matplotlib.cycler(color=['0.0', '0.45', '0.7']),
                         'lines.linewidth': 1.0, 'pdf.fonttype': 42})
    return plt


plt = setup_mpl()
from matplotlib.patches import Rectangle, Circle            # noqa: E402
from mpl_toolkits.axes_grid1.inset_locator import mark_inset  # noqa: E402


def fence(ax, s, ls='-', lw=0.9, color='k', label=None):
    ax.add_patch(Rectangle((-s, -s), 2 * s, 2 * s, fill=False, ec=color, lw=lw, ls=ls, label=label))


def grid_mask(xs, ys, pred):
    M = np.zeros((len(ys), len(xs)), dtype=float)
    for i, yv in enumerate(ys):
        for j, xv in enumerate(xs):
            M[i, j] = 1.0 if pred((float(xv), float(yv))) else 0.0
    return M


# ------------------------------------------------------------------ figure 1: tube shapes
S1, H1, P01, W11, W21 = 50.0, (-40.0, -40.0), (-40.0, -40.0), (-30.0, 30.0), (40.0, 40.0)
DT1 = [1.0] * 8
STEP1 = 0.25


def tube_pred(mod, w, p0):
    """y in the tube part of G2: G2 on the two-tick run (y, w2) with every guard of P met (dt = 1). w2 lies in every
    tube and meets every reach part, so G2 holds iff y lies in the tube (the tube is the same at every tick)."""
    e = E(p0, Ticks(DT1, 'dts'))
    return lambda y: bool(mod.G2(w, e, Ticks([y, w.w2], 'y')))


def fig_shapes():
    ys = np.array(controller((W11[0], W11[1], W21[0], W21[1]), P01, DT1, Num()), dtype=float)
    th = next(t for t in range(len(ys)) if np.max(np.abs(ys[t] - np.array(W11))) < CTRL['R'])  # rest of leg 1 < R
    w = W(W11, W21)
    for mod in MODS:
        assert mod.A2(w) and mod.G1(U(S1, H1, W21), w), 'mission not admissible for %s' % mod.NAME
    xs = np.arange(-52, 52 + 1e-9, STEP1)
    fig, axs = plt.subplots(1, 4, figsize=(7, 2.15), sharey=True)
    poly = np.array([P01, W11, W21])
    for k, (ax, mod, (lab, _, (m1, m2))) in enumerate(zip(axs, MODS, PROPS)):
        M = grid_mask(xs, xs, tube_pred(mod, w, P01))
        ax.contourf(xs, xs, M, levels=[0.5, 1.5], colors=['0.78'])
        fence(ax, S1)
        ax.plot(poly[:, 0], poly[:, 1], '--', color='0.35', lw=0.7)
        ax.plot(ys[:, 0], ys[:, 1], 'k.-', ms=3.5, lw=0.5)
        ax.plot(ys[th, 0], ys[th, 1], 'ko', mfc='none', ms=7, mew=0.7)
        ax.annotate('handover $t=%d$' % th, ys[th], xytext=(ys[th, 0] + 3, ys[th, 1] - 14), fontsize=6,
                    arrowprops=dict(arrowstyle='-', lw=0.5, color='k'))
        for name, p, off in (('$p_0$', P01, (2, -7)), ('$w_1$', W11, (-14, 3.5)), ('$w_2$', W21, (-5, -9))):
            ax.annotate(name, p, xytext=(p[0] + off[0], p[1] + off[1]), fontsize=7)
        ax.set_aspect('equal'); ax.set_xlim(-55, 55); ax.set_ylim(-55, 55)
        ax.set_xticks([-50, 0, 50]); ax.set_yticks([-50, 0, 50])
        ax.set_xlabel('$x$ (m)')
        ax.set_title('%s\nmargin $w_1$: %s m, $w_2$: %s m' % (lab, m1, m2), fontsize=7)
    axs[0].set_ylabel('$y$ (m)')
    fig.tight_layout(w_pad=0.6)
    fig.savefig(os.path.join(FIG, 'fig_shapes.pdf')); plt.close(fig)
    return dict(targets=ys.tolist(), handover=th)


# ------------------------------------------------------------------ figure 2: admissible missions under G1
S2, H2, G2A, W12 = 50.0, (-40.0, -40.0), (50.0, 50.0), (-30.0, 30.0)     # panel (a): goal at the fence corner
G2B = (40.0, 40.0)                                                        # panel (b): u = (50, h, (40, 40)), w2 = g
STEP2 = 0.02
STY = [  # fill gray, outline style, per proposal (same order as PROPS)
    dict(fc='0.62', ls='-', lw=0.9),
    dict(fc='0.88', ls='--', lw=0.9),
    dict(fc='0.40', ls='-', lw=0.6),
    dict(fc='0.88', ls=':', lw=1.3),
]


def fig_regions():
    fig, axs = plt.subplots(1, 2, figsize=(7, 3.2))
    xa = np.arange(46.5, 50.9 + 1e-9, STEP2)
    xb = np.arange(-51.5, -43.5 + 1e-9, STEP2)
    panels = [
        (axs[0], xa, xa, lambda mod: (lambda p: bool(mod.G1(U(S2, H2, G2A), W(W12, p))))),
        (axs[1], xb, -xb[::-1], lambda mod: (lambda p: bool(mod.G1(U(S2, H2, G2B), W(p, G2B))))),
    ]
    areas = {}
    for pi, (ax, gx, gy, mk) in enumerate(panels):
        masks = [grid_mask(gx, gy, mk(mod)) for mod in MODS]
        areas[pi] = [float(M.sum() * STEP2 * STEP2) for M in masks]
        order = sorted(range(4), key=lambda k: -areas[pi][k])                  # largest first, nested fills
        for k in order:
            ax.contourf(gx, gy, masks[k], levels=[0.5, 1.5], colors=[STY[k]['fc']])
        for k in (0, 2, 1, 3):
            ax.contour(gx, gy, masks[k], levels=[0.5], colors='k', linewidths=STY[k]['lw'], linestyles=STY[k]['ls'])
        ax.set_aspect('equal')
    # panel (a)
    ax = axs[0]
    ax.axvline(S2, color='k', lw=1.4); ax.axhline(S2, color='k', lw=1.4)
    ax.plot(*G2A, 'k*', ms=8, mfc='white', mew=0.7, zorder=5)
    ax.annotate('goal $g$', G2A, xytext=(G2A[0] - 1.25, G2A[1] + 0.2), fontsize=7)
    ax.text(50.08, 46.6, 'fence', rotation=90, fontsize=7, va='bottom')
    ax.text(46.6, 46.75, 'A and C give the same set here', fontsize=6.5)
    ax.set_xlim(46.5, 50.9); ax.set_ylim(46.5, 50.9)
    ax.set_xlabel('$w_{2,x}$ (m)'); ax.set_ylabel('$w_{2,y}$ (m)')
    ax.set_title('(a) admissible $w_2$, $g=(50, 50)$, $w_1=(-30, 30)$')
    # panel (b)
    ax = axs[1]
    ax.axvline(-S2, color='k', lw=1.4); ax.axhline(S2, color='k', lw=1.4)
    ax.text(-50.15, 44.0, 'fence', rotation=90, fontsize=7, va='bottom', ha='right')
    ax.text(-49.9, 49.35, 'A and C', fontsize=6.5)
    ax.set_xlim(-51.5, -43.5); ax.set_ylim(43.5, 51.5)
    ax.set_xlabel('$w_{1,x}$ (m)'); ax.set_ylabel('$w_{1,y}$ (m)')
    ax.set_title('(b) admissible $w_1$ near a corner, $w_2=g=(40, 40)$')
    from matplotlib.patches import Patch
    hd = [Patch(fc=STY[k]['fc'], ec='k', lw=STY[k]['lw'], ls=STY[k]['ls'], label=PROPS[k][0]) for k in range(4)]
    fig.legend(handles=hd, loc='lower center', ncol=4, frameon=False, handlelength=2.4)
    fig.tight_layout(rect=(0, 0.07, 1, 1))
    fig.savefig(os.path.join(FIG, 'fig_regions.pdf')); plt.close(fig)
    return areas


# ------------------------------------------------------------------ figure 3: proposer B's margin sweep
TRIED = [(0.9, '9/10', 'D3 fail'), (1.0, '1', 'pass'), (1.25, '5/4', 'pass'), (1.2675, '507/400', 'pass'),
         (1.275, '51/40', 'R fail'), (1.3, '13/10', 'R fail')]
RHO_HI = 2.5 / np.sqrt(2) - 0.5          # sqrt(2) (1/2 + rho) <= 5/2


def fig_sweep():
    fig, axs = plt.subplots(1, 3, figsize=(7, 2.5), gridspec_kw=dict(width_ratios=[1.5, 1, 1]))
    ax = axs[0]
    ax.axvspan(1.0, 1.2675, color='0.85', lw=0)
    ax.axhline(0, color='k', lw=0.6)
    mk = {'pass': dict(marker='o', mfc='k', mec='k'), 'D3 fail': dict(marker='x', mfc='k', mec='k'),
          'R fail': dict(marker='s', mfc='white', mec='k')}
    stem = {0.9: (0.3, 'c'), 1.0: (0.3, 'r'), 1.25: (0.25, 'l'), 1.2675: (0.5, 'l'), 1.275: (0.72, 'r'), 1.3: (0.3, 'r')}
    for r, lab, v in TRIED:
        hgt, side = stem[r]
        ax.plot([r, r], [0, hgt], color='k', lw=0.5)
        ax.plot([r], [hgt], ls='none', ms=4.5, mew=0.9, **mk[v])
        if side == 'c':
            ax.text(r, hgt + 0.08, '%s\n%s' % (lab, v), ha='center', va='bottom', fontsize=6)
        else:
            dx = 0.012 if side == 'r' else -0.012
            ax.text(r + dx, hgt, '%s: %s' % (lab, v), ha='left' if side == 'r' else 'right', va='center', fontsize=6)
    ax.axvline(1.0, color='k', lw=0.6, ls='--'); ax.axvline(1.2675, color='k', lw=0.6, ls='--')
    ax.text(0.99, -0.35, 'below: box\nleaves fence', ha='right', va='center', fontsize=6.5)
    ax.text(1.277, -0.35, 'above: corner\ngoal has\nno mission', ha='left', va='center', fontsize=6.5)
    ax.text(1.134, 0.9, 'phase 1 passes', ha='center', fontsize=6.5)
    ax.set_xlim(0.8, 1.4); ax.set_ylim(-0.75, 1.05); ax.set_yticks([])
    for sp in ('left', 'right', 'top'): ax.spines[sp].set_visible(False)
    ax.set_xlabel('fence margin $\\rho$ of proposer B (m)')
    ax.set_title('(a) margin sweep')
    # (b) D3 counterexample at rho = 9/10
    ax = axs[1]
    s, rho, h, w1, w2, y0 = 26.0, 0.9, (-22.0, -22.0), (-25.0, 25.0625), (0.0, 0.0), (0.0, 26.0312)
    lo = [min(h[i], w1[i], w2[i]) - 1 for i in (0, 1)]; hi = [max(h[i], w1[i], w2[i]) + 1 for i in (0, 1)]

    def d3(a, inset):
        a.add_patch(Rectangle((lo[0], lo[1]), hi[0] - lo[0], hi[1] - lo[1], fc='0.85', ec='0.3', lw=0.6))
        fence(a, s, lw=1.0); fence(a, s - rho, ls='--', lw=0.6, color='0.3')
        P = np.array([h, w1, w2]); a.plot(P[:, 0], P[:, 1], 'k-', lw=0.6)
        a.plot(*y0, 'kx', ms=4 if not inset else 6, mew=0.9)
    d3(ax, False)
    ax.annotate('$p_0=h$', h, xytext=(h[0] + 1.5, h[1] + 3), fontsize=6.5)
    ax.annotate('$w_1$', w1, xytext=(w1[0] + 1.5, w1[1] - 4.5), fontsize=6.5)
    ax.annotate('$w_2=g$', w2, xytext=(w2[0] + 1.2, w2[1] + 1.2), fontsize=6.5)
    ax.set_aspect('equal'); ax.set_xlim(-29, 13); ax.set_ylim(-29, 29)
    ax.set_xlabel('$x$ (m)'); ax.set_ylabel('$y$ (m)')
    ax.set_title('(b) D3 fails, $\\rho=9/10$, $s=26$')
    ins = ax.inset_axes([0.5, 0.04, 0.48, 0.4])
    d3(ins, True)
    ins.set_xlim(-1.2, 1.4); ins.set_ylim(25.88, 26.12); ins.set_xticks([]); ins.set_yticks([])
    ins.tick_params(labelsize=5.5, length=2)
    ins.text(-1.1, 25.99, 'fence $s=26$', fontsize=5.5, va='top')
    ins.text(-1.1, 26.072, 'box top 26.06', fontsize=5.5, va='bottom')
    ins.text(0.25, 26.031, '$y_0$', fontsize=6, va='center')
    mark_inset(ax, ins, loc1=2, loc2=1, fc='none', ec='0.5', lw=0.4)
    # (c) R counterexample at rho = 51/40
    ax = axs[2]
    s, rho, g = 25.0, 1.275, (-25.4961, 25.5)
    c = s - rho; corner = (-c, c); dist = float(np.hypot(g[0] + c, g[1] - c))

    def rgeo(a):
        a.add_patch(Rectangle((-c, -c), 2 * c, 2 * c, fc='0.85', ec='0.3', lw=0.6, ls='--'))
        fence(a, s, lw=1.0)
        a.add_patch(Circle(g, 2.5, fill=False, ec='k', lw=0.8))
        a.plot(*g, 'k*', ms=6, mfc='white', mew=0.6); a.plot(*corner, 'k.', ms=3)
        a.plot([g[0], corner[0]], [g[1], corner[1]], ':', color='0.2', lw=0.7)
    rgeo(ax)
    ax.annotate('$g$', g, xytext=(g[0] - 1.6, g[1] + 0.5), fontsize=6.5)
    ax.text(-23.4, 21.2, '$|w_2|_\\infty\\leq s-\\rho$', fontsize=6)
    ax.text(-29.7, 28.6, 'disc $5/2$ around $g$', fontsize=6)
    ax.text(-24.85, 19.4, 'distance %.4f m' % dist, fontsize=5.5)
    ax.set_aspect('equal'); ax.set_xlim(-30, -19); ax.set_ylim(18.8, 29.8)
    ax.set_xlabel('$x$ (m)'); ax.set_ylabel('$y$ (m)')
    ax.set_title('(c) R fails, $\\rho=51/40$, $s=25$')
    ins = ax.inset_axes([0.6, 0.6, 0.38, 0.38])
    rgeo(ins)
    u = np.array([corner[0] - g[0], corner[1] - g[1]]); u /= np.linalg.norm(u)
    m = np.array(g) + u * 2.5035
    ins.set_xlim(m[0] - 0.012, m[0] + 0.012); ins.set_ylim(m[1] - 0.012, m[1] + 0.012)
    ins.set_xticks([]); ins.set_yticks([])
    ins.text(0.04, 0.84, 'gap %.4f m' % (dist - 2.5), transform=ins.transAxes, fontsize=5.5,
             bbox=dict(fc='white', ec='none', pad=0.5))
    mark_inset(ax, ins, loc1=3, loc2=4, fc='none', ec='0.5', lw=0.4)
    fig.tight_layout(w_pad=0.8)
    fig.savefig(os.path.join(FIG, 'fig_sweep.pdf')); plt.close(fig)
    return dict(rho_hi=float(RHO_HI), r_gap=dist - 2.5)


if __name__ == '__main__':
    os.makedirs(FIG, exist_ok=True)
    print('shapes', fig_shapes())
    print('regions (areas m^2, panel a / b, order of PROPS)', fig_regions())
    print('sweep', fig_sweep())
