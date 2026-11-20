"""R211b (2026-11-18): the gamma(eps) curve CP would print, recomputed and certified independently.

(A) floating-point optimisation (numerical; chooses parameters only):
    products CW(6/7) x G(c) (Theorem D_x, r117b.md:342-350, f_dir = 0), level-1 envelope over consecutive pairs
    (Theorem D, x -> infinity), pure tile (f_G = 1, = v1's exact-count curve per r117.md:176-179), the crossing of
    the level-1 envelope with the pure tile (R74(e)'s 0.171511), the crossover products vs pure tile (R117's ~0.134).
(B) certification of the chosen points at rational parameters with r211b_lib (interval arithmetic).
Run: nice -n 19 ~/.venv/bin/python3 r211b_curve.py > r211b_curve_out.txt
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import minimize, brentq, minimize_scalar
import r211b_lib as L
from r211b_lib import I, ln

W = lambda s: (sys.stdout.write(s), sys.stdout.flush())
LN4 = math.log(4)


# ---------------------------------------------------------------- float profile functions (parameter choice only)
_gc = {}


def Gf(q, t):
    key = (q, round(t, 15))
    if key in _gc:
        return _gc[key]
    pi = 1.0 / (q + 2); lq = math.log(q)
    z = np.array([0.55 * t, 0.52 * t, 0.06 * t * t])

    def F(z):
        u, v, y = z
        a = q * pi - u + v; b = pi + u; o = pi - v; w = q * pi - u + y
        ph = lambda s: s * math.log(s)
        D = ph(a) - a * math.log(q * pi) + ph(b) - b * math.log(pi) + ph(o) - o * math.log(pi)
        sg = ph(b) - ph(pi) - ph(y) - ph(u - y) + (u - y) * lq + ph(a) - ph(v - y) - ph(w)
        return -D + t * sg

    def feas(z):
        u, v, y = z
        return 0 < y < v < pi and y < u and u - y < q * pi

    for _ in range(100):
        u, v, y = z
        a = q * pi - u + v; b = pi + u; o = pi - v; w = q * pi - u + y
        dp = lambda s: math.log(s) + 1
        g = np.array([-(math.log(b) - math.log(a) + lq) + t * (dp(b) - dp(u - y) + lq - dp(a) + dp(w)),
                      -(math.log(a) - math.log(o) - lq) + t * (dp(a) - dp(v - y)),
                      t * (-dp(y) + dp(u - y) - lq + dp(v - y) - dp(w))])
        H = np.array([[-(1 / a + 1 / b) + t * (1 / b + 1 / a - 1 / (u - y) - 1 / w), (1 - t) / a, t * (1 / (u - y) + 1 / w)],
                      [(1 - t) / a, -(1 / a + 1 / o) + t * (1 / a - 1 / (v - y)), t / (v - y)],
                      [t * (1 / (u - y) + 1 / w), t / (v - y), t * (-1 / y - 1 / (u - y) - 1 / (v - y) - 1 / w)]])
        d = np.linalg.solve(H, -g)
        st = 1.0
        f0 = F(z)
        while st > 1e-12:
            zn = z + st * d
            if feas(zn) and F(zn) >= f0 - 1e-17:
                break
            st /= 2
        z = zn
        if np.linalg.norm(st * d) < 1e-15 * max(1.0, np.linalg.norm(z)):
            break
    val = F(z)
    _gc[key] = val
    return val


def LGf(t, c):
    d = lambda x: LN4 + math.log(1 - x) - (1 - t) * math.log(c - 1 + x) - t * math.log(x)
    x0 = brentq(d, 1e-300, 1 - 1e-16, xtol=1e-300, rtol=1e-15)
    ph = lambda s: 0.0 if s <= 0 else s * math.log(s)
    val = x0 * LN4 - ph(1 - x0) - (1 - t) * ph(c - 1 + x0) + (1 - t) * ph(c - 1) - t * ph(x0)
    return 2 * val / LN4


def Af(c):
    return (2 * c * math.log(5) - (c * math.log(c) - (c - 1) * math.log(c - 1) + (c - 1) * LN4)) / LN4


def pointf(parts):
    lna = sum(l * (q / (2 * (q + 2))) * math.log(q) for q, l, f in parts)
    lnb = sum(l * (f / (q + 2)) * math.log(q) for q, l, f in parts)
    return lna, lnb


# ---------------------------------------------------------------- (A1) products, fixed CW point
CW = [(6, Fr(181, 1000), Fr(999999, 10 ** 6)), (7, Fr(819, 1000), Fr(999999, 10 ** 6))]
CWf = [(q, float(l), float(f)) for q, l, f in CW]
LNA, LNB = pointf(CWf)
ALPHA = LNB / LNA


def LCWf(t):
    return sum(l * Gf(q, t) for q, l, f in CWf) / LNB


def prod_gamma(eps, c, t):
    """best f for fixed (c, t); returns (gamma, f)"""
    if not (1 < c < 40 and 0 < t < 0.3):
        return -1, None
    Lc, Lg, ag, ac = LCWf(t), LGf(t, c), Af(c), 1 / ALPHA
    Q = lambda f: t / 2 - (1 - f) * Lc - f * Lg
    E = lambda f: 1 / eps - (1 - f) * ac - f * ag
    cand = [0.0, 1.0]
    den = (Lc - Lg) + (ag - ac)
    if den != 0:
        fs = (1 / eps - ac - t / 2 + Lc) / den
        if 0 < fs < 1:
            cand.append(fs)
    best = max(((min(Q(f), E(f)), f) for f in cand))
    return best


def prod_opt(eps, starts=((5.8, 0.04), (6.2, 0.065), (5.5, 0.022))):
    best = (-1, None)
    for c0, t0 in starts:
        if True:
            r = minimize(lambda p: -prod_gamma(eps, p[0], p[1])[0], [c0, t0], method='Nelder-Mead',
                         options=dict(xatol=1e-9, fatol=1e-13, maxiter=600))
            g, f = prod_gamma(eps, r.x[0], r.x[1])
            if g > best[0]:
                best = (g, (r.x[0], r.x[1], f))
    return best


def tile_opt(eps):
    def g(p):
        c, t = p
        if not (1 < c < 40 and 0 < t <= 1):
            return -1
        return min(t / 2 - LGf(t, c), 1 / eps - Af(c))
    best = (-1, None)
    for c0, t0 in ((5.0, 0.025), (6.0, 0.1)):
        if True:
            r = minimize(lambda p: -g(p), [c0, t0], method='Nelder-Mead', options=dict(xatol=1e-10, fatol=1e-14, maxiter=800))
            if -r.fun > best[0]:
                best = (-r.fun, tuple(r.x))
    return best


# ---------------------------------------------------------------- (A2) level-1 envelope over consecutive pairs (x = infinity)
def level1_pair(eps, q1, q2):
    FW = 0.999999

    def val(p):
        lam, t = p
        if not (0 <= lam <= 1 and 0 < t < 0.3):
            return -1
        parts = [(q1, lam, FW), (q2, 1 - lam, FW)]
        lna, lnb = pointf(parts)
        gi = t / 2 - (lam * Gf(q1, t) + (1 - lam) * Gf(q2, t)) / lnb
        return min(gi, 1 / eps - lna / lnb)
    best = (-1, None)
    for l0 in (0.3, 0.8):
        r = minimize(lambda p: -val(p), [l0, 0.022], method='Nelder-Mead', options=dict(xatol=1e-10, fatol=1e-14, maxiter=600))
        if -r.fun > best[0]:
            best = (-r.fun, tuple(r.x))
    return best


def level1_env(eps):
    return max((level1_pair(eps, q, q + 1) + ((q, q + 1),) for q in (10, 11, 12)), key=lambda z: z[0])


# ---------------------------------------------------------------- (B) certification
def cert_product(eps_target, c, t, f, lam6=Fr(181, 1000)):
    parts = [(6, lam6, Fr(999999, 10 ** 6)), (7, 1 - lam6, Fr(999999, 10 ** 6))]
    P = L.point(parts)
    assert P['slack'].lo > 0
    assert Fr(t) <= (P['cbar'] + 2).inv().lo
    tot = I(0)
    for q, lam, _ in parts:
        b, F, g, z0 = L.Gq_auto(q, t)
        tot = tot + I(b) * lam
    LamCW = tot / P['lnb']
    LG, x0 = L.LamG_auto(t, c)
    Ac = L.A_iv(c) / ln(4)
    Qc = I(Fr(t) / 2) - LamCW * (1 - f) - LG * f
    amix = P['alpha'].inv() * (1 - f) + Ac * f
    e1 = (amix + I(Qc.lo)).inv().lo
    return Qc.lo, e1, P


def cert_tile(c, t):
    LG, x0 = L.LamG_auto(t, c)
    Ac = L.A_iv(c) / ln(4)
    Qc = I(Fr(t) / 2) - LG
    e1 = (Ac + I(Qc.lo)).inv().lo
    return Qc.lo, e1


def cert_level1(parts, t):
    P = L.point(parts)
    assert P['slack'].lo > 0 and Fr(t) <= (P['cbar'] + 2).inv().lo
    tot = I(0)
    for q, lam, _ in parts:
        b, F, g, z0 = L.Gq_auto(q, t)
        tot = tot + I(b) * lam
    gam = I(Fr(t) / 2) - tot / P['lnb']
    e1 = (P['alpha'].inv() + I(gam.lo)).inv().lo
    return gam.lo, e1, P, tot / P['lna']


def cert_level1_x(parts, t, x, eps):
    """Theorem D with finite x (r59-theorem-level1.md:253-258): gamma < min{Q(x), E(x)}, eps < (1+alpha x)/(1+x)"""
    gl, e1, P, Lam = cert_level1(parts, t)
    a = P['alpha']; x = Fr(x); t = Fr(t)
    Qx = (a * (t * x / 2) + t / 2 - Lam * x - 1) / (a * x + 1)
    Ex = I(1 / Fr(eps)) - (I(1 + x) / (a * x + 1))
    rng = ((a * x + 1) / (1 + x)).lo
    return Qx.lo, Ex.lo, rng


def rnd(x, k):
    return Fr(round(x * 10 ** k), 10 ** k)


def fdown(x, k):
    return Fr(math.floor(x * 10 ** k), 10 ** k)


def sig(x, n):
    e = math.floor(math.log10(abs(x)))
    return Fr(round(x / 10 ** (e - n + 1))) * Fr(10) ** (e - n + 1)


def dn(x, d):
    x = Fr(x)
    n = (x.numerator * 10 ** d) // x.denominator
    return f"{n // 10 ** d}.{n % 10 ** d:0{d}d}"


def main():
    W(f"CW point of the products: lam6 = 181/1000, u_q(q+2) = 999999/1000000; alpha (float) = {ALPHA:.7f}\n")
    P = L.point(CW)
    W(f"  certified: slack in [{float(P['slack'].lo):.4e}, {float(P['slack'].hi):.4e}], alpha in [{dn(P['alpha'].lo, 10)}, ...]\n")

    W("\n(1) crossing of the level-1 envelope (pairs (q, q+1), q = 9..13, x = infinity) with the pure tile (numerical)\n")
    for eps in (0.170, 0.171, 0.1715, 0.172, 0.173):
        e1, t1 = level1_env(eps), tile_opt(eps)
        W(f"  eps {eps}: level-1 env {e1[0]:.6e} (pair {e1[2]}, lam {e1[1][0]:.4f}, t {e1[1][1]:.5f});  "
          f"pure tile {t1[0]:.6e} (c {t1[1][0]:.5f}, t {t1[1][1]:.5f})\n")
    lo, hi = 0.170, 0.173
    for _ in range(16):
        mid = (lo + hi) / 2
        if tile_opt(mid)[0] > level1_env(mid)[0]:
            lo = mid
        else:
            hi = mid
    ec = (lo + hi) / 2
    e1, t1 = level1_env(ec), tile_opt(ec)
    W(f"  crossing eps = {ec:.6f}: level-1 {e1[0]:.6e} (pair {e1[2]}, lam {e1[1][0]:.4f}, t {e1[1][1]:.5f}), "
      f"tile {t1[0]:.6e} (c {t1[1][0]:.5f}, t {t1[1][1]:.5f})\n")
    # certified values at eps = 0.171511 on both sides
    W("  certified at eps = 0.171511:\n")
    E0 = Fr(171511, 10 ** 6)
    e1 = level1_env(0.171511)
    (q1, q2) = e1[2]
    lam = fdown(e1[1][0], 3)
    parts = [(q1, lam, Fr(999999, 10 ** 6)), (q2, 1 - lam, Fr(999999, 10 ** 6))]
    gl, ee, Pp, _ = cert_level1(parts, sig(e1[1][1], 4))
    W(f"    level-1, pair {q1}/{q2}, lam_{q1} = {lam}, t = {sig(e1[1][1], 4)}: Hyp(eps, gamma) for gamma < {dn(gl, 10)} "
      f"and eps <= {dn(ee, 7)}  (alpha {dn(Pp['alpha'].lo, 7)})\n")
    t1 = tile_opt(0.171511)
    cr, tr = rnd(t1[1][0], 4), sig(t1[1][1], 4)
    gq, ee2 = cert_tile(cr, tr)
    W(f"    pure tile, c = {cr}, t = {tr}: Hyp(eps, gamma) for gamma < {dn(gq, 10)} and eps < {dn(ee2, 7)}\n")

    W("\n(2) products vs pure tile, crossover (numerical)\n")
    for eps in (0.125, 0.13, 0.1325, 0.135, 0.14, 0.145):
        pg, pt = prod_opt(eps), tile_opt(eps)
        W(f"  eps {eps}: products {pg[0]:.6e} (c {pg[1][0]:.4f}, t {pg[1][1]:.5f}, f_G {pg[1][2]:.4f}); pure tile {pt[0]:.6e}; "
          f"ratio {pg[0] / pt[0]:.5f}\n")

    W("\n(3) products CW(6/7, lam6 181/1000) x G(c): optimum (numerical) and certified point at rational parameters\n")
    W("  eps | numerical gamma (c, t, f_G) | certified: c, t, f_G | gamma below | for every eps < | eps*gamma\n")
    rows = []
    for eps in (0.14, 0.15, 0.16, 0.17, 0.1715, 0.172, 0.175, 0.18, 0.19, 0.20, 0.21, 0.22, 0.23, 0.24, 0.25, 0.26,
                0.27, 0.28, 0.29):
        g, (c, t, f) = prod_opt(eps)
        cr, tr = rnd(c, 3), sig(t, 4)
        # f from the certified-side formula with the rounded (c, t), rounded down to 4 digits
        Lc, Lg, ag, ac = LCWf(float(tr)), LGf(float(tr), float(cr)), Af(float(cr)), 1 / ALPHA
        den = (Lc - Lg) + (ag - ac)
        fs = (1 / eps - ac - float(tr) / 2 + Lc) / den
        fr = fdown(min(max(fs, 0), 1), 4)
        qlo, e1, _ = cert_product(eps, cr, tr, fr)
        while e1 < Fr(eps).limit_denominator(10 ** 6) and fr > 0:
            fr -= Fr(1, 10 ** 4)
            qlo, e1, _ = cert_product(eps, cr, tr, fr)
        rows.append((eps, qlo, e1))
        W(f"  {eps} | {g:.6e} ({c:.4f}, {t:.5f}, {f:.4f}) | {cr}, {tr}, {fr} | {dn(qlo, 9)} | {dn(e1, 7)} | {dn(qlo * e1, 7)}\n")

    W("\n(4) level-1 near the range end at P0 (Theorem D, finite x)\n")
    P0 = [(6, Fr(7, 19), Fr(97, 100)), (7, Fr(12, 19), Fr(979, 1000))]
    for eps, x, t in ((Fr(2945, 10 ** 4), 5000, Fr(196, 10 ** 4)), (Fr(295, 1000), 1400, Fr(196, 10 ** 4)),
                      (Fr(2952, 10 ** 4), 1100, Fr(196, 10 ** 4)), (Fr(2954, 10 ** 4), 870, Fr(196, 10 ** 4))):
        Qx, Ex, rng = cert_level1_x(P0, t, x, eps)
        ok = Fr(eps) < rng and min(Qx, Ex) > 0
        W(f"  eps = {float(eps)}, x = {x}, t = {t}: Q(x) >= {dn(Qx, 9) if Qx > 0 else float(Qx)}, E(x) >= {dn(Ex, 9) if Ex > 0 else float(Ex)}, "
          f"range (1+alpha x)/(1+x) >= {dn(rng, 7)}; {'Hyp(eps, gamma) for gamma < ' + dn(min(Qx, Ex), 9) if ok else 'no certificate'}\n")
    W("\nDONE\n")


if __name__ == "__main__":
    main()
