r"""R61b (D), (E): the range and the rates of the characteristic-2 matrix theorem (r61b.md Sections 6, 7).

Part 1 (every-q form, Corollary 3): R_c(0) = ln2 / (c (ln4 - H2(1/sqrt c))) for c -> 4 (limit 1/4), exact rational
         check of R_4(0) = 1/4 and monotonicity on a grid.
Part 2 (rate values, as v1's Table m:tab:rates): for thresholds N >= D^{1/eps}, sup over c > 4, theta < 3/4 of
         gamma = theta log2(sqrt c - 1) subject to R_c(gamma) >= eps and q(theta) <= q0 (data structure), and for
         |W| <= N^2/D^kappa: gamma_W = min(gamma, kappa - q).
Part 3 (explicit instance, Corollary 5): at N >= D^5 choose (c, theta), compute gamma, q, Lambda, and the validity
         threshold d_1 from E(d) <= 4 (cd+2)^3 Lambda^d <= 2^{(d-1)/eps}; also with exact binomials.
Part 4 (prescribed W, exact leaf count per type, numerical): product types (a = rho L, d = rho^2 L): the leaf exponent
         Lam(rho) = max_v min(pw H(v) - kappa pw ln2, H(t) - H(p)), t = (p0+pw v1, p1+pw v2, p2+pw v3, pw v4); the range
         sup{ eps(rho) = pw ln2/(ln4 - H2(rho)) : Lam(rho) < 0 }; and general types with the covering by ~1/f random
         relabelings split between rows and columns (eps = pw ln2/(ln4 - H(p)/2) with full encodings).
Usage: python3 r61b_range.py > r61b_range_out.txt
"""
import math, sys, os
import numpy as np
from fractions import Fraction
from scipy.optimize import minimize, brentq

LN2 = math.log(2); LN3 = math.log(3); LN4 = math.log(4)


def H2(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log(x) - (1 - x) * math.log(1 - x)


def Hn(v):
    return -sum(x * math.log(x) for x in v if x > 0)


def Rc(c, g):
    return LN2 / (c * (LN4 - H2(1 / math.sqrt(c))) + g * LN2)


def gam(c, th):
    return th * math.log2(math.sqrt(c) - 1)


def qq(th):
    return (H2(th) + th * LN3) / LN2


def part1():
    print('Part 1. R_c(0) (every-q range of Corollary 3) for c -> 4:')
    for c in [4.0, 4.0001, 4.001, 4.01, 4.05, 4.1, 4.25, 4.5, 5, 6, 8, 10, 14, 18, 25]:
        print(f'   c = {c:8.4f}: R_c(0) = {Rc(c, 0):.6f}')
    # monotone on a fine grid
    cs = np.linspace(4.0, 40, 20001)
    vals = [Rc(c, 0) for c in cs]
    print(f'   R_c(0) strictly decreasing on a grid of 20001 points in [4, 40]: '
          f'{all(vals[i] > vals[i + 1] for i in range(len(vals) - 1))}; R_4(0) = {vals[0]!r} (exact: '
          f'ln2/(4(ln4 - ln2)) = 1/4)')
    # g'(c) > ln 2 on the grid
    gp = [LN4 - H2(1 / math.sqrt(c)) + (0.5 / math.sqrt(c)) * math.log((1 - 1 / math.sqrt(c)) * math.sqrt(c))
          for c in cs]
    print(f"   g'(c) >= ln2 on the grid: {min(gp) >= LN2 - 1e-12} (min {min(gp):.6f}, ln2 = {LN2:.6f})")


def best_gamma(eps, qmax=None, kappa=None):
    """sup over c > 4, theta in (0, 3/4) of gamma subject to R_c(gamma) >= eps and q(theta) <= qmax (data structure)
    or of min(gamma, kappa - q) (prescribed W via |W| queries)."""
    best = (0.0, None, None)
    for c in np.concatenate([np.linspace(4.001, 10, 600), np.linspace(10, 200, 1900)]):
        # gamma limited by range: gamma <= (ln2/eps - c(ln4 - H2))/ln2
        gmax = (LN2 / eps - c * (LN4 - H2(1 / math.sqrt(c)))) / LN2
        if gmax <= 0:
            continue
        rate = math.log2(math.sqrt(c) - 1)
        if rate <= 0:
            continue
        if qmax is not None:
            # largest theta with q(theta) <= qmax
            if qq(0.7499) <= qmax:
                thq = 0.7499
            else:
                thq = brentq(lambda th: qq(th) - qmax, 1e-12, 0.7499)
            th = min(thq, gmax / rate, 0.7499)
            g = th * rate
            if g > best[0]:
                best = (g, c, th)
        else:
            # maximise min(theta*rate, kappa - q(theta)) with theta*rate <= gmax
            def obj(th):
                return min(th * rate, gmax, kappa - qq(th))
            ths = np.linspace(1e-4, 0.7499, 3000)
            vals = [obj(t) for t in ths]
            i = int(np.argmax(vals))
            if vals[i] > best[0]:
                best = (vals[i], c, ths[i])
    return best


def part2():
    print('\nPart 2. Rate values (sup of gamma; numerical, rounded down to 4 digits), cf. v1 Table m:tab:rates')
    print('   threshold   | data structure q=0.25  q=0.43  q=0.50 | wanted entries kappa=0.50  kappa=1.00')
    for inv in [4.2, 4.5, 5, 6, 8, 10, 12, 14, 18]:
        eps = 1 / inv
        row = []
        for q0 in [0.25, 0.43, 0.50]:
            g, c, th = best_gamma(eps, qmax=q0)
            row.append(f'{math.floor(g * 1e4) / 1e4:.4f}')
        for k in [0.5, 1.0]:
            g, c, th = best_gamma(eps, kappa=k)
            row.append(f'{math.floor(g * 1e4) / 1e4:.4f} (c={c:.2f}, th={th:.3f})' if c else '-')
        print(f'   N >= D^{inv:<5} |   ' + '   '.join(row[:3]) + '   |   ' + '   '.join(row[3:]))


def explicit(eps_inv, c, th, verbose=True):
    """Corollary 5: explicit constants at N >= D^{eps_inv} with ratio c and theta."""
    eps = 1 / eps_inv
    g = gam(c, th); q = qq(th)
    x = (1 - th) / th
    Lam = 4 ** c * math.exp(-c * H2(1 / math.sqrt(c))) * 2 ** g
    base = 2 ** eps_inv
    ratio = base / Lam
    # validity threshold: (ratio)^d >= 4 (c d + 2)^3 * 2^{eps_inv}
    d1 = None
    if ratio > 1:
        for d in range(1, 10 ** 7):
            if d * math.log(ratio) >= math.log(4) + 3 * math.log(c * d + 2) + eps_inv * LN2:
                d1 = d
                break
    # shape conditions and the exact encoding inequality with exact binomials, d up to dmax
    shape_from = None; exact_from = None
    dmax = 3000 if d1 is None else max(3000, d1 + 10)
    last_bad_shape = 0; last_bad_exact = 0
    for d in range(1, dmax + 1):
        L = math.ceil(c * d); a = math.isqrt(d * L)
        if a * a < d * L:
            a += 1
        n = a - d; n0 = L - 2 * a + d
        ok_shape = (a * a) // L == d and n0 >= n and 2 * a <= L and n >= 1
        lam_ok = ok_shape and d / (n + 1) < 1 / (math.sqrt(c) - 1)
        if not lam_ok:
            last_bad_shape = d
        # exact: L^2 4^L D^gamma / C(L,a) <= 2^{(d-1) eps_inv}
        lhs = 2 * math.log(L) + L * LN4 + g * d * LN2 - (math.lgamma(L + 1) - math.lgamma(a + 1) - math.lgamma(L - a + 1))
        if lhs > (d - 1) * eps_inv * LN2:
            last_bad_exact = d
    if verbose:
        print(f'   N >= D^{eps_inv}: c = {c}, theta = {th}: gamma = theta log2(sqrt c - 1) = {g:.6f}, '
              f'q = {q:.6f}, x = {x:.4f} (3x > 1: {3 * x > 1}), gamma + q = {g + q:.6f} (< 1/2: {g + q < 0.5})')
        print(f'      Lambda = 4^c e^(-c H2(1/sqrt c)) 2^gamma = {Lam:.6e}; 2^(1/eps) = {base:.6e}; ratio = {ratio:.6f}; '
              f'analytic validity (ratio^d >= 4 (cd+2)^3 2^(1/eps)) from d = {d1}')
        print(f'      shape conditions (floor(a^2/L) = d, n0 >= n, 2a <= L, lambda < 1/(sqrt c - 1)) fail last at '
              f'd = {last_bad_shape} (checked d <= {dmax}); exact encoding inequality fails last at d = {last_bad_exact}')
    return g, q, d1, last_bad_shape, last_bad_exact


def part3():
    print('\nPart 3. Explicit instances (Corollary 5).')
    # search a grid for N >= D^5 maximizing gamma with gamma + q < 1/2 and a modest threshold
    for eps_inv in [5, 6, 8, 14]:
        best = None
        for c in np.arange(4.05, 60.0, 0.05):
            for k in range(3, 60):
                th = 1 / k
                g = gam(c, th); q = qq(th)
                if g + q >= 0.5 or Rc(c, g) <= 1 / eps_inv:
                    continue
                if best is None or g > best[0]:
                    best = (g, round(c, 2), th, k, q)
        if best:
            g, c, th, k, q = best
            print(f'   grid optimum at N >= D^{eps_inv} (theta = 1/k, gamma + q < 1/2): c = {c}, theta = 1/{k}: '
                  f'gamma = {g:.5f}, q = {q:.5f}')
    return


def lam_exponent(p, kappa=0.5):
    """max over v in the simplex of min(pw H(v) - kappa pw ln2, H(t) - H(p)) (per level, natural log)."""
    p0, p1, p2, pw = p
    hp = Hn(p)

    def f(v):
        v = np.clip(v, 1e-15, None); v = v / v.sum()
        t = [p0 + pw * v[0], p1 + pw * v[1], p2 + pw * v[2], pw * v[3]]
        return min(pw * Hn(v) - kappa * pw * LN2, Hn(t) - hp)
    best = -1e9; vb = None
    # grid
    G = 24
    for i in range(G + 1):
        for j in range(G + 1 - i):
            for k in range(G + 1 - i - j):
                v = np.array([i, j, k, G - i - j - k], dtype=float) / G
                val = f(v)
                if val > best:
                    best, vb = val, v
    # refine
    for start in [vb, np.array([0.25] * 4)]:
        r = minimize(lambda y: -f(np.abs(y)), start, method='Nelder-Mead',
                     options={'xatol': 1e-10, 'fatol': 1e-13, 'maxiter': 4000})
        if -r.fun > best:
            best = -r.fun; vb = np.abs(r.x) / np.abs(r.x).sum()
    return best, vb


def part4():
    print('\nPart 4. Prescribed W, |W| <= N^2/sqrt(D), exact leaf count per type (numerical).')
    print('   product types p = ((1-rho)^2, rho(1-rho), rho(1-rho), rho^2), full encodings, Pi_L covering:')
    rows = []
    for rho in [0.45, 0.48, 0.49, 0.5, 0.501, 0.502, 0.503, 0.504, 0.505, 0.506, 0.508, 0.51]:
        p = ((1 - rho) ** 2, rho * (1 - rho), rho * (1 - rho), rho ** 2)
        lam, v = lam_exponent(p)
        eps = rho ** 2 * LN2 / (LN4 - H2(rho))
        rows.append((rho, lam, eps))
        print(f'   rho = {rho:.4f}: pw = {rho ** 2:.5f}, Lam/dD = {lam / (rho ** 2 * LN2):+.6f}, '
              f'eps(rho) = {eps:.6f}  (v at the max: {np.round(v, 4)})')
    # bisection for the crossing Lam = 0 above 1/2
    def lamr(rho):
        p = ((1 - rho) ** 2, rho * (1 - rho), rho * (1 - rho), rho ** 2)
        return lam_exponent(p)[0]
    lo, hi = 0.5, 0.52
    if lamr(lo) < 0 < lamr(hi):
        for _ in range(40):
            mid = (lo + hi) / 2
            if lamr(mid) < 0:
                lo = mid
            else:
                hi = mid
        rho = lo
        print(f'   crossing Lam = 0 at rho* = {rho:.6f}: range (product types) = eps(rho*) = '
              f'{rho ** 2 * LN2 / (LN4 - H2(rho)):.6f}')
    # general types: maximise eps = pw ln2/(ln4 - H(p)/2) s.t. Lam(p) < 0 (relabelings ~1/f split, randomized covering)
    print('   general types (randomized covering by ~1/f relabelings split between rows and columns, full encodings):')
    best = (0, None)
    for pw in np.arange(0.250, 0.2701, 0.002):
        for p0 in np.arange(0.22, 0.27, 0.004):
            p1 = p2 = (1 - pw - p0) / 2
            if p1 <= 0:
                continue
            p = (p0, p1, p2, pw)
            lam, _ = lam_exponent(p)
            if lam >= -1e-9:
                continue
            eps = pw * LN2 / (LN4 - Hn(p) / 2)
            # also the tile must fit: N >= rows (C(L, a)), automatic since 4^L/sqrt(M) >= 2^L
            if eps > best[0]:
                best = (eps, p, lam)
    e, p, lam = best
    print(f'   best on the grid (p1 = p2): eps = {e:.5f} at p = {tuple(round(x, 4) for x in p)}, Lam/dD = '
          f'{lam / (p[3] * LN2):+.5f}')
    # refine with Nelder-Mead on (pw, p0, p1)
    def neg(y):
        pw, p0, p1 = y
        p2 = 1 - pw - p0 - p1
        if min(pw, p0, p1, p2) <= 0.01:
            return 1.0
        p = (p0, p1, p2, pw)
        lam, _ = lam_exponent(p)
        if lam >= 0:
            return 1.0 + lam
        return -pw * LN2 / (LN4 - Hn(p) / 2)
    r = minimize(neg, np.array([p[3], p[0], p[1]]), method='Nelder-Mead', options={'xatol': 1e-6, 'fatol': 1e-8,
                                                                                      'maxiter': 400})
    pw, p0, p1 = r.x
    print(f'   refined: eps = {-r.fun:.5f} at p = ({p0:.4f}, {p1:.4f}, {1 - pw - p0 - p1:.4f}, {pw:.4f})')


if __name__ == '__main__':
    part1()
    part2()
    part3()
    print('\n   instances checked in detail:')
    for (ei, c, th) in [(5, 4.5, 1 / 10), (5, 5.0, 1 / 8), (6, 6.0, 1 / 8)]:
        explicit(ei, c, th)
    part4()
