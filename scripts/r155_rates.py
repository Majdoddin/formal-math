r"""R155 (task 2): rates eps*gamma of the exact-leaf-count algorithm (prescribed W, |W| <= N^2/sqrt D) for T4 + P3 in
characteristic 2 with PRUNED band encodings (numerical optima of proved bounds; r155-pruned-enc.md Section 2).

Per level (natural logs), type p = (p0, p1, p2, pw), rows of size (p2 + pw)L, columns (p1 + pw)L:
  gamma = -Lam(p)/(pw ln2)                                  (exact leaf count, r61b.md 6.2; r150d_rates.Lam)
  E_L, E_R = max(E_side, reading) per side                  (E_side: dual of r155_lib; = H(p) when B_side <= 1)
  product type, deterministic covering Pi_L (columns relabeled by L(L-1) permutations):
      rate = max(E_L, E_R) - H2(r)
  general type, unsplit covering (one side relabeled by ceil(2 d ln2 / f) independent permutations):
      rate = min( max(E_L - H2r, E_R + H2r - H),  max(E_R - H2c, E_L + H2c - H) )
  general type, split covering (Lemma S: T = d blocks, K_r K_c >= 4/f per block, balance xi):
      rate = min_{|xi| <= X} max(E_L + (H2c - H2r - H)/2 + xi, E_R + (H2r - H2c - H)/2 - xi),  X = (H2r + H2c - H)/2
  1/eps = rate/(pw ln2) + gamma.   With full encodings E_L = E_R = ln 4.
  Side condition for the randomized coverings (scanning for a covering relabeling):  ln(1/f)/L < (1/2 - gamma) pw ln2.
Usage: python3 r155_rates.py > r155_rates_out.txt
"""
import math
import sys
import time
import numpy as np
from scipy.optimize import minimize, minimize_scalar
import r150d_rates as R
import r155_lib as Lb

LN2, LN4 = math.log(2), math.log(4)
_EC = {}
_GC = {}


def B_side(p, side):
    p0, p1, p2, pw = p
    if side == 'left':
        return max(p0, p1, pw) + max(p0, p2) + p1
    return max(p0, p2, pw) + max(p1, pw) + p2


def E_side(p, side):
    key = (tuple(round(float(x), 12) for x in p), side)
    if key not in _EC:
        if p[3] <= min(p[:3]) and B_side(p, side) <= 1:
            v = R.Hn(p)                      # Proposition 1.5 (needs pw <= min(p0, p1, p2)): E_side = H(p)
        else:
            v = Lb.side_dual(p, side)[0]
        _EC[key] = max(v, Lb.reading_exponent(p, side))
    return _EC[key]


def gamma_leaf(p):
    key = tuple(round(float(x), 12) for x in p)
    if key not in _GC:
        _GC[key] = R.gamma_leaf(p)
    return _GC[key]


def rate_enc(p, cover, pruned):
    p0, p1, p2, pw = p
    H = R.Hn(p)
    h2r, h2c = R.H2(p2 + pw), R.H2(p1 + pw)
    if pruned:
        EL, ER = E_side(p, 'left'), E_side(p, 'right')
    else:
        EL = ER = LN4
    if cover == 'product':
        return max(EL, ER) - h2r
    if cover == 'unsplit':
        return min(max(EL - h2r, ER + h2r - H), max(ER - h2c, EL + h2c - H))
    if cover == 'split':
        A0 = EL + (h2c - h2r - H) / 2
        B0 = ER + (h2r - h2c - H) / 2
        X = (h2r + h2c - H) / 2
        xi = min(max((B0 - A0) / 2, -X), X)
        return max(A0 + xi, B0 - xi)
    raise ValueError(cover)


TILEFIT = True


def value(p, cover, pruned, tilefit=None):
    """eps*gamma; with the tile fit N >= N0 for both bands (r61b.md Theorem 2 assumes N >= N0):
    1/eps >= max(rate/(pw ln2) + gamma, max(H2r, H2c)/(pw ln2))."""
    if tilefit is None:
        tilefit = TILEFIT
    if min(p) <= 1e-4:
        return 0.0, 0.0, 0.0
    g = gamma_leaf(p)
    if g <= 0:
        return 0.0, 0.0, g
    rt = rate_enc(p, cover, pruned)
    inv = rt / (p[3] * LN2) + g
    if tilefit:
        inv = max(inv, max(R.H2(p[2] + p[3]), R.H2(p[1] + p[3])) / (p[3] * LN2))
    e = 1.0 / inv
    return e * g, e, g


def tile_binds(p, cover, pruned):
    g = gamma_leaf(p)
    rt = rate_enc(p, cover, pruned)
    return max(R.H2(p[2] + p[3]), R.H2(p[1] + p[3])) / (p[3] * LN2) >= rt / (p[3] * LN2) + g


def cov_margin(p, g):
    p0, p1, p2, pw = p
    lnf = R.H2(p2 + pw) + R.H2(p1 + pw) - R.Hn(p)
    return (0.5 - g) * pw * LN2 - lnf, lnf


def opt_product(pruned):
    f = lambda r: -value(R.prod_type(r), 'product', pruned)[0]
    grid = np.linspace(0.25, 0.45, 21)
    vals = [f(r) for r in grid]
    i = int(np.argmin(vals))
    res = minimize_scalar(f, bounds=(grid[max(i - 1, 0)], grid[min(i + 1, len(grid) - 1)]), method='bounded',
                          options={'xatol': 1e-8})
    return res.x, value(R.prod_type(res.x), 'product', pruned)


def opt_general(cover, pruned, symmetric, start):
    def unpack(y):
        if symmetric:
            p0, pw = y
            p1 = p2 = (1 - p0 - pw) / 2
        else:
            p0, p1, pw = y
            p2 = 1 - p0 - p1 - pw
        return (p0, p1, p2, pw)

    def neg(y):
        p = unpack(y)
        if min(p) <= 1e-3:
            return 1.0
        return -value(p, cover, pruned)[0]
    best = None
    for st in start:
        r = minimize(neg, np.array(st), method='Nelder-Mead',
                     options={'xatol': 1e-7, 'fatol': 1e-11, 'maxiter': 600})
        if best is None or r.fun < best.fun:
            best = r
    p = unpack(best.x)
    return p, value(p, cover, pruned), best.nit


def fmt(p):
    return '(' + ', '.join(f'{x:.5f}' for x in p) + ')'


def main():
    t0 = time.time()
    print('R155 task 2: eps*gamma with pruned band encodings (numerical optima of the proved bounds).')
    print('A. E_side at product types (dual; = H(p) when B <= 1), reading exponents, B_left, B_right:')
    for r in [0.30, 0.33, 0.34, 0.35, 0.36, 0.37, 0.38, 0.3819660, 0.40, 0.45, 0.50]:
        p = R.prod_type(r)
        print(f'  r = {r:.7f}: H(p) = {R.Hn(p):.6f}, E_left = {E_side(p, "left"):.6f} (B_L = {B_side(p, "left"):.4f}), '
              f'E_right = {E_side(p, "right"):.6f} (B_R = {B_side(p, "right"):.4f}), reading L/R = '
              f'{Lb.reading_exponent(p, "left"):.4f}/{Lb.reading_exponent(p, "right"):.4f}', flush=True)
    print('B. product types, deterministic covering Pi_L:')
    for pruned in [False, True]:
        r, (eg, e, g) = opt_product(pruned)
        p = R.prod_type(r)
        print(f'  {"pruned" if pruned else "full  "}: max eps*gamma = {eg:.7f} at r = {r:.6f} (tile fit binding: '
              f'{tile_binds(p, "product", pruned)}): eps = {e:.6f} '
              f'(1/eps = {1 / e:.4f}), gamma = {g:.6f}; E_left = {E_side(p, "left"):.6f}, E_right = '
              f'{E_side(p, "right"):.6f}, H(p) = {R.Hn(p):.6f}, H2(r) = {R.H2(r):.6f}  [{time.time() - t0:.0f} s]',
              flush=True)
    print('C. general types (tile fit N >= N0 imposed on both bands, as the theorem needs; "free" = without it, the')
    print('   model of r150-detection.md 3.4, shown for comparison):')
    global TILEFIT
    sym_starts = [(0.2909, 0.1273), (0.2949, 0.1154), (0.30, 0.12), (0.31, 0.13)]
    asym_starts = [(0.2974, 0.2974, 0.1286), (0.2949, 0.2949, 0.1154), (0.29, 0.30, 0.12), (0.30, 0.28, 0.12),
                   (0.33, 0.30, 0.13)]
    for tf in [False, True]:
        TILEFIT = tf
        for cover in ['unsplit', 'split']:
            for pruned in [False, True]:
                for symmetric in [True, False]:
                    p, (eg, e, g), nit = opt_general(cover, pruned, symmetric,
                                                     sym_starts if symmetric else asym_starts)
                    cm, lnf = cov_margin(p, g)
                    extra = ''
                    if pruned:
                        extra = (f'; E_left = {E_side(p, "left"):.6f} (B_L = {B_side(p, "left"):.4f}), E_right = '
                                 f'{E_side(p, "right"):.6f} (B_R = {B_side(p, "right"):.4f}), H(p) = {R.Hn(p):.6f}')
                    tb = tile_binds(p, cover, pruned)
                    print(f'  {"tilefit" if tf else "free   "} {cover:7s} {"pruned" if pruned else "full  "} '
                          f'{"p1 = p2   " if symmetric else "p1,p2 free"}: max eps*gamma = {eg:.7f} at p = {fmt(p)}: '
                          f'eps = {e:.6f} (1/eps = {1 / e:.4f}), gamma = {g:.6f}; H2(row), H2(col) = '
                          f'{R.H2(p[2] + p[3]):.5f}, {R.H2(p[1] + p[3]):.5f}; tile fit binding: {tb}; '
                          f'ln(1/f)/L = {lnf:.5f}, scan margin {cm:+.5f}{extra}  [{time.time() - t0:.0f} s]', flush=True)
    TILEFIT = True
    print(f'time {time.time() - t0:.1f} s')


if __name__ == '__main__':
    main()
