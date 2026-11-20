r"""R155 + residue folding (Shr26 Lemma fold, l. 545-571 of its tex; rebuilt for T4 + P3 in r156-shr26-levers.md 3.1):
the folded saving of the pruned-encoding certificates (r155-pruned-enc.md Section 3.3).

Folding feeds the matrix theorem an N x N instance with N = n ceil(sqrt p), D = sigma p = n^e, |W| <= n^2 <= N^2/sqrt D,
so it uses Theorem P / G as a black box with eps' = e/(1 + e/4).  Theorem P / G hold for every eps' with
1/eps' > max(E + gamma, T), where (per unit of d = log2 D)
    E := rate/(pw ln2)   (encodings; rate as in r155_cert / r155_rates),   T := max(H2r, H2c)/(pw ln2)   (tile fit),
so a rational e0 with 1/e0 > max(E + gamma0, T) - 1/4 gives the folded saving s0 = e0 gamma0.  Lines checked exactly:
    (Lf)   leaf count, as in r155_cert;
    (EnF)  1 - e0 (E - 1/4) > e0 gamma0         (the encoding line of calc/r156_certify.py with E = E_pruned);
    (TfF)  1 - e0 (T - 1/4) > 0                 (tile fit N >= N0 for the folded N = n^{1 + e/4});
    (Sc)   as in r155_cert (unchanged: |W| <= N^2/sqrt D in the folded instance too).
Usage: python3 r155_fold.py > r155_fold_out.txt
"""
from fractions import Fraction as F
import math
import numpy as np
from scipy.optimize import minimize, minimize_scalar
import r150d_rates as R
import r155_rates as Q
import r155_cert as C

LN2 = math.log(2)


def fold_value(p, cover):
    if min(p) <= 1e-3:
        return 0.0, 0.0, 0.0
    g = Q.gamma_leaf(p)
    if g <= 0:
        return 0.0, 0.0, 0.0
    pw = p[3]
    E = Q.rate_enc(p, cover, True) / (pw * LN2)
    T = max(R.H2(p[2] + pw), R.H2(p[1] + pw)) / (pw * LN2)
    inv = max(E + g, T) - 0.25
    return g / inv, 1 / inv, g


def opt_fold(cover, symmetric, starts):
    if cover == 'product':
        f = lambda r: -fold_value(R.prod_type(r), 'product')[0]
        res = minimize_scalar(f, bounds=(0.30, 0.40), method='bounded', options={'xatol': 1e-8})
        return R.prod_type(res.x), -res.fun

    def unpack(y):
        if symmetric:
            p0, pw = y
            p1 = p2 = (1 - p0 - pw) / 2
        else:
            p0, p1, pw = y
            p2 = 1 - p0 - p1 - pw
        return (p0, p1, p2, pw)
    best = None
    for st in starts:
        r = minimize(lambda y: -fold_value(unpack(y), cover)[0], np.array(st), method='Nelder-Mead',
                     options={'xatol': 1e-7, 'fatol': 1e-11, 'maxiter': 600})
        if best is None or r.fun < best.fun:
            best = r
    return unpack(best.x), -best.fun


def certify_fold(pq, cover, den=10 ** 6, xi=None):
    c = C.certify(pq, cover, den=den, xi=xi)
    pw = pq[3]
    pwl2 = C.LN2() * pw
    E = c['rate'] / pwl2
    T = C.imax(c['h2r'], c['h2c']) / pwl2
    g0 = c['gamma0']
    bound = C.imax(E + g0, T) - F(1, 4)                 # 1/e0 > bound
    e0 = C.floor_frac(1 / bound.hi, den)
    s0 = e0 * g0
    chk = {'Lf': c['chk']['Lf'],
           'EnF': (s0 - (1 - (E - F(1, 4)) * e0)).hi,      # < 0
           'TfF': ((T - F(1, 4)) * e0 - 1).hi}               # < 0
    if 'Sc' in c['chk']:
        chk['Sc'] = c['chk']['Sc']
    ok = all(v < 0 for v in chk.values()) and 0 < e0 <= F(1, 2) and 0 < g0 <= F(1, 2)
    enc_line = (1 - (E - F(1, 4)) * e0).lo
    return dict(c=c, e0=e0, s0=s0, chk=chk, ok=ok, enc_line=enc_line, E=E, T=T)


def show(name, pq, cover, xi=None):
    r = certify_fold(pq, cover, xi=xi)
    c = r['c']
    print(f'  {name}: p = ({", ".join(str(x) for x in pq)}) = ({", ".join(f"{float(x):.5f}" for x in pq)}), {cover}'
          + (f' ({c["info"]["relabeled"]} relabeled)' if 'relabeled' in c['info'] else ''))
    print(f'    unfolded (r155_cert): (eps0, gamma0) = ({c["eps0"]}, {c["gamma0"]}), s = {float(c["prod"]):.7f}, '
          f'APSP exponent 3 - s = {3 - float(c["prod"]):.7f}')
    print(f'    folded: E = {r["E"]}, T = {r["T"]} (per unit of d), gamma0 = {c["gamma0"]}, e0 = {r["e0"]} '
          f'(1/e0 = {float(1 / r["e0"]):.6f}); s0 = e0 gamma0 = {r["s0"]} = {float(r["s0"]):.8f}; encoding line '
          f'1 - e0 (E - 1/4) >= {float(r["enc_line"]):.8f}; checks ' +
          ', '.join(f'{k} {float(v):+.3e}' for k, v in r['chk'].items()) +
          f'; APSP exponent 3 - s0 = {3 - float(r["s0"]):.8f}; {"ALL CHECKS PASS" if r["ok"] else "FAILED"}',
          flush=True)
    return r


def main():
    print('R155 with residue folding (Shr26 Lemma fold; r156-shr26-levers.md 3.1): folded savings of the pruned-encoding')
    print('certificates, s_fold = gamma/(max(E + gamma, T) - 1/4) (numerical optima) and certified s0 = e0 gamma0.')
    print('A. numerical optima of the folded saving (tile fit imposed; pruned encodings):')
    pP, vP = opt_fold('product', True, None)
    print(f'  product, deterministic covering: {vP:.7f} at r = {math.sqrt(pP[3]):.5f}', flush=True)
    for cover in ['unsplit', 'split']:
        for sym in [True, False]:
            st = [(0.30697, 0.11803), (0.2949, 0.1154), (0.30, 0.125)] if sym else \
                 [(0.3073, 0.27895, 0.1176), (0.30697, 0.2875, 0.11803), (0.30, 0.29, 0.125)]
            p, v = opt_fold(cover, sym, st)
            print(f'  {cover:7s} {"p1 = p2   " if sym else "p1,p2 free"}: {v:.7f} at p = '
                  f'({", ".join(f"{x:.5f}" for x in p)})', flush=True)
    print('B. certificates, at the unfolded certified points of r155_cert_out.txt:')
    show('(P)', ((1 - F(1373, 4000)) ** 2, F(1373, 4000) * (1 - F(1373, 4000)), F(1373, 4000) * (1 - F(1373, 4000)),
                 F(1373, 4000) ** 2), 'product')
    show('(U)', (F(3073, 10000), F(5579, 20000), F(5923, 20000), F(147, 1250)), 'unsplit')
    show('(S)', (F(30697, 100000), F(23, 80), F(23, 80), F(11803, 100000)), 'split', xi=F(0))
    print('C. certificates near the folded optima:')
    r = F(3465, 10000)
    show('(Pf)', ((1 - r) ** 2, r * (1 - r), r * (1 - r), r * r), 'product')
    r = F(3435, 10000)
    show('(Pf2)', ((1 - r) ** 2, r * (1 - r), r * (1 - r), r * r), 'product')
    show('(Uf)', (F(30598, 100000), F(27822, 100000), F(29581, 100000), F(11999, 100000)), 'unsplit')
    show('(Sf)', (F(30562, 100000), F(28696, 100000), F(28696, 100000), F(12046, 100000)), 'split', xi=F(0))


if __name__ == '__main__':
    main()
