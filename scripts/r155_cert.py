r"""R155 (task 3): rigorous certificates (exact rational interval arithmetic) for the exact leaf count with PRUNED band
encodings, characteristic 2, T4 + P3, prescribed W with |W| <= N^2/sqrt(D) (r155-pruned-enc.md Sections 2-3).

Every quantity is an interval [lo, hi] of Fractions, rounded outward to denominators 10^45.  ln of a rational:
ln x = k ln2 + 2 atanh((z-1)/(z+1)), z = x/2^k in [2/3, 4/3], 60 terms plus the remainder bound (as calc/r111b_cert.py);
exp of a rational: Taylor (30 terms, remainder <= 2|y|^n/n!) at y = x/2^k, |y| <= 1/16, then k squarings.
Floats are used only to FIND the certificate data (mu, v*, multipliers, xi); everything checked is exact.

Inequalities per point p (rational), with rational (eps0, gamma0):
 (Lf) U_Lam(p) + gamma0 pw ln2 < 0       leaf count: Lam(p) <= U_Lam (weak duality mu + tangent plane at v*, as
                                          calc/r150d_certify.py), r61b.md 6.2
 (Ep) E_side bounds: Proposition 1.5 (pw <= min p_i and B_side <= 1, exact check) gives E_side <= H(p); otherwise
      Phi(lambda; p) at rational multipliers (Section 1.4).  E_L = max(E_side^L, rd_L), E_R likewise.
 (En) rate(p) + gamma0 pw ln2 < pw ln2 / eps0     encodings; rate per covering:
        product (deterministic Pi_L):   max(E_L, E_R) - H2(r)
        unsplit (randomized):           max(E_L - H2r, E_R + H2r - H)   (columns relabeled)  or the mirror
        split (randomized, Lemma S):    max(E_L + (H2c - H2r - H)/2 + xi, E_R + (H2r - H2c - H)/2 - xi)
 (Sx) split only: |xi| < X = (H2r + H2c - H)/2
 (Tf) max(H2r, H2c) < pw ln2 / eps0     tile fit N >= N0 for both bands (r155-pruned-enc.md 2.1)
 (Sc) randomized only: H2r + H2c - H < (1/2 - gamma0) pw ln2     (scanning for a covering relabeling)
 (Hy) 0 < eps0 <= 1/2, 0 < gamma0 <= 1/2
Result: eps0*gamma0 (exact rational).
Usage: python3 r155_cert.py > r155_cert_out.txt
"""
from fractions import Fraction as F
import math
import sys
import numpy as np
import r155_lib as Lb

PREC = F(1, 10 ** 45)


def _ro(lo, hi):
    return F(math.floor(lo / PREC)) * PREC, F(math.ceil(hi / PREC)) * PREC


class I:
    def __init__(s, lo, hi=None):
        s.lo = F(lo)
        s.hi = F(lo if hi is None else hi)
        assert s.lo <= s.hi, (s.lo, s.hi)

    @staticmethod
    def c(o):
        return o if isinstance(o, I) else I(o)

    def __add__(s, o):
        o = I.c(o)
        return I(*_ro(s.lo + o.lo, s.hi + o.hi))
    __radd__ = __add__

    def __neg__(s):
        return I(-s.hi, -s.lo)

    def __sub__(s, o):
        return s + (-I.c(o))

    def __rsub__(s, o):
        return I.c(o) - s

    def __mul__(s, o):
        o = I.c(o)
        ps = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return I(*_ro(min(ps), max(ps)))
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = I.c(o)
        assert o.lo > 0 or o.hi < 0
        return s * I(*_ro(1 / o.hi, 1 / o.lo))

    def __rtruediv__(s, o):
        return I.c(o) / s

    def f(s):
        return float((s.lo + s.hi) / 2)

    def __repr__(s):
        return f'[{float(s.lo):.12g}, {float(s.hi):.12g}]'


def imax(*xs):
    xs = [I.c(x) for x in xs]
    return I(max(x.lo for x in xs), max(x.hi for x in xs))


def _atanh(y, n=60):
    s = F(0)
    p = y
    y2 = y * y
    for i in range(n):
        s += p / (2 * i + 1)
        p *= y2
    err = abs(p) / ((2 * n + 1) * (1 - y2))
    return s - err, s + err


_LN2 = None


def LN2():
    global _LN2
    if _LN2 is None:
        lo, hi = _atanh(F(1, 3))
        _LN2 = I(*_ro(2 * lo, 2 * hi))
    return _LN2


def ln(x):
    """ln of a positive rational, or of a positive interval (monotone)."""
    if isinstance(x, I):
        assert x.lo > 0
        return I(ln(x.lo).lo, ln(x.hi).hi)
    x = F(x)
    assert x > 0
    k, z = 0, x
    while z > F(4, 3):
        z /= 2
        k += 1
    while z < F(2, 3):
        z *= 2
        k -= 1
    y = (z - 1) / (z + 1)
    lo, hi = _atanh(y)
    return I(*_ro(2 * lo, 2 * hi)) + LN2() * k


def exp_r(x, n=30):
    """exp of a rational."""
    x = F(x)
    k = 0
    y = x
    while abs(y) > F(1, 16):
        y /= 2
        k += 1
    s = F(0)
    t = F(1)
    for i in range(n):
        s += t
        t = t * y / (i + 1)
    err = 2 * abs(t)        # |y|^n/n! * e^{|y|} <= 2 |y|^n / n!
    v = I(*_ro(s - err, s + err))
    for _ in range(k):
        v = v * v
    return v


def ent(v):
    """H(v) = -sum v_i ln v_i for rationals v_i > 0 (zero entries skipped)."""
    out = I(0)
    for x in v:
        if x > 0:
            out = out - ln(x) * x
    return out


def H2(x):
    return ent([F(x), 1 - F(x)])


def lse_r(vals):
    """ln sum exp(v) for rationals v."""
    s = I(0)
    for v in vals:
        s = s + exp_r(v)
    return ln(s)


# ---------------- leaf exponent: weak duality + tangent plane (method of calc/r150d_certify.py) ----------------
def stationary(p, mu):
    p0, p1, p2, pw = p
    lows = [p0, p1, p2]
    lpw = math.log(pw)

    def v_of(C):
        y0 = C - (1 - mu) * lpw
        vs = []
        for lo in lows:
            y = y0
            for _ in range(200):
                ey = math.exp(y)
                s = lo + pw * ey
                g = mu * y + (1 - mu) * math.log(s) - C
                gp = mu + (1 - mu) * pw * ey / s
                st = g / gp
                y -= st
                if abs(st) < 1e-15:
                    break
            vs.append(math.exp(y))
        vs.append(math.exp(y0))
        return vs
    a, b = -80.0, 10.0
    for _ in range(200):
        m = (a + b) / 2
        if sum(v_of(m)) > 1:
            b = m
        else:
            a = m
    v = v_of((a + b) / 2)
    s = sum(v)
    return [x / s for x in v]


def f12_float(p, v):
    p0, p1, p2, pw = p
    t = [p0 + pw * v[0], p1 + pw * v[1], p2 + pw * v[2], pw * v[3]]
    H = lambda z: -sum(x * math.log(x) for x in z if x > 0)
    return pw * H(v) - pw * math.log(2) / 2, H(t) - H(p)


def lam_upper(pq):
    """rigorous upper bound U >= Lam(p) at the rational type pq; returns (U interval, mu, v*)."""
    pf = [float(x) for x in pq]

    def G(mu):
        v = stationary(pf, mu)
        f1, f2 = f12_float(pf, v)
        return mu * f1 + (1 - mu) * f2
    a, b = 0.0, 1.0
    gr = (math.sqrt(5) - 1) / 2
    c1, c2 = b - gr * (b - a), a + gr * (b - a)
    G1, G2 = G(c1), G(c2)
    for _ in range(80):
        if G1 < G2:
            b, c2, G2 = c2, c1, G1
            c1 = b - gr * (b - a)
            G1 = G(c1)
        else:
            a, c1, G1 = c1, c2, G2
            c2 = a + gr * (b - a)
            G2 = G(c2)
    mu = F((a + b) / 2).limit_denominator(10 ** 12)
    v = stationary(pf, float(mu))
    vq = [F(x).limit_denominator(10 ** 15) for x in v[:3]]
    vq.append(1 - sum(vq))
    assert all(x > 0 for x in vq)
    p0, p1, p2, pw = pq
    t = [p0 + pw * vq[0], p1 + pw * vq[1], p2 + pw * vq[2], pw * vq[3]]
    f1 = ent(vq) * pw - LN2() * (pw / 2)
    f2 = ent(t) - ent(list(pq))
    g = f1 * mu + f2 * (1 - mu)
    grad = [(-ln(vq[i]) - 1) * (mu * pw) + (-ln(t[i]) - 1) * ((1 - mu) * pw) for i in range(4)]
    s = I(0)
    for i in range(4):
        s = s + grad[i] * vq[i]
    U = g + imax(*grad) - s
    return U, mu, vq


# ---------------- E_side ----------------
def B_side(pq, side):
    p0, p1, p2, pw = pq
    if side == 'left':
        return max(p0, p1) + max(p0, p2) + p1
    return max(p0, p2) + p1 + p2


def dual_parts_exact(lam, side):
    """a_t, b_s of Section 1.4 in exact rationals."""
    nu, zeta, e1, e2, e3 = [F(x) for x in lam]
    eta = {1: e1, 2: e2, 3: e3, 4: F(0)}

    def cts(t, s):
        return eta[t] - (nu if s in Lb.IN_LETTERS else F(0)) - (zeta if s == Lb.MARKED else F(0))
    a = [max(cts(t, s) for s in Lb.COMP[side][t]) for t in (1, 2, 3, 4)]
    b = [max(cts(t, s) for t in Lb.terms_of_letter(side, s)) for s in (0, 1, 2)]
    assert all(isinstance(x, F) for x in a + b)
    return a, b


def dual_upper(pq, side, lam):
    """Phi(lambda; p) as an interval, lambda rational with zeta, eta >= 0 (Section 1.4)."""
    nu, zeta, e1, e2, e3 = lam
    assert zeta >= 0 and e1 >= 0 and e2 >= 0 and e3 >= 0
    a, b = dual_parts_exact([nu, zeta, e1, e2, e3], side)
    p0, p1, p2, pw = pq
    size = (p2 + pw) if side == 'left' else (p1 + pw)
    lin = nu * size + zeta * pw - e1 * p0 - e2 * p1 - e3 * p2
    A = lse_r(a)
    B = lse_r(b)
    return imax(A, B) + lin


def side_upper(pq, side):
    """rigorous upper bound on max(E_side, reading) for one side; returns (interval, how)."""
    p0, p1, p2, pw = pq
    sz = (p2 + pw) if side == 'left' else (p1 + pw)
    rd = H2(sz) + H2(pw / (sz + pw)) * (sz + pw)
    if pw <= min(p0, p1, p2) and B_side(pq, side) <= 1:
        E = ent(list(pq))
        how = f'Prop. 1.5 (B_{side[0].upper()} = {float(B_side(pq, side)):.4f} <= 1): E_side = H(p)'
    else:
        val, lam = Lb.side_dual(tuple(float(x) for x in pq), side)
        lamq = [F(x).limit_denominator(10 ** 9) for x in lam]
        lamq = [lamq[0]] + [max(F(0), x) for x in lamq[1:]]
        E = dual_upper(pq, side, lamq)
        how = (f'dual at rational multipliers (nu, zeta, eta1, eta2, eta3) = '
               f'({", ".join(f"{float(x):.9f}" for x in lamq)}), float optimum {val:.9f}')
    return imax(E, rd), how, rd


def floor_frac(x, den):
    """largest k/den with k/den <= x - 1/den (one unit of margin below the rational x)."""
    return F(math.floor(x * den) - 1, den)


def certify(pq, cover, den=10 ** 6, xi=None):
    p0, p1, p2, pw = pq
    assert sum(pq) == 1 and min(pq) > 0
    U, mu, vq = lam_upper(pq)
    l2 = LN2()
    pwl2 = l2 * pw
    gam_bound = (-U) / pwl2                     # gamma < this
    gamma0 = floor_frac(gam_bound.lo, den)
    EL, howL, rdL = side_upper(pq, 'left')
    ER, howR, rdR = side_upper(pq, 'right')
    H = ent(list(pq))
    h2r, h2c = H2(p2 + pw), H2(p1 + pw)
    info = {}
    if cover == 'product':
        assert p1 == p2
        rate = imax(EL, ER) - h2r
    elif cover == 'unsplit':
        r_cols = imax(EL - h2r, ER + h2r - H)
        r_rows = imax(ER - h2c, EL + h2c - H)
        if r_cols.hi <= r_rows.hi:
            rate, info['relabeled'] = r_cols, 'columns'
        else:
            rate, info['relabeled'] = r_rows, 'rows'
    elif cover == 'split':
        X = (h2r + h2c - H) * F(1, 2)
        A0 = EL + (h2c - h2r - H) * F(1, 2)
        B0 = ER + (h2r - h2c - H) * F(1, 2)
        if xi is None:
            xf = (B0.f() - A0.f()) / 2
            xf = max(min(xf, 0.999 * X.f()), -0.999 * X.f())
            xi = F(xf).limit_denominator(10 ** 9)
        assert abs(xi) < X.lo, 'balance xi outside (-X, X)'
        info['xi'] = xi
        info['X'] = X
        rate = imax(A0 + xi, B0 - xi)
    else:
        raise ValueError(cover)
    g0 = I(gamma0)
    inv_eps_bound = imax(rate / pwl2 + g0, imax(h2r, h2c) / pwl2)   # 1/eps0 > this (encodings; tile fit)
    eps0 = floor_frac(1 / inv_eps_bound.hi, den)
    # re-check every inequality with the rational pair
    chk = {}
    chk['Lf'] = (U + pwl2 * gamma0).hi                  # < 0
    chk['En'] = (rate + pwl2 * gamma0 - pwl2 / eps0).hi    # < 0
    chk['Tf'] = (imax(h2r, h2c) - pwl2 / eps0).hi                 # < 0: N >= N0 for both bands (tile fit)
    if cover != 'product':
        chk['Sc'] = ((h2r + h2c - H) - pwl2 * (F(1, 2) - gamma0)).hi   # < 0
    ok = all(v < 0 for v in chk.values()) and 0 < eps0 <= F(1, 2) and 0 < gamma0 <= F(1, 2)
    return dict(U=U, mu=mu, vq=vq, gamma0=gamma0, eps0=eps0, prod=eps0 * gamma0, EL=EL, ER=ER, howL=howL, howR=howR,
                rdL=rdL, rdR=rdR, H=H, h2r=h2r, h2c=h2c, rate=rate, chk=chk, ok=ok, info=info)


def report(name, pq, cover, **kw):
    c = certify(pq, cover, **kw)
    print(f'{name}: p = ({", ".join(str(x) for x in pq)}) = ({", ".join(f"{float(x):.5f}" for x in pq)}), covering {cover}'
          + (f' ({c["info"]["relabeled"]} relabeled)' if 'relabeled' in c['info'] else '')
          + (f' (xi = {c["info"]["xi"]}, X = {c["info"]["X"]})' if 'xi' in c['info'] else ''))
    print(f'  leaf exponent: mu = {float(c["mu"]):.6f}, v* = {[round(float(x), 6) for x in c["vq"]]}; '
          f'Lam(p) <= U = {c["U"]}; gamma < {float(-c["U"].lo / (LN2().hi * pq[3])):.9f}')
    print(f'  E_left  <= {c["EL"]}  [{c["howL"]}; reading {c["rdL"]}]')
    print(f'  E_right <= {c["ER"]}  [{c["howR"]}; reading {c["rdR"]}]')
    print(f'  H(p) = {c["H"]}, H2(row) = {c["h2r"]}, H2(col) = {c["h2c"]}; encoding rate <= {c["rate"]} per level')
    print(f'  checks (each must be < 0): ' + ', '.join(f'{k} {float(v):+.4e}' for k, v in c['chk'].items()))
    print(f'  certified pair (eps0, gamma0) = ({c["eps0"]}, {c["gamma0"]}) = ({float(c["eps0"]):.6f}, '
          f'{float(c["gamma0"]):.6f}); eps0*gamma0 = {c["prod"]} = {float(c["prod"]):.7f}; '
          f'{"ALL CHECKS PASS" if c["ok"] else "FAILED"}', flush=True)
    return c


def main():
    print('R155 certificates: exact leaf count with pruned band encodings (T4 + P3, characteristic 2), |W| <= N^2/sqrt D.')
    print(f'ln 2 enclosure: {LN2()} ; self-test exp(ln 3) = {exp_r(F(10986122886681098, 10 ** 16))} (3 expected), '
          f'ln(e^{{1/3}}) check: {ln(exp_r(F(1, 3)))} (0.333.. expected)')
    out = {}
    print('A. product type, deterministic covering Pi_L (Lemma C):')
    for r in [F(1373, 4000), F(343, 1000), F(3435, 10000)]:
        pq = ((1 - r) ** 2, r * (1 - r), r * (1 - r), r * r)
        out[('P', r)] = report(f'  r = {r}', pq, 'product')
    print('B. general type, UNSPLIT randomized covering (one side relabeled by ceil(2 d ln2/f) independent permutations):')
    for pq in [(F(30730, 100000), F(27895, 100000), F(29615, 100000), F(11760, 100000)),
               (F(30697, 100000), F(23, 80), F(23, 80), F(11803, 100000))]:
        out[('U', pq)] = report('  unsplit', pq, 'unsplit')
    print('C. general type, SPLIT randomized covering (Lemma S, Section 2.2):')
    for pq in [(F(30697, 100000), F(23, 80), F(23, 80), F(11803, 100000)),
               (F(307, 1000), F(2875, 10000), F(2875, 10000), F(1180, 10000))]:
        out[('S', pq)] = report('  split', pq, 'split', xi=F(0))
    print('E. the r150 model point of the split covering (0.0098650), for the record: the tile fit fails there')
    pq = (F(1843, 6250), F(1843, 6250), F(1843, 6250), F(721, 6250))
    c = certify(pq, 'split', xi=F(0))
    print(f'  p = (0.29488, 0.29488, 0.29488, 0.11536): with the tile fit the certified pair is ({c["eps0"]}, '
          f'{c["gamma0"]}), eps0*gamma0 = {float(c["prod"]):.7f} (checks {", ".join(f"{k} {float(v):+.3e}" for k, v in c["chk"].items())})')
    print('D. for comparison, the same certificate with FULL encodings (E_L = E_R = ln 4) is r150d_certify_out.txt:')
    print('   (C1) 0.0076111 product, (C2) 0.0090769 general unsplit.')


if __name__ == '__main__':
    main()
