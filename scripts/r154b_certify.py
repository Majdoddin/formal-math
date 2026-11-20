r"""R154(b) review: independent re-check of the certificates (C1), (C2) of r150-detection.md 3.3 and of r61b.md
Theorem 6, written from scratch (nothing imported from r150d_* or r61b_*), with mpmath interval arithmetic.

Quantity (r61b.md 6.2, Lemma 11 for P3 (c); r150 3.1): for a type p = (p0, p1, p2, pw),
    Lam(p) = max_{v in simplex} min(f1(v), f2(v)),  f1 = pw H(v) - pw ln2/2,  f2 = H(t(v)) - H(p),
    t(v) = (p0 + pw v1, p1 + pw v2, p2 + pw v3, pw v4).
Method (different from r150d_certify.py, which uses one tangent plane of the 4-variable function):
  (1) weak duality, any mu in [0,1]:  min(f1, f2) <= g_mu := mu f1 + (1-mu) f2;
  (2) g_mu is SEPARABLE: g_mu(v) = K + sum_i phi_i(v_i), K = -mu pw ln2/2 - (1-mu) H(p),
        phi_i(v) = mu pw h(v) + (1-mu) h(p_i + pw v) (i = 0,1,2),  phi_3(v) = mu pw h(v) + (1-mu) h(pw v),
      h(x) = -x ln x; each phi_i is concave on [0, oo);
  (3) Lagrange bound of the constraint sum v_i = 1, any real C:
        max_simplex g_mu <= K + C + sum_i sup_{v >= 0} F_i(v),   F_i(v) := phi_i(v) - C v;
  (4) per coordinate: rationals v_lo < v_hi with F_i'(v_lo) > 0 > F_i'(v_hi), verified with intervals; by concavity
        sup_{v >= 0} F_i <= F_i(v_lo) + F_i'(v_lo) (v_hi - v_lo).
  The result UB is a rigorous upper bound of Lam(p).  A rigorous LOWER bound LB = min(f1, f2) at an explicit rational
  point of the simplex shows how tight UB is.
Then: gamma < -UB/(pw ln2) is a leaf-count saving, and a pair (eps0, gamma0) is certified iff gamma0 < -UB/(pw ln2)
and 1/eps0 > E/(pw ln2) + gamma0 (both checked with intervals), with the encoding exponent E per level:
  product type, deterministic covering Pi_L (r61b Theorem 2):   E = ln4 - H2(p2 + pw)
  general type, UNSPLIT random covering (columns relabeled, r150 3.3):  E = ln4 + H2(p2 + pw) - H(p)
      (and the unrelabeled row side needs ln4 - H2(p2 + pw) <= E, i.e. H(p) <= 2 H2(p2 + pw); checked)
  general type, SPLIT random covering (both sides relabeled, f^{-1/2} each; r61b 6.2 model): E = ln4 - H(p)/2
Run with the system python (mpmath): /usr/bin/python3 r154b_certify.py > r154b_certify_out.txt
"""
from fractions import Fraction as Fr
import math
from mpmath import iv, mpf, nstr

iv.prec = 160
LN2f = math.log(2)


def I(q):
    q = Fr(q)
    return iv.mpf(q.numerator) / q.denominator


def lo(x):
    return mpf(x.a)


def hi(x):
    return mpf(x.b)


# ---------------- float machinery (search only; nothing rigorous here) ----------------
def hf(x):
    return -x * math.log(x) if x > 0 else 0.0


def dphi_f(i, v, p, mu):
    pw = p[3]
    if i < 3:
        return mu * pw * (-math.log(v) - 1) + (1 - mu) * pw * (-math.log(p[i] + pw * v) - 1)
    return mu * pw * (-math.log(v) - 1) + (1 - mu) * pw * (-math.log(pw * v) - 1)


def root_f(i, C, p, mu):
    """v > 0 with dphi_i(v) = C (dphi decreasing in v); bisection in y = ln v."""
    a, b = -700.0, 10.0
    for _ in range(300):
        m = 0.5 * (a + b)
        if dphi_f(i, math.exp(m), p, mu) > C:
            a = m
        else:
            b = m
    return math.exp(0.5 * (a + b))


def primal_f(p, mu):
    """argmax of g_mu on the simplex: C with sum_i root_i(C) = 1."""
    a, b = -50.0, 50.0
    for _ in range(300):
        C = 0.5 * (a + b)
        s = sum(root_f(i, C, p, mu) for i in range(4))
        if s > 1:
            a = C
        else:
            b = C
    C = 0.5 * (a + b)
    return C, [root_f(i, C, p, mu) for i in range(4)]


def f12_f(p, v):
    pw = p[3]
    t = [p[0] + pw * v[0], p[1] + pw * v[1], p[2] + pw * v[2], pw * v[3]]
    f1 = pw * sum(hf(x) for x in v) - pw * LN2f / 2
    f2 = sum(hf(x) for x in t) - sum(hf(x) for x in p)
    return f1, f2


def dual_f(p, mu):
    C, v = primal_f(p, mu)
    f1, f2 = f12_f(p, v)
    return mu * f1 + (1 - mu) * f2, C, v


def best_mu(p):
    a, b = 1e-6, 1 - 1e-6
    gr = (math.sqrt(5) - 1) / 2
    c1, c2 = b - gr * (b - a), a + gr * (b - a)
    g1, g2 = dual_f(p, c1)[0], dual_f(p, c2)[0]
    for _ in range(90):
        if g1 < g2:
            b, c2, g2 = c2, c1, g1
            c1 = b - gr * (b - a)
            g1 = dual_f(p, c1)[0]
        else:
            a, c1, g1 = c1, c2, g2
            c2 = a + gr * (b - a)
            g2 = dual_f(p, c2)[0]
    return 0.5 * (a + b)


# ---------------- rigorous part ----------------
def hI(x):
    return -x * iv.log(x)


def phiI(i, v, P, MU):
    pw = P[3]
    if i < 3:
        return MU * pw * hI(v) + (1 - MU) * hI(P[i] + pw * v)
    return MU * pw * hI(v) + (1 - MU) * hI(pw * v)


def dphiI(i, v, P, MU):
    pw = P[3]
    if i < 3:
        return MU * pw * (-iv.log(v) - 1) + (1 - MU) * pw * (-iv.log(P[i] + pw * v) - 1)
    return MU * pw * (-iv.log(v) - 1) + (1 - MU) * pw * (-iv.log(pw * v) - 1)


def HI(vec):
    s = iv.mpf(0)
    for x in vec:
        s += hI(x)
    return s


def upper_bound(pq):
    """rigorous UB >= Lam(p) for the rational type pq; returns dict with the pieces."""
    pf = [float(x) for x in pq]
    mu = best_mu(pf)
    C, v = primal_f(pf, mu)
    muq = Fr(mu).limit_denominator(10 ** 12)
    Cq = Fr(C).limit_denominator(10 ** 14)
    P = [I(x) for x in pq]
    MU = I(muq)
    CI = I(Cq)
    K = -MU * P[3] * iv.log(2) / 2 - (1 - MU) * HI(P)
    total = K + CI
    brackets = []
    for i in range(4):
        r = root_f(i, float(Cq), pf, float(muq))
        rel = 1e-12
        while True:
            vlo = Fr(r * (1 - rel)).limit_denominator(10 ** 18)
            vhi = Fr(r * (1 + rel)).limit_denominator(10 ** 18)
            dlo = dphiI(i, I(vlo), P, MU) - CI
            dhi = dphiI(i, I(vhi), P, MU) - CI
            if lo(dlo) > 0 and hi(dhi) < 0 and vlo < vhi:
                break
            rel *= 4
            if rel > 1e-2:
                raise RuntimeError('bracket failed')
        Flo = phiI(i, I(vlo), P, MU) - CI * I(vlo)
        b_i = Flo + dlo * (I(vhi) - I(vlo))
        total += iv.mpf([lo(b_i), hi(b_i)])
        brackets.append((float(vlo), float(vhi)))
    UB = hi(total)
    # rigorous lower bound: an explicit rational point of the simplex
    vq = [Fr(x).limit_denominator(10 ** 15) for x in v[:3]]
    vq.append(1 - sum(vq))
    V = [I(x) for x in vq]
    T = [P[0] + P[3] * V[0], P[1] + P[3] * V[1], P[2] + P[3] * V[2], P[3] * V[3]]
    f1 = P[3] * HI(V) - P[3] * iv.log(2) / 2
    f2 = HI(T) - HI(P)
    LB = min(lo(f1), lo(f2))
    return dict(UB=UB, LB=LB, mu=float(muq), C=float(Cq), v=[float(x) for x in vq], brackets=brackets,
                f1=float(mpf(f1.mid)), f2=float(mpf(f2.mid)))


def H2I(x):
    return hI(x) + hI(1 - x)


def enc_exponent(pq, kind):
    P = [I(x) for x in pq]
    if kind == 'product':
        return iv.log(4) - H2I(P[2] + P[3]), None
    if kind == 'unsplit':
        E = iv.log(4) + H2I(P[2] + P[3]) - HI(P)
        side = hi(HI(P)) < lo(2 * H2I(P[2] + P[3]))   # unrelabeled row side dominated
        return E, side
    if kind == 'split':
        return iv.log(4) - HI(P) / 2, None
    raise ValueError(kind)


def check_pair(pq, kind, eps0, gam0, ub):
    P = [I(x) for x in pq]
    LN2 = iv.log(2)
    gcert = -iv.mpf(ub) / (P[3] * LN2)
    leaf_ok = lo(gcert) > Fr(gam0).numerator / mpf(Fr(gam0).denominator)
    E, side = enc_exponent(pq, kind)
    rhs = E / (P[3] * LN2) + I(gam0)
    enc_ok = hi(rhs) < mpf(Fr(eps0).denominator) / Fr(eps0).numerator
    # reading cost <= 4^L needs a + d <= L and b + d <= L (r61b 2.3)
    a, b, d = pq[2] + pq[3], pq[1] + pq[3], pq[3]
    read_ok = (a + d <= 1) and (b + d <= 1)
    return leaf_ok, enc_ok, read_ok, side, lo(gcert), hi(rhs)


def best_pair(pq, kind, ub, den=10 ** 6):
    """the largest eps0*gamma0 on a grid of step 1/den for this UB (gamma0 just below the leaf bound)."""
    P = [I(x) for x in pq]
    LN2 = iv.log(2)
    gcert = lo(-iv.mpf(ub) / (P[3] * LN2))
    E, _ = enc_exponent(pq, kind)
    best = None
    # eps*gamma with 1/eps = E/(pw ln2) + gamma is increasing in gamma, so take gamma0 maximal
    g0 = Fr(int(gcert * den) - 1, den)
    rhs = hi(E / (P[3] * LN2) + I(g0))
    e0 = Fr(int(den / rhs) - 1, den)
    return e0, g0, e0 * g0


def main():
    print('R154(b): independent certificates (Lagrange dual of the simplex constraint, separable, interval '
          'arithmetic, mpmath iv.prec = 160).\n')
    rows = []
    # (label, type, kind, claimed pair or None)
    r1 = Fr(1843, 5000)
    prod = lambda r: ((1 - r) ** 2, r * (1 - r), r * (1 - r), r * r)
    items = [
        ('C1 r = 1843/5000', prod(r1), 'product', (Fr(3209, 25000), Fr(11859, 200000))),
        ('C1 alt r = 7373/20000', prod(Fr(7373, 20000)), 'product', (Fr(128399, 1000000), Fr(14819, 250000))),
        ('C1 alt r = 3687/10000', prod(Fr(3687, 10000)), 'product', (Fr(128439, 1000000), Fr(29629, 500000))),
        ('C1 alt r = 7/19', prod(Fr(7, 19)), 'product', (Fr(64109, 500000), Fr(371, 6250))),
        ('C2 p = (1487,1487,1383,643)/5000', tuple(Fr(x, 5000) for x in (1487, 1487, 1383, 643)), 'unsplit',
         (Fr(6127, 50000), Fr(74073, 1000000))),
        ('C2 sym p = (2909,2909,2909,1273)/10^4', tuple(Fr(x, 10000) for x in (2909, 2909, 2909, 1273)), 'unsplit',
         (Fr(24087, 200000), Fr(75111, 1000000))),
        ('C2 alt p = (371/1250, 2869/10^4, 2869/10^4, 647/5000)',
         (Fr(371, 1250), Fr(2869, 10000), Fr(2869, 10000), Fr(647, 5000)), 'unsplit', (Fr(307, 2500), Fr(73739, 1000000))),
        ('split covering at p = (2909,2909,2909,1273)/10^4', tuple(Fr(x, 10000) for x in (2909, 2909, 2909, 1273)),
         'split', None),
        ('split covering at C2 p = (1487,1487,1383,643)/5000', tuple(Fr(x, 5000) for x in (1487, 1487, 1383, 643)),
         'split', None),
        ('r61b Thm 6 rho = 0.5085', prod(Fr(1017, 2000)), 'product', None),
        ('r61b 6.2 rho = 0.509', prod(Fr(509, 1000)), 'product', None),
        ('r61b 6.2 rho = 1/2', prod(Fr(1, 2)), 'product', None),
    ]
    for label, pq, kind, claimed in items:
        assert sum(pq) == 1
        u = upper_bound(pq)
        pw = float(pq[3])
        print(f'{label}: kind {kind}')
        print(f'  mu = {u["mu"]:.8f}, C = {u["C"]:.8f}, primal v = {[round(x, 7) for x in u["v"]]}, '
              f'f1 = {u["f1"]:+.9e}, f2 = {u["f2"]:+.9e}')
        print(f'  rigorous: LB = {nstr(u["LB"], 12)} <= Lam(p) <= UB = {nstr(u["UB"], 12)} '
              f'(gap {float(u["UB"] - u["LB"]):.2e}); leaf saving gamma < -UB/(pw ln2) = '
              f'{-float(u["UB"]) / (pw * LN2f):.9f}')
        if claimed is not None:
            eps0, gam0 = claimed
            leaf_ok, enc_ok, read_ok, side, gc, rhs = check_pair(pq, kind, eps0, gam0, u['UB'])
            print(f'  claimed (eps0, gamma0) = ({eps0}, {gam0}) = ({float(eps0):.6f}, {float(gam0):.6f}), '
                  f'eps0*gamma0 = {float(eps0 * gam0):.8f}: gamma0 < leaf bound {nstr(gc, 10)}: {leaf_ok}; '
                  f'1/eps0 = {float(1 / eps0):.6f} > E/(pw ln2) + gamma0 = {nstr(rhs, 10)}: {enc_ok}; '
                  f'reading a + d, b + d <= L: {read_ok}' + (f'; row side dominated (H(p) < 2 H2(p2+pw)): {side}'
                                                              if side is not None else ''))
            rows.append((label, leaf_ok and enc_ok and read_ok and (side is not False)))
        e0, g0, eg = best_pair(pq, kind, u['UB'])
        if float(u['UB']) < 0:
            print(f'  best certified pair at this type (grid 1e-6): ({e0}, {g0}) = ({float(e0):.6f}, {float(g0):.6f}), '
                  f'eps0*gamma0 = {float(eg):.8f}')
        print(flush=True)
    print('Summary of the claimed pairs: ' + '; '.join(f'{l}: {"CERTIFIED" if ok else "NOT certified"}'
                                                      for l, ok in rows))


if __name__ == '__main__':
    main()
