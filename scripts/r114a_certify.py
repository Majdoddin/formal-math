"""r114a_certify.py (2026-10-22), for exponents/r114a.md (task R114(a)).

Certified evaluation of the column-degree switching threshold of v1's squared run (r20.md Section 5, r109.md item 5)
at column budgets q = 1 and q = 1/2.

Notation (per m, natural units; c = L/m; x = d/m in [0, 1]):
  F(x,c) = x ln4 - (1-x)ln(1-x) - (c-1+x)ln(c-1+x) + (c-1)ln(c-1)      (leaves of order xm per output, r14 b(x,c))
  G(x,c) = (c-1+x)ln(c-1+x) - x ln x - (c-1)ln(c-1)                       (log of C(L-m+d, d))
  column-degree rate of a class (x1, x2):  k(x1,x2) = G(x1) - x1 ln2 + G(x2)
  Lam_col(t,c) = [ max_x (F + t(G - x ln2)) + max_x (F + t G) ] / ln4     (units of ln D, D = 4^m)
  g1(x) = H(x) + x ln2, g2(x) = H(x) + x ln4  (= F + G - x ln2 and F + G: column incidences per entry)
  A(c) = 2c ln5 - c H(1/c) - (c-1) ln4,  eps(c) = ln4 / A(c)                 (r14 Theorem 2 encoding range)

Part 1 (lower bound, the theorem's hypothesis): rational c0, t0 with  Lam_col(t0, c0) < t0 q  certified.  By
r114a.md Theorem 1 this gives, for every eps < ln4/A(c0), a deterministic structure with saving
gamma = t0 q - Lam_col(t0,c0) > 0 and column cost N D^{q - gamma + o(1)}.
  Each 1-D maximum of the concave function h on [0,1] is bounded above by
     max h <= max(h(xa), h(xb)) + h'(xa)(xb - xa),   if h'(xa) > 0 > h'(xb), xa < xb,
  (concavity: h is increasing left of xa, decreasing right of xb, and below its tangent at xa in between).
Part 2 (upper bound, optimality among cuts by per-half order classes): rational c1 < c0 and a rational point
(x1, x2) with g1(x1) + g2(x2) > q ln4 and F(x1,c1) + F(x2,c1) > 0 certified.  Then at every c <= c1 (F decreases in
c) every up-closed cut with query exponent <= q must put the classes near (x1 m, x2 m) into High, and those have
box rate > 0: no saving.  So the construction's threshold c* lies in (c1, c0) and its range in
(ln4/A(c0), ln4/A(c1)).
Part 3: the same at R20's total-order cut, for comparison (float only; r20.md has the proved 0.190464).

Interval arithmetic: exact Fractions for + - * /, and ln of a positive rational through Python's decimal module at
60 significant digits.  decimal's ln is correctly rounded (documented, ROUND_HALF_EVEN), so the true value lies within
one unit in the last place of the returned value; we widen by 2 units.  No mpmath.
Run: ~/.venv/bin/python r114a_certify.py > r114a_certify_out.txt   (single process, a few seconds)
"""
from fractions import Fraction as Fr
from decimal import Decimal, getcontext
from math import log
from scipy.optimize import brentq, minimize_scalar

getcontext().prec = 60


class I:
    """closed interval [lo, hi] of Fractions"""
    def __init__(s, lo, hi=None):
        s.lo = Fr(lo); s.hi = Fr(lo if hi is None else hi)
        assert s.lo <= s.hi

    def __add__(s, o): o = o if isinstance(o, I) else I(o); return I(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__

    def __neg__(s): return I(-s.hi, -s.lo)

    def __sub__(s, o): o = o if isinstance(o, I) else I(o); return s + (-o)

    def __rsub__(s, o): return I(o) - s

    def __mul__(s, o):
        o = o if isinstance(o, I) else I(o)
        p = [s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi]
        return I(min(p), max(p))
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        assert o.lo > 0 or o.hi < 0
        return s*I(min(1/o.lo, 1/o.hi), max(1/o.lo, 1/o.hi))

    def __repr__(s): return f"[{float(s.lo):.15g}, {float(s.hi):.15g}]"


_lncache = {}


def ln(x):
    """enclosure of ln(x) for a positive rational x"""
    x = Fr(x); assert x > 0
    if x in _lncache:
        return _lncache[x]
    d = (Decimal(x.numerator)/Decimal(x.denominator))       # rounded to 60 digits
    # the quotient itself is rounded: x_dec = x(1 + r), |r| <= 10^-59; ln changes by <= 2*10^-59
    v = d.ln()
    ulp = Decimal(1).scaleb(v.adjusted() - getcontext().prec + 1) if v != 0 else Decimal(1).scaleb(-80)
    err = Fr(2*ulp) + Fr(1, 10**58)
    r = I(Fr(v) - err, Fr(v) + err)
    _lncache[x] = r
    return r


def xlx(x):
    x = Fr(x)
    return I(0) if x == 0 else x*ln(x)


L2, L4, L5 = ln(2), ln(4), ln(5)


def F(x, c): x, c = Fr(x), Fr(c); return x*L4 - xlx(1 - x) - xlx(c - 1 + x) + xlx(c - 1)
def G(x, c): x, c = Fr(x), Fr(c); return xlx(c - 1 + x) - xlx(x) - xlx(c - 1)
def Fp(x, c): x, c = Fr(x), Fr(c); return ln(4*(1 - x)/(c - 1 + x))
def Gp(x, c): x, c = Fr(x), Fr(c); return ln((c - 1 + x)/x)
def H(x): x = Fr(x); return -xlx(x) - xlx(1 - x)
def g1(x): return H(x) + Fr(x)*L2
def g2(x): return H(x) + Fr(x)*L4


def A(c): c = Fr(c); return 2*c*L5 - c*H(1/c) - (c - 1)*L4


# --------------------------------------------------------------------------- float versions for locating optima
def Ff(x, c): return x*log(4) - (0 if x >= 1 else (1-x)*log(1-x)) - (c-1+x)*log(c-1+x) + (c-1)*log(c-1)
def Gf(x, c): return (c-1+x)*log(c-1+x) - (0 if x <= 0 else x*log(x)) - (c-1)*log(c-1)
def Hf(x): return 0.0 if x <= 0 or x >= 1 else -x*log(x) - (1-x)*log(1-x)
def Af(c): return 2*c*log(5) - c*Hf(1/c) - (c-1)*log(4)


def argmaxf(f):
    r = minimize_scalar(lambda x: -f(x), bounds=(1e-15, 1 - 1e-15), method="bounded", options=dict(xatol=1e-14))
    return r.x, -r.fun


def Lamf(t, c):
    return (argmaxf(lambda x: Ff(x, c) + t*(Gf(x, c) - x*log(2)))[1]
            + argmaxf(lambda x: Ff(x, c) + t*Gf(x, c))[1])/log(4)


def Lcolf(q, c):
    r = minimize_scalar(lambda t: -(t*q - Lamf(t, c)), bounds=(0, 1), method="bounded", options=dict(xatol=1e-13))
    return -r.fun, r.x


def region_maxf(c, q):
    """max F(x1)+F(x2) over g1(x1)+g2(x2) >= q ln4 (boundary parametrisation, F decreasing past its peak)"""
    g1f = lambda x: Hf(x) + x*log(2); g2f = lambda x: Hf(x) + x*log(4)

    def val(x1):
        r = q*log(4) - g1f(x1)
        if r <= 0: return Ff(x1, c) + Ff(min(max(0.0, (5 - c)/5), 1.0), c)
        if r >= log(5) - 1e-15: return -1e9
        if r < 1e-300: return Ff(x1, c) + Ff(0.0, c)
        x2 = brentq(lambda x: g2f(x) - r, 0, 0.8)
        return Ff(x1, c) + Ff(x2, c)
    best = max((val(i/4000*2/3), i/4000*2/3) for i in range(4001))
    lo, hi = max(best[1] - 1/3000, 0), min(best[1] + 1/3000, 2/3)
    r = minimize_scalar(lambda x: -val(x), bounds=(lo, hi), method="bounded", options=dict(xatol=1e-14))
    x1 = r.x; rr = q*log(4) - g1f(x1)
    x2 = min(max(0.0, (5 - c)/5), 1.0) if rr <= 0 else brentq(lambda x: g2f(x) - rr, 0, 0.8, xtol=1e-15)
    return -r.fun, x1, x2


# --------------------------------------------------------------------------- certified pieces
def rat(x, den=10**12):
    return Fr(round(x*den), den)


def cert_max(h, hp, xstar, delta=Fr(1, 10**7)):
    """certified upper bound on max_{[0,1]} h for concave h, using the tangent bracket around xstar"""
    xa = rat(xstar) - delta; xb = rat(xstar) + delta
    sa, sb = hp(xa), hp(xb)
    assert sa.lo > 0 and sb.hi < 0, ("bracket failed", sa, sb)
    ha, hb = h(xa), h(xb)
    return max(ha.hi, hb.hi) + sa.hi*(xb - xa)


def certify_lower(q, c0, t0):
    q, c0, t0 = Fr(q), Fr(c0), Fr(t0)
    x1s = argmaxf(lambda x: Ff(x, float(c0)) + float(t0)*(Gf(x, float(c0)) - x*log(2)))[0]
    x2s = argmaxf(lambda x: Ff(x, float(c0)) + float(t0)*Gf(x, float(c0)))[0]
    M1 = cert_max(lambda x: F(x, c0) + t0*(G(x, c0) - Fr(x)*L2), lambda x: Fp(x, c0) + t0*(Gp(x, c0) - L2), x1s)
    M2 = cert_max(lambda x: F(x, c0) + t0*G(x, c0), lambda x: Fp(x, c0) + t0*Gp(x, c0), x2s)
    # Lam_col(t0,c0) * ln4 <= M1 + M2 ; need M1 + M2 < t0 q ln4
    rhs = t0*q*L4
    ok = M1 + M2 < rhs.lo
    gamma_lo = (rhs.lo - (M1 + M2))/L4.hi if ok else None
    eps_lo = (L4/A(c0)).lo
    return ok, M1, M2, rhs, gamma_lo, eps_lo


def certify_upper(q, c1, x1, x2):
    q, c1 = Fr(q), Fr(c1)
    gsum = g1(x1) + g2(x2); fsum = F(x1, c1) + F(x2, c1)
    ok = gsum.lo > (q*L4).hi and fsum.lo > 0
    return ok, gsum, fsum, (L4/A(c1)).hi


def main():
    print("Column-degree switching threshold of v1's squared run: certified enclosures\n")
    for q in (1.0, 0.5):
        cstar = brentq(lambda c: Lcolf(q, c)[0], 4.3, 4.99, xtol=1e-13)
        tstar = Lcolf(q, cstar)[1]
        creg = brentq(lambda c: region_maxf(c, q)[0], 4.3, 4.99, xtol=1e-12)
        print(f"q = {q}: float zero of L_col: c* = {cstar:.10f}, t* = {tstar:.8f}, eps = {log(4)/Af(cstar):.10f}")
        print(f"         float zero of the optimal region cut (R20 Sec. 5, by duality the same): c = {creg:.10f}")
        qF = Fr(q)
        # lower side
        c0 = rat(cstar + 2e-7, 10**10); t0 = rat(tstar, 10**10)
        ok, M1, M2, rhs, gam, eps_lo = certify_lower(qF, c0, t0)
        print(f"  LOWER: c0 = {c0} = {float(c0):.10f}, t0 = {t0} = {float(t0):.10f}")
        print(f"         ln4 * Lam_col(t0,c0) <= M1 + M2 = {float(M1):.15f} + {float(M2):.15f} = {float(M1+M2):.15f}")
        print(f"         t0 q ln4 >= {float(rhs.lo):.15f};  certified: {ok};  gamma >= {float(gam):.3e}")
        print(f"         => range eps >= ln4/A(c0) >= {float(eps_lo):.10f}  (certified lower bound)")
        # upper side
        c1 = rat(cstar - 2e-7, 10**10)
        val, x1f, x2f = region_maxf(float(c1), q)
        # move the point slightly into the region's interior (g-sum strictly above q ln4)
        x1 = rat(x1f + 1e-9); x2 = rat(x2f + 1e-9)
        ok2, gsum, fsum, eps_hi = certify_upper(qF, c1, x1, x2)
        print(f"  UPPER: c1 = {c1} = {float(c1):.10f}; point x1 = {float(x1):.12f}, x2 = {float(x2):.12f}")
        print(f"         g1+g2 in {gsum} vs q ln4 = {float(qF*L4.hi):.15f}; F(x1,c1)+F(x2,c1) in {fsum}; certified: {ok2}")
        print(f"         => no up-closed order-class cut with query exponent <= q saves at c <= c1;"
              f" eps of this construction <= ln4/A(c1) <= {float(eps_hi):.10f}")
        print()
    # total-order comparison (R20 headline), float
    def tot_rate(c, theta):
        return 2*Ff(theta, c)
    def qb(theta):
        r = minimize_scalar(lambda x: (-2*theta*log(x) + log((1+2*x)*(1+4*x)))/log(4), bounds=(1e-9, 1),
                            method="bounded", options=dict(xatol=1e-14))
        return r.fun
    for q in (1.0, 0.5):
        th = brentq(lambda th: qb(th) - q, 1e-4, 0.7, xtol=1e-14)
        cm = brentq(lambda c: Ff(th, c), 4.0, 4.999, xtol=1e-13)
        print(f"R20 total-order cut (Theorem 4 / Cor. 5), q = {q}: theta = {th:.8f}, c_min = {cm:.8f},"
              f" eps = {log(4)/Af(cm):.8f}  (float)")


if __name__ == "__main__":
    main()
