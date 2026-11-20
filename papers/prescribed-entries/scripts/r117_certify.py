"""R117 (r117.md): certified rational points for Theorem D with a product top algorithm CW(6/7) x G(c).

No mpmath: logarithms of rationals are enclosed with exact Fractions (artanh series with an explicit tail bound,
ln x = k ln 2 + 2 artanh((y-1)/(y+1)), y = x/2^k in [2/3, 4/3]); every interval endpoint is rounded outward to the
grid 2^-200.  All other arithmetic is exact rational arithmetic on interval endpoints.

Certified quantities at a rational point (lam6, u6(q+2), u7(q+2), c, t, f):
  CW factor: slack > 0, ln a_1, ln b_1, alpha(P), cbar (t <= 1/(cbar+2)), and the upper bound of r74a Lemma 1:
     G_q(t) <= F_q(t, z0) + sum_i |dF_q/dz_i(t, z0)|  (F_q concave on its polytope in [0,1]^3, z0 interior rational),
     Lambda_CW,D(t) <= (lam6 G_6 + lam7 G_7)/ln b_1;
  G factor (r105 Section 1): Lambda_G(t, c) = (2/ln4) max_{0<=x<1} phi(x), phi = F + tG concave, so
     max phi <= phi(x0) + |phi'(x0)|;  A(c) = 2c ln5 - g(c), g(c) = ln c + (c-1) ln(c/(c-1)) + (c-1) ln 4;
  Theorem D (product form, r117.md Section 2):  Qc = t/2 - (1-f) Lambda_CW,D - f Lambda_G   (lower bound),
     a_mix = (1-f) ln a_1/ln b_1 + f A(c)/ln4  (upper bound);  Hyp(eps, gamma) for every gamma < Qc and every
     eps < eps1 = 1/(a_mix + Qc).
Run: ~/.venv/bin/python r117_certify.py > r117_certify_out.txt
"""
import os, sys
from fractions import Fraction as Fr
from math import floor, log2
import numpy as np
from scipy.optimize import minimize, brentq
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

PREC = 200
SC = 1 << PREC


def rdn(x):
    return Fr(floor(x*SC), SC)


def rup(x):
    return -rdn(-x)


class I:
    """closed interval with Fraction endpoints."""
    def __init__(self, lo, hi=None):
        self.lo = Fr(lo); self.hi = Fr(lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def c(x):
        return x if isinstance(x, I) else I(x)

    def __add__(self, o):
        o = I.c(o); return I(self.lo + o.lo, self.hi + o.hi)
    __radd__ = __add__

    def __sub__(self, o):
        o = I.c(o); return I(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return I.c(o) - self

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __mul__(self, o):
        o = I.c(o)
        p = [self.lo*o.lo, self.lo*o.hi, self.hi*o.lo, self.hi*o.hi]
        return I(rdn(min(p)), rup(max(p)))
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = I.c(o)
        assert o.lo > 0 or o.hi < 0
        return self*I(rdn(1/o.hi), rup(1/o.lo)) if o.lo > 0 else self*I(rdn(1/o.hi), rup(1/o.lo))

    def __rtruediv__(self, o):
        return I.c(o)/self

    def mag(self):
        return max(abs(self.lo), abs(self.hi))

    def __repr__(self):
        return f"[{float(self.lo):.15g}, {float(self.hi):.15g}]"


def artanh(z, J=60):
    """enclosure of artanh(z) = sum_j z^(2j+1)/(2j+1), |z| < 1, by the partial sum and a geometric tail bound."""
    z = Fr(z)
    if z < 0:
        r = artanh(-z, J); return I(-r.hi, -r.lo)
    zz = z*z; plo = phi_ = z; lo = hi = Fr(0)
    for j in range(J):
        lo += rdn(plo/(2*j + 1)); hi += rup(phi_/(2*j + 1))
        plo = rdn(plo*zz); phi_ = rup(phi_*zz)
    tail = rup(phi_/((2*J + 1)*(1 - zz)))
    return I(lo, hi + tail)


LN2 = 2*artanh(Fr(1, 3))
LNC = {}


def ln(x):
    x = Fr(x)
    assert x > 0
    if x in LNC:
        return LNC[x]
    k = x.numerator.bit_length() - x.denominator.bit_length()
    y = x/Fr(2)**k
    while y > Fr(4, 3):
        y /= 2; k += 1
    while y < Fr(2, 3):
        y *= 2; k -= 1
    r = k*LN2 + 2*artanh((y - 1)/(y + 1))
    LNC[x] = r
    return r


def lnI(xi):
    """ln of an interval with rational endpoints (monotone)."""
    a, b = ln(xi.lo), ln(xi.hi)
    return I(a.lo, b.hi)


# ------------------------------------------------------------------ CW part (r74a_certify formulas, intervals)
def phi(s):
    return s*ln(s)


def F_cw(q, t, u, v, y):
    pi = Fr(1, q + 2); qpi = Fr(q, q + 2); lq = ln(q)
    a = qpi - u + v; b = pi + u; o = pi - v
    D = phi(a) - a*ln(qpi) + phi(b) - b*ln(pi) + phi(o) - o*ln(pi)
    sig = phi(b) - phi(pi) - phi(y) - phi(u - y) + (u - y)*lq + phi(a) - phi(v - y) - phi(qpi - u + y)
    return -D + t*sig


def grad_cw(q, t, u, v, y):
    dphi = lambda s: ln(s) + 1
    pi = Fr(1, q + 2); qpi = Fr(q, q + 2); lq = ln(q)
    a = qpi - u + v; b = pi + u; o = pi - v; w = qpi - u + y
    Du = ln(b) - ln(a) + lq
    Dv = ln(a) - ln(o) - lq
    su = dphi(b) - dphi(u - y) + lq - dphi(a) + dphi(w)
    sv = dphi(a) - dphi(v - y)
    sy = -dphi(y) + dphi(u - y) - lq + dphi(v - y) - dphi(w)
    return (-Du + t*su, -Dv + t*sv, t*sy)


def float_argmax_cw(q, t):
    import r112_smallt as R
    v, (u, vv, y, res) = R.Gq(q, t)
    return u, vv, y


def certify_Gq(q, t):
    u, v, y = float_argmax_cw(q, float(t))
    z0 = [Fr(x).limit_denominator(10**18) for x in (u, v, y)]
    u, v, y = z0
    pi = Fr(1, q + 2)
    assert 0 < v < pi and 0 < y < v and y < u and u - y < q*pi, "z0 not interior"
    Fz = F_cw(q, t, u, v, y)
    g = grad_cw(q, t, u, v, y)
    return Fz.hi + sum(rup(x.mag()) for x in g), Fz


def point_cw(lam6, f6, f7):
    slack = I(0); lna = I(0); lnb = I(0); cb = I(0)
    for q, lam, f in ((6, lam6, f6), (7, 1 - lam6, f7)):
        w = Fr(1, q + 2); u = f*w; v = (w - u)/2; p = Fr(q, 2*(q + 2))
        X = [p + w + v, p + u, v]; Z = [u + 2*v, 2*p, w]
        H = lambda V: -sum((cc*ln(cc) for cc in V), I(0))
        slack = slack + lam*(H(X) - H(Z))
        lna = lna + (lam*p)*ln(q)
        lnb = lnb + (lam*u)*ln(q)
        cb = cb + lam*((ln(q + 2) + q*LN2)*Fr(1, q + 2))
    return slack, lna, lnb, cb/lna


# ------------------------------------------------------------------ G part
def phiG(x, c, t):
    c1 = c - 1
    F = x*ln(4/c1) - (1 - x)*ln(1 - x) - (c1 + x)*ln((c1 + x)/c1)
    G = (c1 + x)*ln(c1 + x) - x*ln(x) - c1*ln(c1)
    return F + t*G


def dphiG(x, c, t):
    c1 = c - 1
    return ln(4*(1 - x)/(c1 + x)) + t*ln((c1 + x)/x)


def certify_LamG(c, t):
    cf, tf = float(c), float(t)
    d = lambda x: np.log(4*(1 - x)/(cf - 1 + x)) + tf*np.log((cf - 1 + x)/x)
    x0 = brentq(d, 1e-300, 1 - 1e-15, xtol=1e-18, rtol=1e-15)
    x0 = Fr(x0).limit_denominator(10**18)
    val = phiG(x0, c, t)
    slope = dphiG(x0, c, t)
    ub = val.hi + rup(slope.mag())
    L4 = 2*LN2
    return I(0, ub)*2/L4, x0          # Lambda_G >= 0 (x = 0 gives phi = 0)


def Ac(c):
    g = ln(c) + (c - 1)*ln(c/(c - 1)) + (c - 1)*2*LN2
    return 2*c*ln(5) - g


def certify(lam6, f6, f7, c, t, f, label, prof="num"):
    slack, lna, lnb, cbar = point_cw(lam6, f6, f7)
    alpha = lnb/lna
    T = 1/(cbar + 2)
    assert slack.lo > 0, f"slack not certified positive: {slack}"
    assert t <= T.lo, f"t = {t} above 1/(cbar+2) = {T}"
    if prof == "num":
        G6, _ = certify_Gq(6, t); G7, _ = certify_Gq(7, t)
    else:                                   # proved closed-form bound t^2 ln^2(4eq/t) (P2-Theorem 2.4, Lean part 11b)
        lpr = lambda q: (lambda L: L*L)(ln(Fr(4*q)/t) + 1)*(t*t)
        G6, G7 = lpr(6).hi, lpr(7).hi
    LamCW = I(0, lam6*G6 + (1 - lam6)*G7)/lnb
    LamG, x0 = certify_LamG(c, t)
    Qc = t/2 - (1 - f)*LamCW - f*LamG
    aG = Ac(c)/(2*LN2)
    amix = (1 - f)*(lna/lnb) + f*aG
    eps1 = 1/(amix + Qc)
    print(f"  {label} [CW profile: {prof}]: lam6 = {lam6}, u6(q+2) = {f6}, u7(q+2) = {f7}, c = {c}, t = {t}, f = {f}")
    print(f"     slack {slack.lo:.3e}>0 (float {float(slack.lo):.3e}); alpha(P) in {alpha}; 1/(cbar+2) >= {float(T.lo):.4f}")
    print(f"     G_6(t) <= {float(G6):.12e}, G_7(t) <= {float(G7):.12e}; Lambda_CW,D(t) <= {float(LamCW.hi):.10e}")
    print(f"     Lambda_G(t, c) <= {float(LamG.hi):.10e} (x0 = {float(x0):.6e}); A(c)/ln4 in {aG}")
    print(f"     query term Qc >= {float(Qc.lo):.10e};  encoding a_mix <= {float(amix.hi):.10f}")
    print(f"     => Hyp(eps, gamma) for every gamma < {float(Qc.lo):.7e} and every eps < {float(eps1.lo):.7f}"
          f"   (eps1*gamma = {float(eps1.lo*Qc.lo):.6e})", flush=True)
    return float(Qc.lo), float(eps1.lo)


def selftest():
    import math
    for x in (Fr(2), Fr(3), Fr(5), Fr(7, 3), Fr(1, 1000), Fr(123456789, 1000)):
        r = ln(x)
        assert r.lo <= Fr(math.log(float(x))) + Fr(1, 10**12) and r.hi >= Fr(math.log(float(x))) - Fr(1, 10**12)
        assert float(r.hi - r.lo) < 1e-50, (x, r)
    print("  ln enclosures: widths < 1e-50 and consistent with math.log at 6 points")
    # r74a's certified value G_6(0.0196) = 0.0012944331521 (r78 / r74a)
    ub, Fz = certify_Gq(6, Fr(49, 2500))
    print(f"  check: G_6(49/2500) <= {float(ub):.13e} (r74a/r78: 0.0012944331521); F(z0) in {Fz}")
    ub, Fz = certify_Gq(7, Fr(49, 2500))
    print(f"  check: G_7(49/2500) <= {float(ub):.13e} (r78: 0.0012082016806)")
    LamG, _ = certify_LamG(Fr(9, 2), Fr(0))
    print(f"  check: Lambda_G(0, 4.5) <= {float(LamG.hi):.6e} (r105: 0.00976)")
    print(f"  check: ln4/A(4.82681) in {(2*LN2)/Ac(Fr(482681, 100000))} (r105: eps_1/2 = 0.178434)")


if __name__ == "__main__":
    print("(0) self-tests")
    selftest()
    print("\n(1) certified points (product CW(6/7) x G(c); parameters rounded from r117_refine_out.txt)")
    PTS = [l.split() for l in open(os.path.join(HERE, "r117_certify_points.txt")) if l.strip() and not l.startswith("#")]
    for p in PTS:
        lab, lam6, f6, f7, c, t, f = p[:7]
        certify(Fr(lam6), Fr(f6), Fr(f7), Fr(c), Fr(t), Fr(f), lab, p[7] if len(p) > 7 else "num")
