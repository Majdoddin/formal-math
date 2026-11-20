"""R211b (2026-11-18): independent certification library for CP part (B1).

Written from scratch for R211b; it does not import or copy r74a_certify.py or r117_certify.py.
Trust base: Python's exact Fraction arithmetic and the series below (no floating point enters any certified number).

Intervals: pairs (lo, hi) of Fractions, every operation rounded outward to the grid 2^-PREC.
Logarithm of a positive rational x: x = 2^k y with y in [2/3, 4/3), ln x = k ln 2 + 2 artanh((y-1)/(y+1)),
ln 2 = 2 artanh(1/3); artanh(s) = sum_{j>=0} s^{2j+1}/(2j+1), truncated when the next term is below 2^-(PREC+10),
with the remainder bound |R_J| <= |s|^{2J+1}/((2J+1)(1 - s^2)) added as an interval [-R, R].
Points z0, x0 (where the concave functions are linearised) and the tilts t are chosen in floating point (mpmath,
non-interval); they do not enter validity, which only needs z0 interior (checked exactly on the rational z0).
"""
import sys
from fractions import Fraction as Fr
import mpmath as mp

PREC = 240
SC = 1 << PREC


def rdn(x):
    return Fr((x.numerator * SC) // x.denominator, SC)


def rup(x):
    return Fr(-((-x.numerator * SC) // x.denominator), SC)


class I:
    __slots__ = ('lo', 'hi')

    def __init__(self, lo, hi=None):
        lo = Fr(lo)
        hi = lo if hi is None else Fr(hi)
        if lo > hi:
            raise ValueError('empty interval')
        self.lo, self.hi = lo, hi

    @staticmethod
    def out(lo, hi):
        return I(rdn(lo), rup(hi))

    def __add__(s, o):
        o = cv(o)
        return I.out(s.lo + o.lo, s.hi + o.hi)

    __radd__ = __add__

    def __sub__(s, o):
        o = cv(o)
        return I.out(s.lo - o.hi, s.hi - o.lo)

    def __rsub__(s, o):
        return cv(o) - s

    def __neg__(s):
        return I(-s.hi, -s.lo)

    def __mul__(s, o):
        o = cv(o)
        p = (s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi)
        return I.out(min(p), max(p))

    __rmul__ = __mul__

    def inv(s):
        if not (s.lo > 0 or s.hi < 0):
            raise ZeroDivisionError('interval contains 0')
        return I.out(1 / s.hi, 1 / s.lo)

    def __truediv__(s, o):
        return s * cv(o).inv()

    def __rtruediv__(s, o):
        return cv(o) * s.inv()

    def absmax(s):
        return max(abs(s.lo), abs(s.hi))

    def width(s):
        return s.hi - s.lo

    def __repr__(s):
        return f'[{float(s.lo):.15g}, {float(s.hi):.15g}]'


def cv(o):
    return o if isinstance(o, I) else I(Fr(o))


def _artanh2(s):
    """interval of 2 artanh(s) for a rational |s| <= 1/3"""
    s = Fr(s)
    assert abs(s) <= Fr(1, 3)
    s2 = s * s
    tot = I(0)
    p = I(s)
    j = 0
    eps = Fr(1, 1 << (PREC + 10))
    while True:
        tot = tot + p / (2 * j + 1)
        j += 1
        p = p * s2
        if p.absmax() / (2 * j + 1) < eps:
            break
    # remainder: sum_{i>=j} |s|^{2i+1}/(2i+1) <= |s|^{2j+1}/((2j+1)(1-s^2))
    R = rup(abs(s) ** (2 * j + 1) / ((2 * j + 1) * (1 - s2)))
    tot = tot + I(-R, R)
    return tot * 2


LN2 = _artanh2(Fr(1, 3))
_cache = {}


def ln(x):
    """interval of ln x for a positive rational x"""
    x = Fr(x)
    if x in _cache:
        return _cache[x]
    if x <= 0:
        raise ValueError('ln of nonpositive')
    k = x.numerator.bit_length() - x.denominator.bit_length()
    y = x / Fr(2) ** k
    while y >= Fr(4, 3):
        y /= 2
        k += 1
    while y < Fr(2, 3):
        y *= 2
        k -= 1
    r = LN2 * k + _artanh2((y - 1) / (y + 1))
    _cache[x] = r
    return r


def phi(x):
    x = Fr(x)
    if x == 0:
        return I(0)
    return ln(x) * x


def H(ps):
    tot = I(0)
    for p in ps:
        tot = tot - phi(p)
    return tot


# ---------------------------------------------------------------- level-1 point
def point(parts):
    """parts: list of (q, lam, f) with f = u_q (q+2); returns intervals slack, lna, lnb, cbar, alpha"""
    slack = lna = lnb = cov = I(0)
    assert sum(Fr(l) for _, l, _ in parts) == 1
    for q, lam, f in parts:
        lam, f = Fr(lam), Fr(f)
        assert 0 < f < 1 and 0 < lam
        w = Fr(1, q + 2); u = f * w; v = (w - u) / 2; p = Fr(q, 2 * (q + 2))
        X = [p + w + v, p + u, v]; Z = [u + 2 * v, 2 * p, w]
        assert sum(X) == 1 and Z == [w, 2 * p, w]
        slack = slack + (H(X) - H(Z)) * lam
        lna = lna + ln(q) * (lam * p)
        lnb = lnb + ln(q) * (lam * u)
        cov = cov + (ln(q + 2) + LN2 * q) * (lam / (q + 2))
    return dict(slack=slack, lna=lna, lnb=lnb, cbar=cov / lna, alpha=lnb / lna)


# ---------------------------------------------------------------- the merged CW profile F_q (r74a Section 1)
def Fq_iv(q, t, z):
    """interval of F_q(t; z) and of its gradient at a rational interior z = (u, v, y)"""
    u, v, y = (Fr(c) for c in z)
    t = Fr(t)
    pi = Fr(1, q + 2)
    a = q * pi - u + v; b = pi + u; o = pi - v; w = q * pi - u + y
    # interior of P_q (strict), checked exactly
    assert 0 < y < v < pi and y < u and u - y < q * pi, 'z0 not interior'
    assert min(a, b, o, w, u - y, v - y, y) > 0
    lnq = ln(q)
    D = phi(a) - ln(q * pi) * a + phi(b) - ln(pi) * b + phi(o) - ln(pi) * o
    sig = (phi(b) - phi(pi) - phi(y) - phi(u - y) + lnq * (u - y) + phi(a) - phi(v - y) - phi(w))
    F = -D + sig * t
    dp = lambda s: ln(s) + 1
    Du = ln(b) - ln(a) + lnq
    Dv = ln(a) - ln(o) - lnq
    su = dp(b) - dp(u - y) + lnq - dp(a) + dp(w)
    sv = dp(a) - dp(v - y)
    sy = -dp(y) + dp(u - y) - lnq + dp(v - y) - dp(w)
    g = (-Du + su * t, -Dv + sv * t, sy * t)
    return F, g


def Gq_cert(q, t, z0):
    """certified upper bound G_q(t) <= F(z0) + sum |g_i| (r74a Lemma 3; P_q in [0,1]^3)"""
    F, g = Fq_iv(q, t, z0)
    bound = F.hi + sum(gi.absmax() for gi in g)
    return rup(bound), F, g


# float (mpmath) maximiser of F_q, used only to choose z0
def _Fq_mp(q, t, z):
    u, v, y = z
    pi = mp.mpf(1) / (q + 2)
    a = q * pi - u + v; b = pi + u; o = pi - v; w = q * pi - u + y
    ph = lambda s: s * mp.log(s)
    D = ph(a) - a * mp.log(q * pi) + ph(b) - b * mp.log(pi) + ph(o) - o * mp.log(pi)
    sig = ph(b) - ph(pi) - ph(y) - ph(u - y) + (u - y) * mp.log(q) + ph(a) - ph(v - y) - ph(w)
    return -D + t * sig


def _feasible(q, z):
    u, v, y = z
    pi = mp.mpf(1) / (q + 2)
    return 0 < y < v < pi and y < u and u - y < q * pi


def maximise_Fq(q, t, dps=50, start=None):
    mp.mp.dps = dps
    t = Fr(t)
    t = mp.mpf(t.numerator) / t.denominator
    pi = mp.mpf(1) / (q + 2)
    z = mp.matrix(start if start else [t * 0.55, t * 0.52, t * t * 0.06])
    lnq = mp.log(q)
    for it in range(200):
        u, v, y = z[0], z[1], z[2]
        a = q * pi - u + v; b = pi + u; o = pi - v; w = q * pi - u + y
        dp = lambda s: mp.log(s) + 1
        Du = mp.log(b) - mp.log(a) + lnq; Dv = mp.log(a) - mp.log(o) - lnq
        su = dp(b) - dp(u - y) + lnq - dp(a) + dp(w); sv = dp(a) - dp(v - y)
        sy = -dp(y) + dp(u - y) - lnq + dp(v - y) - dp(w)
        g = mp.matrix([-Du + t * su, -Dv + t * sv, t * sy])
        Huu = -(1 / a + 1 / b) + t * (1 / b + 1 / a - 1 / (u - y) - 1 / w)
        Huv = (1 / a) + t * (-1 / a)
        Huy = t * (1 / (u - y) + 1 / w)
        Hvv = -(1 / a + 1 / o) + t * (1 / a - 1 / (v - y))
        Hvy = t * (1 / (v - y))
        Hyy = t * (-1 / y - 1 / (u - y) - 1 / (v - y) - 1 / w)
        Hm = mp.matrix([[Huu, Huv, Huy], [Huv, Hvv, Hvy], [Huy, Hvy, Hyy]])
        d = mp.lu_solve(Hm, -g)
        f0 = _Fq_mp(q, t, z)
        st = mp.mpf(1)
        while True:
            zn = z + st * d
            if _feasible(q, zn) and _Fq_mp(q, t, zn) >= f0 - mp.mpf(10) ** (-dps + 5):
                break
            st /= 2
            if st < mp.mpf(10) ** -30:
                break
        z = zn
        if mp.norm(st * d) < mp.mpf(10) ** (-dps + 8):
            break
    return [z[0], z[1], z[2]]


def rat(x, digits=45):
    return Fr(mp.nstr(x, digits))


def Gq_auto(q, t):
    z = maximise_Fq(q, Fr(t))
    z0 = tuple(rat(c) for c in z)
    return Gq_cert(q, t, z0) + (z0,)


def Lpr_iv(q, t):
    """the closed-form (Lean part 11b) per-part bound t^2 ln^2(4 e q / t), as an interval"""
    t = Fr(t)
    L = ln(4 * q / t) + 1
    return L * L * (t * t)


# ---------------------------------------------------------------- the tile (r117b Lemma G')
def g_iv(c):
    c = Fr(c)
    return phi(c) - phi(c - 1) + ln(4) * (c - 1)


def A_iv(c):
    c = Fr(c)
    return ln(5) * (2 * c) - g_iv(c)


def tilephi_iv(t, c, x):
    """phi(x) = F(x) + t G(x) = x ln4 - phi(1-x) - (1-t) phi(c-1+x) + (1-t) phi(c-1) - t phi(x), and phi'(x)"""
    t, c, x = Fr(t), Fr(c), Fr(x)
    assert 0 < x < 1
    val = ln(4) * x - phi(1 - x) - phi(c - 1 + x) * (1 - t) + phi(c - 1) * (1 - t) - phi(x) * t
    der = ln(4) + ln(1 - x) - ln(c - 1 + x) * (1 - t) - ln(x) * t
    return val, der


def LamG_auto(t, c, dps=40):
    """certified upper bound on Lambda_G(t, c) = (2/ln4) max_{[0,1]} phi (concave; tangent bound, |x - x0| <= 1)"""
    mp.mp.dps = dps
    tt = mp.mpf(Fr(t).numerator) / Fr(t).denominator
    cc = mp.mpf(Fr(c).numerator) / Fr(c).denominator
    der = lambda x: mp.log(4) + mp.log(1 - x) - (1 - tt) * mp.log(cc - 1 + x) - tt * mp.log(x)
    lo, hi = mp.mpf(10) ** -30, 1 - mp.mpf(10) ** -30
    for _ in range(400):
        mid = (lo + hi) / 2
        if der(mid) > 0:
            lo = mid
        else:
            hi = mid
    x0 = rat((lo + hi) / 2, 40)
    val, d = tilephi_iv(t, c, x0)
    bound = val + I(0, d.absmax())
    return bound * 2 / ln(4), x0
