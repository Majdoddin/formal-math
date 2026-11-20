"""R206j: rigorous interval logarithms over exact rationals (own code, written for this review).

ln x for a positive Fraction x: x = 2^k z with z in [2/3, 4/3], ln z = 2 atanh(s), s = (z-1)/(z+1), |s| <= 1/5,
atanh(s) = sum_{j>=0} s^(2j+1)/(2j+1) summed in fixed point with denominator 2^P, every term rounded outward,
tail |R| <= |s|^(2N+1) / ((2N+1)(1-s^2)).  ln 2 = 2 atanh(1/3) the same way.
An interval is a pair (lo, hi) of Fractions with lo <= true value <= hi.
"""
from fractions import Fraction as Fr

P = 320
SCALE = 1 << P


def _atanh_fixed(p, q, N):
    """Integers lo, hi with lo/SCALE <= atanh(p/q) <= hi/SCALE, for q > 0, |p/q| <= 1/3."""
    assert q > 0 and 3 * abs(p) <= q
    lo = hi = 0
    num, den = p, q
    p2, q2 = p * p, q * q
    for j in range(N):
        k = 2 * j + 1
        a = num * SCALE
        b = den * k
        fl = a // b
        lo += fl
        hi += fl if fl * b == a else fl + 1
        num *= p2
        den *= q2
    a = abs(num) * q2 * SCALE
    b = den * (2 * N + 1) * (q2 - p2)
    r = -(-a // b)
    return lo - r, hi + r


_l2lo, _l2hi = _atanh_fixed(1, 3, 110)
LN2 = (Fr(2 * _l2lo, SCALE), Fr(2 * _l2hi, SCALE))


def ln(x):
    x = Fr(x)
    assert x > 0
    k = x.numerator.bit_length() - x.denominator.bit_length()
    z = x / (Fr(2) ** k) if k >= 0 else x * (Fr(2) ** (-k))
    while z > Fr(4, 3):
        z /= 2
        k += 1
    while z < Fr(2, 3):
        z *= 2
        k -= 1
    p = z.numerator - z.denominator
    q = z.numerator + z.denominator
    lo, hi = _atanh_fixed(p, q, 75)
    alo, ahi = Fr(2 * lo, SCALE), Fr(2 * hi, SCALE)
    if k >= 0:
        return (k * LN2[0] + alo, k * LN2[1] + ahi)
    return (k * LN2[1] + alo, k * LN2[0] + ahi)


def scale(c, iv):
    c = Fr(c)
    return (c * iv[0], c * iv[1]) if c >= 0 else (c * iv[1], c * iv[0])


def add(*ivs):
    return (sum((v[0] for v in ivs), Fr(0)), sum((v[1] for v in ivs), Fr(0)))


def const(c):
    c = Fr(c)
    return (c, c)


def lin(*pairs):
    """sum of coef * interval over (coef, interval) pairs."""
    return add(*[scale(c, v) for c, v in pairs])


def width(iv):
    return iv[1] - iv[0]


def selftest():
    from decimal import Decimal, getcontext
    getcontext().prec = 110
    worst = Fr(0)
    pts = [Fr(1, 3), Fr(2), Fr(3), Fr(5), Fr(7, 10), Fr(45108852936, 10 ** 10), Fr(35108852936, 10 ** 10),
           Fr(1, 10 ** 9), Fr(999999, 10 ** 6), Fr(18220, 10 ** 5), Fr(10 ** 12 + 1, 10 ** 12), Fr(123456789, 1000)]
    ok = True
    for x in pts:
        lo, hi = ln(x)
        d = (Decimal(x.numerator) / Decimal(x.denominator)).ln()
        dlo = Fr(d) - Fr(1, 10 ** 100)
        dhi = Fr(d) + Fr(1, 10 ** 100)
        if not (lo <= dhi and dlo <= hi):
            ok = False
        worst = max(worst, hi - lo)
    # identity check: ln(a) + ln(b) and ln(ab) overlap
    a, b = Fr(17, 7), Fr(3, 11)
    la, lb, lab = ln(a), ln(b), ln(a * b)
    s = add(la, lb)
    ok = ok and s[0] <= lab[1] and lab[0] <= s[1]
    return ok, float(worst)


if __name__ == "__main__":
    ok, w = selftest()
    print("selftest agrees with decimal ln at 100 digits:", ok, " largest width:", "%.3e" % w)
