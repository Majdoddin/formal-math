"""R206a: rigorous interval arithmetic over Fractions with logarithm enclosures.

Written for the adversarial check of r111b (independent of r111b_cert.py and r110b_certify.py).
Method for ln x, x a positive rational:
  x = 2^k z with z in [1, 2);  ln z = -ln(1-u) = sum_{n>=1} u^n/n,  u = 1 - 1/z in [0, 1/2).
  Partial sum to N terms; tail sum_{n>N} u^n/n <= u^{N+1} / ((N+1)(1-u)).
  ln 2 = sum_{n>=1} 1/(n 2^n), tail <= 2^{-N}/(N+1).
Every term is rounded outward to the grid 10^-PREC; the result is an Interval [lo, hi] with lo <= ln x <= hi.
(This is the Mercator series in u = 1 - 1/z, a different series from the atanh series of r111b/r110b.)
"""
from fractions import Fraction as F
import math

PREC = 60
SCALE = 10 ** PREC
NTERMS = 230          # u < 1/2  =>  tail < 2^-231 < 1e-69


def _floor(q):
    return F(math.floor(q * SCALE), SCALE)


def _ceil(q):
    return F(math.ceil(q * SCALE), SCALE)


class I:
    """Closed interval [lo, hi] of Fractions."""
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = lo, hi

    @staticmethod
    def c(x):
        return x if isinstance(x, I) else I(x)

    def __add__(self, o):
        o = I.c(o); return I(self.lo + o.lo, self.hi + o.hi)
    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, o):
        o = I.c(o); return I(self.lo - o.hi, self.hi - o.lo)

    def __rsub__(self, o):
        return I.c(o) - self

    def __mul__(self, o):
        o = I.c(o)
        p = [self.lo * o.lo, self.lo * o.hi, self.hi * o.lo, self.hi * o.hi]
        return I(min(p), max(p))
    __rmul__ = __mul__

    def inv(self):
        assert self.lo > 0 or self.hi < 0
        return I(1 / self.hi, 1 / self.lo)

    def __truediv__(self, o):
        return self * I.c(o).inv()

    def __rtruediv__(self, o):
        return I.c(o) * self.inv()

    def width(self):
        return self.hi - self.lo

    def mid(self):
        return float((self.lo + self.hi) / 2)

    def __repr__(self):
        return f"[{float(self.lo):.15g}, {float(self.hi):.15g}]"


def _mercator(u):
    """Enclosure of -ln(1-u) for rational 0 <= u <= 1/2 (u = 1/2 allowed for ln 2)."""
    u = F(u)
    assert 0 <= u <= F(1, 2)
    lo = F(0); hi = F(0)
    p = F(1)
    for n in range(1, NTERMS + 1):
        p *= u
        t = p / n
        lo += _floor(t); hi += _ceil(t)
    tail = p * u / ((NTERMS + 1) * (1 - u))
    return I(lo, hi + _ceil(tail))


_LN2 = _mercator(F(1, 2))


def ln2():
    return _LN2


def ln(x):
    """Rigorous enclosure of ln x for a positive rational x."""
    x = F(x)
    assert x > 0
    k = 0
    # reduce to z in [1, 2)
    num, den = x.numerator, x.denominator
    k = num.bit_length() - den.bit_length()
    z = x / F(2) ** k if k >= 0 else x * F(2) ** (-k)
    while z >= 2:
        z /= 2; k += 1
    while z < 1:
        z *= 2; k -= 1
    u = 1 - 1 / z          # in [0, 1/2)
    return k * _LN2 + _mercator(u)


def selftest():
    from decimal import Decimal, getcontext
    getcontext().prec = 70
    worst = 0
    for x in [F(2), F(3), F(1, 3), F(10), F(110057, 10000), F(56013, 1000000), F(100012, 100000), F(7, 5)]:
        e = ln(x)
        d = (Decimal(x.numerator) / Decimal(x.denominator)).ln()
        dd = F(str(d))
        assert e.lo <= dd + F(1, 10 ** 65) and dd - F(1, 10 ** 65) <= e.hi, (x, e, d)
        worst = max(worst, float(e.width()))
    return worst


if __name__ == "__main__":
    print("self-test against decimal.ln (70 digits): max enclosure width", selftest())
