#!/usr/bin/env python3
"""R206c (independent review of R82a / R110 / R110b): exact recomputation of r110b's certificate.

Written from scratch; it does not import or copy r110b_certify.py. Only the rational parameters (c, theta, eps, d)
of the three chains are taken from calc/r110b_certify_out.txt (as data). Two independent log enclosures:
  (M) own Mercator series ln(1+z), |z| <= 1/3, after reduction r = 2^k y with y in [2/3, 4/3]; ln 2 = ln(4/3) - ln(2/3);
      tail bound |z|^{n+1}/((n+1)(1-|z|)); exact Fractions, endpoints rounded outward to 2^-220.
  (D) Python's decimal module ln() at 90 digits (correctly rounded), widened by 1e-80.
Checks per chain (r110b.md Theorem 1): T1, B, R, Q, C2, C3, V, end condition, S. In addition an identity-free
check of the coverage step: on each strip p in [d_{i-1}, min(d_i, x)], alpha in [tau, p/2] the space exponent
max(1-alpha, M) + max(1-p+alpha, M) - gamma d is convex piecewise linear, so its maximum is at one of the four
vertices; all four are checked against 2 - x in exact interval arithmetic.
Then r82a / Lean witness numbers (cor:zt, eta_r14_witness, eta_split_witness).
"""
from fractions import Fraction as F
import decimal

BITS = 220
SC = 1 << BITS


def rdown(x):
    return F((x.numerator * SC) // x.denominator, SC)


def rup(x):
    return F(-((-x.numerator * SC) // x.denominator), SC)


class Iv:
    __slots__ = ('lo', 'hi')

    def __init__(s, lo, hi=None):
        lo = F(lo); hi = lo if hi is None else F(hi)
        assert lo <= hi, (lo, hi)
        s.lo, s.hi = lo, hi

    def __add__(s, o): o = iv(o); return Iv(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__
    def __neg__(s): return Iv(-s.hi, -s.lo)
    def __sub__(s, o): o = iv(o); return Iv(s.lo - o.hi, s.hi - o.lo)
    def __rsub__(s, o): return iv(o) - s

    def __mul__(s, o):
        o = iv(o); p = (s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi); return Iv(min(p), max(p))
    __rmul__ = __mul__

    def inv(s):
        assert s.lo > 0 or s.hi < 0
        return Iv(1 / s.hi, 1 / s.lo)

    def __truediv__(s, o): return s * iv(o).inv()
    def __rtruediv__(s, o): return iv(o) * s.inv()
    def tidy(s): return Iv(rdown(s.lo), rup(s.hi))
    def w(s): return float(s.hi - s.lo)
    def __repr__(s): return f"[{float(s.lo):.15g}, {float(s.hi):.15g}]"


def iv(x): return x if isinstance(x, Iv) else Iv(x)


def imax(*a):
    a = [iv(t) for t in a]; return Iv(max(t.lo for t in a), max(t.hi for t in a))


# ---- (M) Mercator enclosure ----
def ln1p_M(z):
    z = F(z); az = abs(z); assert az <= F(1, 3)
    s, term, n = F(0), F(1), 0
    tol = F(1, 1 << (BITS + 8))
    while True:
        n += 1; term *= z; s += term / n if n % 2 else -term / n
        tail = az ** (n + 1) / ((n + 1) * (1 - az))
        if tail < tol:
            return Iv(rdown(s - tail), rup(s + tail))
        # keep sizes bounded
        if n % 20 == 0:
            pass


LN2_M = (ln1p_M(F(1, 3)) - ln1p_M(F(-1, 3))).tidy()


def ln_M(r):
    r = F(r); assert r > 0
    k = 0; y = r
    while y > F(4, 3): y /= 2; k += 1
    while y < F(2, 3): y *= 2; k -= 1
    return (k * LN2_M + ln1p_M(y - 1)).tidy()


# ---- (D) decimal enclosure ----
decimal.getcontext().prec = 90
WID = F(1, 10 ** 80)


def ln_D(r):
    r = F(r); v = (decimal.Decimal(r.numerator) / decimal.Decimal(r.denominator)).ln()
    v = F(v); return Iv(v - WID, v + WID)


# ---- (W) robustness: every log widened by +-2e-9 and ln 2 replaced by Mathlib's [0.6931471803, 0.6931471808] ----
LN2_W = Iv(F(6931471803, 10 ** 10), F(6931471808, 10 ** 10))
WW = F(2, 10 ** 9)


def ln_W(r):
    r = F(r); k = 0; y = r
    while y > F(4, 3): y /= 2; k += 1
    while y < F(2, 3): y *= 2; k -= 1
    v = k * LN2_W + ln1p_M(y - 1)
    return Iv(v.lo - WW, v.hi + WW).tidy()


def quantities(c, th, LN):
    c, th = F(c), F(th)
    l2, l4, l5 = LN(2), LN(4), LN(5)
    lth, l1th = LN(th), LN(1 - th)
    lcm1, lcm1t, lc = LN(c - 1), LN(c - 1 + th), LN(c)
    b = th * l4 - (1 - th) * l1th - (c - 1 + th) * lcm1t + (c - 1) * lcm1
    H = -th * lth - (1 - th) * l1th
    q = (H + th * l4) / l2
    gam = -b / l2
    A = 2 * c * l5 - c * lc + (c - 1) * lcm1 - (c - 1) * l4
    return dict(b=b.tidy(), q=q.tidy(), gam=gam.tidy(), A=A.tidy(), l4=l4, l2=l2)


def check_chain(tau, eta0, chain, LN, out, tag):
    tau, eta0 = F(tau), F(eta0); x = 2 * tau + eta0
    rows = []
    rows.append(("S  (2-eta0)-(1+2tau)", 0, Iv(2 - eta0 - 1 - 2 * tau)))
    prev = 2 * tau; Qs = []
    for i, (c, th, eps, d) in enumerate(chain, 1):
        c, th, eps, d = map(F, (c, th, eps, d))
        assert c >= 2 and 0 < th < F(4, 5) and eps > 0 and d > 0          # T1
        Q = quantities(c, th, LN); Qs.append(Q)
        M = d / eps
        rows.append(("B  -b", i, -Q['b']))
        rows.append(("R  ln4-eps(A-2b)", i, Q['l4'] - eps * (Q['A'] - 2 * Q['b'])))
        rows.append(("Q  tau-q d", i, tau - Q['q'] * d))
        rows.append(("C2 (1+tau-x)-(M-gam d)", i, (1 + tau - x) - (M - Q['gam'] * d)))
        rows.append(("C3 (2-x)-(2M-gam d)", i, (2 - x) - (2 * M - Q['gam'] * d)))
        rows.append(("V  d_prev-(x-gam d)", i, prev - (x - Q['gam'] * d)))
        prev = d
    rows.append(("Vend d_K - x", len(chain), Iv(prev - x)))
    # identity-free vertex check of the coverage step
    prev = 2 * tau; vmin = None
    for i, (c, th, eps, d) in enumerate(chain, 1):
        c, th, eps, d = map(F, (c, th, eps, d)); Q = Qs[i - 1]; M = d / eps
        hi = min(d, x)
        if hi > prev:
            for p in (prev, hi):
                for al in (tau, p / 2):
                    cost = imax(1 - al, M) + imax(1 - p + al, M) - Q['gam'] * d
                    m = (2 - x) - cost
                    vmin = m if vmin is None or m.lo < vmin.lo else vmin
                    assert d >= p
        prev = d
    rows.append(("VX vertex cost margin (min)", '-', vmin))
    ok = all(r[2].lo > 0 for r in rows if r[0] != "Vend d_K - x") and rows[-2][2].lo >= 0
    mn = min(rows, key=lambda r: r[2].lo)
    out.append(f"  [{tag}] all {len(rows)} checks positive: {ok}; smallest lower bound {float(mn[2].lo):.4e} "
               f"({mn[0].strip()}, structure {mn[1]}); max enclosure width {max(r[2].w() for r in rows):.1e}")
    return rows, ok


CHAINS = {
    "eta0=0.0069": (F(3279, 100000), F(69, 10000), [
        (F(24227, 2000), F(68257, 1000000), F(8545507, 125000000), F(66121309, 1000000000)),
        (F(114169, 10000), F(31563, 500000), F(18198529, 250000000), F(35183189, 500000000)),
        (F(13423, 2000), F(797, 25000), F(25473353, 200000000), F(61289959, 500000000))]),
    "eta0=0.00697": (F(3279, 100000), F(697, 100000), [
        (F(7628, 625), F(13789, 200000), F(13564369, 200000000), F(13119363, 200000000)),
        (F(30457, 2500), F(3439, 50000), F(67951727, 1000000000), F(65721523, 1000000000)),
        (F(60101, 5000), F(67569, 1000000), F(68926793, 1000000000), F(33327857, 500000000)),
        (F(108347, 10000), F(58937, 1000000), F(76945373, 1000000000), F(18584617, 250000000))]),
    "eta0=0.006973": (F(131, 4000), F(6973, 1000000), [
        (F(6111, 500), F(13793, 200000), F(8465187, 125000000), F(6550261, 100000000)),
        (F(61093, 5000), F(68939, 1000000), F(16935371, 250000000), F(3276111, 50000000)),
        (F(121929, 10000), F(68747, 1000000), F(67892901, 1000000000), F(513027, 7812500)),
        (F(120033, 10000), F(67337, 1000000), F(69030553, 1000000000), F(66757569, 1000000000)),
        (F(26561, 2500), F(28677, 500000), F(9820039, 125000000), F(18971911, 250000000))]),
}


def main():
    out = []
    out.append(f"ln2 (M) = {LN2_M} width {LN2_M.w():.1e};  ln2 (D) = {ln_D(2)}")
    # sanity: the two enclosures of a few logs must overlap
    for r in (F(3, 7), F(122228, 10000), F(5), F(931743, 1000000)):
        a, b = ln_M(r), ln_D(r)
        assert a.lo <= b.hi and b.lo <= a.hi, r
    out.append("(M) and (D) enclosures overlap on test values: True")
    for name, (tau, eta0, chain) in CHAINS.items():
        x = 2 * tau + eta0
        out.append(f"\n=== {name}: tau = {tau} ({float(tau)}), eta0 = {eta0}, x = {float(x)}, K = {len(chain)}")
        for LN, tag in ((ln_M, "Mercator"), (ln_D, "decimal"), (ln_W, "wide 2e-9 + Mathlib ln2")):
            rows, ok = check_chain(tau, eta0, chain, LN, out, tag)
            if tag == "Mercator":
                for r in rows:
                    out.append(f"    {r[0]:28s} Pi_{r[1]}: lower bound {float(r[2].lo): .6e}")
        out.append("    decimals: " + "; ".join(f"({float(c):.6g}, {float(th):.6g}, {float(eps):.9g}, {float(d):.9g})"
                                               for c, th, eps, d in chain))
        for i, (c, th, eps, d) in enumerate(chain, 1):
            Q = quantities(c, th, ln_M)
            g, q = float(Q['gam'].lo), float(Q['q'].lo)
            out.append(f"    Pi_{i}: gamma {g:.7f} q {q:.7f}  serves p in [{float(x) - g * float(d):.9f}, {float(d):.9f}]")

    # ---- r82a / Lean witnesses ----
    out.append("\n=== r82a construction numbers (eta = 2 g eps/(4 + (2 - 2 gamma - g) eps), g = min(2 gamma, 1 - 2q))")
    eps, gam, q = F(1, 18), F(63, 1000), F(437, 1000)
    g = min(2 * gam, 1 - 2 * q); lam = 2 / (4 / eps + 2 - 2 * gam - g); eta = g * lam
    out.append(f"  cor:zt: g = {g}, lambda = {lam} = {float(lam):.7f}, eta = {eta} = {float(eta):.7f}, "
               f"T exp = {float(lam * (1 - g)):.7f}, S exp = {float(2 - eta - 2 * lam * (1 - g)):.6f}; "
               f"padding term exp = {float(lam * (4 / eps - 2 * gam + 2 - 2 * g)):.6f}; eta == 63/18437: {eta == F(63, 18437)}")
    # eta_r14_witness
    th, c, eps = F(5654, 100000), F(10525, 1000), F(79346, 1000000)
    Q = quantities(c, th, ln_M)
    Rm = Q['l4'] - eps * (Q['A'] - 2 * Q['b'])
    g = Q['gam'] * 2 if (Q['gam'] * 2).hi < (1 - 2 * Q['q']).lo else None
    g2 = 1 - 2 * Q['q']
    out.append(f"  eta_r14_witness (theta 0.05654, c 10.525, eps 0.079346): b {Q['b']}, q {Q['q']}, "
               f"R-margin {Rm}, 2gamma {Q['gam']*2}, 1-2q {g2}")
    gI = Iv(min((Q['gam'] * 2).lo, g2.lo), min((Q['gam'] * 2).hi, g2.hi))
    den = 4 + (2 - 2 * Q['gam'] - gI) * eps
    etaI = (2 * gI * eps) / den
    out.append(f"    eta in {etaI}; eta > 0.00563: {etaI.lo > F(563, 100000)}; margin {float(etaI.lo - F(563,100000)):.3e}")
    # eta_split_witness (main.tex Cor. m:cor:tradeoff: gamma = theta log2((c-1)/4))
    th, c, eps = F(5656, 100000), F(10815, 1000), F(77126, 1000000)
    l2, l4, l5 = ln_M(2), ln_M(4), ln_M(5)
    gam = (th * (ln_M(c - 1) - l4) / l2).tidy()
    H = -th * ln_M(th) - (1 - th) * ln_M(1 - th)
    q = ((H + th * l4) / l2).tidy()
    A = 2 * c * l5 - c * ln_M(c) + (c - 1) * ln_M(c - 1) - (c - 1) * l4
    Rm = l4 - eps * (A + gam * l4)
    g2 = 1 - 2 * q
    gI = Iv(min((gam * 2).lo, g2.lo), min((gam * 2).hi, g2.hi))
    etaI = (2 * gI * eps) / (4 + (2 - 2 * gam - gI) * eps)
    out.append(f"  eta_split_witness (theta 0.05656, c 10.815, eps 0.077126): gamma {gam}, q {q}, R-margin {Rm.tidy()}, "
               f"eta in {etaI.tidy()}; eta > 0.00546: {etaI.lo > F(546, 100000)}")
    print("\n".join(out))


if __name__ == "__main__":
    main()
