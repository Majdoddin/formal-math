"""R111b (3): exact rational certificate of explicit points for v1's data structure with pruned encodings.

Every quantity is an interval [lo, hi] of Fractions. Logarithms of rationals are enclosed rigorously:
ln x = k ln 2 + 2 atanh(y), y = (z-1)/(z+1), z = x/2^k in [2/3, 4/3] (|y| <= 1/7), with the alternating-free series
2 sum_{i<n} y^{2i+1}/(2i+1) and the remainder bound 2|y|^{2n+1}/((2n+1)(1-y^2)); ln 2 = 2 atanh(1/3) likewise.
Enclosures are rounded outward to denominators 10^45. Nothing is a float.

Point = (a = 1/eps, c, theta, gamma_c (claimed saving), gamma' (encoding), q_c (claimed query exponent), r).
Inequalities checked (source in brackets; the report r111b.md Section 3 lists them with margins):
 (C1) c > 5                                   [Lemma P needs rho_c = 4/(c-1) < 1; Thm m:thm:tech needs L >= 5m]
 (C2) 0 < theta <= 4/5                        [R14 Thm 1 / R14Boxes query_exact: 4x > 1]
 (C3) b(theta,c) + gamma' ln 2 < 0            [boxes: gamma(theta,c) = -b/ln2 > gamma'; R14 Step 1]
 (C4) 0 <= gamma_c < gamma'                   [absorbs the polynomial factors of boxes and encodings]
 (C5) H(theta) + theta ln 4 < q_c ln 2        [queries: q(theta) < q_c; R14 Step 2]
 (C6) q_c + gamma_c <= 1/2                    [Hyp: |W| D^{q_c} <= N^2/D^{gamma_c} at |W| <= N^2/sqrt D]
 (C7) ln r + g(c) + gamma' ln 4 < a ln 4, r>1 [pruned encodings, rate form; g(c) = c ln c - (c-1)ln(c-1) + (c-1)ln 4]
 (C8) 4^a C_P (c m0 + 2) <= r^{m0} and c <= (r-1)(c m0 + 2)   [threshold, base case and induction step]
      with C_P = 4c(c-1)/(mu2 (c-5)^2), mu2 = 0.08339 <= mu_inf^2   [encoding condition (encP), Section 2]
 (C9) m0 >= 2/(1-theta)                       [s = ceil(theta m)+1 <= m, R14 Step 1]
 (C10) gamma_c <= 1/2, 1/a <= 1/2              [Hyp's range]
Result: Hyp(1/a, gamma_c), eps*gamma = gamma_c/a.
"""
from fractions import Fraction as F
import math

PREC = F(1, 10**45)

def _round_out(lo, hi):
    lo_r = F(math.floor(lo / PREC)) * PREC
    hi_r = F(math.ceil(hi / PREC)) * PREC
    return lo_r, hi_r

def atanh_enc(y, n=60):
    s = F(0); p = y; y2 = y*y
    for i in range(n):
        s += p / (2*i+1)
        p *= y2
    err = abs(p) / ((2*n+1) * (1 - y2))   # |y|^{2n+1}/((2n+1)(1-y^2))
    return s - err, s + err

LN2 = None
def ln2():
    global LN2
    if LN2 is None:
        lo, hi = atanh_enc(F(1, 3))
        LN2 = _round_out(2*lo, 2*hi)
    return LN2

class I:
    def __init__(s, lo, hi=None):
        s.lo = F(lo); s.hi = F(lo if hi is None else hi)
        assert s.lo <= s.hi
    def __add__(s, o): o = o if isinstance(o, I) else I(o); return I(s.lo+o.lo, s.hi+o.hi)
    __radd__ = __add__
    def __neg__(s): return I(-s.hi, -s.lo)
    def __sub__(s, o): return s + (-(o if isinstance(o, I) else I(o)))
    def __rsub__(s, o): return I(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, I) else I(o)
        ps = [s.lo*o.lo, s.lo*o.hi, s.hi*o.lo, s.hi*o.hi]
        return I(min(ps), max(ps))
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        assert o.lo > 0 or o.hi < 0
        return s * I(1/o.hi, 1/o.lo) if o.lo > 0 else s * I(1/o.hi, 1/o.lo)
    def __repr__(s): return f"[{float(s.lo):.12g}, {float(s.hi):.12g}]"

def ln(x):
    x = F(x); assert x > 0
    k = 0; z = x
    while z > F(4, 3): z /= 2; k += 1
    while z < F(2, 3): z *= 2; k -= 1
    y = (z-1)/(z+1)
    lo, hi = atanh_enc(y)
    l2 = ln2()
    base = I(*_round_out(2*lo, 2*hi))
    return base + I(k*l2[0], k*l2[1]) if k >= 0 else base + I(k*l2[1], k*l2[0])

def LN2I(): return I(*ln2())

def b_enc(th, c):
    th, c = F(th), F(c)
    return th*2*LN2I() - (1-th)*ln(1-th) - (c-1+th)*ln(c-1+th) + (c-1)*ln(c-1)

def Hq_enc(th):           # H(theta) + theta ln 4
    th = F(th)
    return -th*ln(th) - (1-th)*ln(1-th) + th*2*LN2I()

def g_enc(c):
    c = F(c)
    return c*ln(c) - (c-1)*ln(c-1) + (c-1)*2*LN2I()

def find_m0(a, c, r, CP):
    """smallest m0 (by bisection on a float estimate, then exact check) with base and step conditions."""
    lhs = lambda m: math.log(float(F(4)**a if a.denominator == 1 else 2**float(2*a))) + math.log(float(CP)) + math.log(float(c*m + 2))
    f = lambda m: m*math.log(float(r)) - lhs(m)
    lo, hi = 1, 1
    while f(hi) < 0: hi *= 2
    while hi - lo > 1:
        mid = (lo+hi)//2
        if f(mid) >= 0: hi = mid
        else: lo = mid
    return hi

def exact_base(a, c, r, CP, m0):
    # 4^a C_P (c m0 + 2) <= r^m0, exactly (4^a with a = p/2: 2^p)
    four_a = F(4)**a if a.denominator == 1 else F(2)**int(2*a)
    assert (2*a).denominator == 1
    lhs = four_a * CP * (c*m0 + 2)
    return lhs <= F(r)**m0

def certify(name, a, c, th, gc, gp, qc, r, mu2=F(8339, 100000)):
    a, c, th, gc, gp, qc, r = map(F, (a, c, th, gc, gp, qc, r))
    print(f"\n=== {name}: 1/eps = {a}, c = {c}, theta = {th}, gamma_c = {gc}, gamma' = {gp}, q_c = {qc}, r = {r}")
    L2 = LN2I(); L4 = 2*L2
    rows = []
    def chk(label, ok, margin, src):
        rows.append((label, ok, margin, src)); print(f"  {label:6s} {'OK ' if ok else 'FAIL'} margin {margin}  [{src}]")
    chk("C1", c > 5, float(c-5), "c > 5")
    chk("C2", 0 < th <= F(4, 5), float(F(4,5)-th), "0 < theta <= 4/5")
    bb = b_enc(th, c)
    e3 = bb + gp*L2
    chk("C3", e3.hi < 0, f"{-float(e3.hi):.3e} (gamma(theta,c) in {(-bb/L2)})", "b + gamma' ln2 < 0")
    chk("C4", 0 <= gc < gp, float(gp-gc), "0 <= gamma_c < gamma'")
    hq = Hq_enc(th)
    e5 = hq - qc*L2
    chk("C5", e5.hi < 0, f"{-float(e5.hi):.3e} (q(theta) in {hq/L2})", "H(theta)+theta ln4 < q_c ln2")
    chk("C6", qc + gc <= F(1, 2), float(F(1,2) - qc - gc), "q_c + gamma_c <= 1/2")
    gg = g_enc(c)
    e7 = ln(r) + gg + gp*L4 - a*L4
    chk("C7", r > 1 and e7.hi < 0, f"{-float(e7.hi):.3e} (g(c) in {gg})", "ln r + g(c) + gamma' ln4 < a ln4")
    CP = 4*c*(c-1)/(mu2*(c-5)**2)
    m0 = find_m0(a, c, r, CP)
    ok8 = exact_base(a, c, r, CP, m0) and c <= (r-1)*(c*m0 + 2)
    chk("C8", ok8, f"m0 = {m0} (C_P = {float(CP):.4f})", "4^a C_P (c m0+2) <= r^m0 and induction step")
    chk("C9", m0 >= 2/(1-th), float(m0 - 2/(1-th)), "m0 >= 2/(1-theta)")
    chk("C10", gc <= F(1,2) and 1/a <= F(1,2), 0, "Hyp range")
    allok = all(r_[1] for r_ in rows)
    print(f"  ALL OK: {allok};  Hyp(1/{a}, {gc}) with eps*gamma = {gc/a} = {float(gc/a):.7f};  "
          f"3SUM exponent 2 - eps*gamma = {float(2 - gc/a):.7f}, Exact Triangle/APSP 3 - eps*gamma = {float(3 - gc/a):.7f}")
    return allok, m0

def exact_binomial_m0(a, c, gp, mu2=0.08339, mmax=None, start=1):
    """Computed (floats with lgamma; not part of the certificate): the first m from which (encP) itself holds,
    D^{gamma'} (L+1) P(L)^2 / (Kg N0) <= 4^{a(m-1)} with Kg = mu2*K, L = ceil(c m), P(L) = sum_{j<=m} C(L,j)4^{L-j}."""
    from math import lgamma, log, exp, ceil
    a, c, gp = float(a), float(c), float(gp)
    def lnP(L, m):
        lb0 = lgamma(L+1) - lgamma(m+1) - lgamma(L-m+1) + (L-m)*log(4)
        s = 0.0; term = 0.0  # ratios beta_e/beta_0 for e = 0..m (e = m - j)
        t = 0.0
        acc = 1.0
        for e in range(1, m+1):
            t += log(4*(m-e+1)/(L-m+e))
            acc += exp(t)
            if t < -50: break
        return lb0 + log(acc), lb0
    def holds(m):
        L = ceil(c*m)
        lp, lb0 = lnP(L, m)
        lK = lgamma(L+1) - lgamma(m+1) - lgamma(L-m+1)
        lhs = gp*m*log(4) + log(L+1) + 2*lp - (log(mu2) + lK) - (L-m)*log(4)
        return lhs <= a*(m-1)*log(4)
    # scan every m up to mmax and report the last m at which (encP) fails
    last_fail = 0
    for m in range(start, mmax + 1):
        if not holds(m): last_fail = m
    hi, spot = last_fail + 1, True
    return hi, spot

if __name__ == "__main__":
    pts = [
        ("P1 (eps*gamma = 0.0061)", 12, "10.5414", "0.05654", "0.0732", "0.07335", "0.4268", "1.00033"),
        ("P2 (eps*gamma = 0.00612)", F(25, 2), "11.0057", "0.056013", "0.0765", "0.07656", "0.4235", "1.00012"),
        ("P0 (comfortable, eps*gamma = 0.006)", 12, "10.45", "0.0566", "0.072", "0.0725", "0.428", "1.12"),
    ]
    for p in pts:
        ok, m0 = certify(*p)
        mb, _ = exact_binomial_m0(F(p[1]), F(p[2]), F(p[5]), mmax=m0 + 5000)
        print(f"  computed (lgamma floats, not certified): (encP) with exact binomials, exact P(L) and Kg = mu2 K holds"
              f" for every m in [{mb}, {m0 + 5000}] and fails at m = {mb - 1}" if mb > 1 else "  computed: holds from m = 1")
