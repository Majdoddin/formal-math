#!/usr/bin/python3
"""R202: independent re-certification of r61b Theorem 7 (Section 6.4).

Box exponent at the product type p(rho) = ((1-rho)^2, rho(1-rho), rho(1-rho), rho^2) =: (p0,p1,p2,pw):
    B(p, theta) = max { H(t(v)) - H(p) : v in simplex, v4 <= 1 - theta },
    t(v) = (p0 + pw v1, p1 + pw v2, p2 + pw v3, pw v4).
Method (my own; not the tangent plane of r61b nor the bracketed stationary points of r154b):
the Lagrange dual with CLOSED-FORM inner suprema. For any real C and mu >= 0,
    B <= C + mu (1-theta) + sum_{i<3} s_i(C) + exp(-1 - (C+mu)/pw) - H(p),
    s_i(C) = sup_{y >= p_i} [ -y ln y - C (y - p_i)/pw ]
           = x + C p_i/pw  if x := exp(-1 - C/pw) >= p_i,   = -p_i ln p_i  otherwise,
(the v4 term is the same sup with p = 0). C, mu are read off the water-filling optimum and rounded to
rationals; everything is then evaluated in mpmath interval arithmetic (iv, 200 bits).
A rigorous LOWER bound comes from H(t(v)) - H(p) at an explicit rational feasible v.
Also: q(theta) = (H(theta) + theta ln 3)/ln 2 (query exponent), eps(rho) = rho^2 ln2/(ln4 - H2(rho))
(encoding range, deterministic covering by Lemma C), and the gamma these allow.
Run: nice /usr/bin/python3 r202_thm7_certify.py > r202_thm7_certify_out.txt
"""
from fractions import Fraction as Fr
import mpmath
from mpmath import mp, iv

mp.dps = 60
iv.prec = 200

def I(fr):
    """exact rational -> interval"""
    fr = Fr(fr)
    return iv.mpf(fr.numerator) / iv.mpf(fr.denominator)

def ih(y):  # -y ln y on an interval, y > 0
    return -y * iv.log(y)

def ptype(rho):
    rho = Fr(rho)
    return [(1 - rho) ** 2, rho * (1 - rho), rho * (1 - rho), rho ** 2]

def waterfill(p, theta):
    """float (mp) optimum of B: returns (t, C, mu, active)"""
    p = [mp.mpf(Fr(a).numerator) / Fr(a).denominator for a in p]
    th = mp.mpf(Fr(theta).numerator) / Fr(theta).denominator
    pw = p[3]
    t4 = pw * (1 - th)
    m = 1 - t4
    f = lambda x: sum(max(pi, x) for pi in p[:3]) - m
    x = mp.findroot(f, (min(p[:3]) * 0 + mp.mpf('1e-9'), 1), solver='bisect') if False else None
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(400):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            hi = mid
        else:
            lo = mid
    x = (lo + hi) / 2
    if x >= t4:  # constraint v4 <= 1-theta active
        C = -pw * (1 + mp.log(x))
        mu = pw * (mp.log(x) - mp.log(t4))
        t = [max(pi, x) for pi in p[:3]] + [t4]
        return t, C, mu, True
    # inactive: free water level y with t4 = min(pw, y)
    g = lambda y: sum(max(pi, y) for pi in p[:3]) + min(pw, y) - 1
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(400):
        mid = (lo + hi) / 2
        if g(mid) > 0:
            hi = mid
        else:
            lo = mid
    y = (lo + hi) / 2
    C = -pw * (1 + mp.log(y))
    t = [max(pi, y) for pi in p[:3]] + [min(pw, y)]
    return t, C, mp.mpf(0), False

def rat(x, den=10 ** 18):
    return Fr(int(mp.nint(x * den)), den)

def dual_UB(p, theta, C, mu):
    pI = [I(a) for a in p]
    pw = pI[3]
    CI, muI, thI = I(C), I(mu), I(theta)
    x = iv.exp(-1 - CI / pw)
    tot = CI + muI * (1 - thI)
    for pi in pI[:3]:
        a = x + CI * pi / pw
        if x.a > pi.b:
            tot += a
        elif x.b < pi.a:
            tot += ih(pi)
        else:  # undecided: x + C p/pw is an upper bound in all cases (sup over the larger set y > 0)
            tot += a
    tot += iv.exp(-1 - (CI + muI) / pw)
    Hp = sum(ih(pi) for pi in pI)
    return tot - Hp

def primal_LB(p, theta, t):
    """H(t(v)) - H(p) at a rational feasible v close to the water-filling optimum t"""
    p = [Fr(a) for a in p]
    theta = Fr(theta)
    pw = p[3]
    v = [max(Fr(0), rat((mp.mpf(ti) - mp.mpf(pi.numerator) / pi.denominator) /
                       (mp.mpf(pw.numerator) / pw.denominator))) for ti, pi in zip(t[:3], p[:3])]
    v4 = 1 - theta
    # fix the sum exactly: residual into the largest of v1..v3
    res = theta - sum(v)
    k = max(range(3), key=lambda i: v[i])
    v[k] += res
    assert all(vi >= 0 for vi in v) and sum(v) + v4 == 1 and v4 <= 1 - theta
    tt = [p[i] + pw * v[i] for i in range(3)] + [pw * v4]
    val = sum(ih(I(a)) for a in tt) - sum(ih(I(a)) for a in p)
    return val, v

LN2 = iv.log(2)
def q_of(theta):
    th = I(theta)
    return (ih(th) + ih(1 - th) + th * iv.log(3)) / LN2

def eps_of(rho):
    r = I(rho)
    H2 = ih(r) + ih(1 - r)
    return r * r * LN2 / (iv.log(4) - H2)

def show(x, n=10):
    return "[%s, %s]" % (mpmath.nstr(mpmath.mpf(x.a), n), mpmath.nstr(mpmath.mpf(x.b), n))

points = [(Fr(1, 2), Fr(1, 100)), (Fr(505, 1000), Fr(5, 100)), (Fr(51, 100), Fr(1, 10)),
          (Fr(522, 1000), Fr(185, 1000)), (Fr(523, 1000), Fr(189, 1000)),
          (Fr(52, 100), Fr(15, 100)), (Fr(5235, 10000), Fr(1892, 10000))]

print("R202 certificate for r61b 6.4 / Theorem 7: Lagrange dual with closed-form inner suprema, iv 200 bits")
print("columns: rho, theta | LB <= B <= UB | certified (UB<0) | gamma_box = -UB/(pw ln2) | q(theta) | eps(rho)")
for rho, theta in points:
    p = ptype(rho)
    t, C, mu, active = waterfill(p, theta)
    Cr, mur = rat(C), max(Fr(0), rat(mu))
    UB = dual_UB(p, theta, Cr, mur)
    LB, v = primal_LB(p, theta, t)
    pw = I(p[3])
    gbox = -UB / (pw * LN2)
    print("rho=%s theta=%s  active=%s" % (rho, theta, active))
    print("   LB = %s   UB = %s   gap = %.2e" % (mpmath.nstr(mpmath.mpf(LB.a), 12), mpmath.nstr(mpmath.mpf(UB.b), 12),
                                                  float(mpmath.mpf(UB.b) - mpmath.mpf(LB.a))))
    print("   certified B < 0: %s ;  B > 0 proved (LB > 0): %s" % (UB.b < 0, LB.a > 0))
    print("   gamma_box <= %s   q(theta) = %s   eps(rho) = %s" % (mpmath.nstr(mpmath.mpf(gbox.a), 8) if UB.b < 0 else "-",
                                                                  show(q_of(theta), 9), show(eps_of(rho), 9)))
    print("   optimum t = (%s)" % ", ".join(mpmath.nstr(ti, 9) for ti in t))

# Theorem 7's claim
rho, theta = Fr(523, 1000), Fr(189, 1000)
p = ptype(rho)
t, C, mu, active = waterfill(p, theta)
UB = dual_UB(p, theta, rat(C), max(Fr(0), rat(mu)))
e = eps_of(rho)
q = q_of(theta)
print()
print("Theorem 7 at (rho, theta) = (0.523, 0.189):")
print("   B <= %s < 0: %s" % (mpmath.nstr(mpmath.mpf(UB.b), 12), UB.b < 0))
print("   eps(rho) > 0.2731: %s (eps(rho) in %s)" % (e.a > I(Fr(2731, 10000)).b, show(e, 12)))
print("   q(theta) < 0.99894: %s (q in %s)" % (q.b < I(Fr(99894, 100000)).a, show(q, 12)))
print("   margin 0.99894 - q(theta) >= %s" % mpmath.nstr(mpmath.mpf((I(Fr(99894, 100000)) - q).a), 6))
pw = I(p[3])
gbox = -UB / (pw * LN2)
genc = I(Fr(10000, 2731)) - 1 / e
print("   gamma_box >= %s ; at eps = 0.2731 the encoding margin 1/eps - 1/eps(rho) >= %s" %
      (mpmath.nstr(mpmath.mpf(gbox.a), 8), mpmath.nstr(mpmath.mpf(genc.a), 8)))
print("   so any gamma < min of the two works at eps = 0.2731 (asymptotically, poly(L) factors absorbed)")
