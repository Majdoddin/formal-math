"""R211a: certified enclosures at the level-1 point P0 = (lam_6, u_6 (q+2), u_7 (q+2)) = (7/19, 97/100, 979/1000).
Exact rational arithmetic (fractions.Fraction); every logarithm of a rational is enclosed by the artanh series
with a rigorous tail bound, so every printed interval is CERTIFIED (no floating point enters an enclosure).
Quantities (r59-theorem-level1.md Section 1, 2.2): ln a_1, ln b_1, alpha(P0) = ln b_1/ln a_1, slack(P0),
cbar(P0), and the Salem-Spencer exponent unit H(joint) - H(Z) per part.  Usage: python3 -I r211a_p0_certify.py"""
from fractions import Fraction as F

TERMS = 40  # artanh terms; tail bound below makes the width far below 1e-20

def ln_iv(x):
    """Rigorous (lo, hi) with lo <= ln x <= hi for rational x > 0."""
    x = F(x)
    assert x > 0
    k = 0
    while x > F(4, 3):
        x /= 2; k += 1
    while x < F(2, 3):
        x *= 2; k -= 1
    lo2, hi2 = _artanh_ln(F(2))
    lo, hi = _artanh_ln(x)
    if k >= 0:
        return lo + k * lo2, hi + k * hi2
    return lo + k * hi2, hi + k * lo2

def _artanh_ln(y):
    z = (y - 1) / (y + 1)
    s = F(0)
    for n in range(TERMS):
        s += z ** (2 * n + 1) / (2 * n + 1)
    s *= 2
    az = abs(z)
    tail = 2 * az ** (2 * TERMS + 1) / ((2 * TERMS + 1) * (1 - az * az))
    return s - tail, s + tail

def xlnx_iv(x):
    """enclosure of x ln x for rational x > 0 (x exact, so monotone in the log enclosure)."""
    lo, hi = ln_iv(x)
    return x * lo, x * hi

def H_iv(dist):
    """enclosure of -sum x ln x."""
    lo = hi = F(0)
    for x in dist:
        a, b = xlnx_iv(x)
        lo -= b; hi -= a
    return lo, hi

def add(a, b): return a[0] + b[0], a[1] + b[1]
def sub(a, b): return a[0] - b[1], a[1] - b[0]
def scal(c, a): return (c * a[0], c * a[1]) if c >= 0 else (c * a[1], c * a[0])
def div_pos(a, b):
    assert b[0] > 0 and a[0] >= 0
    return a[0] / b[1], a[1] / b[0]

lam = {6: F(7, 19), 7: F(12, 19)}
u = {6: F(97, 800), 7: F(979, 9000)}           # u_q = (97/100)/8, (979/1000)/9

la1 = (F(0), F(0)); lb1 = (F(0), F(0)); slack = (F(0), F(0)); cnum = (F(0), F(0)); ssu = (F(0), F(0))
rows = []
for q in (6, 7):
    p = F(q, 2 * (q + 2)); w = F(1, q + 2); v = (w - u[q]) / 2
    assert 0 < u[q] < w and v > 0
    X = (p + w + v, p + u[q], v)
    Z = (F(1, q + 2), F(q, q + 2), F(1, q + 2))
    joint = (p, p, w, u[q], v, v)                  # p011, p101, p002, p110, p200, p020
    assert sum(X) == 1 and sum(Z) == 1 and sum(joint) == 1
    # marginals of the joint type are X (=Y) and Z (checks the level-1 identity: joint determined by marginals)
    assert (p + w + v, p + u[q], v) == (joint[0] + joint[2] + joint[5], joint[1] + joint[3], joint[4])
    assert (joint[3] + joint[4] + joint[5], joint[0] + joint[1], joint[2]) == Z
    lnq = ln_iv(q)
    la1 = add(la1, scal(lam[q] * p, lnq))
    lb1 = add(lb1, scal(lam[q] * u[q], lnq))
    HX = H_iv(X); HZ = H_iv(Z); HJ = H_iv(joint)
    slack = add(slack, scal(lam[q], sub(HX, HZ)))
    cq = div_pos(add(ln_iv(q + 2), scal(q, ln_iv(2))), (F(q + 2), F(q + 2)))
    cnum = add(cnum, scal(lam[q], cq))
    ssu = add(ssu, scal(lam[q], sub(HJ, HZ)))
    # Lemma B (a) at P0: x0 x2 / x1^2 < 1 (so d slack/d u_q < 0)
    rows.append((q, X, Z, (X[0] * X[2]) / X[1] ** 2, HX, HZ, HJ))

alpha = div_pos(lb1, la1)
cbar = div_pos(cnum, la1)
ssr = div_pos(ssu, la1)

def f(iv, d=12): return "[%.*f, %.*f]" % (d, float(iv[0]), d, float(iv[1]))
print("R211a certified enclosures at P0 = (7/19, 97/100, 979/1000)")
for q, X, Z, ratio, HX, HZ, HJ in rows:
    print(f"q={q}: X-marg={tuple(str(a) for a in X)}  Z-marg={tuple(str(a) for a in Z)}")
    print(f"      H_X in {f(HX)}  H_Z in {f(HZ)}  H_joint in {f(HJ)}  x0 x2/x1^2 = {float(ratio):.6e} (exact rational, < 1: {ratio < 1})")
print("ln a_1  in", f(la1))
print("ln b_1  in", f(lb1))
print("alpha(P0) in", f(alpha, 13))
print("  certified 0.2945976 < alpha(P0) < 0.2945977:", alpha[0] > F(2945976, 10**7) and alpha[1] < F(2945977, 10**7))
print("  certified alpha(P0) > 0.29459:", alpha[0] > F(29459, 10**5))
print("slack(P0) in", f(slack, 14))
print("  certified slack(P0) > 0:", slack[0] > 0, "; 3.46e-5 < slack < 3.47e-5:", slack[0] > F(346, 10**7) and slack[1] < F(347, 10**7))
print("cbar(P0) in", f(cbar, 10), " certified cbar <= 1.077861:", cbar[1] <= F(1077861, 10**6))
print("1/(cbar+2) >=", "%.10f" % float(1 / (cbar[1] + 2)))
print("Salem-Spencer unit sum_q lam_q (H_joint - H_Z) in", f(ssu), "; per ln a_1:", f(ssr, 10))
