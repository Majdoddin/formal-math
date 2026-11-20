"""R214: certificate for Corollary m:cor:abfk of v2 (Section m:sec:abfk), OD10 (c) and run 1's question Q3.

F(kappa) := eps_kappa for 0 < kappa <= 1 (Theorem m:thm:fixedq), and for kappa > 1
F(kappa) := R'_{c(kappa)}(kappa - 1) = ln4 / (A(c) + (kappa - 1) ln4), where c = c(kappa) > c_min(theta_1) solves
b(theta_1, c) = -(kappa - 1) ln 2 (r206d-abfk-review.md Section 6 last paragraph, "F_DS"; Section 9 note).

Part 1 (exact): the proof of Corollary m:cor:abfk needs kappa F(kappa) < 1 for every kappa > 0, and the paragraph on
ABFK's Theorem 1.10 needs (kappa + 1) F(kappa) < 1 for every kappa > 0.  Both reduce to A(c) > 2 ln 4 for c >= 2:
  kappa > 1:  (kappa+1) F < 1  <=>  (kappa+1) ln4 < A(c) + (kappa-1) ln4  <=>  2 ln4 < A(c);
  kappa <= 1: F = eps_kappa = ln4 / A(c_min(theta)) with c_min > 2 (Thm m:thm:fixedq (iii)), so 2F < 1 <=> 2 ln4 < A.
A(c) = 2c ln5 - c ln c + (c-1) ln(c-1) - (c-1) ln4 has A'(c) = ln(25(c-1)/(4c)) > 0 for c > 25/21, so A(c) >= A(2)
on c >= 2, and A(2) = 4 ln(5/2).  So everything follows from 4 ln(5/2) > 2 ln 4, i.e. (5/2)^4 > 16, checked exactly.
kappa F <= (kappa+1) F gives the first claim.  The same argument covers v1's F (c(kappa) = 1 + 4*2^((kappa-1)/theta_1) > 5).

Part 2 (interval arithmetic, outward-rounded rationals with decimal logarithms at 60 digits widened by 1e-50):
enclosures of theta_1, of c(kappa) and of F(kappa) at kappa = 1.1, 1.5, 2, and of eps_kappa at kappa = 1/2, 1
(to compare with \\HypHalfRfourteen = 0.17843 and \\HintedOMvRfourteen = 0.18840), for the printed values.
Run: nice -n 19 python3 -I calc/r214_abfk_cert.py > calc/r214_abfk_cert_out.txt   (one process, seconds).
"""
from fractions import Fraction as Fr
from decimal import Decimal, getcontext
getcontext().prec = 60
W = Fr(1, 10**50)

def ln_iv(x):
    """enclosure of ln(x) for a rational x > 0 (Decimal ln is correctly rounded at 60 digits; widened by 1e-50)."""
    x = Fr(x)
    d = (Decimal(x.numerator) / Decimal(x.denominator)).ln()
    v = Fr(d)
    return (v - W, v + W)

def add(a, b): return (a[0] + b[0], a[1] + b[1])
def neg(a): return (-a[1], -a[0])
def sub(a, b): return add(a, neg(b))
def scal(k, a):
    k = Fr(k)
    return (k * a[0], k * a[1]) if k >= 0 else (k * a[1], k * a[0])
def mul(a, b):
    p = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return (min(p), max(p))
def div(a, b):
    assert b[0] > 0 or b[1] < 0
    return mul(a, (1 / b[1], 1 / b[0]))
def xlnx(x):  # x ln x for rational x >= 0
    x = Fr(x)
    return (Fr(0), Fr(0)) if x == 0 else scal(x, ln_iv(x))

LN2 = ln_iv(2); LN4 = ln_iv(4); LN5 = ln_iv(5)

def q_iv(th):     # q(theta) = (H(theta) + theta ln4)/ln2, H natural entropy
    th = Fr(th)
    H = neg(add(xlnx(th), xlnx(1 - th)))
    return div(add(H, scal(th, LN4)), LN2)

def b_iv(th, c):  # b(theta,c) = theta ln4 - (1-theta)ln(1-theta) - (c-1+theta)ln(c-1+theta) + (c-1)ln(c-1)
    th = Fr(th); c = Fr(c)
    return add(sub(sub(scal(th, LN4), xlnx(1 - th)), xlnx(c - 1 + th)), xlnx(c - 1))

def A_iv(c):      # A(c) = 2c ln5 - c ln c + (c-1) ln(c-1) - (c-1) ln4
    c = Fr(c)
    return sub(add(sub(scal(2 * c, LN5), xlnx(c)), xlnx(c - 1)), scal(c - 1, LN4))

def bisect_cert(pred_lo, pred_hi, lo, hi, it=120):
    """lo, hi rationals with pred_lo(lo) and pred_hi(hi) certified; shrink by bisection keeping certificates."""
    lo, hi = Fr(lo), Fr(hi)
    assert pred_lo(lo) and pred_hi(hi)
    for _ in range(it):
        mid = (lo + hi) / 2
        mid = Fr(round(mid * 10**40), 10**40)
        if pred_lo(mid): lo = mid
        elif pred_hi(mid): hi = mid
        else: break
    return lo, hi

out = []
# Part 1
r = Fr(5, 2) ** 4
out.append("Part 1 (exact).")
out.append(f"  (5/2)^4 = {r} = {float(r)} > 16: {r > 16}  =>  A(2) = 4 ln(5/2) > 2 ln 4 = ln 16")
out.append(f"  25/21 = {float(Fr(25,21)):.6f} < 2, so A'(c) = ln(25(c-1)/(4c)) > 0 on c >= 2 and A(c) >= A(2) there")
A2 = A_iv(2); out.append(f"  A(2) in [{float(A2[0]):.12f}, {float(A2[1]):.12f}], 2 ln 4 in [{float(2*LN4[0]):.12f}, {float(2*LN4[1]):.12f}]; margin >= {float(A2[0]-2*LN4[1]):.6f}")
out.append(f"  ln4/A(2) <= {float(LN4[1]/A2[0]):.6f} < 1/2, so eps_kappa < 1/2 for kappa <= 1 (c_min > 2)")
out.append("  Conclusion (PROVED): kappa F(kappa) < (kappa+1) F(kappa) < 1 for every kappa > 0.")
# Part 2
out.append("Part 2 (interval enclosures).")
th1 = bisect_cert(lambda t: q_iv(t)[1] < 1, lambda t: q_iv(t)[0] > 1, Fr(17, 100), Fr(171, 1000))
out.append(f"  theta_1 in [{float(th1[0]):.15f}, {float(th1[1]):.15f}]  (q(theta_1) = 1)")
for kap in (Fr(11, 10), Fr(3, 2), Fr(2)):
    target = scal(-(kap - 1), LN2)  # b(theta_1, c) = -(kappa-1) ln2
    # b decreases in c, and (for these c, where phi_c(theta) < 0) in theta: b(theta_1,c) in [b(th_hi,c), b(th_lo,c)]
    def above(c):  # certified b(theta_1,c) > target  => c < c(kappa)
        return b_iv(th1[1], c)[0] > target[1]
    def below(c):  # certified b(theta_1,c) < target  => c > c(kappa)
        return b_iv(th1[0], c)[1] < target[0]
    # check the monotonicity in theta used above: phi_c(theta) < 0 at the bracket, i.e. 4(1-theta) < c-1+theta
    cl, ch = bisect_cert(above, below, Fr(45, 10), Fr(1000))
    assert 4 * (1 - th1[0]) < cl - 1 + th1[0]
    Fl = div(LN4, add(A_iv(ch), scal(kap - 1, LN4)))[0]
    Fh = div(LN4, add(A_iv(cl), scal(kap - 1, LN4)))[1]
    out.append(f"  kappa = {float(kap)}: c(kappa) in [{float(cl):.10f}, {float(ch):.10f}], F(kappa) in [{float(Fl):.10f}, {float(Fh):.10f}]")
for kap in (Fr(1, 2), Fr(1)):
    tk = bisect_cert(lambda t: q_iv(t)[1] < kap, lambda t: q_iv(t)[0] > kap, Fr(1, 100), Fr(79, 100))
    # c_min decreasing in theta: c_min(theta_kappa) in [c_min(th_hi), c_min(th_lo)]
    cl, _ = bisect_cert(lambda c: b_iv(tk[1], c)[0] > 0, lambda c: b_iv(tk[1], c)[1] < 0, Fr(201, 100), Fr(5))
    _, ch = bisect_cert(lambda c: b_iv(tk[0], c)[0] > 0, lambda c: b_iv(tk[0], c)[1] < 0, Fr(201, 100), Fr(5))
    el = div(LN4, A_iv(ch))[0]; eh = div(LN4, A_iv(cl))[1]
    out.append(f"  eps_kappa at kappa = {float(kap)}: theta in [{float(tk[0]):.12f}, {float(tk[1]):.12f}], c_min in [{float(cl):.10f}, {float(ch):.10f}], eps in [{float(el):.10f}, {float(eh):.10f}]")
print("\n".join(out))
