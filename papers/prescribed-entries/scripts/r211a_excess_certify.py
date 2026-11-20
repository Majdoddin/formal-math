"""R211a: certified check of Theorem D's range beyond alpha(P0) with the proved profile bound (L1 Section 4
comment (2), r79 1.1 (c)): at kappa = 1/2 find rational (t, x) with (D1) t kappa (1 + alpha x) - x Lambda_pr(t) - 1 > 0,
certified, and print a certified lower bound on (1 + alpha x)/(1 + x).  Lambda_pr(t) = sum_q lam_q t^2 ln^2(4 e q/t)/ln a_1
with ln(4eq/t) = 1 + ln(4q/t).  Exact rationals + rigorous log enclosures (imports r211a_p0_certify's routines by
path).  Usage: python3 -I r211a_excess_certify.py"""
import importlib.util, os
from fractions import Fraction as F
spec = importlib.util.spec_from_file_location("cert", os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                              "r211a_p0_certify.py"))
import io, contextlib
cert = importlib.util.module_from_spec(spec)
with contextlib.redirect_stdout(io.StringIO()):
    spec.loader.exec_module(cert)
la1, alpha = cert.la1, cert.alpha
lam = cert.lam
kappa = F(1, 2)

def Lpr_hi(t):
    tot = F(0)
    for q in (6, 7):
        lo, hi = cert.ln_iv(F(4 * q) / t)
        L = 1 + hi                      # upper bound of ln(4eq/t) (positive)
        tot += lam[q] * t * t * L * L
    return tot / la1[0]                 # divide by the lower end of ln a_1: upper bound

best = None
for t in [F(k, 100000) for k in range(30, 60)]:
    Lh = Lpr_hi(t)
    for x in [F(k * 100) for k in range(300, 600)]:
        D1 = t * kappa * (1 + alpha[0] * x) - x * Lh - 1   # lower bound of (D1) numerator
        if D1 > 0:
            rng = (1 + alpha[0] * x) / (1 + x)              # increasing in alpha: lower bound
            if best is None or rng > best[0]:
                best = (rng, t, x, D1)
            break
rng, t, x, D1 = best
print("kappa = 1/2, t = %s, x = %s: (D1) numerator >= %.3e > 0 (certified)" % (t, x, float(D1)))
print("range (1 + alpha x)/(1 + x) >= %.10f, alpha(P0) <= %.10f, excess >= %.3e (certified)" %
      (float(rng), float(alpha[1]), float(rng - alpha[1])))
print("certified: every eps < 0.294616 lies in Theorem D's range at P0 with the proved profile:", rng > F(294616, 10**6))
