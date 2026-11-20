"""R211e, second pass: R45.1 at the safe 6-digit value 0.187823, and R77's Q-table rows re-optimised over the
mixture (the row Q = 3/4 is not reached at P1). Imports the interval code of r211e_cert.py (own file)."""
from fractions import Fraction as F
import math
from scipy.optimize import minimize
import r211e_cert as C

out = []
P = lambda *a: out.append(" ".join(str(x) for x in a))

def certify(valfun, target, x, label):
    for den in [10 ** 6, 10 ** 7, 10 ** 8]:
        l6 = F(round(x[0] * den), den)
        for back in [0, 1, 2, 5, 10, 20, 50, 100, 200, 500, 1000]:
            u6 = F(min(round(x[1] * 8 * den), den - 1) - back, den) / 8
            u7 = F(min(round(x[2] * 9 * den), den - 1) - back, den) / 9
            d = C.point(l6, u6, u7)
            v = valfun(d)
            if d["slack"].lo > 0 and v.lo > target:
                P("  %s CERTIFIED > %s at lam6 = %s, u6(q+2) = %s, u7(q+2) = %s; slack in %s; alpha in %s; c_g in %s; c_o in %s; value in %s (margin %.3e)" % (
                    label, float(target), l6, u6 * 8, u7 * 9, d["slack"], d["alpha"], d["cg"], d["co"], v, float(v.lo - target)))
                return True
    P("  %s NOT certified > %s" % (label, float(target)))
    return False

# R45.1 at 0.187823
v, x = C.search("r45")
P("R45.1: float optimum %.10f at lam6=%.7f u(q+2)=(%.7f, %.7f)" % (v, x[0], x[1] * 8, x[2] * 9))
certify(lambda d: C.rangeF(d["alpha"], d["cg"], C.EPS), F(187823, 10 ** 6), x, "R45.1")

# R77 Q-table, re-optimised
def fq(z, Q):
    l6, u6, u7 = z
    lam = {6: l6, 7: 1 - l6}; uu = {6: u6, 7: u7}
    la = lb = lc = sl = 0.0
    for q in (6, 7):
        w = 1 / (q + 2); p = q / (2 * (q + 2)); v_ = (w - uu[q]) / 2
        H = lambda *ps: -sum(t * math.log(t) for t in ps if t > 0)
        sl += lam[q] * (H(p + w + v_, p + uu[q], v_) - H(w, q * w, w))
        la += lam[q] * p * math.log(q); lb += lam[q] * uu[q] * math.log(q)
        lc += lam[q] * (math.log(q + 2) + q * math.log(2)) / (q + 2)
    a, co, e = lb / la, lc / la, math.log(4) / (5 * math.log(5))
    return co * e / (Q * e + co - Q * a), sl

P("\nR77 Q-table, mixture re-optimised per Q (value c_o e/(Q e + c_o - Q alpha)):")
for Q, pr in [(0.1, "0.174273"), (0.3, "0.178422"), (0.4, "0.180571"), (0.49, "0.182550"), (0.75, "0.188520")]:
    best = None
    for x0 in [(0.19, 0.997 / 8, 0.9987 / 9), (0.3, 0.99 / 8, 0.999 / 9)]:
        r = minimize(lambda z: -fq(z, Q)[0], x0, method="SLSQP",
                     bounds=[(0.01, 0.99), (0.05, 1 / 8 - 1e-9), (0.05, 1 / 9 - 1e-9)],
                     constraints=[{"type": "ineq", "fun": lambda z: fq(z, Q)[1]}], options={"ftol": 1e-15, "maxiter": 500})
        if best is None or -r.fun > best[0]:
            best = (-r.fun, r.x)
    P("  Q = %s: float optimum %.9f at lam6 = %.5f; printed %s" % (Q, best[0], best[1][0], pr))
    Qf = F(Q).limit_denominator(1000)
    tgt = F(pr) if best[0] > float(F(pr)) else F(math.floor(best[0] * 10 ** 6), 10 ** 6)
    certify(lambda d: C.rangeQ(d["alpha"], d["co"], C.EPS, Qf), tgt, best[1], "Q=%s" % Q)

txt = "\n".join(out)
print(txt)
open(__file__.replace(".py", "_out.txt"), "w").write(txt + "\n")
