"""R215 item (a): independent certificate of the instances A11 of Theorem R89.1 (kappa in (0, 1]).

Written from the statement (r206d-abfk-review.md:225-262, r89.md:13-56, :240-246) before reading r89's scripts.
Exact rational arithmetic (fractions.Fraction) only; the inputs are r79b's certified enclosures
(calc/r79b_certify.json: alpha_lo <= alpha(P0), M_hi(t) >= Lambda^+(t) on the grid).

Conditions checked, for a top with exponent a_B >= a' and profile lambda_B(t) <= M' (a' = alpha_lo - ETA0,
M' = M_hi(t) + ETA0, reachable by r79b Lemma 1 with eta = ETA0), at one rational eps = v and one grid t,
with s = t*kappa (kappa <= 1) and x chosen by checklist E1, phi(x) = (1 + a x)/(x + 1/e) = v, i.e.
x = (1 - v/e)/(v - a):
  (P)  a' < v < e, a' s - M' > 0, x > 0;
  (S)  margin := x (a' s - M') - (t - s) - (1 - t) g / e > 0   (sub-entry saving at delta = 0);
then delta can be any number in (0, e*margin/(1-t)) and the sub-entry saving is positive. The other cost lines
(encodings: positive iff e < 1 and delta_B < (1/e - 1)/x; needed entries: implied by a s > M, s > 0; bucketing,
input/output: 2x/(1+ax), kappa, 1/v - 1 > 0) are checked too. Monotonicity in (a, M) (all conditions improve
when a grows or M falls, and x(a) = (1 - v/e)/(v - a) grows with a) carries the check from (a', M') to the true top.
Hyp_kappa(eps, gamma) is monotone in eps (D <= N^eps' implies D <= N^eps for eps <= eps'), so the check at eps = v
gives every eps <= v.
"""
import json, os, sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
d = json.load(open(os.path.join(HERE, "r79b_certify.json")))
ALPHA_LO = Fr(d["alpha_lo"])
ETA0 = Fr(1, 10**12)
A = ALPHA_LO - ETA0
GRID = [(Fr(p["t"]), Fr(p["M_hi"]) + ETA0, p["src"]) for p in d["points"]]

def check(kappa, e, g, v, t, M):
    """All cost lines at eps = v, grid point (t, M); returns dict of exact margins or None if (P) fails."""
    s = t * kappa
    if not (A < v < e and A * s - M > 0 and s > 0):
        return None
    x = (1 - v / e) / (v - A)
    assert (1 + A * x) / (x + 1 / e) == v          # E1's choice: bottom range binds
    out = {}
    out["sub"] = x * (A * s - M) - (t - s) - (1 - t) * g / e        # times 1/(1+ax): saving of the sub-entries
    out["enc"] = (1 / e - 1) / (v * (x + 1 / e))                       # 1/v - (1+x)/(1+ax) at delta_B = 0
    out["need"] = (t * kappa * (1 + A * x) - x * M) / (1 + A * x)
    out["buck"] = min(2 * x / (1 + A * x), kappa)
    out["io"] = 1 / v - 1
    out["x"] = x
    out["delta_max"] = e * out["sub"] / (1 - t) if out["sub"] > 0 else Fr(0)
    return out

def F_exact(kappa, e, g, t, M):
    """phi(x_min) at one grid point (exact), the supremum of eps reachable there; None if a s <= M."""
    s = t * kappa
    if not (A * s - M > 0 and s > 0):
        return None
    num = (t - s) + (1 - t) * g / e
    xmin = max(num, Fr(0)) / (A * s - M)
    return (1 + A * xmin) / (xmin + 1 / e)

def best(kappa, e, g):
    vals = [(F_exact(kappa, e, g, t, M), t, M) for (t, M, src) in GRID]
    vals = [z for z in vals if z[0] is not None]
    return max(vals, key=lambda z: z[0])

def floor6(q):
    return Fr(int(q * 10**6), 10**6) if q >= 0 else None

INST = [
    # (label, kappa, e, g, printed value to certify)
    ("A11.1 VXXZ alpha > 0.321334, kappa = 1/2", Fr(1, 2), Fr("0.321334"), Fr(0), Fr("0.307314")),
    ("A11.1' same with e = 0.321334 - 1e-9 (no use of alpha > e)", Fr(1, 2), Fr("0.321334") - Fr(1, 10**9), Fr(0), Fr("0.307314")),
    ("A11.3 VXXZ Table 1 omega(1,0.33,1) <= 2.000100, kappa = 1/2", Fr(1, 2), Fr("0.33"), Fr("0.000100"), Fr("0.308262")),
    ("A11.4 VXXZ Table 1 omega(1,0.35,1) <= 2.001363, kappa = 1", Fr(1), Fr("0.35"), Fr("0.001363"), Fr("0.340984")),
]

print("R215 (a) certificate; alpha_lo =", float(ALPHA_LO), "; a' = alpha_lo - 1e-12; grid points:", len(GRID))
print("alpha_lo exact:", ALPHA_LO)
print()
for (lab, kappa, e, g, v) in INST:
    Fb, tb, Mb = best(kappa, e, g)
    print("==", lab)
    print("   sup over grid of phi(x_min) (exact rational, float shown): F = %.10f at t = %s" % (float(Fb), tb))
    print("   floor to 6 digits: %s" % (float(floor6(Fb)),))
    # certify the printed value v at the best t, and test v + 1e-6
    r = check(kappa, e, g, v, tb, Mb)
    ok = r is not None and all(r[k] > 0 for k in ("sub", "enc", "need", "buck", "io"))
    print("   eps = %s at t = %s: %s" % (v, tb, "CERTIFIED (all margins > 0)" if ok else "FAILS"))
    if r:
        for k in ("sub", "enc", "need", "buck", "io", "x", "delta_max"):
            print("      %-9s = %.6e" % (k, float(r[k])))
        print("      delta_B must be < (1/e - 1)/x = %.6e" % float((1 / e - 1) / r["x"]))
    # every grid point at which v certifies
    good = [str(t) for (t, M, src) in GRID if (lambda z: z is not None and z["sub"] > 0)(check(kappa, e, g, v, t, M))]
    print("   grid points certifying eps = v:", good)
    vp = v + Fr(1, 10**6)
    anyp = [str(t) for (t, M, src) in GRID if (lambda z: z is not None and z["sub"] > 0)(check(kappa, e, g, vp, t, M))]
    print("   eps = v + 1e-6 = %s certifies at: %s" % (vp, anyp if anyp else "no grid point (so v is the 6-digit floor on this grid)"))
    print()

# kappa = 1, g = 0: every eps < e (analytic in eps, one grid point needed)
print("== A11.2 kappa = 1, g = 0, e = 0.321334: every eps < e")
e = Fr("0.321334")
pts = [(t, A * t - M) for (t, M, src) in GRID if A * t - M > 0]
print("   grid points with a' t - M' > 0:", len(pts), "; best (a't - M')/(1-t) =",
      "%.10f at t = %s" % max(((float(c / (1 - t)), str(t)) for t, c in pts)))
print("   a' < e:", A < e)
print("   Argument: for any eps in (a', e), x = (1 - eps/e)/(eps - a') > 0 and the sub-entry margin is")
print("   x (a' t - M') > 0 (t - s = 0, g = 0), so delta in (0, e x (a't - M')/(1-t)) works; eps <= a' by monotonicity.")
# spot check at eps = e - 1e-6 and e - 1e-9
for vv in (e - Fr(1, 10**6), e - Fr(1, 10**9)):
    t0, c0 = max(pts, key=lambda z: z[1] / (1 - z[0]))
    M0 = [M for (t, M, src) in GRID if t == t0][0]
    r = check(Fr(1), e, Fr(0), vv, t0, M0)
    print("   eps = e - %s: sub margin %.3e, all lines > 0: %s" % (float(e - vv), float(r["sub"]),
          all(r[k] > 0 for k in ("sub", "enc", "need", "buck", "io"))))

# closed form at kappa = 1: F(1; e, g) = (C e + a g)/(C + g), C = max_t (a t - M_t)/(1 - t)
C = max(c / (1 - t) for t, c in pts)
print()
print("closed form kappa = 1: C = %.10f; F(1; 0.35, 0.001363) = %.10f" %
      (float(C), float((C * Fr("0.35") + A * Fr("0.001363")) / (C + Fr("0.001363")))))
