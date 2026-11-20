"""R215 items (b), (c), (d): small exact checks (fractions) and 50-digit decimal values.

(b) ABFK Theorem 1.10 triples T(r) = (sigma-1, 2-sigma, 1+r-sigma) against R87.2's region a/min(b,c) < E(min/max),
    kappa = (b+c-1)/a <= 1, b+c > 1, a > 0; E = step function of R87.1's seven rows (r211f Section 6.3).
    Route 1: worst cases over sigma in [1 + r/3, 1 + r mu/(1+mu)], mu = 0.5286 (GU18) and 0.527661 (VXXZ).
    Threshold beyond which T(r) is outside for every admissible sigma: r211f's 3(1+mu)/(16+mu), and the sharper
    (1+mu)/(5+mu) from the monotonicity of s in sigma.
    E18: C/(1/2 - a) with the certified C (r79b grid, a' = alpha_lo - 1e-12, M' = M_hi + 1e-12).
(c) c-bound for D13 in the N-parametrisation: u = N^c is served by D3 for every instance iff c/(1-c) < 0.182773.
(d) A_q = q ln q/(2(q+2)), kappa_typ(q) closed form, c_g = kappa_typ/A_q.
"""
import json, os
from fractions import Fraction as Fr
from decimal import Decimal as Dm, getcontext
getcontext().prec = 50
HERE = os.path.dirname(os.path.abspath(__file__))

ROWS = [(Fr(3, 4), Fr(333, 1000)), (Fr(1, 2), Fr(2757, 7000)), (Fr(1, 3), Fr(179, 400)), (Fr(1, 4), Fr(197, 400)),
        (Fr(1, 5), Fr(2853, 5500)), (Fr(1, 7), Fr(887, 1625)), (Fr(1, 10), Fr(10703, 18000))]
AP0 = Fr(2945976, 10**7)          # alpha(P0) > 0.2945976 (r211f 6.1); only used as the s > 3/4 value (a lower bound)

def E(s):
    return max([AP0] + [Ei for (si, Ei) in ROWS if si >= s])

def triple(r, sig):
    return (sig - 1, 2 - sig, 1 + r - sig)

def inside(r, sig):
    a, b, c = triple(r, sig)
    if not (a > 0 and b + c > 1):
        return False
    kap = (b + c - 1) / a
    s = min(b, c) / max(b, c)
    return kap <= 1 and a / min(b, c) < E(s)

print("(b) E(1/7) =", E(Fr(1, 7)), "=", float(E(Fr(1, 7))), "; E(1/5) =", float(E(Fr(1, 5))), "; E(s), s in (1/5,1/4]:", float(E(Fr(21, 100))))
for mu in (Fr("0.5286"), Fr("0.527661")):
    print(" mu =", float(mu))
    for r in [Fr(1, 100), Fr(1, 20), Fr(1, 10), Fr(3, 20), Fr(1, 5), Fr(1, 4), Fr(3, 11), Fr(7, 25)]:
        lo, hi = 1 + r / 3, 1 + r * mu / (1 + mu)
        grid = [lo + (hi - lo) * Fr(k, 200) for k in range(201)]
        ins = [inside(r, g) for g in grid]
        a, b, c = triple(r, hi)
        print("  r = %-6s sigma in [%.6f, %.6f]: inside at all 201 grid sigmas: %s; at sigma = 1 + r/3: %s; eps at upper end = %s"
              % (r, float(lo), float(hi), all(ins), inside(r, lo), a / c))
    print("  r211f threshold 3(1+mu)/(16+mu) = %.6f; sharper (1+mu)/(5+mu) = %.6f" %
          (float(3 * (1 + mu) / (16 + mu)), float((1 + mu) / (5 + mu))))
    # check the two lower bounds on s at the upper end of sigma
    r = Fr(27, 100)
    hi = 1 + r * mu / (1 + mu)
    print("  at r = 0.27: s(sigma_max) = %.6f, r/(1+mu-r mu) = %.6f, 3r/((1+mu)(3-r)) = %.6f" %
          (float((1 + r - hi) / (2 - hi)), float(r / (1 + mu - r * mu)), float(3 * r / ((1 + mu) * (3 - r)))))
# route 2: sigma0 = 1 + r/3 gives s0 = 2r/(3-r) <= 1/5 iff r <= 3/11
print(" route 2: s0(3/11) =", Fr(2) * Fr(3, 11) / (3 - Fr(3, 11)))
# homogeneity identity: omega(r/3, 1-r/3, 2r/3) = (1 - r/3)(1 + s0) = 1 + r/3
for r in (Fr(1, 10), Fr(3, 11)):
    s0 = 2 * r / (3 - r)
    print("  r =", r, ": (1 - r/3)(1 + s0) =", (1 - r / 3) * (1 + s0), "= 1 + r/3:", (1 - r / 3) * (1 + s0) == 1 + r / 3,
          "; scaled triple:", (r / 3) / (1 - r / 3), "=", s0 / 2, ",", (2 * r / 3) / (1 - r / 3), "=", s0)

# E18 with the certified grid
d = json.load(open(os.path.join(HERE, "r79b_certify.json")))
A = Fr(d["alpha_lo"]) - Fr(1, 10**12)
C = max((A * Fr(p["t"]) - (Fr(p["M_hi"]) + Fr(1, 10**12))) / (1 - Fr(p["t"])) for p in d["points"] if Fr(p["t"]) < 1)
print()
print("(b) E18: certified C >= %.10f; C/(1/2 - a') = %.8f (a' = alpha_lo - 1e-12; larger a' only raises it)" %
      (float(C), float(C / (Fr(1, 2) - A))))
print("   ABFK Table 2 vs 1 + r/3: r = 0.05: 1.0171 vs %.4f; 0.10: 1.0342 vs %.4f; 0.20: 1.0684 vs %.4f; 0.25: 1.0855 vs %.4f"
      % tuple(float(1 + Fr(x) / 3) for x in ("0.05", "0.10", "0.20", "0.25")))

# (c)
e3 = Fr("0.182773")
print()
print("(c) N-parametrisation: c < e3/(1 + e3) = %.9f; floor6 = %.6f" % (float(e3 / (1 + e3)), int(e3 / (1 + e3) * 10**6) / 10**6))

# (d)
print()
print("(d) A_q = q ln q / (2 (q+2)), kappa_typ(q) = [-2 ln x - (q-1) ln(1-x)]/(q+2), (q-1)x^2 - (q+1)x + 1 = 0")
for q in range(4, 11):
    qd = Dm(q)
    Aq = qd * qd.ln() / (2 * (qd + 2))
    x = ((qd + 1) - ((qd + 1) ** 2 - 4 * (qd - 1)).sqrt()) / (2 * (qd - 1))
    kap = (-2 * x.ln() - (qd - 1) * (1 - x).ln()) / (qd + 2)
    print("  q = %2d: A_q = %.9f, x_q = %.9f, kappa_typ = %.9f, c_g = %.6f" % (q, Aq, x, kap, kap / Aq))
