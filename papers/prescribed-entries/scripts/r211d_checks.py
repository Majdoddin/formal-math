"""R211d checks (stdlib only).
(1) Prop. 4.1 instances in exact rational arithmetic (CERTIFIED: Fractions, no rounding until the
    final floor to 6 digits); monotonicity of the range formula in alpha_C and alpha_B checked by
    exact difference quotients on a grid (COMPUTED, used only as a sanity check; the proof of
    monotonicity is in the report).
(2) kappa_typ(q) for the standard CW_q decomposition: closed form vs a direct maximisation of
    [H(x) + sum_j h(x_j)]/(q+2) over the symmetric line and over random non-symmetric points
    (COMPUTED, floating point).
(3) The q = 5 identity 7 kappa_typ(5) = 6 ln 2 (COMPUTED to 1e-15; proof in the report).
"""
from fractions import Fraction as F
import math, random

def rng(aC, aB, c):
    # eps_lim = aC + theta* (aB - aC), theta* = aC/(2c - aB + aC)
    D = 2 * c - aB + aC
    assert D > 0
    th = aC / D
    return aC + th * (aB - aC), th

def floor6(x):
    return F(math.floor(x * 10**6), 10**6)

print("(1) Prop 4.1 instances, exact rationals")
for name, aC in [("alpha_C = 0.29459 (certified lower bound at P0)", F(29459, 100000)),
                 ("alpha_C = 0.2945976 (computed alpha(P0))", F(2945976, 10**7)),
                 ("alpha_C = 0.294629 (computed sup, not certified)", F(294629, 10**6))]:
    for aB in [F(321334, 10**6), F(31389, 10**5)]:
        for c in [F(2), aB]:
            v, th = rng(aC, aB, c)
            print(f"  {name}; alpha_B = {float(aB)}; cbar_B = {float(c)}: theta* = {float(th):.9f},"
                  f" range = {float(v):.9f}, floor6 = {floor6(v)} = {float(floor6(v))}")

# monotonicity sanity check of the range in aC and aB at cbar = 2 (exact difference quotients)
bad = 0
for i in range(1, 60):
    aC = F(25, 100) + F(i, 1000)
    for j in range(1, 60):
        aB = aC + F(j, 100)
        if aB > 1:
            continue
        v0, _ = rng(aC, aB, F(2))
        v1, _ = rng(aC + F(1, 10**6), aB, F(2))
        v2, _ = rng(aC, aB + F(1, 10**6), F(2))
        if not (v1 > v0 and v2 > v0):
            bad += 1
print("  monotonicity grid violations (cbar = 2):", bad)

print("(2) kappa_typ(q), standard CW_q")
def H(v):
    return -sum(t * math.log(t) for t in v if t > 0)
def h(t):
    return H([t, 1 - t])
def obj(x, q):
    # x = (x0, x1..xq) distribution of B's row
    return (H(x) + sum(h(t) for t in x[1:])) / (q + 2)
def closed(q):
    x = ((q + 1) - math.sqrt(q * q - 2 * q + 5)) / (2 * (q - 1))
    return (-2 * math.log(x) - (q - 1) * math.log(1 - x)) / (q + 2), x
random.seed(211)
for q in range(2, 13):
    kc, xq = closed(q)
    # symmetric line search
    best = -1
    n = 200000
    for k in range(1, n):
        x = k / (n * q)
        v = obj([1 - q * x] + [x] * q, q)
        best = max(best, v)
    # random non-symmetric points
    rbest = -1
    for _ in range(20000):
        w = [random.random() ** 3 for _ in range(q + 1)]
        s = sum(w)
        rbest = max(rbest, obj([t / s for t in w], q))
    A = q * math.log(q) / (2 * (q + 2))
    print(f"  q={q:2d}: closed {kc:.9f} at x={xq:.6f}, x0={xq*xq/(1-xq):.6f}; line max {best:.9f};"
          f" random max {rbest:.9f} (<= closed: {rbest <= kc + 1e-12}); A={A:.8f}; kappa/A={kc/A:.6f};"
          f" (q+1)ln2/(q+2)={(q+1)*math.log(2)/(q+2):.6f}")

print("(3) q = 5 identity: 7 kappa_typ(5) - 6 ln 2 =", 7 * closed(5)[0] - 6 * math.log(2))
print("    x_5 - (3 - sqrt 5)/4 =", closed(5)[1] - (3 - math.sqrt(5)) / 4)
print("DONE")
