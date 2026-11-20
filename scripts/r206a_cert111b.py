"""R206a Task 1: independent exact-rational re-certification of r111b's points P0, P1, P2.

Does not import or copy r111b_cert.py. Uses r206a_iv (Mercator-series log enclosures over Fractions).
Inequalities (r111b.md Section 3, lines 228-242; Theorem B / Corollary C, lines 121-179):
 C1 c > 5;  C2 0 < theta <= 4/5;  C3 b(theta,c) + gamma' ln2 < 0;  C4 0 <= gamma_c < gamma';
 C5 H(theta) + theta ln4 < q_c ln2;  C6 q_c + gamma_c <= 1/2;  C7 ln r + g(c) + gamma' ln4 < a ln4, r > 1;
 C8 4^a C_P (c m0 + 2) <= r^m0 and c <= (r-1)(c m0 + 2), C_P = 4c(c-1)/(mu^2 (c-5)^2), mu^2 >= 0.08339;
 C9 m0 >= 2/(1-theta);  C10 gamma_c <= 1/2, 1/a <= 1/2.
"""
from fractions import Fraction as F
import math, sys, time
from r206a_iv import I, ln, ln2

LN2 = ln2()
LN4 = 2 * LN2

def H(t):
    return -(t * ln(t)) - (1 - t) * ln(1 - t)

def b(t, c):
    return t * LN4 - (1 - t) * ln(1 - t) - (c - 1 + t) * ln(c - 1 + t) + (c - 1) * ln(c - 1)

def g(c):
    return c * ln(c) - (c - 1) * ln(c - 1) + (c - 1) * LN4

def A(c):   # paper's encoding exponent: 2c ln5 - g(c)
    return 2 * c * ln(5) - g(c)

# ---- mu_inf^2 >= 0.08339 ------------------------------------------------------------
def mu_lower(n=64):
    p = F(1)
    for i in range(1, n + 1):
        p *= 1 - F(1, 2 ** i)
    # prod_{i>n} (1 - 2^-i) >= 1 - sum_{i>n} 2^-i = 1 - 2^-n  (Weierstrass product inequality)
    return p * (1 - F(1, 2 ** n))

MU = mu_lower()
MU2_CLAIM = F(8339, 100000)
print("mu_inf >= %.12f, mu_inf^2 >= %.12f, claim mu^2 >= 0.08339 holds: %s" % (float(MU), float(MU * MU), MU * MU >= MU2_CLAIM))
assert MU * MU >= MU2_CLAIM

POINTS = {
    # name: a, c, theta, gamma_c, gamma', q_c, r, m0     (r111b.md lines 230-231, 239)
    "P0": (F(12), F("10.45"), F("0.0566"), F("0.072"), F("0.0725"), F("0.428"), F("1.12"), 262),
    "P1": (F(12), F("10.5414"), F("0.05654"), F("0.0732"), F("0.07335"), F("0.4268"), F("1.00033"), 108012),
    "P2": (F(25, 2), F("11.0057"), F("0.056013"), F("0.0765"), F("0.07656"), F("0.4235"), F("1.00012"), 311373),
}

def lo(x): return float(x.lo)

allok = True
for name, (a, c, th, gc, gp, qc, r, m0) in POINTS.items():
    print("=" * 100)
    print(f"{name}: a = 1/eps = {a}, c = {c}, theta = {th}, gamma_c = {gc}, gamma' = {gp}, q_c = {qc}, r = {r}, m0 = {m0}")
    res = {}
    res["C1 c-5 > 0"] = I(c - 5)
    res["C2 theta in (0,4/5]: 4/5-theta"] = I(F(4, 5) - th) if th > 0 else I(-1)
    bb = b(th, c)
    res["C3 -(b + gamma' ln2) > 0"] = -(bb + gp * LN2)
    res["C4 gamma'-gamma_c > 0 (gamma_c >= 0)"] = I(gp - gc) if gc >= 0 else I(-1)
    res["C5 q_c ln2 - (H+theta ln4) > 0"] = qc * LN2 - (H(th) + th * LN4)
    res["C6 1/2 - q_c - gamma_c >= 0"] = I(F(1, 2) - qc - gc)
    gg = g(c)
    res["C7 a ln4 - ln r - g - gamma' ln4 > 0"] = a * LN4 - ln(r) - gg - gp * LN4
    CP = 4 * c * (c - 1) / (MU2_CLAIM * (c - 5) ** 2)     # upper bound on C_P since mu^2 >= 0.08339
    # C8 by logs: m0 ln r - [a ln4 + ln CP + ln(c m0 + 2)] >= 0
    res["C8a m0 ln r - ln(4^a C_P (c m0+2)) >= 0"] = m0 * ln(r) - (a * LN4 + ln(CP) + ln(c * m0 + 2))
    res["C8b (r-1)(c m0+2) - c >= 0"] = I((r - 1) * (c * m0 + 2) - c)
    res["C9 m0 - 2/(1-theta) >= 0"] = I(m0 - 2 / (1 - th))
    res["C10 1/2-gamma_c, 1/2-1/a >= 0"] = I(min(F(1, 2) - gc, F(1, 2) - 1 / a))
    for k, v in res.items():
        strict = not (k.startswith("C6") or k.startswith("C8") or k.startswith("C9") or k.startswith("C10"))
        ok = (v.lo > 0) if strict else (v.lo >= 0)
        allok &= ok
        print(f"  {k:48s} lower bound {lo(v): .6e}   width {float(v.width()):.1e}   {'ok' if ok else 'FAIL'}")
    # C8 exact integer form: r^m0 >= 4^a * CP * (c m0 + 2)   (4^a is an integer for a in {12, 25/2})
    t0 = time.time()
    four_a = 4 ** a.numerator if a.denominator == 1 else 2 ** (2 * a).numerator
    assert F(four_a) == F(4) ** int(a) if a.denominator == 1 else True
    rhs = four_a * CP * (c * m0 + 2)
    rn, rd = r.numerator, r.denominator
    lhs_num = pow(rn, m0); lhs_den = pow(rd, m0)
    okint = lhs_num * rhs.denominator >= rhs.numerator * lhs_den
    allok &= okint
    print(f"  C8 exact big-integer form r^m0 >= 4^a C_P (c m0 + 2): {okint}  ({time.time()-t0:.1f} s, r^m0 has {len(str(rn))*m0} digits approx)")
    # m0 minimal for the closed form? check m0-1 fails (by logs; informative only)
    v1 = (m0 - 1) * ln(r) - (a * LN4 + ln(CP) + ln(c * (m0 - 1) + 2))
    print(f"  closed form at m0-1: margin upper bound {float(v1.hi): .3e}  (negative = m0 is the least m of the closed form)")
    # values for the report
    gam = -bb / LN2
    q = (H(th) + th * LN4) / LN2
    print(f"  gamma(theta,c) in {gam}, q(theta) in {q}, g(c) in {gg}")
    print(f"  full encoding: A(c)/ln4 + gamma' in {A(c)/LN4 + gp}  vs a = {float(a)}")
    print(f"  pruned rate: g(c)/ln4 + gamma' in {gg/LN4 + gp}  vs a = {float(a)}")
    print(f"  C_P (with mu^2 = 0.08339) = {float(CP):.4f};  eps*gamma_c = {gc / a} = {float(gc/a):.8f}; 3SUM exponent 2 - eps*gamma = {float(2 - gc/a):.6f}")

print("=" * 100)
print("ALL INEQUALITIES HOLD" if allok else "SOME INEQUALITY FAILS")
