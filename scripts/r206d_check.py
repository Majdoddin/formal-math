"""R206d (independent review of the ABFK Hypothesis 1.9 refutation): numerical checks.
Written from the formulas re-derived in r206d-abfk-review.md, not from r81/r86/r89's scripts.
(A) v1's own range (main.tex Cor. m:cor:tradeoff, split form): theta_1, the kappa > 1 range F_v1, sample triples,
    the conditions F(kappa)(kappa+1) <= 1 and eps*kappa < 1.
(B) the alpha-parametric composite (r89 Thm R89.1) on r79b's certified profile grid: C, kappa*, F(kappa; e, g)
    via phi(x_min), and a direct re-check at eps slightly below F with the exact choice x = (1-eps/e)/(eps-a)
    (phi(x) = eps), every cost line evaluated.
Reads calc/r79b_certify.json only. Run: nice -n 19 ~/.venv/bin/python3 -I calc/r206d_check.py > calc/r206d_check_out.txt
"""
import json, os, random
from fractions import Fraction as Fr
import math

HERE = os.path.dirname(os.path.abspath(__file__))

def H(p):
    p = float(p)
    return -p*math.log(p) - (1-p)*math.log(1-p)

def nstr(x, d):
    return format(float(x), '.%dg' % d)

def bisect(f, lo, hi, it=200):
    flo = f(lo)
    for _ in range(it):
        mid = (lo + hi)/2
        if (f(mid) > 0) == (flo > 0): lo, flo = mid, f(mid)
        else: hi = mid
    return (lo + hi)/2

# ---------------- (A) v1's own range ----------------
ES = math.log(4)/(5*math.log(5))
def q_of(theta):            # main.tex Cor. m:cor:tradeoff: q = (H(theta) + theta ln 4)/ln 2
    return (H(theta) + theta*math.log(4))/math.log(2)
def gamma_of(theta, c):     # gamma = theta log2((c-1)/4)
    return theta*math.log((c-1)/float(4))/math.log(2)
def Rp(c, g):               # main.tex eq. (m:eq:Rc): R'_c(gamma)
    c = float(c)
    return math.log(2)/(c*math.log(5) - c/2*H(1/c) - (c-1)*math.log(2) + g*math.log(2))

theta1 = bisect(lambda th: q_of(th) - 1, 0.1, 0.3)
def F_v1(kap):
    """sup of R'_c(gamma) over c > 5, 0 < theta < theta_1 (q < 1), gamma = theta log2((c-1)/4) > kap - 1."""
    kap = float(kap)
    c = 1 + 4*math.pow(2, (kap-1)/theta1)
    return Rp(c, kap-1), c

print("(A) v1's own range (main.tex Corollary m:cor:tradeoff, Theorem m:thm:general)")
print(f"  es = ln4/(5 ln5) = {nstr(ES, 12)}")
print(f"  theta_1 (q(theta_1) = 1) = {nstr(theta1, 12)}; q is increasing on (0, 0.8): "
      f"q(0.1) = {nstr(q_of(0.1), 8)}, q(0.3) = {nstr(q_of(0.3), 8)}")
print(f"  R'_5(0) = {nstr(Rp(5, 0), 12)} (should equal es)")
print("  kappa > 1: F_v1(kappa) = R'_c(kappa-1), c = 1 + 4*2^((kappa-1)/theta_1)")
print("   kappa      F_v1         c            kappa*F    (kappa+1)*F")
worst_kF, worst_k1F = 0, 0
for kap in ["1.0001", "1.001", "1.01", "1.0238", "1.05", "1.1", "1.2", "1.3", "1.5", "2", "3", "4", "5"]:
    F, c = F_v1(kap)
    k = float(kap)
    worst_kF = max(worst_kF, k*F); worst_k1F = max(worst_k1F, (k+1)*F)
    print(f"   {kap:8s} {nstr(F, 8):12s} {nstr(c, 8):12s} {nstr(k*F, 6):10s} {nstr((k+1)*F, 6)}")
# dense scan for the two conditions
mx_kF, mx_k1F, arg1, arg2 = 0, 0, None, None
for i in range(1, 20001):
    k = 1 + float(i)/2000        # (1, 11]
    F, _ = F_v1(k)
    if k*F > mx_kF: mx_kF, arg1 = k*F, k
    if (k+1)*F > mx_k1F: mx_k1F, arg2 = (k+1)*F, k
print(f"  scan kappa in (1, 11], step 5e-4: max kappa*F_v1 = {nstr(mx_kF, 8)} at {nstr(arg1, 6)}; "
      f"max (kappa+1)*F_v1 = {nstr(mx_k1F, 8)} at {nstr(arg2, 6)}")
print("  (for kappa > 11: F_v1 < R'_c(0) with c > 1 + 4*2^(10/theta_1), below 1e-15; both products far below 1)")
F11, c11 = F_v1(11)
print(f"   F_v1(11) = {nstr(F11, 5)}, c = {nstr(c11, 5)}")
# sanity: random feasible (theta, c) never exceed the formula
random.seed(1)
viol = 0
for _ in range(20000):
    kap = 1 + random.random()*1.5
    th = random.random()*float(theta1)
    gmin = kap - 1
    # c from gamma > kap - 1
    if th <= 0 or gmin/th > 40: continue
    cmin = 1 + 4*2**(gmin/th)
    if cmin > 1e12: continue
    c = cmin*(1 + random.random())
    g = gamma_of(th, c)
    if not (g > gmin and c > 5): continue
    if Rp(c, g) > F_v1(kap)[0] + 1e-12: viol += 1
print(f"  random feasible (theta, c) exceeding F_v1: {viol} of the sampled points")

print("  sample triples, case kappa <= 1 (eps = a/min(b,c) < es, kappa = (b+c-1)/a):")
for (a, b, c) in [(Fr(1,27), Fr(14,27), Fr(14,27)), (Fr(1,20), Fr(13,25), Fr(13,25)), (Fr(1,100), Fr(1,10), Fr(91,100)),
                  (Fr(3,50), Fr(3,5), Fr(23,50))]:
    eps = a/min(b, c); kap = (b + c - 1)/a
    print(f"   (a,b,c) = ({float(a):.5f}, {float(b):.5f}, {float(c):.5f}): eps = {float(eps):.5f}, kappa = {float(kap):.5f},"
          f" in region: {bool(eps < ES and 0 < kap <= 1)}")
# the explicit instance of Cor. m:cor:explicit(b): (eps, gamma, q) = (1/14, 0.077, 0.421) at kappa = 1, b = c
a, b = Fr(1, 27), Fr(14, 27)
print(f"  explicit point (1/27, 14/27, 14/27): m = N^(27/14); saving in m-units a*min(0.077, kappa - 0.421) = "
      f"{float(a*min(Fr(77,1000), 1 - Fr(421,1000))):.6f}; hypothesised exponent 28/27 = {28/27:.6f}; "
      f"algorithm exponent {28/27 - float(a*Fr(77,1000)):.6f}")

# ---------------- (B) alpha-parametric composite ----------------
J = json.load(open(os.path.join(HERE, "r79b_certify.json")))
A = Fr(J["alpha_lo"])
PTS = sorted((Fr(p["t"]), Fr(p["M_hi"])) for p in J["points"] if 0 < Fr(p["t"]) < 1)
print()
print("(B) alpha-parametric composite on r79b's certified grid")
print(f"  alpha(P0) lower end a = {float(A):.12f}; {len(PTS)} grid points t in (0,1)")
Cbest = max(((A*t - M)/(1 - t), t) for t, M in PTS)
print(f"  C = max_t (a t - M_t)/(1 - t) = {float(Cbest[0]):.9f} at t = {Cbest[1]}")
kst = max(((1 - M/A)/(1 - t), t) for t, M in PTS)
print(f"  kappa* = max_t (1 - M_t/a)/(1 - t) = {float(kst[0]):.9f} at t = {kst[1]}")
npos = sum(1 for t, M in PTS if A*t > M)
print(f"  grid points with a t > M_t: {npos}")

def s_of(kap, t):
    return t*kap if kap <= 1 else 1 - kap*(1 - t)

def F_formula(kap, e, g):
    best = (Fr(-1), None)
    for t, M in PTS:
        s = s_of(kap, t)
        if s <= 0 or A*s <= M: continue
        need = (t - s) + (1 - t)*g/e
        xmin = max(need, Fr(0))/(A*s - M)
        v = (1 + A*xmin)/(xmin + 1/e)
        if kap > 1:
            v = min(v, 1/((1 + xmin)/(1 + A*xmin) + kap - 1))
        if v > best[0]: best = (v, t)
    return best

def lines_at(kap, e, g, eps, t, M):
    """all savings (times (1+ax) where natural) at x with phi(x) = eps exactly; delta = 0, delta_B = 0."""
    x = (1 - eps/e)/(eps - A)
    s = s_of(kap, t)
    sub = x*(A*s - M) - (t - s) - (1 - t)*g*((1 + A*x)/eps - x)      # Lean saving_le_one/gt_one, exact excess
    need = s*(1 + A*x) - x*M                                          # needed entries (read-off/decoding)
    enc = 1/eps - (1 + x)/(1 + A*x) - (max(kap - 1, 0))               # top encodings vs target
    io = 1/eps - 1 - max(kap - 1, 0)                                  # input/output N D vs target
    rng = (1 + A*x)/(x + 1/e) - eps                                   # bottom range D_A <= N_sub^e (= 0 by choice)
    return x, sub, need, enc, io, rng

print("  F(kappa; e, g) (sup over grid t of phi(x_min)); direct re-check at eps = F - 1e-7 with x = (1-eps/e)/(eps-a):")
cases = [(Fr(1,10), Fr(1,2), 0), (Fr(1,2), Fr(1,2), 0), (Fr(9,10), Fr(1,2), 0), (Fr(1), Fr(1,2), 0),
         (Fr(1,2), Fr(321334,10**6), 0), (Fr(1), Fr(321334,10**6), 0), (Fr(1), Fr(35,100), Fr(1363,10**6)),
         (Fr(201,200), Fr(1,2), 0), (Fr(51,50), Fr(1,2), 0)]
for kap, e, g in cases:
    F, t = F_formula(kap, e, g)
    M = dict(PTS)[t]
    eps = F - Fr(1, 10**7)
    x, sub, need, enc, io, rng = lines_at(kap, e, g, eps, t, M)
    ok = sub > 0 and need > 0 and enc > 0 and io > 0 and rng >= 0
    extra = ""
    if kap == 1:
        Ct = (A*t - M)/(1 - t)
        extra = f"; closed form (C e + a g)/(C + g) = {float((Ct*e + A*g)/(Ct + g)):.6f}"
    print(f"   kappa {float(kap):.4f}, e {float(e):.6f}, g {float(g):.6f}: F = {float(F):.6f} (t = {t}){extra}")
    print(f"      re-check at eps = F - 1e-7: x = {float(x):.5g}, savings: sub {float(sub):.3g}, needed {float(need):.3g}, "
          f"enc {float(enc):.3g}, io {float(io):.3g}, range slack {float(rng):.1g} -> all positive: {ok}")
# E3/E7: ABFK Theorem 1.3/1.10 triples have eps (kappa+1) = c/min(b,c) >= 1
print("  ABFK Thm 1.10 triples (sigma-1, 2-sigma, 1+r-sigma): eps*(kappa+1) = c/min(b,c) >= 1; region needs F(kappa) > 1/(kappa+1).")
for kap in [Fr(1,2), Fr(9,10), Fr(1)]:
    F, _ = F_formula(kap, Fr(1,2), 0)
    print(f"   alpha = 1/2 (g = 0): kappa {float(kap)}: F = {float(F):.6f} vs 1/(kappa+1) = {float(1/(kap+1)):.6f}")

# ---------------- (A2) v1's data structure with R14's exact box count (r14.md Thm 1-2; v2 addition) ----------------
print()
print("(A2) v1's data structure with the exact box count (r14.md Theorems 1-2, planned v2 Corollary m:cor:exactboxes)")
def bR(th, c):
    return th*math.log(4) - (1-th)*math.log(1-th) - (c-1+th)*math.log(c-1+th) + (c-1)*math.log(c-1)
def Afun(c):
    return 2*c*math.log(5) - c*H(1/c) - (c-1)*math.log(4)
def cmin(th):          # unique c > 1 with b(th, c) = 0
    return bisect(lambda c: bR(th, c), 1 + 1e-12, 1e6)
def eps_theta(th):
    return math.log(4)/Afun(cmin(th))
def eps_q(q):
    th = bisect(lambda t: q_of(t) - q, 1e-12, 0.8 - 1e-12)
    return eps_theta(th)
for q in [1e-6, 0.25, 0.5, 0.75, 1.0]:
    print(f"   eps_q at q = {q}: {eps_q(q):.6f}")
def F_DS(kap):         # kappa > 1: theta -> theta_1, c with -b(theta_1, c)/ln 2 = kappa - 1
    c = bisect(lambda c: -bR(theta1, c)/math.log(2) - (kap - 1), 1 + 1e-9, 1e15)
    return math.log(4)/(Afun(c) + (kap - 1)*math.log(4)), c
for kap in [1.0001, 1.0239, 1.05, 1.1, 1.2, 1.5, 2.0]:
    F, c = F_DS(kap)
    print(f"   F_DS({kap}) = {F:.6f} (c = {c:.4f}); compare F_v1 = {F_v1(kap)[0]:.6f}")
