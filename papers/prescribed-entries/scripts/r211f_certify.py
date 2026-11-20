#!/usr/bin/env python3
"""R211f: independent certification for CP part (E) (R87).

(A) Theorem R87.1's seven rational points (r87.md 4.3): exact rational checks of (4.1), positivity, u < pe <= pl,
    eps = u/pe, and rigorous enclosures of slack_X, slack_Y (exact Fraction arithmetic; ln by the atanh series with
    a proved tail bound, range reduction by powers of 2, outward rounding to 1e-45).  Label: CERTIFIED.
(B) The square point P0 = (7/19, 97/100, 979/1000) used for E on (3/4, 1]: alpha(P0) and slack(P0). CERTIFIED.
(C) Per row: sigma_A, beta_A, cbar bound, t-range 1/(2(cbar+1)), and the x -> infinity query rate
    sup_t (t kappa - (1+sigma) Lam_pr(t)/beta) on a t grid (floating point; COMPUTED).
(D) Cor. R87.2 samples (exact rationals): refuted a-intervals for kappa <= 1 under E (R87.1), under the square
    Theorem D (alpha(P0)), under v1 (0.17227), input-size ceiling min(b,c).
(E) ABFK Theorem 1.10 triples (a,b,c) = (s-1, 2-s, 1+r-s), s = sigma(r) in [1 + r/3, 1 + r mu/(1+mu)]:
    eps = a/min(b,c), shape ratio, kappa, at sample r (exact rationals, mu = 0.5286 [GU18] as cited by ABFK).
(F) Wedge extremes under E: max a and max min(b,c) over the rows (closed form, exact rationals).
"""
from fractions import Fraction as F
import math

PREC = F(1, 10**45)

def _round_out(lo, hi):
    s = 10**45
    return F(math.floor(lo * s), s), F(math.ceil(hi * s), s)

def _atanh2(y, n=60):
    """enclosure of 2*atanh(y) for |y| <= 1/5, rational y"""
    S = F(0)
    p = y
    y2 = y * y
    for k in range(n):
        S += p / (2 * k + 1)
        p *= y2
    # tail: sum_{k>=n} |y|^{2k+1}/(2k+1) <= |y|^{2n+1}/((2n+1)(1-y^2))
    tail = abs(y) ** (2 * n + 1) / ((2 * n + 1) * (1 - y2))
    return 2 * (S - tail), 2 * (S + tail)

LN2 = _round_out(*_atanh2(F(1, 3)))

def ln_enc(x):
    x = F(x)
    assert x > 0
    k = 0
    while x > F(4, 3):
        x /= 2; k += 1
    while x < F(2, 3):
        x *= 2; k -= 1
    y = (x - 1) / (x + 1)
    lo, hi = _atanh2(y)
    if k >= 0:
        lo += k * LN2[0]; hi += k * LN2[1]
    else:
        lo += k * LN2[1]; hi += k * LN2[0]
    return _round_out(lo, hi)

def negplogp(p):
    lo, hi = ln_enc(p)
    return -p * hi, -p * lo

def H(ps):
    lo = sum(negplogp(p)[0] for p in ps)
    hi = sum(negplogp(p)[1] for p in ps)
    return lo, hi

def fl(x, d=12):
    return f"{float(x):.{d}g}"

out = []
def P(*a):
    s = " ".join(str(x) for x in a)
    print(s); out.append(s)

P("R211f certification (calc/r211f_certify.py). ln enclosures: atanh series, 60 terms, outward rounding 1e-45.")
P("ln 2 in [", fl(LN2[0], 20), ",", fl(LN2[1], 20), "]; width", fl(LN2[1] - LN2[0], 3))

# ---------------- (A) the seven rows -----------------
rows = [  # q, sigma, u(q+2), vx(q+2), printed eps
    (7, F(3, 4), F(999, 1000), F(1, 2000), F(333, 1000)),
    (7, F(1, 2), F(919, 1000), F(237, 5000), F(2757, 7000)),
    (8, F(1, 3), F(179, 200), F(337, 5000), F(179, 400)),
    (10, F(1, 4), F(197, 200), F(47, 5000), F(197, 400)),
    (11, F(1, 5), F(951, 1000), F(83, 2500), F(2853, 5500)),
    (13, F(1, 7), F(887, 1000), F(53, 625), F(887, 1625)),
    (18, F(1, 10), F(973, 1000), F(49, 2500), F(10703, 18000)),
]
# Lean R87Points.lean values (pe, pl, w, u, vx, vy) for comparison
lean = {
    F(3, 4): (F(1, 3), F(4, 9), F(1, 9), F(111, 1000), F(1, 18000), F(1, 18000)),
    F(1, 2): (F(7, 27), F(14, 27), F(1, 9), F(919, 9000), F(79, 15000), F(7, 1875)),
    F(1, 3): (F(1, 5), F(3, 5), F(1, 10), F(179, 2000), F(337, 50000), F(47, 12500)),
    F(1, 4): (F(1, 6), F(2, 3), F(1, 12), F(197, 2400), F(47, 60000), F(7, 15000)),
    F(1, 5): (F(11, 78), F(55, 78), F(1, 13), F(951, 13000), F(83, 32500), F(79, 65000)),
    F(1, 7): (F(13, 120), F(91, 120), F(1, 15), F(887, 15000), F(53, 9375), F(47, 25000)),
    F(1, 10): (F(9, 110), F(9, 11), F(1, 20), F(973, 20000), F(49, 50000), F(37, 100000)),
}
P("")
P("(A) Theorem R87.1 rows (CERTIFIED: exact rationals; slack enclosures rigorous)")
allok = True
rowdata = []
for q, sig, uq, vxq, eps_pr in rows:
    w = F(1, q + 2)
    pl = F(q, q + 2) / (1 + sig)
    pe = sig * pl
    u = uq * w
    vx = vxq * w
    vy = w - u - vx
    checks = {
        "pe+pl=q/(q+2)": pe + pl == F(q, q + 2),
        "u+vx+vy=w": u + vx + vy == w,
        "all six > 0": min(pe, pl, w, u, vx, vy) > 0,
        "u<pe<=pl": u < pe <= pl,
        "pe/pl=sigma": pe / pl == sig,
        "eps=u/pe printed": u / pe == eps_pr,
        "Lean values equal": lean[sig] == (pe, pl, w, u, vx, vy),
    }
    X = (pl + w + vy, pe + u, vx)
    Y = (pe + w + vx, pl + u, vy)
    Z = (u + vx + vy, pe + pl, w)
    assert Z == (w, F(q, q + 2), w)
    HX, HY, HZ = H(X), H(Y), H(Z)
    sX = (HX[0] - HZ[1], HX[1] - HZ[0])
    sY = (HY[0] - HZ[1], HY[1] - HZ[0])
    checks["slack_X > 0"] = sX[0] > 0
    checks["slack_Y > 0"] = sY[0] > 0
    ok = all(checks.values())
    allok &= ok
    beta = u / pl
    P(f" q={q} sigma={sig}: pe={pe} pl={pl} u={u} vx={vx} vy={vy}")
    P(f"    slack_X in [{fl(sX[0])}, {fl(sX[1])}], slack_Y in [{fl(sY[0])}, {fl(sY[1])}]")
    P(f"    eps=u/pe={u/pe}={fl(u/pe,8)}, beta_A=u/pl={beta}={fl(beta,8)}, sigma_A={sig}; checks: "
      + ", ".join(k + ("=ok" if v else "=FAIL") for k, v in checks.items()))
    rowdata.append((q, sig, pe, pl, u, beta))
P(" all rows pass:", allok)

# ---------------- (B) the square point P0 -----------------
P("")
P("(B) square point P0 = (lam_6, u_6(q+2), u_7(q+2)) = (7/19, 97/100, 979/1000) (CERTIFIED)")
lam = {6: F(7, 19), 7: F(12, 19)}
uP = {6: F(97, 100) / 8, 7: F(979, 1000) / 9}
num_lo = num_hi = den_lo = den_hi = F(0)
sl_lo = sl_hi = F(0)
for q in (6, 7):
    w = F(1, q + 2); p = F(q, 2 * (q + 2)); u = uP[q]; v = (w - u) / 2
    lq = ln_enc(q)
    num_lo += lam[q] * u * lq[0]; num_hi += lam[q] * u * lq[1]
    den_lo += lam[q] * p * lq[0]; den_hi += lam[q] * p * lq[1]
    HX = H((p + w + v, p + u, v)); HZ = H((w, F(q, q + 2), w))
    sl_lo += lam[q] * (HX[0] - HZ[1]); sl_hi += lam[q] * (HX[1] - HZ[0])
a_lo, a_hi = num_lo / den_hi, num_hi / den_lo
P(f" alpha(P0) in [{fl(a_lo,15)}, {fl(a_hi,15)}]; > 0.2945976: {a_lo > F(2945976, 10**7)}; < 0.2945977: {a_hi < F(2945977, 10**7)}")
P(f" slack(P0) in [{fl(sl_lo)}, {fl(sl_hi)}]; > 0: {sl_lo > 0}")
alphaP0_lo = a_lo

# ---------------- (C) per-row cbar, t-range, gamma rate -----------------
P("")
P("(C) per row: cbar bound (Prop. 4.1), t-range t <= 1/(2(cbar+1)), and x->inf query rate "
  "sup_t [t kappa - (1+sigma) Lam_pr(t)/beta], Lam_pr(t) = t^2 ln^2(4 e q/t)/((q/(q+2)) ln q) (COMPUTED, grid)")
def lam_pr(t, q):
    return t * t * math.log(4 * math.e * q / t) ** 2 / ((q / (q + 2)) * math.log(q))
for q, sig, pe, pl, u, beta in rowdata:
    L1 = (q / (q + 2)) * math.log(q)
    cbar = ((math.log(q + 2) + q * math.log(2)) / (q + 2)) / L1
    tmax = 1 / (2 * (cbar + 1))
    res = []
    for kap in (0.5, 1.0):
        best = (-1, None)
        for i in range(1, 200001):
            t = tmax * i / 200000
            g = t * kap - (1 + float(sig)) * lam_pr(t, q) / float(beta)
            if g > best[0]:
                best = (g, t)
        res.append(best)
    P(f" q={q} sigma={sig}: cbar<={cbar:.6f}, t<={tmax:.5f}; rate(kappa=1/2)={res[0][0]:.4g} at t={res[0][1]:.3g};"
      f" rate(kappa=1)={res[1][0]:.4g} at t={res[1][1]:.3g}")

# ---------------- (D) Cor. R87.2 samples -----------------
P("")
P("(D) Cor. R87.2 samples, kappa <= 1 (exact rationals): refuted a in (b+c-1, min(b,c)*F)")
Etab = [(F(3, 4), F(333, 1000)), (F(1, 2), F(2757, 7000)), (F(1, 3), F(179, 400)), (F(1, 4), F(197, 400)),
        (F(1, 5), F(2853, 5500)), (F(1, 7), F(887, 1625)), (F(1, 10), F(10703, 18000))]
E_SQ = F(2945976, 10**7)  # alpha(P0) > this (certified in (B)); used as a safe value
def E(s):
    best = E_SQ  # the square row, sigma_A = 1, covers every s <= 1
    for si, ei in Etab:
        if si >= s:
            best = max(best, ei)
    return best
V1 = F(17227, 100000)
samples = [(F(10, 100), F(91, 100)), (F(5, 100), F(96, 100)), (F(20, 100), F(85, 100)), (F(30, 100), F(75, 100)),
           (F(40, 100), F(65, 100)), (F(55, 100), F(60, 100)), (F(10, 100), F(95, 100))]
def interval(lo, hi):
    return f"({fl(lo,6)}, {fl(hi,6)})" if hi > lo else "empty"
for b, c in samples:
    mn, mx = min(b, c), max(b, c)
    s = mn / mx
    lo = b + c - 1
    P(f" (b,c)=({fl(b,3)},{fl(c,3)}) s={fl(s,4)} E(s)={fl(E(s),6)}: R87.2 a in {interval(lo, mn*E(s))};"
      f" square Thm D (alpha(P0)) a in {interval(lo, mn*E_SQ)}; v1 (0.17227, kappa<=1 part) a in {interval(lo, mn*V1)};"
      f" ceiling a < {fl(mn,3)}")

# ---------------- (E) ABFK Theorem 1.10 triples -----------------
P("")
P("(E) ABFK Thm 1.10 triples (a,b,c)=(s-1,2-s,1+r-s), s=sigma(r) in [1+r/3, 1+r mu/(1+mu)], mu=0.5286 [GU18]")
MU = F(5286, 10000)
for r in [F(1, 100), F(1, 20), F(1, 10), F(3, 20), F(1, 5), F(1, 4), F(3, 11), F(3, 10), F(1, 2), F(1)]:
    rows_e = []
    for sg in (1 + r / 3, 1 + r * MU / (1 + MU)):
        a, b, c = sg - 1, 2 - sg, 1 + r - sg
        mn, mx = min(b, c), max(b, c)
        eps = a / mn; shape = mn / mx; kap = (b + c - 1) / a
        rows_e.append((sg, eps, shape, kap, E(shape)))
    (s0, e0, sh0, k0, E0), (s1, e1, sh1, k1, E1) = rows_e
    # the true triple has eps in [e0, e1] and shape in [sh1, sh0] (shape decreasing in sigma for r<1); E non-increasing
    inside = e1 < E(sh0)
    P(f" r={fl(r,4)}: sigma in [{fl(s0,6)}, {fl(s1,6)}], eps in [{fl(e0,6)}, {fl(e1,6)}], shape in [{fl(sh1,5)}, {fl(sh0,5)}],"
      f" kappa in [{fl(k1,5)}, {fl(k0,5)}], E(shape_max)={fl(E(sh0),6)} -> in R87.2 region for every sigma(r) in the interval: {inside}")
P(" route 2 (sigma(r) = 1 + r/3 forced by R87.1 + Prop. 2.1): at sigma0 = 1 + r/3, eps = 1/2 and shape = 2r/(3-r);"
  " eps*(shape) >= E(shape) > 1/2 iff shape <= 1/5 iff r <= 3/11 =", fl(F(3, 11), 6))

# ---------------- (F) wedge extremes -----------------
P("")
P("(F) wedge extremes under E (kappa <= 1): at shape s (min side beta0, max side beta0/s), b+c-1 <= a < beta0 E(s)")
P("    => beta0 < 1/(1 + 1/s - E(s)), a < E(s)/(1 + 1/s - E(s)); value at the right end of each step of E")
best = None
for s, e in [(F(1), E_SQ)] + Etab:
    b0 = 1 / (1 + 1 / s - e); amax = e * b0
    P(f"  s={s}: E={fl(e,6)}: min(b,c) < {fl(b0,6)}, a < {fl(amax,6)}")
    if best is None or amax > best[0]:
        best = (amax, s)
P(f"  largest a over the steps: {fl(best[0],6)} at s={best[1]} (E is constant on each step and 1 + 1/s grows as s falls,"
  f" so the right end of each step is its maximum)")

with open(__file__.replace(".py", "_out.txt"), "w") as fh:
    fh.write("\n".join(out) + "\n")
