"""R76: batch-size theory.  Closed forms of r76.md, evaluated numerically.

Model: X (N x D), Y (D x N), D = N^eps preprocessed in N^{2-delta}; a batch B of wanted entries is then answered.
Literal measure (task): batch cost polynomially below |B| D.  Hyp measure: below min(|B| D, N^2).

(1) Columns, no preprocessing: k = D^b columns by fast rectangular MM, per-entry saving (in powers of D)
       g_MM(b) = 1 + 2b - b omega(1, 1/b, 1)   (eps-independent; > 0 for every b > 0).
    omega(1,r,1) upper bound used: r <= alpha_V: 2; alpha_V <= r <= 1: convex interpolation to omega;
    r >= 1: omega + r - 1 (split the inner dimension).  omega = 2.371339, alpha_V = 0.321334.
(2) One column with preprocessing (R32 composite): per-entry exponent Q = (x c' + q_A)/(1 + alpha x), range
    eps < (1 + alpha x)/(x + 1/eps_A(q_A)); g_col(eps) = sup (1 - Q).
(3) k = D^b columns, composite (column union) with fast-MM bottom (sub-columns batched per term, adversary spreads):
    Q = (x c' + 1 - g_MM(b_A))/(1 + alpha x), b_A = max(0, b(1 + alpha x) - (2 - c_col) x), eps < (1+alpha x)/(1+x).
(4) Spread entries, |B| = N^2/D^kappa: Lemma 1 (r59-part1) gives sub-queries N^2 D^{-t kappa} K^{Lambda(t)}, each
    D_A^{q_A}; condition [x Lambda(t) + q_A]/(1 + alpha x) < T + t kappa with T = 1 - kappa (literal) or
    min(0, 1 - kappa) (Hyp measure); range eps < (1 + alpha x)/(x + 1/eps_A); bottoms: direct inner products
    (q_A = 1, eps_A = 1) or the paper's data structure (q_A in (0,1), eps_A = r14's eps_q(q_A); q_A -> 0: eps*).
    Lambda: numerical limit profile (r76_lamtable.json, linear interpolation of a convex function = upper bound).
(5) range_b(sigma) for |B| = N^sigma: kappa = (2 - sigma)/eps; sup eps with eps < f((2-sigma)/eps); plus the full
    product without preprocessing (literal measure): omega(1,eps,1) < sigma + eps.
Run: ~/.venv/bin/python r76_curve.py > r76_curve_out.txt
"""
import json, os, sys
from math import log, inf
import numpy as np
from scipy.optimize import minimize
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r20_rates as R          # read-only import (functions only)
from r32_column_rates import part, epsA_single

E = log(4)/(5*log(5))
OM, AV = 2.371339, 0.321334
HERE = os.path.dirname(os.path.abspath(__file__))
TAB = json.load(open(os.path.join(HERE, "r76_lamtable.json")))
TG = np.array(TAB["t"]); LQ = {q: np.array(TAB["Lam"][str(q)]) for q in (6, 7)}
TG0 = np.concatenate([[0.0], TG]); LQ0 = {q: np.concatenate([[0.0], LQ[q]]) for q in (6, 7)}

def om_ub(r):
    if r <= AV: return 2.0
    if r <= 1: return 2 + (r - AV)*(OM - 2)/(1 - AV)
    return OM + r - 1

def g_MM(b):
    if b <= 0: return 0.0
    return min(1.0, 1 + 2*b - b*om_ub(1/b))

# ------------------------------------------------------------------ laser point
def point(lam6, us=None):
    """alpha_max(lam6) over u (slack >= 0), and ln a, c_o, c_col, Lambda(t) on the grid."""
    qs = (6, 7); lams = (lam6, 1 - lam6)
    def comb(u):
        ps = [part(q, uu) for q, uu in zip(qs, u)]
        S = lambda k: sum(l*p[k] for l, p in zip(lams, ps))
        return S, ps
    if us is None:
        best = None
        for s0 in (0.9, 0.97, 0.99):
            u0 = [s0/(q + 2) for q in qs]
            r = minimize(lambda u: -comb(u)[0]("lnb")/comb(u)[0]("lna"), u0, method="SLSQP",
                         bounds=[(0, 1/(q + 2)) for q in qs],
                         constraints=[dict(type="ineq", fun=lambda u: comb(u)[0]("slack"))],
                         options=dict(ftol=1e-15, maxiter=500))
            if comb(r.x)[0]("slack") >= -1e-10 and (best is None or -r.fun > best[0]):
                best = (-r.fun, r.x)
        us = best[1]
    S, ps = comb(us)
    lna = S("lna")
    Lam = (lam6*LQ0[6] + (1 - lam6)*LQ0[7])/lna
    return dict(lam6=lam6, us=us, alpha=S("lnb")/lna, co=S("lncov")/lna, ccol=S("lncol")/lna, Lam=Lam,
                slack=S("slack"))

# ------------------------------------------------------------------ bottoms
QA_GRID = [0.0, 1e-4, 1e-3, 3e-3, 0.01, 0.02, 0.04, 0.07, 0.1, 0.15, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 0.97]
BOTTOMS = [(0.0, E)] + [(g, epsA_single(g)) for g in QA_GRID[1:]] + [(1.0, 1.0)]   # (q_A, eps_A); last = direct

def rng(alpha, x, eA):
    return (1 + alpha*x)/(x + 1/eA)

def best_range_lin(alpha, A, Bc, eA):
    """sup over x > 0 of rng(alpha,x,eA) subject to x*A < Bc  (A = Lam - alpha s, Bc = s - q_A)."""
    if abs(A) < 1e-15:
        if Bc <= 0: return -inf
        lo, hi = 0.0, inf
    elif A > 0:
        if Bc <= 0: return -inf
        lo, hi = 0.0, Bc/A
    else:
        lo, hi = max(0.0, Bc/A), inf      # x > Bc/A (A < 0)
    if lo >= hi: return -inf
    if eA < alpha:      # increasing in x
        return alpha if hi == inf else rng(alpha, hi, eA)
    else:               # decreasing in x
        return rng(alpha, lo, eA) if lo > 0 else (eA if Bc > 0 and hi > 0 else -inf)

def f_spread(P, kappa, measure="lit", tmax=1.0, bottoms=BOTTOMS):
    """sup eps over t, bottom, x (strict inequalities: value is a supremum)."""
    alpha, Lam = P["alpha"], P["Lam"]
    T = 1 - kappa if measure == "lit" else min(0.0, 1 - kappa)
    best = (-inf, None)
    for i, t in enumerate(TG0):
        if t > tmax + 1e-12: break
        s = T + t*kappa
        A = Lam[i] - alpha*s
        for qA, eA in bottoms:
            v = best_range_lin(alpha, A, s - qA, eA)
            if v > best[0]:
                best = (v, (round(float(t), 5), qA, round(eA, 6)))
    return best

# ------------------------------------------------------------------ columns
def g_col(P, eps, bottoms=BOTTOMS[:-1]):
    """R32 one-column composite with the paper's data structure (q_A < 1); also x = 0 (data structure alone)."""
    a, cp = P["alpha"], P["ccol"] - 1
    best = 0.0
    for qA, eA in bottoms:
        if eps < eA:
            best = max(best, 1 - qA); continue
        if eps >= a: continue
        x0 = (eps/eA - 1)/(a - eps)
        if eps >= rng(a, x0*(1 + 1e-12), eA) - 1e-15 and x0 > 0:
            pass
        Q = (x0*cp + qA)/(1 + a*x0)
        best = max(best, 1 - Q)
    return best

def g_comb(P, eps, b):
    a, cc = P["alpha"], P["ccol"]; cp = cc - 1
    best = g_MM(b)
    for x in np.concatenate([np.linspace(0.01, 2, 200), np.linspace(2, 60, 300)]):
        if not eps < (1 + a*x)/(1 + x): break
        bA = max(0.0, b*(1 + a*x) - (2 - cc)*x)
        Q = (x*cp + 1 - g_MM(bA))/(1 + a*x)
        best = max(best, 1 - Q)
    return best

def main():
    print("(0) laser points")
    P0 = point(7/19, us=[0.97/8, 0.979/9])
    print(f"  P0 (lam6 = 7/19, u(q+2) = 0.97, 0.979): alpha = {P0['alpha']:.7f}, c_o = {P0['co']:.6f}, "
          f"c_col = {P0['ccol']:.6f}, slack = {P0['slack']:.2e}, Lambda(1) = {P0['Lam'][-1]:.6f}")
    P23 = point(0.1972); P32 = point(0.18785); PC = point(0.3635)
    for nm, P in (("R23 point", P23), ("R32 point", P32), ("alpha_C point", PC)):
        print(f"  {nm} lam6 = {P['lam6']}: alpha_max = {P['alpha']:.6f}, c_o = {P['co']:.6f}, c_col = {P['ccol']:.6f}, "
              f"slack = {P['slack']:.1e}")
    LAMS = [round(v, 4) for v in np.linspace(0.0, 0.6, 31)]
    PTS = [point(l) for l in LAMS]

    print("\n(1) columns without preprocessing: per-entry saving g_MM(b), k = D^b columns (every eps)")
    for b in (0.01, 0.05, 0.1, 0.2, 0.3, 0.5, 1.0, 1.5, 2.0, 3.0, 1/AV):
        print(f"  b = {b:.4f}: g_MM = {g_MM(b):.5f}   (k = N^beta columns: beta = b eps)")

    print("\n(2) one column with preprocessing (R32): g_col(eps), best over the q6/q7 mixture")
    for eps in (0.05, 1/14, 0.1, 0.12, 0.15, 0.17, 0.18, 0.19, 0.2, 0.203, 0.2045, 0.2046):
        g = max(g_col(P, eps) for P in PTS + [P32])
        print(f"  eps = {eps:.4f}: g_col = {g:.5f}")
    # threshold check
    lo, hi = 0.17, 0.25
    for _ in range(50):
        m = (lo + hi)/2
        if g_col(P32, m) > 1e-12: lo = m
        else: hi = m
    print(f"  threshold g_col > 0 at the R32 point: eps < {lo:.6f}  (R32: 0.204684)")

    print("\n(3) k = D^b columns: max(g_MM(b), g_col(eps)) against the composite with fast-MM bottom g_comb")
    for eps in (0.1, 0.15, 0.19, 0.2, 0.22, 0.25, 0.29):
        row = []
        for b in (0.0, 0.05, 0.1, 0.2, 0.5, 1.0):
            gc = max(g_col(P, eps) for P in PTS[::3] + [P32])
            gm = g_MM(b)
            gk = max(g_comb(P, eps, b) for P in PTS[::3] + [P32])
            row.append(f"b={b}: {max(gc, gm):.4f}/{gk:.4f}")
        print(f"  eps = {eps}: " + "  ".join(row))

    print("\n(4) spread entries |B| = N^2/D^kappa: f(kappa) = sup eps (literal measure), at P0 and best over lam6")
    print("    columns: P0 all t | P0 t <= 0.3249 or t = 1 (proved-t set) | best lam6 all t [lam6, alpha, (t, q_A, eps_A)]")
    KAP = [1.0, 1.02, 1.05, 1.1, 1.2, 1.3, 1.5, 1.75, 2.0, 2.5, 3.0, 4.0, 5.0, 6.0, 8.0, 10.0, 15.0, 30.0, 100.0]
    fbest = {}
    for kap in KAP:
        a0 = f_spread(P0, kap)
        tm = max(f_spread(P0, kap, tmax=0.3249)[0], t1_only(P0, kap))
        bb = max(((f_spread(P, kap), P) for P in PTS), key=lambda z: z[0][0])
        fbest[kap] = bb[0][0]
        print(f"  kappa = {kap:7.2f}: {a0[0]:.6f} | {tm:.6f} | {bb[0][0]:.6f} [lam6 = {bb[1]['lam6']}, alpha = "
              f"{bb[1]['alpha']:.5f}, {bb[0][1]}]")
    print("  check kappa -> infinity at the R23 point with t = 1 only (R23: 0.194639):",
          f"{t1_only(P23, 1e6):.6f}")

    print("\n(4b) Hyp measure (target min(|B| D, N^2)), kappa <= 1, at P0 (R75 strong form via Theorem D):")
    for kap in (0.01, 0.05, 0.1, 0.25, 0.5, 0.75, 1.0):
        v = f_spread(P0, kap, measure="hyp")
        print(f"  kappa = {kap}: sup eps = {v[0]:.6f} at (t, q_A, eps_A) = {v[1]}   (alpha(P0) = {P0['alpha']:.6f})")

    print("\n(5) range_b(sigma), |B| = N^sigma spread entries, literal measure (best lam6, all t)")
    for sig in (0.0, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 1.6, 1.65, 1.68, 1.7, 1.705, 1.71, 1.75, 1.8, 1.9):
        comp = range_sigma(sig, PTS)
        fp = full_product_range(sig)
        print(f"  sigma = {sig:5.3f}: composite {comp:.6f}   full product (no preprocessing) {fp:.6f}   "
              f"range >= {max(comp, fp):.6f}")

def t1_only(P, kappa):
    a = P["alpha"]; L1 = P["Lam"][-1]
    T = 1 - kappa; s = T + kappa
    best = -inf
    for qA, eA in BOTTOMS:
        best = max(best, best_range_lin(a, L1 - a*s, s - qA, eA))
    return best

def range_sigma(sig, PTS):
    best = 0.0
    for eps in np.linspace(0.15, 0.40, 501):
        kap = (2 - sig)/eps
        if kap < 1:   # full-product side handled separately; composite also works there
            v = max(f_spread(P, kap)[0] for P in PTS[::5])
        else:
            v = max(f_spread(P, kap)[0] for P in PTS[::5])
        if eps < v: best = max(best, eps)
    return best

def full_product_range(sig):
    best = 0.0
    for eps in np.linspace(0.0, 1.0, 10001)[1:]:
        if om_ub(eps) < sig + eps: best = eps
    return best

if __name__ == "__main__":
    main()
