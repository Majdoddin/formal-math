"""R32: column coverage of the level-1 CW laser algorithm and the hinted-OMv threshold of the composite with
column sharing at the top (and, optionally, R20's batched column queries in the sub-instances).

Per coordinate of a kept copy <a,b,a> (block triple), column part = 011 coordinates, row part = 101 coordinates.
Terms of CW_q^{(x)N} covering SOME output of a fixed column (union over rows):
   101 coord: union_i {i, q+1} = q+1 terms;  011 coord: {kappa_c, q+1} = 2;  z0 coords: q+2;  002: 1.
At the forced z-type (n0, n101 = n011, n002) = N(1, q/2, q/2, 1)/(q+2):
   ln U / N = p ln(2(q+1)) + ln(q+2)/(q+2),  p = q/(2(q+2));   ln a / N = p ln q.
Column exponent c_col = ln U / ln a, per-entry average c' = c_col - 1 (against c_o = 2(ln2 + ln(q+2)/q)/ln q).
Composite (r11 5.1, r18r23 1): a column of XY costs N_sub * U * D_A^{qA} (sub-queries) plus the combination,
which is a Kronecker-structured linear map applied in |U| K^{o(1)} time.  Need < N D^Q, Q<1:
   x (c' - alpha) < 1 - qA,  eps = (1 + alpha x)/(x + 1/eps_A(qA)).
eps_A(qA): r14 eps_q (single-entry sub-queries) or r20 eps^b_q (batched column sub-queries).
Run: ~/.venv/bin/python r32_column_rates.py
"""
from math import log
import sys, os
import numpy as np
from scipy.optimize import minimize, brentq
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r20_rates as R   # read-only import (functions only)

E = log(4)/(5*log(5))

def Hn(*ps):
    return -sum(x*log(x) for x in ps if x > 1e-300)

def part(q, u):
    t = 1/(q+2); p = q/(2*(q+2)); w = t; v = (t-u)/2
    slack = Hn(p+w+v, p+u, v) - Hn(t, 2*p, w)
    return dict(lna=p*log(q), lnb=u*log(q), lncov=(log(q+2)+q*log(2))/(q+2),
                lncol=p*log(2*(q+1)) + log(q+2)/(q+2), slack=slack)

def combo(qs, lams, us):
    ps = [part(q, u) for q, u in zip(qs, us)]
    S = lambda k: sum(l*pp[k] for l, pp in zip(lams, ps))
    return dict(alpha=S("lnb")/S("lna"), co=S("lncov")/S("lna"), ccol=S("lncol")/S("lna"), slack=S("slack"))

def eps_entry(a, c):          # r18r23: per-entry coverage, qA -> 0
    return c*E/(E + c - a)

def eps_col(a, cp, epsA=E, qA=0.0):   # column sharing: cp = c_col - 1
    if cp <= a: return a      # x unbounded -> eps -> alpha (only reached in the limit)
    x = (1-qA)/(cp - a)
    return (1 + a*x)/(x + 1/epsA)

# eps_A(qA) tables
def epsA_single(qA):
    th = brentq(lambda t: R.q1(t) - qA, 1e-12, 0.79); return R.eps_of(th)
def epsA_batched(qA):
    th = brentq(lambda t: R.qb(t) - qA, 1e-12, 0.79); return R.eps_of(th)

def best_qA(a, cp, fA):
    grid = np.concatenate([np.linspace(1e-4, 0.02, 40), np.linspace(0.02, 0.95, 94)])
    vals = [(eps_col(a, cp, fA(g), g), g) for g in grid]
    v0 = eps_col(a, cp, E, 0.0)
    best = max(vals)
    return max(best, (v0, 0.0))

def optimise(qs, target, starts=30, seed=1):
    rng = np.random.default_rng(seed); n = len(qs); best = (-1, None)
    split = lambda z: (z[:n], z[n:])
    def obj(z):
        c = combo(qs, *split(z)); return -target(c)
    cons = [dict(type="eq", fun=lambda z: sum(z[:n]) - 1),
            dict(type="ineq", fun=lambda z: combo(qs, *split(z))["slack"])]
    bounds = [(1e-9, 1)]*n + [(0, 1/(q+2)) for q in qs]
    for _ in range(starts):
        z0 = np.concatenate([rng.dirichlet(np.ones(n)), [rng.uniform(0, 1/(q+2)) for q in qs]])
        r = minimize(obj, z0, method="SLSQP", bounds=bounds, constraints=cons, options=dict(maxiter=2000, ftol=1e-15))
        lam, us = split(r.x)
        if abs(sum(lam)-1) > 1e-8: continue
        c = combo(qs, lam, us)
        if c["slack"] >= -1e-10 and target(c) > best[0]:
            best = (target(c), (list(np.round(lam, 5)), [round(float(u*(q+2)), 5) for u, q in zip(us, qs)], c))
    return best

if __name__ == "__main__":
    print("(1) per q (alpha = alpha_max(q)): c_o per entry, c_col per column, c' = c_col - 1, closed forms")
    for q in range(4, 13):
        co = 2*(log(2)+log(q+2)/q)/log(q)
        ccol = (log(2*(q+1)) + 2*log(q+2)/q)/log(q)
        print(f"   q={q:2d}: c_o={co:.6f}  c_col={ccol:.6f}  c'={ccol-1:.6f}  1+c_o-c_col = ln(2q/(q+1))/ln q = {log(2*q/(q+1))/log(q):.6f}")
    print("(2) best over mixtures, qA -> 0 (eps_A = eps*): per-entry (R23 check) and column-shared")
    tg_entry = lambda c: eps_entry(c["alpha"], min(c["co"], 2))
    tg_col = lambda c: eps_col(c["alpha"], c["ccol"] - 1)
    for qs in ([6], [7], [8], [6, 7], [6, 7, 8], [5, 6, 7, 8, 9], [6, 7, 8, 9, 10], [7, 8, 9, 10, 12]):
        be = optimise(qs, tg_entry); bc = optimise(qs, tg_col)
        c = bc[1][2]
        print(f"   q in {qs}: per-entry {be[0]:.6f} | column {bc[0]:.6f} lam={bc[1][0]} u(q+2)={bc[1][1]} "
              f"alpha={c['alpha']:.6f} c_col={c['ccol']:.6f} c'={c['ccol']-1:.6f} c_o={c['co']:.6f} slack={c['slack']:.1e}")
    print("(3) positive sub-instance query exponent qA at the column optimum of (2) for q in {6,7}")
    bc = optimise([6, 7], tg_col); c = bc[1][2]; a, cp = c["alpha"], c["ccol"]-1
    print(f"   qA->0: {eps_col(a, cp):.6f}")
    print(f"   single-entry sub-queries (r14 eps_q): best (eps, qA) = {best_qA(a, cp, epsA_single)}")
    print(f"   batched column sub-queries (r20 eps^b_q): best (eps, qA) = {best_qA(a, cp, epsA_batched)}")
    print("   (4) joint optimisation over mixture AND qA (batched), coarse qA grid")
    best = (-1, None)
    for g in [0.0, 0.001, 0.003, 0.01, 0.03, 0.1]:
        eA = E if g == 0 else epsA_batched(g)
        b2 = optimise([6, 7, 8], lambda c: eps_col(c["alpha"], c["ccol"]-1, eA, g), starts=15)
        print(f"     qA={g}: eps_A={eA:.6f} eps={b2[0]:.6f} lam={b2[1][0]}")
