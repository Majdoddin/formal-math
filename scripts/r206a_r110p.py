"""R206a Task 2: R110's per-pair SetDisjointness construction (r110b.md Theorem 1, lines 83-110) with the PRUNED
structure (r111b Theorem B with gamma' = gamma(theta,c)) in place of r14.md Theorem 1.

Only change in the conditions of r110b's Theorem 1 table (r110b.md lines 87-96):
  T1: c_i > 5 (Theorem B needs c > 5) instead of c_i >= 2;   R: eps_i (g(c_i) - 2 b(theta_i,c_i)) < ln 4
  instead of eps_i (A(c_i) - 2b) < ln 4  [eps < ln4/(g + gamma ln4), gamma ln4 = -2b].
  B, Q, C2, C3, V, S unchanged.
Design: float greedy on a rational grid (c in 1e-4 Z, theta in 1e-6 Z); nothing from the design is trusted.
Certificate: exact Fractions with r206a_iv log enclosures.
Usage: r206a_r110p.py eta0 tau  (decimal strings)
"""
import sys, math
from fractions import Fraction as F
import numpy as np
from r206a_iv import I, ln, ln2

LN2f = math.log(2); LN4f = math.log(4)

def Hf(t): return -t * np.log(t) - (1 - t) * np.log(1 - t)
def bf(t, c): return t * LN4f - (1 - t) * np.log(1 - t) - (c - 1 + t) * np.log(c - 1 + t) + (c - 1) * np.log(c - 1)
def gf(c): return c * np.log(c) - (c - 1) * np.log(c - 1) + (c - 1) * LN4f
def qf(t): return (Hf(t) + t * LN4f) / LN2f

SL = 5e-7   # relative design slack in R, absolute in Q, C2, C3, V

def dmax_arr(c, t, tau, x):
    G = -bf(t, c) / LN2f
    Rp = LN4f / (gf(c) + G * LN4f)
    e = Rp * (1 - SL)
    q = qf(t)
    with np.errstate(divide="ignore", invalid="ignore"):
        d = np.minimum.reduce([(tau - SL) / q, (1 + tau - x - SL) / (1 / e - G), (2 - x - SL) / (2 / e - G)])
    d = np.where((G > 0) & (c > 5), d, -1)
    return d, G, e

def _pick(cs, ts, tau, x, need, dprev):
    C, Tt = np.meshgrid(cs, ts, indexing="ij")
    d, G, e = dmax_arr(C, Tt, tau, x)
    ok = (G * d >= need) & (d > dprev)
    if ok.any():
        d2 = np.where(ok, d, -1)
    else:   # no feasible point yet: move towards the largest gamma*d (closest to feasibility)
        d2 = np.where(d > 0, G * d, -1)
    k = np.unravel_index(np.argmax(d2), d2.shape)
    return cs[k[0]], ts[k[1]], bool(ok.any())

def design(eta0, tau, maxK=12):
    x = 2 * tau + eta0
    dprev = 2 * tau
    chain = []
    for i in range(maxK):
        need = x - dprev + SL            # gamma d >= x - d_prev + slack
        cs = np.arange(5.05, 25.0, 0.01)
        ts = np.concatenate([np.arange(0.005, 0.0685, 0.0001), np.arange(0.0685, 0.068968, 0.000005)])
        c0, t0, feas = _pick(cs, ts, tau, x, need, dprev)
        for rad_c, rad_t in ((0.05, 3e-4), (0.01, 6e-5), (0.002, 1.5e-5), (0.0006, 4e-6)):
            cs2 = np.round(np.arange(max(5.0001, c0 - rad_c), c0 + rad_c, 1e-4), 4)
            ts2 = np.round(np.arange(max(1e-6, t0 - rad_t), min(0.068968, t0 + rad_t), 1e-6), 6)
            c0, t0, feas = _pick(cs2, ts2, tau, x, need, dprev)
        if not feas:
            return None, chain
        cR, tR = F(str(round(float(c0), 4))), F(str(round(float(t0), 6)))
        d, G, e = dmax_arr(np.array(float(cR)), np.array(float(tR)), tau, x)
        epsR = F(math.floor(float(e) * 1e10), 10 ** 10)
        dR = F(math.floor(float(d) * 1e10), 10 ** 10)
        chain.append((cR, tR, epsR, dR))
        dprev = float(dR)
        if dprev >= x:
            return chain, chain
    return None, chain

LN2 = ln2(); LN4 = 2 * LN2
def Hi(t): return -(t * ln(t)) - (1 - t) * ln(1 - t)
def bi(t, c): return t * LN4 - (1 - t) * ln(1 - t) - (c - 1 + t) * ln(c - 1 + t) + (c - 1) * ln(c - 1)
def gi(c): return c * ln(c) - (c - 1) * ln(c - 1) + (c - 1) * LN4

def certify(eta0, tau, chain, out):
    x = 2 * tau + eta0
    allok = True
    out.append(f"eta0 = {eta0} = {float(eta0)}, tau = {tau}, x = 2 tau + eta0 = {x} = {float(x)}, K = {len(chain)} structures")
    out.append("  i |  c        theta      eps            d            | gamma (lo)    q (hi)       | margins (exact lower bounds): T1 c-5, B -b, R ln4-eps(g-2b), Q tau-qd, C2, C3, V")
    dprev = 2 * tau
    minm = None
    for i, (c, t, e, d) in enumerate(chain, 1):
        bb = bi(t, c); G = -bb / LN2; q = (Hi(t) + t * LN4) / LN2
        m = {}
        m["T1"] = I(min(c - 5, F(4, 5) - t, e))
        m["B"] = -bb
        m["R"] = LN4 - e * (gi(c) - 2 * bb)
        m["Q"] = tau - q * d
        m["C2"] = (1 + tau - x) - (d / e - G * d)
        m["C3"] = (2 - x) - (2 * d / e - G * d)
        m["V"] = dprev - (x - G * d)
        oks = {k: (v.lo > 0 if k in ("T1", "B", "R") else v.lo >= 0) for k, v in m.items()}
        allok &= all(oks.values())
        for k in ("R", "Q", "C2", "C3", "V"):
            minm = float(m[k].lo) if minm is None else min(minm, float(m[k].lo))
        out.append(f"  {i} | {str(c):8s} {str(t):10s} {str(e):14s} {str(d):12s} | {float(G.lo):.7f}  {float(q.hi):.7f} | "
                   + "  ".join(f"{k} {float(v.lo):.3e}{'' if oks[k] else ' FAIL'}" for k, v in m.items())
                   + f"   serves p in [{float((x - G * d).lo):.9f}, {float(d):.9f}]")
        dprev = d
    endV = chain[-1][3] - x
    S = (2 - eta0) - (1 + 2 * tau)
    allok &= endV >= 0 and S >= 0
    out.append(f"  end condition d_K - x = {float(endV):.4e} (exact rational, {'ok' if endV >= 0 else 'FAIL'}); S: (2-eta0)-(1+2tau) = {float(S):.4f}")
    out.append(f"  smallest margin among R, Q, C2, C3, V: {minm:.3e}")
    out.append(f"  RESULT: {'ALL ' + str(7*len(chain)+2) + ' CONDITIONS HOLD' if allok else 'FAILS'}")
    return allok

if __name__ == "__main__":
    out = []
    if sys.argv[1].startswith("--slack="):
        SL = float(sys.argv[1].split("=")[1]); sys.argv.pop(1)
        out.append(f"design slack {SL}")
    pts = [(F(a), F(b)) for a, b in zip(sys.argv[1::2], sys.argv[2::2])]
    for eta0, tau in pts:
        chain, partial = design(float(eta0), float(tau))
        if chain is None:
            out.append(f"eta0 = {eta0}, tau = {tau}: design did not close; partial chain {[(float(c), float(t), float(e), float(d)) for c, t, e, d in partial]}")
            continue
        certify(eta0, tau, chain, out)
        out.append("")
    print("\n".join(out))
