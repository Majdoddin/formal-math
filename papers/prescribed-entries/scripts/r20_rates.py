"""r20_rates.py (2026-10-15), for exponents/r20.md (item R20 of research-beyond-0172.md).

Rates and exact finite-m counts for the BATCHED COLUMN QUERY (r20.md Sections 2-4).

Notation as r14_rates.py (main.tex Sections m:sec:leaves, m:sec:ds):
  b(theta,c) = theta ln4 - (1-theta)ln(1-theta) - (c-1+theta)ln(c-1+theta) + (c-1)ln(c-1)   (half-count rate)
  gamma = -b/ln2 (boxes), A(c) = 2c ln5 - c H(1/c) - (c-1) ln4, R'_c(gamma) = ln4/(A(c)+gamma ln4).
Per-entry query, single entry (paper):      sum_{d<=t} C(2m,d)4^d,                     q(theta)  = (H+theta ln4)/ln2.
Per-entry query, batched column (r20 Lemma 3/Thm 4), average over the columns:
  O(L^3) * sum_{d1+d2<=t} C(m,d1) 2^d1 C(m,d2) 4^d2   (first half shared, second half not),
  q_b(theta) = min_{0<x<=1} [ -2 theta ln x + ln((1+2x)(1+4x)) ] / ln4   (Chernoff form; equals the max form).
Range at a fixed column-query exponent q: theta_q^b solves q_b(theta) = q, c_min solves b(theta,c) = 0,
  eps_q^b = ln4 / A(c_min(theta_q^b))   (same proof as r14 Theorem 2 with q_b in place of q).

Parts
 (1) q_b by the min-x form and by the max form (grid), table of eps_q (single entry, = r14) and eps_q^b (batched).
 (2) Switching region in (d1, d2) instead of total order (r20.md Section 4): best up-closed High region,
     condition max{ f(t1)+f(t2) : g1(t1)+g2(t2) >= q ln4 } < 0, with f = b(.,c), g1 = H + x ln2, g2 = H + x ln4.
 (3) EXACT finite-m counts in log space (lgamma): box bound (2m+1) sum_{d>=t} beta'_d, batched query bound
     (2L+1) sum_{d1+d2<=t} Bpe(d1) C(m,d2) 4^d2 with the Delta-free first-half bound
     Bpe(d1) = 2^d1 C(L,m-d1) sum_{b<=d1} C(n,b) 2^(n-b) / (2^(L-m) mu^2 C(L,m)),  n = L-m+d1,
     and the encoding condition; gamma_m, q_m, eps_m for growing m at fixed (c, theta): convergence to (1).
Run: ~/.venv/bin/python r20_rates.py   (numpy, scipy; single process; < 1 min)
"""
from math import log, exp, ceil
import numpy as np
from scipy.optimize import brentq, minimize_scalar

L2, L4, L5 = log(2), log(4), log(5)
MU2 = 0.0833986


def H(x):
    return 0.0 if x <= 0 or x >= 1 else -x*log(x) - (1-x)*log(1-x)


def xlx(x):
    return 0.0 if x <= 0 else x*log(x)


def b(th, c):
    return th*L4 - xlx(1-th) - xlx(c-1+th) + xlx(c-1)


def A(c):
    return 2*c*L5 - c*H(1/c) - (c-1)*L4


def q1(th):
    return (H(th) + th*L4)/L2


def qb(th):
    r = minimize_scalar(lambda x: -2*th*log(x) + log((1+2*x)*(1+4*x)), bounds=(1e-12, 1.0), method="bounded",
                        options={"xatol": 1e-13})
    return min(r.fun, log(15.0))/L4      # x = 1 endpoint: ln(3*5)


def qb_max(th, K=4000):
    best = -1.0
    for k in range(K + 1):
        t1 = min(1.0, 2*th)*k/K
        t2 = 2*th - t1
        if t2 < 0 or t2 > 1:
            continue
        best = max(best, H(t1) + t1*L2 + H(t2) + t2*L4)
    return best/L4


def cmin(th):
    return brentq(lambda c: b(th, c), 1.0 + 1e-9, 60.0, xtol=1e-14)


def eps_of(th):
    return L4/A(cmin(th))


def part1():
    print("(1) batched column query exponent and the range at fixed q")
    for th in [0.05, 0.1, 0.17054, 0.19, 0.25]:
        print(f"   theta={th}: q(theta)={q1(th):.6f}  q_b min-x form={qb(th):.6f}  max form={qb_max(th):.6f}")
    print("   q      theta_q   c_min    eps_q (single entry, r14) | theta_q^b c_min^b  eps_q^b (batched column)")
    out = {}
    for q in [0.1, 0.25, 0.5, 0.75, 0.9, 1.0]:
        ts = brentq(lambda t: q1(t) - q, 1e-9, 0.79)
        tb = brentq(lambda t: qb(t) - q, 1e-9, 0.79)
        print(f"   {q:4.2f}   {ts:.5f}  {cmin(ts):.5f}  {eps_of(ts):.6f}              | {tb:.5f}   {cmin(tb):.5f}"
              f"  {eps_of(tb):.6f}")
        out[q] = (ts, tb)
    return out


def part2():
    print("(2) switching region in (d1,d2): best up-closed High = {g1+g2 >= q ln4}")
    xs = np.linspace(0, 1, 2001)[:-1]
    Hx = np.array([H(x) for x in xs])
    g1 = Hx + xs*L2
    g2 = Hx + xs*L4
    for q in [0.5, 1.0]:
        G = g1[:, None] + g2[None, :]
        mask = G >= q*L4

        def worst(c):
            f = np.array([b(x, c) for x in xs])
            return (f[:, None] + f[None, :])[mask].max()
        c0 = brentq(worst, 3.0, 5.0, xtol=1e-7)
        print(f"   q={q}: c_min={c0:.5f}  eps={L4/A(c0):.6f}  (grid 2000^2)")


from scipy.special import gammaln


def lCv(n, k):
    k = np.asarray(k, dtype=float)
    out = gammaln(n+1) - gammaln(k+1) - gammaln(n-k+1)
    return np.where((k < 0) | (k > n), -np.inf, out)


def lse(v):
    v = np.asarray(v, dtype=float)
    mx = v.max()
    return mx + np.log(np.exp(v - mx).sum())


def part3():
    print("(3) exact finite-m counts (log space): gamma_m, q_m (batched, Delta-free bound), eps_m")
    for (c, th) in [(4.62, 0.18), (4.56, 0.185), (4.535, 0.1885), (4.75, 0.16), (4.88, 0.10)]:
        g_inf = -b(th, c)/L2
        print(f"   c={c}, theta={th}: limits gamma={g_inf:.5f} q_b={qb(th):.5f} (single entry q={q1(th):.5f})"
              f" eps=R'_c(gamma)={L4/(A(c)+g_inf*L4):.5f}")
        for m in [100, 400, 1600, 6400, 25600]:
            L = ceil(c*m)
            t = 2*ceil(th*m)
            lD = m*L4
            e = np.arange(m+1)
            lbeta = lCv(L, m-e) + (L-m+e)*L4
            # suffix log-sums of beta_e
            suf = np.logaddexp.accumulate(lbeta[::-1])[::-1]
            d1 = np.arange(m+1)
            need = t - d1
            ok = need <= m
            lbox = log(2*m+1) + lse(lbeta[ok] + suf[np.clip(need[ok], 0, m)])
            lM = 2*(log(MU2) + float(lCv(L, m)) + (L-m)*L4)
            gam_m = (lM - lbox)/lD
            # Delta-free first-half bound per entry
            lBpe = np.empty(m+1)
            for k in range(m+1):
                n = L-m+k
                bb = np.arange(k+1)
                lsum = lse(lCv(n, bb) + (n-bb)*L2)
                lBpe[k] = k*L2 + float(lCv(L, m-k)) + lsum - (L-m)*L2 - log(MU2) - float(lCv(L, m))
            l2 = lCv(m, d1) + d1*L4                 # second half per entry, by d2
            pre = np.logaddexp.accumulate(l2)       # prefix sums over d2
            ok2 = (t - d1) >= 0
            lq = log(2*L+1) + lse(lBpe[ok2] + pre[np.clip(t - d1[ok2], 0, m)])
            q_m = lq/lD
            lenc = L*log(25) - log(MU2) - float(lCv(L, m)) - (L-m)*L4
            eps_m = lD/(gam_m*lD + lenc) if gam_m > 0 else float('nan')
            print(f"      m={m:6d}: gamma_m={gam_m:+.5f}  q_m={q_m:.5f}  eps_m(at gamma_m)={eps_m:.5f}"
                  f"  1/eps from encodings alone={lenc/lD:.4f}")


if __name__ == "__main__":
    part1()
    part2()
    part3()
