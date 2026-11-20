"""R109 check 1 (idea 19): the convex dual of r78 Lemma 4.2's profile, a Sinkhorn-type solver, duality gaps,
and rigorous rational certificates.

Primal (r78 Lemma 4.2, per CW coordinate):
    Lambda(t) = max_P [ -D(P_J || U_r) + t H_P(K|J) ],
    H(K|J) = sum P(j,b) ln(P(j)/P(j,b)) + sum_j P(j,1) ln k_j,  block marginal pi = (1, q, 1)/(q+2).
Dual (r107-lit.md 2.1), with y_b = exp(-phi_b/t):
    V(y) = -t sum_b pi_b ln y_b + ln( (1/r) sum_j S_j(y)^t ),   S_j = sum_{b ~ j} k_jb y_b.
Lambda(t) <= V(y) for every y > 0 (weak duality); equality at the optimum (strong duality).
Solver: IPF/Sinkhorn-type update ln y_b += ln pi_b - ln P_b(y) (P_b = block marginal of the Gibbs law of y),
then Newton polish on the 2-dim convex problem (gauge y_0 = 1).
Primal lower bound: Gibbs law of y with its columns rescaled to the exact block marginal (feasible), objective
evaluated -> gap = V(y) - primal.
Certificate: y rounded to rationals, t rational; V evaluated with outward-rounded rational interval arithmetic
(ln via atanh series, exp via Taylor series, both with explicit remainders) -> rigorous upper bound on Lemma 4.2's
expression.
Run: ~/.venv/bin/python r109_dual.py > r109_dual_out.txt
"""
import sys, re, time
from fractions import Fraction as Fr
import numpy as np

sys.path.insert(0, '.')
from r78_family import structures, classes  # read-only import (no side effects)

LAM = {6: Fr(7, 19), 7: Fr(12, 19)}
LNA1 = 0.725488559770971
ALPHA = 0.294597647050482
LNB1 = ALPHA*LNA1


# ------------------------------------------------------------------ structures as (count, k, allowed blocks)
def units_from_classes(cl):
    out = []
    for (n, k, h2) in cl:
        bl = [0] + ([1] if k > 0 else []) + ([2] if h2 else [])
        out.append((n, k, tuple(bl)))
    return out


def merged(q):
    return [(1, 0, (0,)), (q, 1, (0, 1)), (1, q, (0, 1, 2))]


def kjb(k, b):
    return k if b == 1 else 1


# ------------------------------------------------------------------ dual value, Gibbs law, primal
def dual_and_law(q, t, units, ly):
    """ly = ln y (3,).  returns V, list of per-class conditional laws, class weights w (per unit), P_b."""
    pi = np.array([1, q, 1], float)/(q + 2); r = q + 2
    lS = []
    for (n, k, bl) in units:
        a = np.array([np.log(kjb(k, b)) + ly[b] for b in bl])
        m = a.max(); lS.append(m + np.log(np.exp(a - m).sum()))
    lS = np.array(lS); ns = np.array([u[0] for u in units], float)
    z = t*lS + np.log(ns); zm = z.max(); lse = zm + np.log(np.exp(z - zm).sum())
    V = -t*float(pi @ ly) + lse - np.log(r)
    wcls = np.exp(z - lse)               # total mass of each class
    Pb = np.zeros(3); conds = []
    for ci, (n, k, bl) in enumerate(units):
        a = np.array([np.log(kjb(k, b)) + ly[b] for b in bl]); c = np.exp(a - lS[ci])
        conds.append(c)
        for b, cb in zip(bl, c):
            Pb[b] += wcls[ci]*cb
    return V, conds, wcls, Pb


def primal(q, t, units, P):
    """P: list per class of dict b -> mass (class total); per unit mass = class mass / n."""
    r = q + 2; D = 0.0; H = 0.0
    for (n, k, bl), Pc in zip(units, P):
        tot = sum(Pc.values())
        if tot <= 0:
            continue
        pu = tot/n                       # mass of one unit
        D += n*pu*np.log(pu*r)
        for b, m in Pc.items():
            if m > 0:
                H += m*np.log(tot/m) + (m*np.log(k) if b == 1 else 0.0)
    return -D + t*H


def feasible_from(q, units, conds, wcls):
    pi = np.array([1, q, 1], float)/(q + 2)
    P = []; Pb = np.zeros(3)
    for (n, k, bl), c, w in zip(units, conds, wcls):
        d = {b: w*cb for b, cb in zip(bl, c)}; P.append(d)
        for b, m in d.items():
            Pb[b] += m
    for d in P:
        for b in d:
            d[b] *= pi[b]/Pb[b]
    return P


def solve(q, t, units, ipf_iters=20000, tol=1e-15, newton=True):
    pi = np.array([1, q, 1], float)/(q + 2)
    ly = np.zeros(3); hist = []
    for it in range(ipf_iters):
        V, conds, w, Pb = dual_and_law(q, t, units, ly)
        err = np.abs(Pb - pi).max()
        if it in (0, 10, 100, 1000) :
            hist.append((it, V, err))
        if err < tol:
            break
        ly = ly + (np.log(pi) - np.log(Pb)); ly -= ly[0]
    n_ipf = it
    if newton:
        for _ in range(50):
            V, conds, w, Pb = dual_and_law(q, t, units, ly)
            g = t*(Pb - pi)
            # numerical Hessian on coordinates 1, 2 (gauge y_0 = 1)
            h = 1e-6; Hm = np.zeros((2, 2))
            for i in (1, 2):
                e = np.zeros(3); e[i] = h
                gp = t*(dual_and_law(q, t, units, ly + e)[3] - pi)
                gm = t*(dual_and_law(q, t, units, ly - e)[3] - pi)
                Hm[:, i - 1] = ((gp - gm)/(2*h))[1:]
            try:
                step = np.linalg.solve(Hm, g[1:])
            except np.linalg.LinAlgError:
                break
            ly[1:] -= step
            if np.abs(step).max() < 1e-15:
                break
    V, conds, w, Pb = dual_and_law(q, t, units, ly)
    P = feasible_from(q, units, conds, w)
    pr = primal(q, t, units, P)
    return V, pr, ly, n_ipf, hist


# ------------------------------------------------------------------ rigorous rational interval arithmetic
PREC = 2**-200


def rdn(x):
    return Fr((x.numerator*2**200)//x.denominator, 2**200)


def rup(x):
    return -rdn(-x)


def _atanh_series(z, N=None):
    """2 atanh(z) for rational 0 <= z < 1/2 with error bound; returns (lo, hi)."""
    s = Fr(0); p = z; k = 0; z2 = z*z
    while True:
        term = p/(2*k + 1)
        s = rdn(s + term)
        p = rdn(p*z2) if p > 0 else p
        k += 1
        if p < Fr(1, 2**220):
            break
    # remainder of sum_{j>=k} z^{2j+1}/(2j+1) <= z^{2k+1}/(1 - z^2)
    rem = Fr(z)**(2*k + 1)/(1 - z2) + Fr(k + 2, 2**200)   # + accumulated rounding
    return 2*s - Fr(k + 2, 2**199), 2*s + 2*rem + Fr(k + 2, 2**199)


LN2 = _atanh_series(Fr(1, 3))


def ln_bounds(x):
    x = Fr(x); assert x > 0
    k = 0
    while x > Fr(4, 3):
        x /= 2; k += 1
    while x < Fr(2, 3):
        x *= 2; k -= 1
    z = (x - 1)/(x + 1)
    if z >= 0:
        lo, hi = _atanh_series(z)
    else:
        lo, hi = _atanh_series(-z); lo, hi = -hi, -lo
    if k >= 0:
        return lo + k*LN2[0], hi + k*LN2[1]
    return lo + k*LN2[1], hi + k*LN2[0]


def exp_bounds(r):
    """exp of rational r with |r| small-ish: halve until |r| < 2^-8, Taylor, square back."""
    r = Fr(r); s = 0
    while abs(r) > Fr(1, 256):
        r /= 2; s += 1
    lo = hi = Fr(0); term = Fr(1); n = 0
    while True:
        lo = rdn(lo + term); hi = rup(hi + term)
        n += 1; term = term*r/n
        term = rdn(term) if term > 0 else rup(term)
        if abs(term) < Fr(1, 2**210):
            break
    tail = 2*abs(term) + Fr(1, 2**200)
    lo -= tail; hi += tail
    for _ in range(s):
        lo = rdn(lo*lo); hi = rup(hi*hi)
    return lo, hi


def certify(q, t, units, ly, den=10**12):
    """rational y_b = round(e^{ly_b}); returns rigorous upper bound on V(y) (hence on Lemma 4.2's Lambda(t))."""
    t = Fr(t)
    y = [Fr(round(np.exp(v)*den), den) for v in ly]
    pi = [Fr(1, q + 2), Fr(q, q + 2), Fr(1, q + 2)]
    first = -t*sum(pi[b]*ln_bounds(y[b])[0] for b in range(3))      # upper bound
    tot_hi = Fr(0)
    for (n, k, bl) in units:
        S = sum(kjb(k, b)*y[b] for b in bl)
        lhi = ln_bounds(S)[1]
        tot_hi += n*exp_bounds(t*lhi)[1]
    second = ln_bounds(tot_hi/(q + 2))[1]
    return first + second, y


def main():
    t0 = time.time()
    print("(1) merged structure (r74a's F_q = r78 Lemma 4.2), dual solver vs r78's printed values")
    printed = {(0.0196, 6): 0.0012944331521, (0.0196, 7): 0.0012082016806,
               (0.02, 6): 0.0013393, (0.02, 7): 0.0012502, (0.05, 6): 0.0061826, (0.05, 7): 0.0058108,
               (0.1, 6): 0.0192589, (0.1, 7): 0.0182224, (0.2, 6): 0.0590177, (0.2, 7): 0.0563572,
               (0.3, 6): 0.1130108, (0.3, 7): 0.1087247}
    sol = {}
    for (t, q), ref in printed.items():
        V, pr, ly, nit, hist = solve(q, t, merged(q))
        sol[(t, q)] = ly
        print(f"  t={t:<6} q={q}: dual V = {V:.15f}  primal(feasible) = {pr:.15f}  gap = {V - pr:.1e}  "
              f"r78 = {ref}  |V - r78| = {abs(V - ref):.1e}  IPF iters = {nit}")
    print("  IPF convergence (t = 0.0196, q = 6): (iter, V, max marginal error):")
    _, _, _, _, hist = solve(6, 0.0196, merged(6), newton=False)
    for h in hist:
        print(f"    {h[0]:6d}  {h[1]:.15f}  {h[2]:.2e}")
    print("  IPF without Newton, iterations to 1e-15:", solve(6, 0.0196, merged(6), newton=False)[3])

    print("\n(2) mixture P0 (lam_6 = 7/19): Lambda per coordinate and t/2 - Lambda/ln b_1 (r78 prints 0.0012400, 0.003998)")
    for t in (0.0196, 0.02, 0.05, 0.1, 0.2, 0.3):
        Vs = {q: solve(q, t, merged(q))[0] for q in (6, 7)}
        Lm = float(LAM[6])*Vs[6] + float(LAM[7])*Vs[7]
        print(f"  t={t:<6}: Lambda = {Lm:.7f}, per ln a = {Lm/LNA1:.7f}, t/2 - Lambda/ln b_1 = {t/2 - Lm/LNB1:.6f}")

    print("\n(3) all 67 minimal structures of r78 Section 4: dual vs r78_family_out.txt (6 printed digits)")
    txt = open('r78_family_out.txt').read()
    pat = re.compile(r"ks=\(([\d, ]+)\) k2=(\d+): H0 = [\d.]+\s+Lambda_q\(0.05\) = ([\d.]+)\s+Lambda_q\(0.0196\) = ([\d.]+)"
                     r"\s+Lambda_q\(0.1\) = ([\d.]+)\s+Lambda_q\(0.2\) = ([\d.]+)")
    worst = 0.0; worst_gap = 0.0; nrows = 0; lower = 0
    for m in pat.finditer(txt):
        ks = tuple(int(s) for s in m.group(1).split(',')); k2 = int(m.group(2)); q = len(ks) - 2
        units = units_from_classes(classes(q, ks, k2))
        for t, ref in zip((0.05, 0.0196, 0.1, 0.2), (float(m.group(i)) for i in (3, 4, 5, 6))):
            V, pr, ly, nit, _ = solve(q, t, units)
            worst = max(worst, abs(V - ref)); worst_gap = max(worst_gap, V - pr); nrows += 1
            if V < ref - 6e-7:
                lower += 1
                print(f"    dual BELOW printed (SLSQP overshoot?): q={q} ks={ks} k2={k2} t={t}: {V:.7f} vs {ref}")
    print(f"  {nrows} (structure, t) pairs: max |dual - printed| = {worst:.1e} (printed to 6 decimals), "
          f"max duality gap = {worst_gap:.1e}, dual below printed by > 6e-7: {lower}")

    print("\n(4) rigorous rational certificates (y rounded to 1e-12, t = 49/2500): upper bounds on Lemma 4.2's G_q(t)")
    ups = {}
    for q in (6, 7):
        ub, y = certify(q, Fr(49, 2500), merged(q), sol[(0.0196, q)])
        ups[q] = ub
        print(f"  q={q}: y = ({y[0]}, {y[1]}, {y[2]})")
        print(f"         certified G_{q}(0.0196) <= {float(ub):.16f}  (r78: {printed[(0.0196, q)]}; "
              f"excess {float(ub) - printed[(0.0196, q)]:.1e})")
    Lup = LAM[6]*ups[6] + LAM[7]*ups[7]
    print(f"  P0 mixture: Lambda(0.0196) <= {float(Lup):.16f}; gamma_D >= 0.0098 - Lambda/ln b_1 = "
          f"{0.0098 - float(Lup)/LNB1:.9f} (ln b_1 = {LNB1:.15f} taken as given)")
    # sanity: certificate arithmetic vs float
    print("  sanity: float V at the rounded y:",
          {q: f"{dual_and_law(q, 0.0196, merged(q), np.log([float(v) for v in certify(q, Fr(49, 2500), merged(q), sol[(0.0196, q)])[1]]))[0]:.16f}" for q in (6, 7)})
    print("  enclosure self-test: ln 2 in", [float(v) for v in LN2], " exp(1) in", [float(v) for v in exp_bounds(1)],
          " ln 10 in", [float(v) for v in ln_bounds(10)])
    print(f"\n(time {time.time() - t0:.1f} s)")


if __name__ == "__main__":
    main()
