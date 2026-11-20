"""R78 step 3 (r78.md Section 4): the profile Lambda_q(t) of every block-level support structure of a (q+2)-term
border decomposition of F_q that satisfies the slice-rank coverage bounds, and the best gamma_D over them.

A unit j (one term) has z-support meeting blocks B_j subset {0, 1, 2} with k_j middle letters (block 1).
Coverage bounds (r27r28.md Sections 4-5: cov(z) >= rank of z's slice): z_0 in every unit (slice rank q+2),
each z_i (1 <= i <= q) in >= 2 units, z_{q+1} in >= 1 unit.  S_all is monotone in the supports, so only minimal
structures matter: sum_j k_j = 2q, exactly one unit carries block 2.  Structure = (multiset of k_j, k of the
block-2 unit).

Per CW coordinate, tau uniform over the (q+2)^M strings, U = all z-strings of block type (pi, q pi, pi):
    Lambda_q(t) = max_P [ -D(P_J || uniform) + t H_P(K | J) ],
P a joint law of (unit, block) with P(j, b) > 0 only for b in B_j, block marginal (pi, q pi, pi), and
H(K|J) = sum_{j,b} P(j,b) ln(P(j)/P(j,b)) + sum_j P(j,1) ln k_j   (letters inside block 1 uniform).
Identical units are aggregated (optimum symmetric by concavity).
(0) brute force: S_all(tau) by enumeration of z-strings vs the coupling count, random structures, q = 2, 3;
(1) merged structure reproduces r74a's G_q; (2) all minimal structures, q = 6, 7: c_g-at-typical H0, Lambda(0.1),
gamma_D of each structure used at both parts; (3) envelope: per t the minimum over structures, per part.
Run: ~/.venv/bin/python r78_family.py > r78_family_out.txt
"""
import itertools, random
from math import comb, factorial, log
import numpy as np
from scipy.optimize import minimize, minimize_scalar

LAM = {6: 7/19, 7: 12/19}
LNA1 = 0.725488559770971
ALPHA = 0.294597647050482
LNB1 = ALPHA*LNA1
TMAX = 0.3249


def xlogx(s):
    return np.where(s > 0, s*np.log(np.maximum(s, 1e-300)), 0.0)


def structures(q):
    """minimal structures under (a) z_0 in every unit, (b) z_{q+1} in >= 1 unit, (c) surplus Hall: every set S of
    middle letters meets >= |S| + 1 units (flattening rank of F_q restricted to S, r78.md 4.1).  Minimal ones are
    trees: q+1 units with k_j >= 1, sum k_j = 2q, every letter in exactly 2 units, one unit with k = 0; the block-2
    letter on one unit (any k).  So ks = partition of 2q into q+1 positive parts (each <= q) plus a 0."""
    out = []
    def parts(n, maxp, nparts):
        if nparts == 0:
            if n == 0:
                yield []
            return
        for p in range(min(n - (nparts - 1), maxp), 0, -1):
            for rest in parts(n - p, p, nparts - 1):
                yield [p] + rest
    for pa in parts(2*q, q, q + 1):
        ks = pa + [0]
        for k2 in sorted(set(ks)):
            out.append((tuple(ks), k2))
    return out


def classes(q, ks, k2):
    """list of (count, k, has2); one unit with k = k2 carries block 2."""
    from collections import Counter
    c = Counter(ks)
    cl = []
    for k, n in sorted(c.items()):
        if k == k2:
            cl.append((1, k, True))
            if n > 1:
                cl.append((n - 1, k, False))
        else:
            cl.append((n, k, False))
    return cl


def feasible_start(idx, cl, mass, m, uniform):
    """interior-ish feasible point: maximise the smallest entry s.t. block masses (and, if uniform, class masses)."""
    from scipy.optimize import linprog
    nv = len(idx)
    A, bvec = [], []
    for b in (0, 1, 2):
        A.append([1.0 if bb == b else 0.0 for (ci, bb) in idx] + [0.0]); bvec.append(mass[b])
    if uniform:
        for c in range(len(cl)):
            A.append([1.0 if ci == c else 0.0 for (ci, bb) in idx] + [0.0]); bvec.append(cl[c][0]/m)
    Aub = [[-1.0 if i == j else 0.0 for j in range(nv)] + [1.0] for i in range(nv)]
    r = linprog(c=[0.0]*nv + [-1.0], A_ub=Aub, b_ub=[0.0]*nv, A_eq=A, b_eq=bvec,
                bounds=[(0, 1)]*nv + [(0, 1)], method="highs")
    if r.status != 0:
        return None
    return np.maximum(r.x[:nv], 1e-12)


def Lam(q, t, cl, return_H0=False):
    pi = 1/(q + 2); m = q + 2
    mass = np.array([pi, q*pi, pi])
    # variables: for each class, entries for allowed blocks (0 always; 1 if k > 0; 2 if has2)
    idx = []
    for ci, (n, k, h2) in enumerate(cl):
        for b in (0, 1, 2):
            if b == 0 or (b == 1 and k > 0) or (b == 2 and h2):
                idx.append((ci, b))
    nv = len(idx)
    def unpackX(X):
        xc = np.zeros(len(cl))
        for (ci, b), val in zip(idx, X):
            xc[ci] += val
        return xc
    def obj(X, tt):
        xc = unpackX(X)
        nvec = np.array([c[0] for c in cl], float)
        D = float(np.sum(xlogx(xc)) - np.sum(xc*np.log(nvec/m)))
        H = 0.0
        for (ci, b), val in zip(idx, X):
            if val > 0:
                H += val*np.log(xc[ci]/val)
            if b == 1:
                H += val*np.log(cl[ci][1])
        return -D + tt*H
    cons = []
    for b in (0, 1, 2):
        rows = [i for i, (ci, bb) in enumerate(idx) if bb == b]
        cons.append(dict(type="eq", fun=lambda X, rows=rows, b=b: np.sum(X[rows]) - mass[b]))
    # start: typical-ish feasible point
    X0 = feasible_start(idx, cl, mass, m, uniform=False)
    best = None
    for start in (X0, ):
        r = minimize(lambda X: -obj(X, t), start, method="SLSQP", constraints=cons,
                     bounds=[(1e-14, 1.0)]*nv, options=dict(ftol=1e-15, maxiter=2000))
        if best is None or r.fun < best.fun:
            best = r
    val = -best.fun
    if return_H0:
        # H0 = max H(K|J) at the uniform unit law (c_g per coordinate, Danskin): maximise H subject to x uniform
        nvec = np.array([c[0] for c in cl], float)
        cons2 = cons[:2] + [dict(type="eq", fun=lambda X, ci=ci: unpackX(X)[ci] - nvec[ci]/m) for ci in range(len(cl))]
        X1 = feasible_start(idx, cl, mass, m, uniform=True)
        if X1 is None:
            return val, float("-inf")
        r2 = minimize(lambda X: -(obj(X, 1.0) + 0.0) - (float(np.sum(xlogx(unpackX(X))) - np.sum(unpackX(X)*np.log(nvec/m)))),
                      X1, method="SLSQP", constraints=cons2, bounds=[(1e-14, 1.0)]*nv,
                      options=dict(ftol=1e-15, maxiter=2000))
        return val, -r2.fun
    return val


# ------------------------------------------------------------------------------------------- brute force check
def brute(q, M, ks, k2, trials, rng):
    """S_all(tau) by enumeration vs the coupling count sum over integer couplings of prod multinomials * k^n1."""
    m = q + 2; n0 = n2 = M//m; n1 = M - n0 - n2
    # concrete letter supports: unit j gets k_j distinct middle letters (round robin), all contain 0
    letters = []; nxt = 0
    for j, k in enumerate(ks):
        L = {0}
        for _ in range(k):
            L.add(1 + nxt % q); nxt += 1
        letters.append(L)
    j2 = ks.index(k2); letters[j2].add(q + 1)
    bad = 0
    for _ in range(trials):
        tau = [rng.randrange(m) for _ in range(M)]
        cnt = 0
        for o in itertools.product(*[sorted(letters[j]) for j in tau]):
            if sum(1 for a in o if a == 0) == n0 and sum(1 for a in o if a == q + 1) == n2:
                cnt += 1
        # coupling count: per unit j with count c_j: choose numbers (z0_j, z1_j, z2_j) summing to c_j
        cj = [tau.count(j) for j in range(m)]
        def rec(j, r0, r2):
            if j == m:
                return 1 if r0 == 0 and r2 == 0 else 0
            tot = 0
            h2 = (q + 1) in letters[j]; k = len(letters[j]) - 1 - (1 if h2 else 0)
            for a0 in range(0, min(cj[j], r0) + 1):
                for a2 in range(0, (min(cj[j] - a0, r2) if h2 else 0) + 1):
                    a1 = cj[j] - a0 - a2
                    if a1 > 0 and k == 0:
                        continue
                    w = factorial(cj[j])//(factorial(a0)*factorial(a1)*factorial(a2))*k**a1
                    tot += w*rec(j + 1, r0 - a0, r2 - a2)
            return tot
        bad += (cnt != rec(0, n0, n2))
    return bad


def gamma_of(Lfun):
    ts = np.linspace(0.005, TMAX, 24)
    vals = [t/2 - Lfun(t)/LNB1 for t in ts]
    i = int(np.argmax(vals))
    lo, hi = ts[max(i - 1, 0)], ts[min(i + 1, len(ts) - 1)]
    r = minimize_scalar(lambda t: -(t/2 - Lfun(t)/LNB1), bounds=(lo, hi), method="bounded",
                        options=dict(xatol=1e-6))
    return r.x, -r.fun


def main():
    rng = random.Random(78)
    print("(0) brute force: S_all by enumeration vs coupling count")
    for q, M in ((2, 4), (2, 8), (3, 5), (3, 10)):
        for ks, k2 in structures(q)[:6]:
            b = brute(q, M, list(ks), k2, 30, rng)
            print(f"  q={q} M={M} ks={ks} k2={k2}: 30 random tau, {b} mismatches")
            assert b == 0

    print("\n(1) merged structure (ks = (q, 1 x q, 0), block 2 on the k = q unit) vs r74a's G_q(0.0196)")
    for q, ref in ((6, 0.0012944331520783), (7, 0.0012082016806783)):
        cl = classes(q, tuple([q] + [1]*q + [0]), q)
        print(f"  q={q}: {Lam(q, 0.0196, cl):.13f} (r74a {ref:.13f})")

    print("\n(2) all minimal structures (sum k = 2q, one block-2 unit); H0 = max H(K|J) at uniform units "
          "(c_g per coordinate, estimated as Lambda_q(1e-5)/1e-5 >= H0; ~0 iff c_g = 0); Lambda_q(0.1); gamma_D if used at both parts needs q=6,7 jointly, "
          "so per q we list Lambda_q(t) at t = 0.05, 0.1, 0.2")
    table = {}
    for q in (6, 7):
        sts = structures(q)
        print(f"  q = {q}: {len(sts)} structures")
        rows = []
        for ks, k2 in sts:
            cl = classes(q, ks, k2)
            l01 = Lam(q, 0.1, cl); H0 = Lam(q, 1e-5, cl)/1e-5
            rows.append((l01, H0, ks, k2, cl))
        rows.sort(key=lambda r: r[0])
        table[q] = rows
        for l01, H0, ks, k2, cl in rows:
            print(f"    ks={ks} k2={k2}: H0 = {H0:.5f}  Lambda_q(0.05) = {Lam(q, 0.05, cl):.6f}  "
                  f"Lambda_q(0.0196) = {Lam(q, 0.0196, cl):.6f}  Lambda_q(0.1) = {l01:.6f}  Lambda_q(0.2) = {Lam(q, 0.2, cl):.6f}")

    print("\n(3) gamma_D at P0 (ln b_1 = %.6f, t <= %.4f)" % (LNB1, TMAX))
    merged = {q: classes(q, tuple([q] + [1]*q + [0]), q) for q in (6, 7)}
    t, g = gamma_of(lambda t: sum(LAM[q]*Lam(q, t, merged[q]) for q in (6, 7)))
    print(f"  merged at both parts: t_opt = {t:.4f}, gamma_D = {g:.6f}")
    best = []
    for q in (6, 7):
        for l01, H0, ks, k2, cl in table[q][:3]:
            best.append((q, ks, k2, cl))
    # each structure that is among the 8 lowest Lambda(0.1) per q: gamma with the same-shaped structure per part
    for q6 in [b for b in best if b[0] == 6]:
        for q7 in [b for b in best if b[0] == 7]:
            t, g = gamma_of(lambda t: LAM[6]*Lam(6, t, q6[3]) + LAM[7]*Lam(7, t, q7[3]))
            e1 = 1/(1/ALPHA + g) if g > 0 else 0
            print(f"  q=6 {q6[1]} k2={q6[2]} | q=7 {q7[1]} k2={q7[2]}: t_opt = {t:.4f}, gamma_D = {g:.6f}, "
                  f"eps*gamma = {e1*g:.6f}")
    # envelope: per t the minimum over all structures of each part (optimistic bound on any choice)
    def Lenv(t):
        return sum(LAM[q]*min(Lam(q, t, r[4]) for r in table[q]) for q in (6, 7))
    t, g = gamma_of(Lenv)
    print(f"  envelope (min over all minimal structures per part and per t): t_opt = {t:.4f}, gamma_D = {g:.6f}, "
          f"eps*gamma = {1/(1/ALPHA + g)*g if g > 0 else 0:.6f}")


if __name__ == "__main__":
    main()
