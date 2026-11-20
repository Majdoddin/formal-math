"""R206b: independent checks of r84.md (written from r84.md and main.tex, not from calc/r84_check.py).

(1) Lemma B.1 (CMWW19 Lemma 26 with a common bit length) exhaustively, and the kind-2 padding claim.
(2) Theorem A's algorithm (r84 2.4) with exact counts, two regimes:
    (a) toy primes: Lemma A.2 (i)-(iii) per probe and Lemma A.4 (answers) against brute force;
    (b) theorem parameters (r84 2.2 formulas for P, zeta, ell, with the pool condition checked numerically):
        Lemma A.3 halving asserted in every stage, on random and structured (multiples-of-q) instances.
(3) Theorem B's chain (Steps A-D with Corollary A' per-c form) against brute-force MinConv,
    with a brute-force first-role oracle and with the algorithm of (2a) as oracle.
(4) The exponents of r84's tables, rounded up at the 5th decimal.
(5) CMWW19 Theorem 17 (MCSP by one MaxConv) and Theorem 18 (SuperAdditivity via MCSP) against brute force.
Run: nice -n 19, ulimit -v 3000000; output calc/r206b_check_out.txt.
"""
import math, random, sys
from fractions import Fraction

random.seed(20261118)

# ---------- (1) Lemma B.1 ----------
def pre(v, s, Lam):
    return v >> (Lam - s)

def beta(v, s, Lam):
    return (v >> (Lam - s - 1)) & 1

def lemB1(x, y, z, Lam):
    if any(pre(x, s, Lam) + pre(y, s, Lam) == pre(z, s, Lam) + 1 for s in range(Lam + 1)):
        return True
    return any(beta(x, s, Lam) == 1 and beta(y, s, Lam) == 1 and beta(z, s, Lam) == 0 and
               pre(z, s, Lam) == pre(x, s, Lam) + pre(y, s, Lam) for s in range(Lam))

def kind2_vals(x, y, z, s, Lam):
    D = 2 ** (Lam + 1) + 1
    al = pre(x, s, Lam) if beta(x, s, Lam) == 1 else -D
    be = pre(y, s, Lam) if beta(y, s, Lam) == 1 else -D
    ga = pre(z, s, Lam) if beta(z, s, Lam) == 0 else D
    return al, be, ga

def check1(maxLam):
    tot = bad = bad2 = 0
    for Lam in range(1, maxLam + 1):
        R = range(1 << Lam)
        for x in R:
            for y in R:
                for z in R:
                    tot += 1
                    if lemB1(x, y, z, Lam) != (x + y > z):
                        bad += 1
                    for s in range(Lam):
                        al, be, ga = kind2_vals(x, y, z, s, Lam)
                        cond2 = (beta(x, s, Lam) == 1 and beta(y, s, Lam) == 1 and beta(z, s, Lam) == 0 and
                                 pre(z, s, Lam) == pre(x, s, Lam) + pre(y, s, Lam))
                        if (al + be == ga) != cond2:
                            bad2 += 1
    return tot, bad, bad2

# ---------- (2) Theorem A ----------
def primes_in(lo, hi):
    return [p for p in range(max(2, lo), hi) if all(p % q for q in range(2, int(p ** 0.5) + 1))]

def groups_and_R(A, sigma):
    S = sorted(A)
    G = [S[i:i + sigma] for i in range(0, len(S), sigma)]
    g = len(G)
    R = [(i, j, k) for i in range(g) for j in range(g) for k in range(g)
         if G[i][0] + G[j][0] <= G[k][-1] and G[i][-1] + G[j][-1] >= G[k][0]]
    return G, R

def thmA(A, U, sigma, Pi, Plow, r, L, stats, check_halving=False):
    """r84 2.4. Pi: candidate primes, all >= Plow; ell from Plow and 2U. Returns the marked set."""
    G, R = groups_and_R(A, sigma)
    grp = {a: i for i, Gi in enumerate(G) for a in Gi}
    probes = sorted({(a, j, k) for (i, j, k) in R for a in G[i]})
    def cnt(m, Q):
        a, j, k = Q
        return sum(1 for b in G[j] for c in G[k] if (a + b - c) % m == 0)
    def Z(Q):
        a, j, k = Q
        return sum(1 for b in G[j] for c in G[k] if a + b == c)
    ell = 0
    while Plow ** (ell + 1) <= 2 * U:
        ell += 1
    marked = set()
    cur = list(probes)
    for t in range(L):
        if not cur:
            break
        m, pool = 1, list(Pi)
        for _ in range(r - 1):
            best = min(pool, key=lambda p: (sum(cnt(m * p, Q) for Q in cur), p))
            m *= best
            pool.remove(best)
        cm = {Q: cnt(m, Q) for Q in cur}
        mu = {Q: min(cnt(m * p, Q) for p in pool) for Q in cur}
        nxt = []
        for Q in cur:
            z = Z(Q)
            f = cm[Q] - z
            if mu[Q] == 0:
                stats['cf'] += 1
                if z != 0:
                    stats['A2i_bad'] += 1
            elif mu[Q] * len(pool) > ell * cm[Q]:
                stats['ct'] += 1
                if z < 1:
                    stats['A2ii_bad'] += 1
                marked.add(Q[0])
            else:
                stats['unc'] += 1
                if ell * f < len(pool) - ell:
                    stats['A2iii_bad'] += 1
        nxt = [Q for Q in cur if mu[Q] != 0 and not (mu[Q] * len(pool) > ell * cm[Q]) and Q[0] not in marked]
        if check_halving:
            stats['stages_checked'] += 1
            if 2 * len(nxt) > len(cur):
                stats['A3_bad'] += 1
            stats['max_ratio'] = max(stats['max_ratio'], len(nxt) / len(cur))
        stats['stages'] += 1
        cur = nxt
    Aset = set(A)
    for (a, j, k) in cur:
        if a not in marked and any(a + b in set(G[k]) for b in G[j]):
            marked.add(a)
            stats['merge_yes'] += 1
    return marked

def brute_first_role(A):
    S = set(A)
    return {a for a in A if any(a + b in S for b in A)}

def newstats():
    return dict(cf=0, ct=0, unc=0, merge_yes=0, stages=0, stages_checked=0, A2i_bad=0, A2ii_bad=0,
                A2iii_bad=0, A3_bad=0, max_ratio=0.0)

def check2a(trials):
    st = newstats(); wrong = 0
    for _ in range(trials):
        n = random.randint(1, 30)
        U = random.choice([20, 40, 80, 160])
        A = random.sample(range(1, U + 1), min(n, U))
        sigma = random.randint(1, 5)
        Plow = random.choice([3, 5, 7, 11])
        Pi = primes_in(Plow, 4 * Plow)
        r = random.randint(1, min(3, len(Pi)))
        L = random.randint(0, 4)
        if thmA(A, U, sigma, Pi, Plow, r, L, st) != brute_first_role(A):
            wrong += 1
    return wrong, st

def theorem_params(U, sigma, r):
    zeta = math.log(2 * U)
    P = math.ceil(4 * zeta * (4 * sigma * sigma) ** (1.0 / r))
    Pi = primes_in(P, 2 * P)
    ok = (P >= 8 * zeta) and (len(Pi) - r >= P / (4 * math.log(P)))
    return zeta, P, Pi, ok

def check2b(trials):
    st = newstats(); wrong = 0; used = 0; skipped = 0
    for tr in range(trials):
        r = random.choice([1, 2])
        sigma = random.choice([2, 3]) if r == 2 else 2
        U = random.choice([10 ** 5, 10 ** 6, 10 ** 7])
        zeta, P, Pi, ok = theorem_params(U, sigma, r)
        if not ok:
            skipped += 1
            continue
        used += 1
        n = random.randint(6, 24)
        if tr % 2 == 0:
            A = random.sample(range(1, U + 1), n)
        else:  # structured: multiples of q (q a product of pool primes), plus a few others
            q = 1
            for p in random.sample(Pi, random.randint(1, 2)):
                if q * p * 3 <= U:
                    q *= p
            A = sorted(set(q * random.randint(1, U // q) for _ in range(n)) |
                       set(random.sample(range(1, U + 1), random.randint(0, 3))))
            if random.random() < 0.5:  # add true solutions
                A = sorted(set(A) | {A[0] + A[1]} if A[0] + A[1] <= U else set(A))
        L = 3
        if thmA(A, U, sigma, Pi, P, r, L, st, check_halving=True) != brute_first_role(A):
            wrong += 1
    return used, skipped, wrong, st

def check2c(trials):
    """r = 3, sigma = 4, U = 10^7: here sigma^2 = 16 exceeds (|Pi'| - ell)/ell, so an uncertified probe is
    arithmetically possible; structured instances with all a+b-c divisible by one or two pool primes."""
    st = newstats(); wrong = 0
    r, sigma, U = 3, 4, 10 ** 7
    zeta, P, Pi, ok = theorem_params(U, sigma, r)
    ell = 0
    while P ** (ell + 1) <= 2 * U:
        ell += 1
    thr = (len(Pi) - (r - 1) - ell) / ell
    for tr in range(trials):
        n = random.randint(12, 24)
        q = 1
        for p in random.sample(Pi, 1 + tr % 2):
            q *= p
        A = sorted(set(q * random.randint(1, U // q) for _ in range(n)))
        if len(A) >= 2 and A[0] + A[1] <= U:
            A = sorted(set(A) | {A[0] + A[1]})
        if thmA(A, U, sigma, Pi, P, r, 3, st, check_halving=True) != brute_first_role(A):
            wrong += 1
    return (P, len(Pi), ell, thr, ok), wrong, st

# ---------- (3) Theorem B chain ----------
def core_oracle_brute(S):
    return brute_first_role(S)

def core_oracle_thmA(S, st):
    U = max(S)
    return thmA(sorted(S), U, 3, primes_in(5, 20), 5, 2, 2, st)

def per_c_corA(X, Y, Zs, core):
    """Corollary A' per-c form: for z in Zs, exists x in X, y in Y with x + y = z.
    Rewrite z + (-y) = x, i.e. three sets (Zs, -Y, X) in the first-role construction."""
    A1, B1, C1 = list(Zs), [-y for y in Y], list(X)
    Up = max(1, max(abs(v) for v in A1 + B1 + C1))
    S = {a + 10 * Up for a in A1} | {b + 30 * Up for b in B1} | {c + 40 * Up for c in C1}
    yes = core(sorted(S))
    return {z for z in Zs if z + 10 * Up in yes}

def allout_conv3sum(al, be, ga, n, core):
    M = 4 * n
    X = [al[i] * M + i for i in range(n)]
    Y = [be[j] * M + j for j in range(n)]
    Zs = [ga[k] * M + k for k in range(2 * n - 1)]
    assert len(set(X)) == n and len(set(Y)) == n and len(set(Zs)) == 2 * n - 1
    yes = per_c_corA(X, Y, Zs, core)
    return [Zs[k] in yes for k in range(2 * n - 1)]

def minconv_chain(a, b, core):
    n = len(a)
    U = max(1, max(abs(v) for v in a + b))
    K = 2 * n - 1
    lo, hi = [-2 * U] * K, [2 * U] * K
    rounds = math.ceil(math.log2(4 * U + 1))
    Lam = (4 * U + 1).bit_length()
    for _ in range(rounds):
        t = [(lo[k] + hi[k]) // 2 for k in range(K)]
        x = [U - v + 1 for v in a]; y = [U - v + 1 for v in b]; z = [2 * U - t[k] + 1 for k in range(K)]
        assert max(x + y + z) < 2 ** Lam and min(x + y + z) >= 0
        ans = [False] * K
        for s in range(Lam + 1):
            res = allout_conv3sum([pre(v, s, Lam) for v in x], [pre(v, s, Lam) for v in y],
                                  [pre(v, s, Lam) + 1 for v in z], n, core)
            ans = [p or q for p, q in zip(ans, res)]
        for s in range(Lam):
            D = 2 ** (Lam + 1) + 1
            al = [pre(v, s, Lam) if beta(v, s, Lam) == 1 else -D for v in x]
            be = [pre(v, s, Lam) if beta(v, s, Lam) == 1 else -D for v in y]
            ga = [pre(v, s, Lam) if beta(v, s, Lam) == 0 else D for v in z]
            res = allout_conv3sum(al, be, ga, n, core)
            ans = [p or q for p, q in zip(ans, res)]
        for k in range(K):
            if ans[k]:
                hi[k] = t[k]
            else:
                lo[k] = t[k] + 1
    assert lo == hi
    return lo

def minconv_brute(a, b):
    n = len(a)
    return [min(a[i] + b[k - i] for i in range(n) if 0 <= k - i < n) for k in range(2 * n - 1)]

def check3(tb, ta):
    wb = wa = 0; st = newstats()
    for _ in range(tb):
        n = random.randint(1, 6); W = random.randint(0, 9)
        a = [random.randint(-W, W) for _ in range(n)]; b = [random.randint(-W, W) for _ in range(n)]
        if minconv_chain(a, b, core_oracle_brute) != minconv_brute(a, b):
            wb += 1
    for _ in range(ta):
        n = random.randint(1, 4); W = random.randint(0, 3)
        a = [random.randint(-W, W) for _ in range(n)]; b = [random.randint(-W, W) for _ in range(n)]
        if minconv_chain(a, b, lambda S: core_oracle_thmA(S, st)) != minconv_brute(a, b):
            wa += 1
    return wb, wa, st

# ---------- (4) numbers ----------
def roundup5(q):
    return math.ceil(q * 10 ** 5) / 10 ** 5

def check4():
    rows = [("v1 Hyp(1/14,0.077)", Fraction(1, 14) * Fraction(77, 1000)),
            ("R14 Hyp(1/14,0.079)", Fraction(1, 14) * Fraction(79, 1000)),
            ("R14 Thm1 Hyp(0.08199,0.07099)", Fraction(8199, 100000) * Fraction(7099, 100000)),
            ("R111b Hyp(2/25,0.0765)", Fraction(2, 25) * Fraction(765, 10000))]
    out = []
    for name, x in rows:
        out.append("%s: eps*gamma = %.9f, 2-x = %.9f -> %.5f, 2-x/2 = %.9f -> %.5f" % (
            name, float(x), float(2 - x), roundup5(float(2 - x)), float(2 - x / 2), roundup5(float(2 - x / 2))))
    return out

# ---------- (5) CMWW19 Thm 17, 18 ----------
def maxconv(u, v):
    return [max(u[i] + v[k - i] for i in range(len(u)) if 0 <= k - i < len(v)) for k in range(len(u) + len(v) - 1)]

def mcsp_brute(a):
    n = len(a)
    return [max(sum(a[j:j + k]) for j in range(0, n - k + 1)) for k in range(1, n + 1)]

def mcsp_thm17(a):
    n = len(a)
    ps = [sum(a[:i + 1]) for i in range(n)]
    D = 2 * max([abs(sum(a[:i])) for i in range(n + 1)]) + 2 * max(1, max(abs(v) for v in a)) * (n + 1) + 1
    b = [ps[k] if k < n else -D for k in range(2 * n)]
    c = [-sum(a[:n - k]) if k <= n else -D for k in range(2 * n)]
    bc = maxconv(b, c)
    return [bc[n + k - 1] for k in range(1, n + 1)]

def superadd_brute(a):
    n = len(a)
    return all(a[k] >= a[i] + a[k - i] for k in range(n) for i in range(k + 1))

def superadd_thm18(a):
    n = len(a)
    if n == 1:
        return a[0] <= 0
    b = [a[i + 1] - a[i] for i in range(n - 1)]
    mc = mcsp_brute([-v for v in b])  # for each length k = 1..n-1: max of -(window sums) = -min window sum
    return a[0] <= 0 and all(a[k] <= -mc[k - 1] for k in range(1, n))

def check5(trials):
    w17 = w18 = 0
    for _ in range(trials):
        n = random.randint(1, 9); W = random.randint(0, 6)
        a = [random.randint(-W, W) for _ in range(n)]
        if mcsp_thm17(a) != mcsp_brute(a):
            w17 += 1
        # superadditive-leaning sequences so both outcomes occur
        if random.random() < 0.5:
            base = [random.randint(-1, 0)] + [random.randint(0, 3) for _ in range(n - 1)]
            a = [base[0]] + [sum(base[1:k + 1]) * k for k in range(1, n)]
        if superadd_thm18(a) != superadd_brute(a):
            w18 += 1
    return w17, w18

if __name__ == "__main__":
    tot, bad, bad2 = check1(6)
    print("(1) Lemma B.1 exhaustive, Lambda = 1..6: %d triples, %d wrong; kind-2 padding (all s): %d wrong" % (tot, bad, bad2))
    sys.stdout.flush()
    w, st = check2a(300)
    print("(2a) Theorem A toy primes: 300 instances, %d wrong answers; Lemma A.2 violations (i) %d (ii) %d (iii) %d; "
          "counts cf=%d ct=%d unc=%d merge_yes=%d stages=%d" % (w, st['A2i_bad'], st['A2ii_bad'], st['A2iii_bad'],
                                                              st['cf'], st['ct'], st['unc'], st['merge_yes'], st['stages']))
    sys.stdout.flush()
    used, skipped, w, st = check2b(40)
    print("(2b) Theorem A theorem parameters: %d instances (%d skipped: pool/8zeta condition false), %d wrong answers; "
          "halving violations %d in %d stages, max |P_t|/|P_{t-1}| = %.3f; Lemma A.2 violations %d/%d/%d; cf=%d ct=%d unc=%d" % (
              used, skipped, w, st['A3_bad'], st['stages_checked'], st['max_ratio'], st['A2i_bad'], st['A2ii_bad'],
              st['A2iii_bad'], st['cf'], st['ct'], st['unc']))
    for U in (10 ** 5, 10 ** 6, 10 ** 7):
        for (r, sigma) in ((1, 2), (2, 2), (2, 3)):
            zeta, P, Pi, ok = theorem_params(U, sigma, r)
            ell = 0
            while P ** (ell + 1) <= 2 * U:
                ell += 1
            print("     U=%d r=%d sigma=%d: zeta=%.3f P=%d |Pi|=%d ell=%d pool condition %s" % (U, r, sigma, zeta, P, len(Pi), ell, ok))
    sys.stdout.flush()
    info, w, st = check2c(30)
    print("(2c) r=3, sigma=4, U=10^7: P=%d |Pi|=%d ell=%d, uncertified needs f_m >= %.2f <= sigma^2=16, pool condition %s; "
          "30 structured instances, %d wrong; halving violations %d in %d stages, max ratio %.3f; cf=%d ct=%d unc=%d" % (
              info[0], info[1], info[2], info[3], info[4], w, st['A3_bad'], st['stages_checked'], st['max_ratio'],
              st['cf'], st['ct'], st['unc']))
    sys.stdout.flush()
    wb, wa, st = check3(60, 12)
    print("(3) Theorem B chain vs brute-force MinConv: 60 instances with brute-force core oracle, %d wrong; "
          "12 instances with the Theorem A algorithm (toy primes) as core oracle, %d wrong (A.2 violations %d/%d/%d)" % (
              wb, wa, st['A2i_bad'], st['A2ii_bad'], st['A2iii_bad']))
    print("(4) exponents, rounded up at the 5th decimal:")
    for line in check4():
        print("    " + line)
    w17, w18 = check5(400)
    print("(5) CMWW19 Thm 17 (MCSP by one MaxConv of length 2n): 400 instances, %d wrong; Thm 18 (SuperAdditivity via MCSP of -b): %d wrong" % (w17, w18))
    print("DONE")
