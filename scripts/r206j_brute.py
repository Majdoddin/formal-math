"""R206j: brute-force check of R114a's Lemmas A, B, C, of R20's Lemma 1 (column = product set) and Lemma 3(a),
and of the computability claim of Step 4 (kappa(v) by enumerating (Q, Z, A2, R)).  Own code, abstract model:
Pi is a random integer function on all 5^(2L) leaves (stronger than the paper's tensor values: only the cube
structure of main.tex:491 is used).  Levels 0..2L-1, first half 0..L-1 (lower), as main.tex change (10).
Terms: 0 = P0, 1 + 2(i-1) + (j-1) = P_ij; letters: 0 = z0, same code for z_ij; 5 = star.
"""
import itertools, random, sys
from math import comb

STAR = 5


def ij(code):
    return (code - 1) // 2 + 1, (code - 1) % 2 + 1


def upsets(m):
    grid = [(a, b) for a in range(m + 1) for b in range(m + 1)]
    res = []
    for mask in range(1 << len(grid)):
        S = {grid[k] for k in range(len(grid)) if mask >> k & 1}
        ok = all(((a + 1, b) in S or a == m) and ((a, b + 1) in S or b == m) for (a, b) in S)
        if ok:
            res.append(frozenset(S))
    return res


class Model:
    def __init__(self, L, m, seed):
        self.L, self.m = L, m
        rng = random.Random(seed)
        self.Pi = [rng.randrange(-10 ** 6, 10 ** 6) for _ in range(5 ** (2 * L))]
        # random re-indexing maps over GF(2), columns as bit masks; Q good iff Gamma cols at Q and Delta cols off Q
        # are bases
        while True:
            self.Gam = [rng.randrange(1 << m) for _ in range(L)]
            self.Del = [rng.randrange(1 << (L - m)) for _ in range(L)]
            self.Qg = [Q for Q in itertools.combinations(range(L), m)
                       if self.rank([self.Gam[l] for l in Q]) == m
                       and self.rank([self.Del[l] for l in range(L) if l not in Q]) == L - m]
            if len(self.Qg) >= 2:
                break

    @staticmethod
    def rank(vecs):
        rows, r = list(vecs), 0
        basis = []
        for v in rows:
            for b in basis:
                v = min(v, v ^ b)
            if v:
                basis.append(v)
                r += 1
        return r

    def DeltaS(self, S):
        v = 0
        for l in S:
            v ^= self.Del[l]
        return v

    def leaf_index(self, tau):
        k = 0
        for s in reversed(tau):
            k = 5 * k + s
        return k

    # half strings: (Q, iota, S) -> tuple of L letters
    def half_string(self, Q, iota, S):
        out, k = [], 0
        for l in range(self.L):
            if l in Q:
                out.append(0)
            else:
                i = iota[k]
                k += 1
                j = 2 if l in S else 1
                out.append(1 + 2 * (i - 1) + (j - 1))
        return tuple(out)

    def column(self, v, ipp, Qpp):
        """U = U'_v x U'' of R20 Lemma 1 for column (v, i'') of the column block Qpp."""
        L, m = self.L, self.m
        Up = []
        for Q in self.Qg:
            outer = [l for l in range(L) if l not in Q]
            Sv = None
            for r in range(len(outer) + 1):
                for S in itertools.combinations(outer, r):
                    if self.DeltaS(S) == v:
                        assert Sv is None
                        Sv = S
            for iota in itertools.product((1, 2), repeat=L - m):
                Up.append(self.half_string(Q, iota, Sv))
        outer = [l for l in range(L) if l not in Qpp]
        Upp = [self.half_string(Qpp, ipp, S) for r in range(len(outer) + 1) for S in itertools.combinations(outer, r)]
        return Up, Upp

    def cube(self, w):
        choices = [range(5) if a == 0 else (a,) for a in w]
        return itertools.product(*choices)

    def orders(self, tau):
        L, m = self.L, self.m
        return (m - sum(1 for s in tau[:L] if s == 0), m - sum(1 for s in tau[L:] if s == 0))

    def entry(self, w):
        return sum(self.Pi[self.leaf_index(t)] for t in self.cube(w))


def is_node(M, pi, High):
    L, m = M.L, M.m
    f1 = sum(1 for s in pi[:L] if s in (0, STAR))
    f2 = sum(1 for s in pi[L:] if s in (0, STAR))
    if f1 > m or f2 > m or (m - f1, m - f2) not in High:
        return False
    stars = [l for l, s in enumerate(pi) if s == STAR]
    p0 = [l for l, s in enumerate(pi) if s == 0]
    return not stars or not p0 or max(stars) < min(p0)


class NodeStore:
    def __init__(self, M, High):
        self.M, self.High, self.memo, self.bad_child = M, High, {}, 0

    def value(self, pi):
        if pi in self.memo:
            return self.memo[pi]
        assert is_node(self.M, pi, self.High), ("not a node", pi)
        stars = [l for l, s in enumerate(pi) if s == STAR]
        if not stars:
            v = self.M.Pi[self.M.leaf_index(pi)]
        else:
            h = max(stars)
            v = 0
            for s in range(5):
                ch = pi[:h] + (s,) + pi[h + 1:]
                if not is_node(self.M, ch, self.High):
                    self.bad_child += 1
                v += self.value(ch)
        self.memo[pi] = v
        return v


def direct_cube_sum(M, pi):
    choices = [range(5) if s == STAR else (s,) for s in pi]
    return sum(M.Pi[M.leaf_index(t)] for t in itertools.product(*choices))


def lemmaA(M, w, High, store):
    """first-entry boxes of w: partition of the High leaves; entry = Low leaves + box values."""
    L, m = M.L, M.m
    boxes = {}
    low_sum = 0
    for tau in M.cube(w):
        d = M.orders(tau)
        if d not in High:
            low_sum += M.Pi[M.leaf_index(tau)]
            continue
        # scan from the top: state after placing levels >= l
        c1 = c2 = 0
        if (0, 0) in High:
            l_entry = 2 * L
        else:
            l_entry = None
            for l in range(2 * L - 1, -1, -1):
                if w[l] == 0 and tau[l] != 0:
                    if l < L:
                        c1 += 1
                    else:
                        c2 += 1
                if (c1, c2) in High:
                    l_entry = l
                    break
        box = tuple(tau[l] if l >= l_entry else (STAR if w[l] == 0 else w[l]) for l in range(2 * L))
        boxes.setdefault(box, []).append(tau)
    ok = True
    total = low_sum
    for box, leaves in boxes.items():
        if not is_node(M, box, High):
            ok = False
        # the box must contain exactly these High leaves of the cube (partition)
        choices = [range(5) if s == STAR else (s,) for s in box]
        full = set(itertools.product(*choices))
        if full != set(leaves):
            ok = False
        total += store.value(box)
    return ok and total == M.entry(w)


def batched(M, U, High, store):
    """R114a Lemma C: R20 Lemma 2's recursion with stopping rule 'state in High'. Returns (values, per-level counts,
    injection ok)."""
    L, m = M.L, M.m
    levels = []
    cur = {((), w) for w in U}
    levels.append(cur)
    stopped = set()

    def state(prefix, suffix):
        # prefix = symbols at levels 2L-1, 2L-2, ... (top first); suffix = letters at levels 0..len-1
        k = len(prefix)
        z0_1 = sum(1 for l in range(min(len(suffix), L)) if suffix[l] == 0)
        z0_2 = sum(1 for l in range(L, len(suffix)) if suffix[l] == 0)
        p0_1 = p0_2 = 0
        for idx, s in enumerate(prefix):
            l = 2 * L - 1 - idx
            if s == 0:
                if l < L:
                    p0_1 += 1
                else:
                    p0_2 += 1
        return (m - z0_1 - p0_1, m - z0_2 - p0_2)

    for k in range(2 * L):
        nxt = set()
        for (pre, suf) in cur:
            if state(pre, suf) in High:
                stopped.add((pre, suf))
                continue
            a = suf[-1]
            for s in (range(5) if a == 0 else (a,)):
                nxt.add((pre + (s,), suf[:-1]))
        cur = nxt
        levels.append(cur)
    # values bottom-up
    val = {}
    for k in range(2 * L, -1, -1):
        for (pre, suf) in levels[k]:
            if (pre, suf) in stopped or (k < 2 * L and state(pre, suf) in High):
                node = tuple((STAR if suf[l] == 0 else suf[l]) for l in range(len(suf))) + tuple(reversed(pre))
                val[(pre, suf)] = store.value(node)
            elif k == 2 * L:
                tau = tuple(reversed(pre))
                val[(pre, suf)] = M.Pi[M.leaf_index(tau)]
            else:
                a = suf[-1]
                val[(pre, suf)] = sum(val[(pre + (s,), suf[:-1])] for s in (range(5) if a == 0 else (a,)))
    roots = {w: val[((), w)] for w in U}
    # injection into Leaves_{Low+}(U)
    Low = {(a, b) for a in range(m + 1) for b in range(m + 1)} - set(High)
    LowP = set(Low) | {(a + 1, b) for (a, b) in Low} | {(a, b + 1) for (a, b) in Low} | {(0, 0)}
    leavesLP = set()
    for w in U:
        for tau in M.cube(w):
            if M.orders(tau) in LowP:
                leavesLP.add(tau)
    inj_ok = True
    counts = []
    for k in range(2 * L + 1):
        imgs = set()
        for (pre, suf) in levels[k]:
            lam = tuple((0 if suf[l] == 0 else suf[l]) for l in range(len(suf))) + tuple(reversed(pre))
            imgs.add(lam)
            if lam not in leavesLP:
                inj_ok = False
        if len(imgs) != len(levels[k]):
            inj_ok = False
        counts.append(len(levels[k]))
    return roots, counts, len(leavesLP), inj_ok


def all_nodes_count(M, High):
    """Enumerate the nodes via the bijection (leaf with orders in High, e <= #P0) and check against the predicate."""
    L, m = M.L, M.m
    nodes = set()
    for tau in itertools.product(range(5), repeat=2 * L):
        p1 = sum(1 for s in tau[:L] if s == 0)
        p2 = sum(1 for s in tau[L:] if s == 0)
        if p1 > m or p2 > m or (m - p1, m - p2) not in High:
            continue
        p0 = [l for l, s in enumerate(tau) if s == 0]
        for e in range(len(p0) + 1):
            pi = list(tau)
            for l in p0[:e]:
                pi[l] = STAR
            nodes.add(tuple(pi))
    beta = [comb(L, m - e) * 4 ** (L - m + e) for e in range(m + 1)]
    bound = (2 * m + 1) * sum(beta[a] * beta[b] for (a, b) in High)
    return nodes, bound


def run(L, m, seed, full_nodes, max_cols, rand_sets):
    M = Model(L, m, seed)
    print(f"== L+L = {L}+{L}, m = {m}: K_g = {len(M.Qg)} good sets of {comb(L, m)}")
    ups = upsets(m)
    nbad = 0
    # R20 Lemma 1 and Lemma 3(a) (independent of High)
    allv = range(1 << (L - m))
    Dp = {d1: [] for d1 in range(m + 1)}
    prod_ok = True
    for v in allv:
        Up, Upp = M.column(v, tuple([1] * (L - m)), M.Qg[0])
        # first-half distinct leaves by order
        lp = {}
        for wp in Up:
            for t in itertools.product(*[range(5) if a == 0 else (a,) for a in wp]):
                lp.setdefault(m - sum(1 for s in t if s == 0), set()).add(t)
        for d1 in range(m + 1):
            Dp[d1].append(len(lp.get(d1, ())))
        lpp = {}
        for wpp in Upp:
            for t in itertools.product(*[range(5) if a == 0 else (a,) for a in wpp]):
                lpp.setdefault(m - sum(1 for s in t if s == 0), set()).add(t)
        for d2 in range(m + 1):
            if len(lpp.get(d2, ())) != 2 ** (L - m) * comb(m, d2) * 4 ** d2:
                prod_ok = False
        if v == 0:
            U = [a + b for a in Up for b in Upp]
            lu = set()
            for w in U:
                lu.update(M.cube(w))
            pr = {a + b for d1 in lp for a in lp[d1] for d2 in lpp for b in lpp[d2]}
            prod_ok &= (lu == pr)
    print(f"   R20 Lemma 1 (Leaves(U) = Leaves'(U'_v) x Leaves''(U''), |Leaves''_d2| = 2^(L-m) C(m,d2) 4^d2): {prod_ok}")
    for d1 in range(m + 1):
        n = L - m + d1
        bound = 2 ** d1 * comb(L, m - d1) * sum(comb(n, b) * 2 ** (n - b) for b in range(d1 + 1))
        avg = sum(Dp[d1]) / len(Dp[d1])
        print(f"   R20 Lemma 3(a) d1={d1}: avg_v D'(v) = {avg:.2f} <= bound {bound}: {avg <= bound}; "
              f"max_v/avg = {max(Dp[d1]) / avg:.3f}")
        nbad += avg > bound
    # Step 4: kappa(v) ingredients D'_{d1}(v) by enumerating (Q, Z, A2, R)
    enum_ok = True
    trip = {}
    for Q in M.Qg:
        outer = [l for l in range(L) if l not in Q]
        for lab in itertools.product(range(3), repeat=m):  # 0: Z (P0), 1: A2 (j=2 inner), 2: j=1 inner
            Z = frozenset(Q[k] for k in range(m) if lab[k] == 0)
            A2 = frozenset(Q[k] for k in range(m) if lab[k] == 1)
            for r in range(len(outer) + 1):
                for R in itertools.combinations(outer, r):
                    v = M.DeltaS(R)
                    trip.setdefault((m - len(Z), v), set()).add((Z, A2 | frozenset(R)))
    for v in allv:
        for d1 in range(m + 1):
            n = L - m + d1
            cnt = len(trip.get((d1, v), ())) * 2 ** n
            if cnt != Dp[d1][v]:
                enum_ok = False
    print(f"   Step 4: D'_d1(v) from the (Q,Z,A2,R) enumeration equals the direct count for all v, d1: {enum_ok}")
    nbad += (not enum_ok) + (not prod_ok)
    # Lemmas A, B, C for every up-closed High
    rng = random.Random(seed + 7)
    worst_ratio = 0.0
    for High in ups:
        store = NodeStore(M, High)
        a_ok = True
        sample_w = []
        for _ in range(6):
            Q1 = rng.choice(M.Qg)
            Q2 = rng.choice(M.Qg)
            wp = M.half_string(Q1, tuple(rng.choice((1, 2)) for _ in range(L - m)),
                               [l for l in range(L) if l not in Q1 and rng.random() < 0.5])
            wpp = M.half_string(Q2, tuple(rng.choice((1, 2)) for _ in range(L - m)),
                                [l for l in range(L) if l not in Q2 and rng.random() < 0.5])
            sample_w.append(wp + wpp)
        for w in sample_w:
            a_ok &= lemmaA(M, w, High, store)
        c_ok = True
        cnt_ok = True
        cols = [(v, ipp, Qpp) for v in allv for ipp in itertools.product((1, 2), repeat=L - m) for Qpp in M.Qg]
        rng.shuffle(cols)
        test_sets = []
        for (v, ipp, Qpp) in cols[:max_cols]:
            Up, Upp = M.column(v, ipp, Qpp)
            test_sets.append([a + b for a in Up for b in Upp])
        for _ in range(rand_sets):
            pool = []
            for _ in range(12):
                Q1, Q2 = rng.choice(M.Qg), rng.choice(M.Qg)
                pool.append(M.half_string(Q1, tuple(rng.choice((1, 2)) for _ in range(L - m)),
                                          [l for l in range(L) if l not in Q1 and rng.random() < 0.5]) +
                            M.half_string(Q2, tuple(rng.choice((1, 2)) for _ in range(L - m)),
                                          [l for l in range(L) if l not in Q2 and rng.random() < 0.5]))
            test_sets.append(list(set(pool)))
        for U in test_sets:
            roots, counts, nLP, inj = batched(M, U, High, store)
            for w in U:
                if roots[w] != M.entry(w):
                    c_ok = False
            if max(counts) > nLP or not inj:
                cnt_ok = False
            worst_ratio = max(worst_ratio, max(counts) / nLP)
        # node values from the DP equal direct cube sums (sample of the memo)
        dp_ok = all(store.memo[pi] == direct_cube_sum(M, pi) for pi in list(store.memo)[:400])
        b_ok = store.bad_child == 0
        line = (f"   High={sorted(High)}: A {a_ok}, B(b) children nodes {b_ok}, DP=cube sums {dp_ok}, "
                f"C values {c_ok}, C pairs<=|Leaves_Low+| & injective {cnt_ok}")
        if full_nodes:
            nodes, bound = all_nodes_count(M, High)
            pred_ok = True
            if L <= 3:
                allc = [pi for pi in itertools.product(range(6), repeat=2 * L) if is_node(M, pi, High)]
                pred_ok = set(allc) == nodes
            line += f", nodes {len(nodes)} <= {bound}: {len(nodes) <= bound}, predicate = bijection image: {pred_ok}"
            nbad += not (len(nodes) <= bound and pred_ok)
        print(line)
        nbad += not (a_ok and b_ok and dp_ok and c_ok and cnt_ok)
    print(f"   largest (pairs at one level)/|Leaves_Low+(U)| = {worst_ratio:.3f}")
    return nbad


if __name__ == "__main__":
    total_bad = 0
    total_bad += run(3, 1, 11, True, 8, 3)
    total_bad += run(3, 2, 12, True, 8, 3)
    total_bad += run(4, 1, 13, True, 8, 3)
    total_bad += run(4, 2, 14, False, 3, 2)
    print("FAILURES:", total_bad)
