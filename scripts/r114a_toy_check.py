"""r114a_toy_check.py (2026-10-22), for exponents/r114a.md (task R114(a)).

Brute-force check, on the paper's squared construction (arxiv/anc/squared_check.py, imported read-only), of the
batched column query of r20.md Lemma 2 with the cut at an ARBITRARY UP-CLOSED set High of per-half orders
(d1, d2), instead of the total order d1 + d2 = t.  This is the data structure of r114a.md Section 2.

For every up-closed High in {0..m}^2 (all of them), every column of every tile:
  (a) the batched query (stop when the running per-half state (c1, c2) first lies in High, read the cube
      'tau above, stars at the inner levels of w below, outer letters below'; else read Pi at a full leaf)
      returns the right entry for every w in the column;
  (b) every cube read at a cut satisfies the node predicate of r114a.md Lemma B:
        f_h := #(P0 or star) in half h <= m,  (m - f1, m - f2) in High,  every star below every P0;
  (c) the dynamic program (replace the highest star by each of the five terms) stays inside the predicate, and its
      values equal the direct sums over the cube;
  (d) the number of distinct DP nodes reached is <= (2m+1) sum_{(d1,d2) in High} beta_d1 beta_d2;
  (e) per level, the distinct (node, suffix) pairs visited are <= |Leaves_{Low+}(U)|, Low+ = Low u (Low+e1) u
      (Low+e2) u {(0,0)}, the leaves of U whose per-half order lies in Low+.  (The point (0,0) accounts for the
      root pairs ((), w) when High contains (0,0), i.e. the |U| term of Lemma C; a first run without it failed
      only for High = everything, at the root level.)
Run: ~/.venv/bin/python r114a_toy_check.py > r114a_toy_check_out.txt   (single process, about a minute)
"""
import os, sys, itertools
from math import comb
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import squared_check as sc   # read-only import
import numpy as np

P0, Z0, STAR = 4, 4, 5


def column_key(w, L, F):
    Q1 = tuple(l for l in range(L) if w[l] == Z0)
    Q2 = tuple(l for l in range(L) if w[L + l] == Z0)
    S1 = [l for l in range(L) if l not in Q1 and sc.OUT_IJ[w[l]][1] == 1]
    i2 = 0
    for k, l in enumerate(l for l in range(L) if l not in Q2):
        i2 |= sc.OUT_IJ[w[L + l]][0] << k
    return (Q2, sc.hsh(F, S1), i2)


def upsets(m):
    pts = [(a, b) for a in range(m + 1) for b in range(m + 1)]
    out = []
    for mask in range(1 << len(pts)):
        S = {pts[i] for i in range(len(pts)) if mask >> i & 1}
        if all(((a + 1, b) in S or a == m) and ((a, b + 1) in S or b == m) for (a, b) in S):
            out.append(frozenset(S))
    return out


def node_ok(cube, L, m, High):
    f1 = sum(1 for s in cube[:L] if s in (P0, STAR)); f2 = sum(1 for s in cube[L:] if s in (P0, STAR))
    if f1 > m or f2 > m or (m - f1, m - f2) not in High:
        return False
    stars = [i for i, s in enumerate(cube) if s == STAR]; p0s = [i for i, s in enumerate(cube) if s == P0]
    return not stars or not p0s or max(stars) < min(p0s)


def direct(cube, prod):
    return int(prod[tuple(slice(None) if s == STAR else s for s in cube)].sum())


def run(L, m):
    G, F, good, Zm, Wm = sc.build(L, m)
    prod = sc.leaf_products(L, m, G, F, good, Zm, Wm)
    outs = list(sc.read_outputs(L, m, G, F, good, Zm, Wm))
    cols = defaultdict(list)
    for w, val, _ in outs:
        cols[column_key(w, L, F)].append((w, val))
    beta = [comb(L, m - e)*4**(L - m + e) for e in range(m + 1)]
    ups = upsets(m)
    print(f"L={L}+{L}, m={m}+{m}: K_g={len(good)}, {len(cols)} columns, {len(ups)} up-closed sets High")
    allok = True
    for High in ups:
        Low = {(a, b) for a in range(m + 1) for b in range(m + 1)} - High
        LowP = Low | {(a + 1, b) for a, b in Low if a < m} | {(a, b + 1) for a, b in Low if b < m}
        LowP = LowP | {(0, 0)}        # the root pairs ((), w): state (0,0); the '+|U|' term of the cost
        wrong = 0; pred = True; dpok = True; lvl_ok = True
        dpmemo = {}

        def dp(cube):                       # value of a node by the dynamic program, with predicate checks
            nonlocal pred, dpok
            if cube in dpmemo:
                return dpmemo[cube]
            pred &= node_ok(cube, L, m, High)
            st = [i for i, s in enumerate(cube) if s == STAR]
            if not st:
                v = int(prod[cube])
            else:
                h = max(st)
                v = sum(dp(cube[:h] + (s,) + cube[h + 1:]) for s in range(5))
            dpmemo[cube] = v
            return v

        for key, col in cols.items():
            U = [w for w, _ in col]
            memo = {}; visited = defaultdict(set)

            def val(node, l, suf):
                nonlocal wrong
                k = (node, suf)
                if k in memo:
                    return memo[k]
                visited[l].add(k)
                # per-half state: non-P0 symbols placed at inner levels
                c1 = m - sum(1 for i, z in enumerate(suf) if z == Z0 and i < L) \
                    - sum(1 for j, s in enumerate(node) if s == P0 and l + j < L)
                c2 = m - sum(1 for i, z in enumerate(suf) if z == Z0 and i >= L) \
                    - sum(1 for j, s in enumerate(node) if s == P0 and l + j >= L)
                if (c1, c2) in High:
                    cube = tuple(STAR if z == Z0 else z for z in suf) + node
                    r = dp(cube)
                    if r != direct(cube, prod):
                        dpok_fail()
                elif l == 0:
                    r = int(prod[node])
                else:
                    z = suf[-1]
                    r = sum(val((s,) + node, l - 1, suf[:-1]) for s in (range(5) if z == Z0 else (z,)))
                memo[k] = r
                return r

            def dpok_fail():
                nonlocal dpok
                dpok = False

            for w, v in col:
                wrong += val((), 2*L, w) != v
            # leaves of U with per-half order in Low+
            seen = set()
            for w in U:
                Q = [l for l in range(2*L) if w[l] == Z0]
                for d in range(2*m + 1):
                    for Dset in itertools.combinations(Q, d):
                        for terms in itertools.product(range(4), repeat=d):
                            tau = [P0 if z == Z0 else z for z in w]
                            for l, x in zip(Dset, terms):
                                tau[l] = x
                            d1 = m - tau[:L].count(P0); d2 = m - tau[L:].count(P0)
                            if (d1, d2) in LowP:
                                seen.add(tuple(tau))
            for l, S in visited.items():
                lvl_ok &= len(S) <= len(seen)
        # DP values of all reached nodes against direct sums
        for cube, v in dpmemo.items():
            dpok &= v == direct(cube, prod)
        bound = (2*m + 1)*sum(beta[a]*beta[b] for a, b in High)
        nodes = len(dpmemo)
        ok = wrong == 0 and pred and dpok and lvl_ok and nodes <= bound
        allok &= ok
        print(f"   High={sorted(High)}: wrong={wrong} predicate={pred} dp={dpok} level-bound={lvl_ok} "
              f"nodes={nodes} <= {bound}: {nodes <= bound}")
    return allok


if __name__ == "__main__":
    res = [run(L, m) for L, m in [(3, 1), (4, 1), (3, 2), (4, 2)]]
    print("ALL OK" if all(res) else "FAILURE")
