"""R201: independent recomputation of the constants of r61b.md Corollary 5 (a) and (b).

Written from r61b.md Section 5.3 (Corollary 3) and 7.2 (Corollary 5), without importing r61b's scripts.
For (c, theta, threshold k) with N >= D^k:
  gamma = theta log2(sqrt c - 1), q = (H(theta) + theta ln 3)/ln 2, x = (1 - theta)/theta,
  Lambda = 4^c exp(-c H2(1/sqrt c)) 2^gamma (analytic base), ratio 2^k / Lambda.
  d := ceil(log2 D), L := ceil(c d), a := ceil(sqrt(d L)), t := ceil(theta d), n = a - d, n0 = L - 2a + d.
  Shape conditions (Corollary 3): floor(a^2/L) = d, n0 >= n, 2a <= L, lambda = d/(min(n, n0)+1) < 1/(sqrt c - 1).
  Encoding condition: E(d) := L^2 4^L 2^{gamma d} / binom(L, a) <= 2^{k(d-1)} (N >= D^k >= 2^{k(d-1)}).
  Analytic bound: E(d) <= 4 (c d + 2)^3 Lambda^d.
"""
import math

def H(x):
    return -x * math.log(x) - (1 - x) * math.log(1 - x)

def check(c, theta, k, dmax):
    gamma = theta * math.log2(math.sqrt(c) - 1)
    q = (H(theta) + theta * math.log(3)) / math.log(2)
    Lam = 4 ** c * math.exp(-c * H(1 / math.sqrt(c))) * 2 ** gamma
    print(f"c = {c}, theta = {theta:.6f}, N >= D^{k}: gamma = {gamma:.6f}, q = {q:.6f}, x = {(1-theta)/theta:.4f}, "
          f"Lambda = {Lam:.4f}, 2^{k} = {2**k}, ratio = {2**k/Lam:.5f}")
    # analytic threshold: last d <= dmax at which 4 (cd+2)^3 Lambda^d > 2^{k(d-1)}
    last_bad_an = None
    for d in range(1, dmax + 1):
        lhs = math.log(4) + 3 * math.log(c * d + 2) + d * math.log(Lam)
        rhs = k * (d - 1) * math.log(2)
        if lhs > rhs:
            last_bad_an = d
    # exact threshold and shape conditions
    last_bad_ex = None
    shape_bad = []
    for d in range(1, dmax + 1):
        L = math.ceil(c * d)
        a = math.isqrt(d * L)
        if a * a < d * L:
            a += 1
        n = a - d
        n0 = L - 2 * a + d
        lam = d / (min(n, n0) + 1)
        ok_shape = (a * a // L == d) and (n0 >= n) and (2 * a <= L) and (lam < 1 / (math.sqrt(c) - 1))
        if not ok_shape:
            shape_bad.append(d)
        lhs = 2 * math.log(L) + L * math.log(4) + gamma * d * math.log(2) - math.log(math.comb(L, a))
        rhs = k * (d - 1) * math.log(2)
        if lhs > rhs:
            last_bad_ex = d
    print(f"  analytic bound 4(cd+2)^3 Lambda^d <= 2^(k(d-1)) fails last at d = {last_bad_an} (checked d <= {dmax}); "
          f"holds for all d from {last_bad_an + 1 if last_bad_an else 1} to {dmax}")
    print(f"  exact E(d) <= 2^(k(d-1)) fails last at d = {last_bad_ex}; holds from {last_bad_ex + 1 if last_bad_ex else 1} to {dmax}")
    sb = [d for d in shape_bad]
    print(f"  shape conditions fail at d in {sb[:20]}{' ...' if len(sb) > 20 else ''} (of 1..{dmax}); "
          f"largest failing d = {max(sb) if sb else None}")
    print(f"  rounding: gamma {gamma:.6f} -> claimed, q {q:.6f} -> claimed")
    return gamma, q, Lam

if __name__ == '__main__':
    print("Corollary 5 (a): claimed gamma = 0.018619..., q = 0.459024..., Lambda = 30.9438..., ratio 1.03413, "
          "analytic from d = 895, exact from d = 731, shape for d >= 6")
    g, q, _ = check(4.9, 1 / 15, 5, 3000)
    print(f"  claimed exponents: preprocessing 0.018 < {g:.6f}: {0.018 < g}; query 0.46 > {q:.6f}: {0.46 > q}; "
          f"0.46 + 0.018 < 1/2: {0.46 + 0.018 < 0.5}")
    print("Corollary 5 (b): claimed gamma = 0.049871, q = 0.436350, Lambda = 246.99, valid from d = 936")
    g, q, _ = check(7.5, 1 / 16, 8, 3000)
    print(f"  claimed exponents: preprocessing 0.049 < {g:.6f}: {0.049 < g}; query 0.437 > {q:.6f}: {0.437 > q}; "
          f"0.437 + 0.049 < 1/2: {0.437 + 0.049 < 0.5}")
