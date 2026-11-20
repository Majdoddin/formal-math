"""R59 part 2: typical output support of the merged CW decomposition at level 1 (r59-part2-typical-support.md).

Notation: pi = 1/(q+2); term letters A (q choices), B', O; a kept-output superset = all z-strings of type
(n0, n1, n2) = N (pi, q pi, pi).  S(tau) = number of such z-strings in the z-form support of tau; depends only on the
composition (nA, nB, nO):
   S = [nO <= n0][nB >= n2] C(nB, n2) sum_j C(nB - n2, j) q^{nB - n2 - j} C(nA, n0 - nO - j).
(1) brute-force check of this formula against enumeration of z-strings (q = 2, 3, small N, random tau);
(2) S = 1 at the exact typical composition;
(3) Lambda(t) = max_x [-D(x) + t sigma(x)] (limit N -> inf of (1/N) ln E S^t) by optimisation, against the proved
    bound t^2 ln^2(4 e q / t), and the finite-N exact (1/N) ln E S^t against bound + 3 ln(N+1)/N;
(4) t = 1: the tilted composition (heavy strings) and Lambda(1) = c(q);
(5) Coppersmith's q = 6/7 mixture: alpha recomputed; saving -min_t [Lambda_hat(t) - t alpha/2] from the superset
    Lambda (no aliveness) and from the proved bound.
Run: ~/.venv/bin/python r59p2_typical.py > r59p2_typical_out.txt
"""
import itertools, random
from math import comb, log, lgamma, e, exp
import numpy as np
from scipy.optimize import minimize


def S_formula(q, nA, nB, nO, n0, n1, n2):
    if nO > n0 or nB < n2:
        return 0
    rest = nB - n2; z = n0 - nO
    return comb(nB, n2)*sum(comb(rest, j)*q**(rest - j)*comb(nA, z - j) for j in range(0, min(rest, z) + 1))


def allowed(q, letter):
    # letter: ('A', i) i in 1..q, ('B',), ('O',)
    if letter[0] == 'A':
        return (0, letter[1])
    if letter[0] == 'B':
        return tuple(range(q + 2))
    return (0,)


def part1():
    print("(1) closed form of S(tau) vs enumeration of z-strings of type N(pi, q pi, pi)")
    rng = random.Random(5)
    for q, N, trials in ((2, 4, 300), (2, 8, 200), (3, 5, 300), (4, 6, 200)):
        m = N//(q + 2); n0, n1, n2 = m, q*m, m
        letters = [('A', i) for i in range(1, q + 1)] + [('B',), ('O',)]
        bad = 0
        for _ in range(trials):
            tau = [rng.choice(letters) for _ in range(N)]
            cnt = 0
            for z in itertools.product(*[allowed(q, c) for c in tau]):
                if sum(1 for a in z if a == 0) == n0 and sum(1 for a in z if a == q + 1) == n2:
                    cnt += 1
            nA = sum(1 for c in tau if c[0] == 'A'); nB = sum(1 for c in tau if c[0] == 'B'); nO = N - nA - nB
            bad += (cnt != S_formula(q, nA, nB, nO, n0, n1, n2))
        print(f"  q={q} N={N}: {trials} random term strings, {bad} mismatches")
        assert bad == 0


def part2():
    print("\n(2) S at the exact typical composition (nA, nB, nO) = (n1, n2, n0)")
    for q in (5, 6, 7, 8):
        for m in (1, 3, 10, 50):
            N = m*(q + 2)
            assert S_formula(q, q*m, m, m, m, q*m, m) == 1
        print(f"  q={q}: S = 1 for m = 1, 3, 10, 50 (N = m(q+2))")


def h(x):
    x = min(max(x, 0.0), 1.0)
    r = 0.0
    if x > 0: r -= x*log(x)
    if x < 1: r -= (1 - x)*log(1 - x)
    return r


def xlnx(x):
    return x*log(x) if x > 0 else 0.0


def obj(q, t, uvy):
    """-D + t sigma at u = b - pi, v = pi - o, y; returns -inf if infeasible."""
    pi = 1/(q + 2)
    u, v, y = uvy
    b = pi + u; o = pi - v; a = 1 - b - o
    if u < 0 or v < 0 or y < 0 or y > u + 1e-15 or y > v + 1e-15 or o < 0 or a <= 0 or v - y > a:
        return -1e9
    D = xlnx(a) - a*log(q*pi) + xlnx(b) - b*log(pi) + xlnx(o) - o*log(pi)
    sig = b*h(pi/b) + (u*h(y/u) if u > 0 else 0.0) + (u - y)*log(q) + (a*h((v - y)/a))
    return -D + t*sig


def Lam(q, t):
    """max over the composition and y; concave, so a few local starts suffice."""
    pi = 1/(q + 2); best = (0.0, (0, 0, 0))
    for u0 in (1e-4, 1e-3, 1e-2, 0.05, 0.2, 0.5):
        for v0 in (1e-4, 1e-3, 1e-2, 0.5*pi, 0.9*pi):
            for yf in (0.0, 0.5):
                x0 = np.array([u0, v0, yf*min(u0, v0)])
                r = minimize(lambda z: -obj(q, t, z), x0, method="Nelder-Mead",
                             options=dict(xatol=1e-12, fatol=1e-15, maxiter=20000, maxfev=40000))
                if -r.fun > best[0]:
                    best = (-r.fun, tuple(r.x))
    return best


def bound(q, t):
    return t*t*log(4*e*q/t)**2


def finiteN(q, N, t):
    """(1/N) ln E_tau S^t exactly (log domain), tau uniform in [q+2]^N."""
    m = N//(q + 2); n0, n1, n2 = m, q*m, m
    lf = [lgamma(i + 1) for i in range(N + 2)]
    lC = lambda n, k: lf[n] - lf[k] - lf[n - k]
    lq = log(q); terms = []
    for nB in range(n2, N + 1):
        for nO in range(0, min(n0, N - nB) + 1):
            nA = N - nB - nO
            rest = nB - n2; z = n0 - nO
            js = [lC(rest, j) + (rest - j)*lq + lC(nA, z - j) for j in range(0, min(rest, z) + 1) if z - j <= nA]
            if not js:
                continue
            mx = max(js); lS = lC(nB, n2) + mx + log(sum(exp(v - mx) for v in js))
            lP = lf[N] - lf[nA] - lf[nB] - lf[nO] + nA*lq - N*log(q + 2)
            terms.append(lP + t*lS)
    mx = max(terms)
    return (mx + log(sum(exp(v - mx) for v in terms)))/N


def part3():
    print("\n(3) Lambda(t) per CW coordinate (limit), proved bound t^2 ln^2(4eq/t), finite-N exact values")
    for q in (6, 7):
        for t in (1e-4, 1e-3, 0.003, 0.01, 0.02, 0.05, 0.1, 0.3, 1.0):
            L, x = Lam(q, t)
            print(f"  q={q} t={t:7.4f}: Lambda={L:.4e}  Lambda/t={L/t:.4e}  bound={bound(q, t):.4e}  "
                  f"argmax (u,v,y)=({x[0]:.2e},{x[1]:.2e},{x[2]:.2e})", flush=True)
        for N in (9*10, 9*30, 9*100) if q == 7 else (8*10, 8*30, 8*100):
            for t in (0.01, 0.1):
                f = finiteN(q, N, t)
                print(f"    N={N:4d} t={t}: (1/N) ln E S^t = {f:.5f}   bound + 3ln(N+1)/N = "
                      f"{bound(q, t) + 3*log(N + 1)/N:.5f}", flush=True)


def part4():
    print("\n(4) t = 1: heavy strings")
    for q in (6, 7):
        pi = 1/(q + 2)
        L, (u, v, y) = Lam(q, 1.0)
        b = pi + u; o = pi - v; a = 1 - b - o
        D = xlnx(a) - a*log(q*pi) + xlnx(b) - b*log(pi) + xlnx(o) - o*log(pi)
        cq = (log(q + 2) + q*log(2))/(q + 2)
        print(f"  q={q}: Lambda(1)={L:.6f}  c(q)={cq:.6f}; tilted composition A:B':O = {a:.4f}:{b:.4f}:{o:.4f} "
              f"(typical {q*pi:.4f}:{pi:.4f}:{pi:.4f}); these strings are a fraction e^(-{D:.4f} N) of all")


def part5():
    print("\n(5) Coppersmith's q = 6/7 mixture")
    qs = (6, 7)

    def parts(us):
        out = []
        for q, uf in zip(qs, us):
            w = 1/(q + 2); u = uf*w; v = (w - u)/2; p = q/(2*(q + 2))
            X = [p + w + v, p + u, v]; Z = [u + 2*v, 2*p, w]
            H = lambda V: -sum(c*log(c) for c in V if c > 0)
            out.append(dict(q=q, lna=p*log(q), lnb=u*log(q), slack=H(X) - H(Z)))
        return out

    def neg_alpha(z):
        l6, u6, u7 = z; ps = parts((u6, u7)); lam = (l6, 1 - l6)
        return -sum(l*pp["lnb"] for l, pp in zip(lam, ps))/sum(l*pp["lna"] for l, pp in zip(lam, ps))

    def slack(z):
        l6, u6, u7 = z; ps = parts((u6, u7)); lam = (l6, 1 - l6)
        return sum(l*pp["slack"] for l, pp in zip(lam, ps))

    best = None
    for st in ((0.36, 0.97, 0.98), (0.2, 0.9, 0.95), (0.5, 0.99, 0.99)):
        r = minimize(neg_alpha, st, method="SLSQP", bounds=[(0, 1), (0, 1), (0, 1)],
                     constraints=[dict(type="ineq", fun=slack)], options=dict(ftol=1e-15, maxiter=1000))
        if best is None or r.fun < best.fun:
            best = r
    l6, u6, u7 = best.x; alpha = -best.fun
    print(f"  max alpha = {alpha:.6f} at lam6={l6:.4f}, u6(q+2)={u6:.5f}, u7(q+2)={u7:.5f}, slack={slack(best.x):.2e}")
    ps = parts((u6, u7)); lam = (l6, 1 - l6)
    lna = sum(l*pp["lna"] for l, pp in zip(lam, ps))
    print(f"  ln a per CW coordinate = {lna:.6f}")
    for name, f in (("superset Lambda", lambda t: sum(l*Lam(q, t)[0] for l, q in zip(lam, qs))),
                    ("proved bound", lambda t: sum(l*bound(q, t) for l, q in zip(lam, qs)))):
        rows = []
        for t in (1e-5, 3e-5, 1e-4, 3e-4, 1e-3, 3e-3, 0.01, 0.02, 0.03, 0.05):
            val = f(t)/lna - t*alpha/2
            rows.append((t, val))
        tb, vb = min(rows, key=lambda r: r[1])
        print(f"  {name}: " + "  ".join(f"t={t:g}:{v:+.2e}" for t, v in rows))
        print(f"    best saving per ln K = {-vb:.3e} at t = {tb:g}")


if __name__ == "__main__":
    part1(); part2(); part3(); part4(); part5()
