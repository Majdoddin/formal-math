r"""R61b (D): rigorous certificate that the exact leaf count of P3 saves at product types beyond rho = 1/2
(prescribed W of size N^2/sqrt(D)), r61b.md Section 6.2.

Leaf exponent (per level, natural log; Lemma 11 for P3 (c) with Stirling bounds):
    Lam(p) = max_{v in simplex_4} min(f1(v), f2(v)),
    f1(v) = pw H(v) - kappa pw ln 2          (log of alpha_T / D^kappa, kappa = 1/2),
    f2(v) = H(t) - H(p),  t = (p0 + pw v1, p1 + pw v2, p2 + pw v3, pw v4)   (log of beta_T / M).
For any mu in [0,1], min(f1, f2) <= g := mu f1 + (1-mu) f2, which is concave; for concave g and any interior v*,
    max_simplex g <= U := g(v*) + max_i dg/dv_i(v*) - sum_i v*_i dg/dv_i(v*)     (tangent plane).
So U < 0 certifies Lam(p) < 0.  mu and v* are found numerically, v* is rounded to rationals, and U is evaluated in
interval arithmetic (mpmath.iv, 60 digits).
Run with the system python (mpmath): /usr/bin/python3 r61b_certify.py > r61b_certify_out.txt
"""
from fractions import Fraction
import math
import mpmath
from mpmath import mp, iv

mp.dps = 40
iv.dps = 60


def H(v, lib):
    return -sum(x * lib.log(x) for x in v)


def stationary(p, mu):
    """v maximising g_mu: mu ln v_i + (1-mu) ln t_i = const (Lagrange), nested bisection in floats."""
    p0, p1, p2, pw = p
    pp = [p0, p1, p2, 0.0]

    def vi(i, K):
        lo, hi = 1e-300, 1.0
        for _ in range(120):
            mid = (lo + hi) / 2
            val = mu * math.log(mid) + (1 - mu) * math.log(pp[i] + pw * mid)
            if val < K:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2
    lo, hi = -700.0, 0.0
    for _ in range(120):
        K = (lo + hi) / 2
        sm = sum(vi(i, K) for i in range(4))
        if sm < 1:
            lo = K
        else:
            hi = K
    v = [vi(i, (lo + hi) / 2) for i in range(4)]
    sm = sum(v)
    return [x / sm for x in v]


def f12(p, v, lib, kappa):
    p0, p1, p2, pw = p
    t = [p0 + pw * v[0], p1 + pw * v[1], p2 + pw * v[2], pw * v[3]]
    f1 = pw * H(v, lib) - kappa * pw * lib.log(2)
    f2 = H(t, lib) - H(list(p), lib)
    return f1, f2, t


def bound(p, mu, v, lib, kappa):
    p0, p1, p2, pw = p
    f1, f2, t = f12(p, v, lib, kappa)
    g = mu * f1 + (1 - mu) * f2
    grad = [mu * pw * (-lib.log(v[i]) - 1) + (1 - mu) * pw * (-lib.log(t[i]) - 1) for i in range(4)]
    s = sum(v[i] * grad[i] for i in range(4))
    return g, grad, s


def certify(rho, kappa=Fraction(1, 2)):
    rho = Fraction(rho)
    pf = ((1 - rho) ** 2, rho * (1 - rho), rho * (1 - rho), rho ** 2)
    pm = tuple(float(x) for x in pf)
    km = float(kappa)

    def G(mu):
        v = stationary(pm, mu)
        f1, f2, _ = f12(pm, v, math, km)
        return mu * f1 + (1 - mu) * f2
    a, b = 0.0, 1.0
    gr = (math.sqrt(5) - 1) / 2
    c1 = b - gr * (b - a); c2 = a + gr * (b - a)
    G1, G2 = G(c1), G(c2)
    for _ in range(60):
        if G1 < G2:
            b, c2, G2 = c2, c1, G1
            c1 = b - gr * (b - a); G1 = G(c1)
        else:
            a, c1, G1 = c1, c2, G2
            c2 = a + gr * (b - a); G2 = G(c2)
    mu = (a + b) / 2
    v = stationary(pm, mu)
    # rationalise mu and v (v normalised exactly)
    muq = Fraction(mu).limit_denominator(10 ** 12)
    vq = [Fraction(x).limit_denominator(10 ** 15) for x in v[:3]]
    vq.append(1 - sum(vq))
    # interval evaluation
    piv = tuple(iv.mpf(x.numerator) / x.denominator for x in pf)
    muiv = iv.mpf(muq.numerator) / muq.denominator
    viv = [iv.mpf(x.numerator) / x.denominator for x in vq]
    kiv = iv.mpf(kappa.numerator) / kappa.denominator
    g, grad, s = bound(piv, muiv, viv, iv, kiv)
    U = g + max(grad, key=lambda z: z.b) - s       # max over i: use the interval with the largest upper end
    # rigorous: max_i grad_i <= max_i (grad_i.b); build an interval upper bound
    Ub = g.b + max(z.b for z in grad) - s.a
    f1, f2, _ = f12(pm, [float(x) for x in vq], math, km)
    pw = pf[3]
    LN2 = mp.log(2)
    rm = mp.mpf(rho.numerator) / rho.denominator
    eps_enc = (mp.mpf(pw.numerator) / pw.denominator * LN2) / (mp.log(4) - (-rm * mp.log(rm) - (1 - rm) * mp.log(1 - rm)))
    return dict(rho=rho, mu=float(muq), v=[float(x) for x in vq], f1=float(f1), f2=float(f2), Ub=Ub,
                gamma=-Ub / (mp.mpf(pw.numerator) / pw.denominator * LN2), eps=eps_enc)


if __name__ == '__main__':
    print('Certificate: Lam(p) <= U < 0 at product types p = ((1-rho)^2, rho(1-rho), rho(1-rho), rho^2), kappa = 1/2')
    for rho in [Fraction(1, 2), Fraction(101, 200), Fraction(1013, 2000), Fraction(127, 250), Fraction(2034, 4000),
                Fraction(509, 1000)]:
        r = certify(rho)
        print(f"rho = {r['rho']} = {float(r['rho']):.4f}: mu = {r['mu']:.6f}, v* = {[round(x, 6) for x in r['v']]}, "
              f"f1(v*) = {r['f1']:+.3e}, f2(v*) = {r['f2']:+.3e}; rigorous upper bound U = {mpmath.nstr(r['Ub'], 8)} "
              f"({'< 0: certified' if r['Ub'] < 0 else 'NOT certified'}); gamma_W <= -U/(pw ln2) = "
              f"{mpmath.nstr(r['gamma'], 6)}; encoding range eps(rho) = pw ln2/(ln4 - H2(rho)) = {mpmath.nstr(r['eps'], 8)}")
