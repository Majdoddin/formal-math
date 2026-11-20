"""R74(a): certify Theorem D's gamma with the sharp level-1 profile (r74a.md).

Goal: a rigorous upper bound on G_q(t) = sup_{z in P_q} F_q(t, z), z = (u, v, y), for q = 6, 7, where
    a = q pi - u + v (= x_A),  b = pi + u (= x_B),  o = pi - v (= x_O),  pi = 1/(q+2),
    F = -D(x || x*) + t sigma,
    D = a ln(a/(q pi)) + b ln(b/pi) + o ln(o/pi),
    sigma = b h(pi/b) + u h(y/u) + (u - y) ln q + a h((v - y)/a)
          = phi(b) - phi(pi) - phi(y) - phi(u - y) + (u - y) ln q + phi(a) - phi(v - y) - phi(q pi - u + y),
    phi(s) = s ln s (phi(0) = 0),
    P_q = { 0 <= v <= pi, 0 <= y <= v, y <= u, u - y <= q pi }   (a closed polytope inside [0,1]^3).
F is concave and continuous on P_q (r74a.md Lemma 1), so for an interior point z0 with gradient g,
    F(z) <= F(z0) + g.(z - z0) <= F(z0) + sum_i |g_i|        (|z_i - z0_i| <= 1 on [0,1]^3).
F(z0) and g are evaluated in mpmath interval arithmetic (outward rounding) at a rational z0.
Then Lambda_cert(t) = (lam6 G_6 + lam7 G_7)/ln a_1 and gamma_cert = t/2 - Lambda_cert/alpha(P0), with interval
enclosures of ln a_1 and alpha(P0) at the rational point P0 = (7/19, 97/100, 979/1000) of r59-theorem-level1.md.

(1) float optimum over t of t/2 - Lambda(t)/alpha (scipy), (2) certification at a grid of rational t,
(3) checks: gradient vs finite differences, F at random feasible points below the certified bound, comparison with
    r59p2_typical.Lam.
Run: ~/.venv/bin/python r74a_certify.py > r74a_certify_out.txt
"""
import sys, os, random
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath
from mpmath import iv, mp
import numpy as np
from scipy.optimize import minimize, minimize_scalar

iv.dps = 60
mp.dps = 60
QS = (6, 7)
LAM6 = Fr(7, 19)
F6, F7 = Fr(97, 100), Fr(979, 1000)


# ------------------------------------------------------------------ the objective, generic in the number type
def make(ln, num):
    """ln: log function; num: converts a Fraction to the number type."""
    def phi(s):
        return s*ln(s)

    def dphi(s):
        return ln(s) + 1

    def F(q, t, u, v, y):
        pi = num(Fr(1, q + 2)); qpi = num(Fr(q, q + 2)); lq = ln(num(Fr(q)))
        a = qpi - u + v; b = pi + u; o = pi - v
        D = phi(a) - a*ln(qpi) + phi(b) - b*ln(pi) + phi(o) - o*ln(pi)
        sig = (phi(b) - phi(pi) - phi(y) - phi(u - y) + (u - y)*lq + phi(a) - phi(v - y) - phi(qpi - u + y))
        return -D + t*sig

    def grad(q, t, u, v, y):
        pi = num(Fr(1, q + 2)); qpi = num(Fr(q, q + 2)); lq = ln(num(Fr(q)))
        a = qpi - u + v; b = pi + u; o = pi - v; w = qpi - u + y
        Du = ln(b) - ln(a) + lq
        Dv = ln(a) - ln(o) - lq
        su = dphi(b) - dphi(u - y) + lq - dphi(a) + dphi(w)
        sv = dphi(a) - dphi(v - y)
        sy = -dphi(y) + dphi(u - y) - lq + dphi(v - y) - dphi(w)
        return (-Du + t*su, -Dv + t*sv, t*sy)
    return F, grad


Ff, Gf = make(np.log, float)
Fm, Gm = make(mp.log, lambda fr: mp.mpf(fr.numerator)/fr.denominator)
Fi, Gi = make(iv.log, lambda fr: iv.mpf(fr.numerator)/fr.denominator)


def feasible(q, u, v, y, strict=False):
    pi = 1/(q + 2)
    if strict:
        return 0 < v < pi and 0 < y < v and y < u and u - y < q*pi
    return 0 <= v <= pi and 0 <= y <= v and y <= u and u - y <= q*pi


def float_max(q, t):
    """float argmax of the concave F_q(t, .) (log-parametrised interior starts)."""
    best = None
    for u0 in (3e-3, 1e-2):
        for v0 in (1e-2,):
            for yr in (1e-2,):
                x0 = np.log([u0, v0, yr*min(u0, v0)])
                def neg(p):
                    u, v, y = np.exp(p)
                    if not feasible(q, u, v, y, strict=True):
                        return 1e9
                    return -Ff(q, t, u, v, y)
                r = minimize(neg, x0, method="Nelder-Mead",
                             options=dict(xatol=1e-13, fatol=1e-18, maxiter=40000, maxfev=80000))
                if best is None or r.fun < best[0]:
                    best = (r.fun, np.exp(r.x))
    return -best[0], best[1]


def newton(q, t, z):
    """refine the critical point in 60-digit arithmetic (Newton with a finite-difference Jacobian in mp)."""
    tt = mp.mpf(t.numerator)/t.denominator
    z = [mp.mpf(float(c)) for c in z]
    for _ in range(60):
        g = Gm(q, t_to(t), *z)
        if max(abs(c) for c in g) < mp.mpf(10)**(-50):
            break
        h = mp.mpf(10)**(-25)
        J = mp.matrix(3, 3)
        for j in range(3):
            zp = list(z); zp[j] += h
            gp = Gm(q, t_to(t), *zp)
            for i in range(3):
                J[i, j] = (gp[i] - g[i])/h
        dz = mp.lu_solve(J, mp.matrix(g))
        z = [z[i] - dz[i] for i in range(3)]
    return z


def t_to(t):
    return mp.mpf(t.numerator)/t.denominator



def certify_G(q, t):
    """returns (z0 as Fractions, interval F(z0), interval gradient, upper bound on G_q(t), float value)."""
    fv, zf = float_max(q, float(t))
    zm = newton(q, t, zf)
    z0 = [Fr(mp.nstr(c, 40)) for c in zm]
    u, v, y = z0
    pi = Fr(1, q + 2)
    assert 0 < v < pi and 0 < y < v and y < u and u - y < q*pi, "z0 not interior"
    ti = iv.mpf(t.numerator)/t.denominator
    zi = [iv.mpf(c.numerator)/c.denominator for c in z0]
    Fz = Fi(q, ti, *zi)
    g = Gi(q, ti, *zi)
    slope = sum(max(abs(c.a), abs(c.b)) for c in g)        # upper bound on sum |g_i| (endpoints are mpf)
    ub = Fz.b + iv.mpf(slope).b
    return z0, Fz, g, iv.mpf(ub).b, fv


def lo(x, n=15):
    return mpmath.nstr(mp.make_mpf(x._mpi_[0]), n)


def hi(x, n=15):
    return mpmath.nstr(mp.make_mpf(x._mpi_[1]), n)


def point_P0():
    """interval enclosures at P0: slack, ln a_1, alpha(P0) = ln b_1/ln a_1."""
    slack = iv.mpf(0); lna = iv.mpf(0); lnb = iv.mpf(0)
    for q, lam, f in ((6, LAM6, F6), (7, 1 - LAM6, F7)):
        I = lambda fr: iv.mpf(fr.numerator)/fr.denominator
        w = Fr(1, q + 2); u = f*w; v = (w - u)/2; p = Fr(q, 2*(q + 2))
        X = [p + w + v, p + u, v]; Z = [u + 2*v, 2*p, w]
        H = lambda V: -sum(I(c)*iv.log(I(c)) for c in V)
        slack += I(lam)*(H(X) - H(Z))
        lna += I(lam*p)*iv.log(q)
        lnb += I(lam*u)*iv.log(q)
    return slack, lna, lnb/lna


def main():
    slack, lna, alpha = point_P0()
    print("(0) the rational point P0 = (lam6, u6(q+2), u7(q+2)) = (7/19, 97/100, 979/1000), interval arithmetic "
          f"({iv.dps} digits, outward rounding)")
    print(f"  slack H_X - H_Z in [{lo(slack)}, {hi(slack)}]  (> 0: admissible)")
    print(f"  ln a_1 in [{lo(lna)}, {hi(lna)}]")
    print(f"  alpha(P0) in [{lo(alpha)}, {hi(alpha)}]")
    assert slack.a > 0
    al, lna_f = float(alpha.a), float(lna.a)

    print("\n(1) float optimum of t/2 - Lambda(t)/alpha, Lambda(t) = sum_q lam_q G_q(t)/ln a_1 (G_q by Nelder-Mead)")
    lam = {6: 7/19, 7: 12/19}
    def gam(t):
        return t/2 - sum(lam[q]*float_max(q, t)[0] for q in QS)/lna_f/al
    r = minimize_scalar(lambda t: -gam(t), bounds=(0.005, 0.05), method="bounded", options=dict(xatol=1e-7))
    print(f"  t_opt = {r.x:.6f}, gamma(t_opt) = {-r.fun:.6e} (float)")
    for t in (0.010, 0.015, 0.018, 0.0196, 0.020, 0.022, 0.025, 0.030):
        print(f"    t = {t:.4f}: gamma = {gam(t):.6e}")

    print("\n(2) certification at rational t (G_q(t) <= F(z0) + sum|grad F(z0)|, interval arithmetic)")
    best = None
    for t in (Fr(15, 1000), Fr(18, 1000), Fr(19, 1000), Fr(195, 10000), Fr(196, 10000), Fr(197, 10000),
              Fr(2, 100), Fr(21, 1000), Fr(25, 1000)):
        ti = iv.mpf(t.numerator)/t.denominator
        Gsum = iv.mpf(0)
        for q in QS:
            z0, Fz, g, ub, fv = certify_G(q, t)
            lamq = LAM6 if q == 6 else 1 - LAM6
            Gsum += (iv.mpf(lamq.numerator)/lamq.denominator)*iv.mpf(ub)
            if t == Fr(196, 10000):
                print(f"  t = {t} (= {float(t)}), q = {q}:")
                print(f"    z0 = (u, v, y) = ({float(z0[0]):.15e}, {float(z0[1]):.15e}, {float(z0[2]):.15e}) "
                      "(rational, 40 significant digits)")
                print(f"    F(z0) in [{lo(Fz, 20)}, {hi(Fz, 20)}]  (float max {fv:.12e})")
                print("    grad F(z0) in " + ", ".join(f"[{lo(c, 3)}, {hi(c, 3)}]" for c in g))
                print(f"    certified G_q(t) <= {hi(iv.mpf(ub), 20)}")
        Lc = Gsum/lna            # upper end uses the lower end of ln a_1
        gc = ti/2 - Lc/alpha     # lower end uses the upper end of Lambda and the lower end of alpha
        print(f"  t = {float(t):.4f}: Lambda_cert(t) <= {hi(Lc, 12)},  "
              f"gamma_cert(t) >= {lo(gc, 12)}")
        if best is None or gc.a > best[1].a:
            best = (t, gc)
    tb, gb = best
    print(f"  best certified: gamma_inf := t/2 - Lambda_cert(t)/alpha >= {lo(gb, 12)} at t = {tb} = {float(tb)}")
    # Theorem D: gamma < min(gamma_inf, 1/eps - 1/alpha); the second binds only for eps > eps1 = 1/(1/alpha + gamma_inf)
    eps1 = 1/(1/alpha + iv.mpf(gb.a))
    print(f"  the encoding term 1/eps - 1/alpha >= gamma_inf iff eps <= eps1 = 1/(1/alpha + gamma_inf), "
          f"eps1 in [{lo(eps1, 10)}, {hi(eps1, 10)}]")
    print(f"  best eps*gamma = eps1*gamma_inf >= {lo(eps1*iv.mpf(gb.a), 10)} (approached at eps = eps1)")

    print("\n(3) checks")
    t = 0.0196
    for q in QS:
        fv, z = float_max(q, t)
        g = Gf(q, t, *z); h = 1e-7; fd = []
        for j in range(3):
            zp = list(z); zm = list(z); zp[j] += h; zm[j] -= h
            fd.append((Ff(q, t, *zp) - Ff(q, t, *zm))/(2*h))
        gg = Gf(q, t, *(z*1.3))
        fd2 = []
        for j in range(3):
            zp = list(z*1.3); zm = list(z*1.3); zp[j] += h; zm[j] -= h
            fd2.append((Ff(q, t, *zp) - Ff(q, t, *zm))/(2*h))
        print(f"  q={q}: analytic gradient vs central differences at 1.3 z*: "
              f"max diff {max(abs(a - b) for a, b in zip(gg, fd2)):.2e} (gradient size {max(abs(c) for c in gg):.2e})")
        # random feasible points, including the boundary (phi(0) = 0)
        z0, Fz, gI, ub, _ = certify_G(q, Fr(196, 10000))
        rng = random.Random(q); worst = -1e9; pi = 1/(q + 2)
        def safe_F(u, v, y):
            ph = lambda s: s*np.log(s) if s > 0 else 0.0
            a = q*pi - u + v; b = pi + u; o = pi - v; lq = np.log(q)
            D = ph(a) - a*np.log(q*pi) + ph(b) - b*np.log(pi) + ph(o) - o*np.log(pi)
            sg = ph(b) - ph(pi) - ph(y) - ph(u - y) + (u - y)*lq + ph(a) - ph(v - y) - ph(q*pi - u + y)
            return -D + t*sg
        for k in range(200000):
            v = rng.random()*pi*(rng.random()**3 if k % 2 else 1)
            y = rng.random()*v*(rng.random()**3 if k % 3 else 1) if k % 7 else 0.0
            u = y + rng.random()*q*pi*(rng.random()**3 if k % 5 else 1)
            if k % 11 == 0: v = pi
            if k % 13 == 0: u = y
            if not feasible(q, u, v, y):
                continue
            worst = max(worst, safe_F(u, v, y))
        print(f"    max F over 200000 random feasible points (boundary included) = {worst:.10e} <= certified "
              f"{float(ub):.10e}: {worst <= float(ub)}")
        try:
            from r59p2_typical import Lam
            print(f"    r59p2_typical.Lam(q, t) = {Lam(q, t)[0]:.10e} (float max here {fv:.10e})")
        except Exception as ex:
            print("    Lam comparison skipped:", ex)
        # Hessian sanity (concavity is proved; this checks the formulas): eigenvalues at z*
        H = np.zeros((3, 3)); e = 1e-6
        for j in range(3):
            zp = list(z); zm = list(z); zp[j] += e; zm[j] -= e
            H[:, j] = (np.array(Gf(q, t, *zp)) - np.array(Gf(q, t, *zm)))/(2*e)
        print(f"    Hessian eigenvalues at the maximiser: {np.linalg.eigvalsh((H + H.T)/2)}")


if __name__ == "__main__":
    main()
