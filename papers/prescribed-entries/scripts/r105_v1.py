"""R105 task 1: v1 (Schoenhage's G, squared run, exact counts) against the Legendre form.

Units: D = 4^m per squared run (m inner levels per half, L = c m letters per half), read set = the tile's
outputs, M ~ beta_0^2 (beta_e = C(L, m-e) 4^{L-m+e}).  A leaf with half-orders (d1, d2) has degree
C(L-m+d1, d1) C(L-m+d2, d2).  Rates per m (x = d/m):
  F(x) = lim (1/m) ln(beta_{xm}/beta_0) = int_0^x ln(4(1-y)/(c-1+y)) dy          (leaves per output)
  G(x) = lim (1/m) ln C((c-1+x)m, xm)                                              (log-degree)
  J(x) = F + G = H(x) + x ln 4                                                     (cube count per output)
Profile in units of ln D (both halves):
  LamD(t) = lim ln( sum_tau deg(tau)^t / M ) / ln D = (2/ln4) max_x [F(x) + t G(x)]     (method of types)
Legendre (t restricted to [0,1]): LamD*(u) = sup_{0<=t<=1} (t u - LamD(t)).
In units of ln K, K = beta_0 = sqrt(M): Lam_K = alpha_G LamD with alpha_G = ln4/g(c), g(c) = cH(1/c)+(c-1)ln4,
and LamD*(b) = Lam_K*(alpha_G b)/alpha_G (the conjecture's form).
R14 (exact box count) at (theta, c): gamma = -2F(theta)/ln4, q = 2J(theta)/ln4, degree threshold u = 2G(theta)/ln4.
Claims tested (numerically; LamD* is computed by a sup over t, independently of the parametrisation):
  (P) gamma_R14 = LamD*(u) and q_R14 = u - LamD*(u)  (parametric Legendre form of the threshold data structure)
  (C) the conjectured gamma(q) = LamD*(q) is strictly smaller than gamma_R14 at the same q
  (T) the thresholds c*(b): LamD_c*(b) = 0 give R14's eps_b = ln4/A(c*(b))
  (H) with q + gamma = b (Hyp-type balance) the best gamma at fixed c is LamD*(b)
"""
from math import log, exp
import numpy as np
from scipy.optimize import brentq, minimize_scalar

L4 = log(4)
def H(x): return 0.0 if x <= 0 or x >= 1 else -x*log(x) - (1-x)*log(1-x)
def F(x, c): return x*L4 - ((1-x)*log(1-x) if x < 1 else 0) - (c-1+x)*log(c-1+x) + (c-1)*log(c-1)
def G(x, c): return (c-1+x)*log(c-1+x) - (x*log(x) if x > 0 else 0) - (c-1)*log(c-1)
def J(x): return H(x) + x*L4
def g(c): return c*H(1/c) + (c-1)*L4
def A(c): return 2*c*log(5) - c*H(1/c) - (c-1)*L4

def xopt(t, c):
    """argmax_x F + tG on (0,1)."""
    if t <= 0:
        return max(0.0, (5-c)/5)
    d = lambda x: log(4*(1-x)/(c-1+x)) + t*log((c-1+x)/x)
    return brentq(d, 1e-300, 1-1e-15, xtol=1e-300, rtol=1e-15, maxiter=500)

def LamD(t, c):
    x = xopt(t, c)
    return 2*(F(x, c) + t*G(x, c))/L4

def LamD_star(u, c):
    """sup_{0<=t<=1} t u - LamD(t), by bounded scalar optimisation of a concave function plus endpoints."""
    f = lambda t: -(t*u - LamD(t, c))
    r = minimize_scalar(f, bounds=(0.0, 1.0), method='bounded', options={'xatol': 1e-13})
    cands = [(-r.fun, r.x), (-f(0.0), 0.0), (-f(1.0), 1.0)]
    return max(cands)

def r14(theta, c):
    return -2*F(theta, c)/L4, 2*J(theta)/L4, 2*G(theta, c)/L4

def cstar(b):
    return brentq(lambda c: LamD_star(b, c)[0], 1.2, 60, xtol=1e-13)

def main():
    print("(0) sanity: F + G = J at random points; LamD(0) = (2/ln4) max F (rank excess, > 0 iff c < 5)")
    rng = np.random.default_rng(1)
    err = max(abs(F(x, c) + G(x, c) - J(x)) for x, c in rng.uniform([0.01, 2], [0.79, 20], (200, 2)))
    print(f"    max |F+G-J| = {err:.2e};  LamD(0) at c = 4.5, 5, 6: "
          f"{LamD(0,4.5):.5f} {LamD(0,5):.5f} {LamD(0,6):.5f};  alpha_G = ln4/g(c) at c = 5: {L4/g(5):.6f}")

    print("\n(P) parametric identity at R14's Theorem 1 points and a random grid:")
    print("    c       theta     u=2G/ln4   gamma_R14   LamD*(u)    t*        q_R14      u - LamD*(u)  conj LamD*(q_R14)")
    pts = [(14.5, 1/19), (11.5, 1/18), (10.0, 0.057), (5.5, 0.05), (4.9, 0.0688), (4.8268, 0.06897), (4.5687, 0.17054)]
    for c, th in pts:
        gm, q, u = r14(th, c)
        ls, ts = LamD_star(u, c)
        cj, _ = LamD_star(q, c)
        print(f"  {c:7.4f}  {th:.5f}  {u:.6f}  {gm: .6f}  {ls: .6f}  {ts:.5f}  {q:.6f}  {u-ls:.6f}    {cj: .6f}")
    worst_g = worst_q = 0; worst_gap = 1e9; n = 0
    for c, th in rng.uniform([2.2, 0.005], [25, 0.75], (400, 2)):
        gm, q, u = r14(th, c)
        # identity needs u beyond the t=0 point (theta past the peak of F) -- otherwise t* = 0
        if th <= max(0, (5-c)/5) + 1e-3:
            continue
        ls, ts = LamD_star(u, c)
        if not (1e-6 < ts < 1-1e-6):
            continue
        n += 1
        worst_g = max(worst_g, abs(gm - ls)); worst_q = max(worst_q, abs(q - (u - ls)))
        if gm > 1e-9:   # below the threshold q > u and no saving exists; the comparison is meaningless there
            cj, _ = LamD_star(q, c)
            worst_gap = min(worst_gap, gm - cj)
    print(f"    random grid ({n} points with theta past F's peak): max|gamma_R14 - LamD*(u)| = {worst_g:.2e},"
          f" max|q_R14 - (u - LamD*(u))| = {worst_q:.2e}; min over gamma_R14 > 0 of (gamma_R14 - LamD*(q_R14)) = {worst_gap:.3e}")

    print("\n(T) thresholds c*(b) with LamD_c*(b) = 0, range ln4/A(c*) (R14 Theorem 2 / r103b):")
    print("    b       c*(b)      eps = ln4/A(c*)    r103b eps = ln4/max(g, 2c ln5 - g)")
    for b in (0.01, 0.05, 0.1, 0.2, 0.3, 0.4, 0.45, 0.49, 0.5, 0.75, 1.0):
        cs = cstar(b)
        print(f"  {b:5.2f}   {cs:.5f}   {L4/A(cs):.6f}           {L4/max(g(cs), 2*cs*log(5)-g(cs)):.6f}")

    print("\n(H) Hyp balance q + gamma = b at fixed c: best over theta of min(gamma_R14, b - q_R14) vs LamD*(b)")
    for c, b in ((11.5, 0.5), (14.5, 0.5), (10.0, 0.5), (4.9, 0.5), (6.0, 1.0)):
        ths = np.linspace(1e-4, 0.79, 200001)
        best = max(min(-2*F(th, c)/L4, b - 2*J(th)/L4) for th in ths[::20])
        # refine
        i = np.argmax([min(-2*F(th, c)/L4, b - 2*J(th)/L4) for th in ths[::20]])
        lo, hi = ths[max(0, i*20-40)], ths[min(len(ths)-1, i*20+40)]
        best = max(min(-2*F(th, c)/L4, b - 2*J(th)/L4) for th in np.linspace(lo, hi, 20001))
        print(f"    c = {c:5.2f}, b = {b}: best balanced gamma = {best:.6f};  LamD*(b) = {LamD_star(b, c)[0]:.6f}")

    print("\n(R) R14 rate table (kappa = 1/2): gamma(eps) = max_c LamD_c*(1/2) s.t. A(c) + gamma ln4 <= ln4/eps")
    for E in (10, 12, 14, 18):
        cc = brentq(lambda c: A(c) + LamD_star(0.5, c)[0]*L4 - E*L4, 5.0, 40)
        gm = LamD_star(0.5, cc)[0]
        print(f"    1/eps = {E}: c = {cc:.4f}, gamma = {gm:.5f}, eps*gamma = {gm/E:.6f}")
    def epsgam(c):
        gm = LamD_star(0.5, c)[0]
        return -(L4/(A(c) + gm*L4))*gm
    r = minimize_scalar(epsgam, bounds=(5.0, 20.0), method='bounded', options={'xatol': 1e-8})
    gm = LamD_star(0.5, r.x)[0]
    print(f"    best eps*gamma = {-r.fun:.6f} at c = {r.x:.4f}, 1/eps = {(A(r.x)+gm*L4)/L4:.3f}, gamma = {gm:.5f}")

    print("\n(C') conjectured form at fixed query exponent q (no balance), c = 11.5 and 14.5:")
    for c in (11.5, 14.5, 6.0):
        for q in (0.1, 0.3, 0.421, 0.6, 1.0):
            th = brentq(lambda th: 2*J(th)/L4 - q, 1e-9, 0.8)
            print(f"    c = {c:5.2f}, q = {q:5.3f}: gamma_R14(q) = {-2*F(th, c)/L4:.6f}, LamD*(q) = {LamD_star(q, c)[0]:.6f}")

if __name__ == "__main__":
    main()
