"""R112 (r112.md): exact small-t asymptotics of the leaf-degree profile Lambda(t) and of L(b), gamma at small budgets.

Families (formulas as in r78.md / r74a.md and r105.md):
 (M) merged level-1 CW family, per part q (pi = 1/(q+2)), per CW coordinate, natural log:
       G_q(t) = max_{u,v,y} -D + t [ b h(pi/b) + (u-y) ln q + a h((v-y)/a) + u h(y/u) ],
       a = q pi - u + v, b = pi + u, o = pi - v,  D = KL((a,b,o) || (q pi, pi, pi)).
     Mixture P0: Lambda = lam6 G_6 + lam7 G_7, units of ln D: Lambda_D = Lambda / ln b_1 (ln b_1 = alpha ln a_1).
     Claimed asymptotic (r112.md Section 1):  G_q(t) = pi t^2 (W^2 + 2W) (1 + O(t W)),  W = W_0(q/t)  (Lambert W),
     leading term pi t^2 ln^2(1/t).
 (G) Schoenhage's G (r105.md Section 1): Lambda_{G,c}(t) = (2/ln4) max_x [F(x) + t G(x)] (units ln D).
     c = 5: claimed (4/(5 ln4)) t^2 (W^2 + 2W), W = W_0(5/t).
     c > 5: claimed (2/ln4) t (c-1) exp(-s/t) (1 + o(1)), s = ln((c-1)/4) (exponentially flat);
            L_{G,c}(b) ~ s b / ln(1/b).
mpmath is not installed in ~/.venv, so everything is in doubles with cancellation-free forms:
KL via x* kl1(x/x* - 1), kl1(e) = (1+e) log1p(e) - e (series for small e); binary entropies via log1p.
The maximisations are solved by their stationarity equations in log variables (the objectives are concave,
r59p2_typical.py, so the stationary point is the maximum).  Cross-checks: r78_decompose.G (Nelder-Mead) at moderate t,
r78's certified values, r105's printed L(kappa), r103a's printed Lambda_num, r105_v1.LamD for G.
Run: ~/.venv/bin/python r112_smallt.py > r112_smallt_out.txt   (single process, under a minute)
"""
import sys, os
from math import log, log1p, exp, sqrt
import numpy as np
from scipy.optimize import fsolve, brentq
from scipy.special import lambertw
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

LAM = {6: 7/19, 7: 12/19}
LNA1 = 0.725488559770971
ALPHA = 0.294597647050482
LNB1 = ALPHA*LNA1
L4 = log(4)


def W0(z):
    return float(lambertw(z).real)


def kl1(e):
    """(1+e) log1p(e) - e, stable for small e."""
    if abs(e) < 1e-4:
        return e*e/2 - e**3/6 + e**4/12 - e**5/20
    return (1 + e)*log1p(e) - e


def Fq(q, t, u, v, y):
    pi = 1/(q + 2); a = q*pi - u + v; b = pi + u; o = pi - v
    D = q*pi*kl1((v - u)/(q*pi)) + pi*kl1(u/pi) + pi*kl1(-v/pi)
    i = pi*log1p(u/pi) + u*log((pi + u)/u)                 # H2(b, pi)
    ii = (u - y)*log(q)
    r = q*pi - u + y                                        # a - (v - y)
    iii = (v - y)*log(a/(v - y)) + r*log1p((v - y)/r)       # H2(a, v - y)
    iv = y*log(u/y) - (u - y)*log1p(-y/u)                   # H2(u, y)
    return -D + t*(i + ii + iii + iv)


def grad(q, t, u, v, y):
    pi = 1/(q + 2); a = q*pi - u + v; b = pi + u; o = pi - v; lq = log(q)
    dDu = log1p(u/pi) - log1p((v - u)/(q*pi)); dDv = log1p((v - u)/(q*pi)) - log1p(-v/pi)
    r = q*pi - u + y
    dEu = log(b/u) + lq + log(r/a) - log1p(-y/u)
    dEv = log(a/(v - y))
    dEy = -lq + log((v - y)/r) + log((u - y)/y)
    return np.array([-dDu + t*dEu, -dDv + t*dEv, t*dEy])


def Gq(q, t):
    """exact G_q(t) via the stationarity equations in log variables (scaled by 1/t, all O(log))."""
    pi = 1/(q + 2)
    W = W0(q/t)
    u0 = pi*t*W; v0 = u0; y0 = u0*v0/(q*q*pi)
    def f(z):
        u, v, y = np.exp(z)
        if y >= min(u, v) or v >= pi:
            return np.array([1e3, 1e3, 1e3])
        return grad(q, t, u, v, y)/t
    z = fsolve(f, np.log([u0, v0, y0]), xtol=1e-14, maxfev=20000)
    u, v, y = np.exp(z)
    res = np.max(np.abs(f(z)))
    return Fq(q, t, u, v, y), (u, v, y, res)


def asym_q(q, t):
    W = W0(q/t)
    return t*t*(W*W + 2*W)/(q + 2)


def Lam_mix(t):
    return sum(LAM[q]*Gq(q, t)[0] for q in (6, 7))


def Lam_mix_asym(t):
    return sum(LAM[q]*asym_q(q, t) for q in (6, 7))


def legendre(LamD, b, tlo=1e-12, thi=0.3249):
    """sup_{t in [tlo, thi]} t b - LamD(t); golden section on log t, plus a check of the endpoints."""
    f = lambda s: exp(s)*b - LamD(exp(s))
    lo, hi = log(tlo), log(thi)
    gr = (sqrt(5) - 1)/2
    x1 = hi - gr*(hi - lo); x2 = lo + gr*(hi - lo); f1 = f(x1); f2 = f(x2)
    for _ in range(120):
        if f1 < f2:
            lo, x1, f1 = x1, x2, f2; x2 = lo + gr*(hi - lo); f2 = f(x2)
        else:
            hi, x2, f2 = x2, x1, f1; x1 = hi - gr*(hi - lo); f1 = f(x1)
    s = (lo + hi)/2
    cands = [(f(s), exp(s)), (f(log(thi)), thi)]
    return max(cands)


# ---- Schoenhage's G, cancellation-free ----
def FG(x, c):
    return x*log(4/(c - 1)) - kl1(-x) - (c - 1)*kl1(x/(c - 1))


def GG(x, c):
    return x*log((c - 1 + x)/x) + (c - 1)*log1p(x/(c - 1))


def LamG(t, c):
    d = lambda lx: log(4*(1 - exp(lx))/(c - 1 + exp(lx))) + t*log((c - 1 + exp(lx))/exp(lx))
    lo, hi = -700.0, log(1 - 1e-15)
    if d(lo) < 0:          # maximiser below exp(-700): Lambda is 0 to double precision
        return 0.0, 0.0
    lx = brentq(d, lo, hi, xtol=1e-15, rtol=1e-15, maxiter=500)
    x = exp(lx)
    return 2*(FG(x, c) + t*GG(x, c))/L4, x


def main():
    print("(0) cross-check of the exact merged evaluator against r78_decompose.G (Nelder-Mead) and r78's values")
    from r78_decompose import G as G78
    for t in (0.0196, 0.05, 0.1):
        for q in (6, 7):
            e, (u, v, y, res) = Gq(q, t); nm = G78(q, t)[0]
            print(f"  q={q} t={t}: stationary {e:.13f}  Nelder-Mead {nm:.13f}  diff {e - nm:.1e}  residual {res:.1e}")
    print("  r78/r74a certified: G_6(0.0196) = 0.0012944331521, G_7(0.0196) = 0.0012082016806")

    print("\n(1) merged family, per part: exact G_q(t) vs the Lambert-W form pi t^2 (W^2+2W), W = W(q/t),"
          "\n    and vs the leading term pi t^2 ln^2(1/t); u, v at the maximiser vs pi t W; y/u")
    for q in (6, 7):
        pi = 1/(q + 2)
        for t in (1e-12, 1e-8, 1e-6, 1e-4, 1e-3, 0.01, 0.0196, 0.05, 0.1, 0.2, 0.3):
            e, (u, v, y, res) = Gq(q, t); a = asym_q(q, t); lead = pi*t*t*log(1/t)**2
            W = W0(q/t)
            print(f"  q={q} t={t:<7.3g}: G={e:.8e}  W-form ratio {e/a:.6f}  leading ratio {e/lead:.4f}  "
                  f"tW={t*W:.2e}  u/(pi t W)={u/(pi*t*W):.5f}  v/(pi t W)={v/(pi*t*W):.5f}  y/u={y/u:.2e}  res {res:.0e}")

    C_nat = sum(LAM[q]/(q + 2) for q in (6, 7))
    C_D = C_nat/LNB1
    print(f"\n(2) mixture P0: C (per CW coordinate, nats) = sum lam_q/(q+2) = {C_nat:.10f}; "
          f"per ln a_1: {C_nat/LNA1:.10f}; per ln D (= / ln b_1): C_D = {C_D:.10f}")
    print(f"    the proved bound Lambda_pr = sum lam_q t^2 ln^2(4eq/t)/ln a_1 has leading constant 1/ln a_1 = "
          f"{1/LNA1:.6f} per ln K, i.e. {1/C_nat:.4f} times the true constant")
    print("    Lambda per ln K at sample t: exact, W-form, r103a's printed Lambda_num, Lambda_pr")
    printed = {0.001: 9.7561e-06, 0.01: 5.4355e-04, 0.02: 1.7684e-03, 0.05: 8.1967e-03, 0.1: 2.5641e-02}
    for t, pv in printed.items():
        ex = Lam_mix(t)/LNA1; wa = Lam_mix_asym(t)/LNA1
        pr = sum(LAM[q]*t*t*log(4*np.e*q/t)**2 for q in (6, 7))/LNA1
        print(f"  t={t:<6}: exact {ex:.5e}  W-form {wa:.5e}  Lambda_num {pv:.4e}  Lambda_pr {pr:.4e}")

    print("\n(3) L(kappa) = sup_t (t kappa - Lambda/ln b_1): exact profile, W-form, leading asymptotic "
          "kappa^2/(4 C_D ln^2(1/kappa)), and r105's printed values (certified grid)")
    r105 = {0.001: None, 0.01: 4.715e-7, 0.05: 1.772e-5, 0.1: 8.729e-5, 0.2: 4.210e-4, 0.5: 3.998e-3}
    for k, pv in r105.items():
        Le, te = legendre(lambda t: Lam_mix(t)/LNB1, k)
        La, ta = legendre(lambda t: Lam_mix_asym(t)/LNB1, k)
        lead = k*k/(4*C_D*log(1/k)**2)
        print(f"  kappa={k:<6}: exact L={Le:.5e} (t*={te:.3e})  W-form {La:.5e} (t*={ta:.3e})  ratio {Le/La:.4f}"
              f"  leading {lead:.3e} (ratio exact/leading {Le/lead:.3f})  r105 {pv}")
    print("    convergence of the leading term: L_Wform(kappa) / [kappa^2/(4 C_D ln^2(1/kappa))]")
    for k in (1e-2, 1e-4, 1e-8, 1e-16, 1e-32, 1e-64):
        La, ta = legendre(lambda t: Lam_mix_asym(t)/LNB1, k, tlo=1e-300)
        lead = k*k/(4*C_D*log(1/k)**2)
        print(f"    kappa={k:<7.0e}: ratio {La/lead:.4f}   (t* = {ta:.3e})")

    print("\n(4) Schoenhage's G: exact Lambda_{G,c}(t) (units ln D) vs asymptotics")
    from r105_v1 import LamD as LamD105
    for t in (0.01, 0.1):
        for c in (5.0, 5.5, 8.0):
            print(f"  cross-check c={c} t={t}: here {LamG(t, c)[0]:.12e}  r105_v1.LamD {LamD105(t, c):.12e}")
    c = 5.0
    for t in (1e-12, 1e-8, 1e-6, 1e-4, 1e-3, 0.01, 0.05, 0.1, 0.2):
        e, x = LamG(t, c); W = W0(5/t)
        a = 4*t*t*(W*W + 2*W)/(5*L4); lead = 4*t*t*log(1/t)**2/(5*L4)
        print(f"  c=5 t={t:<7.3g}: Lambda={e:.8e}  W-form ratio {e/a:.6f}  leading ratio {e/lead:.4f}  "
              f"x/((4/5) t W) = {x/(0.8*t*W):.5f}")
    for c in (5.1, 5.5, 6.0, 8.0, 14.5):
        s = log((c - 1)/4)
        for t in (0.005, 0.01, 0.02, 0.05, 0.1):
            e, x = LamG(t, c)
            a = 2*t*(c - 1)*exp(-s/t)/L4
            print(f"  c={c:<5} t={t:<6}: Lambda={e:.5e}  exp-form {a:.5e}  ratio {e/a if a > 0 else float('nan'):.4f}")

    print("\n(5) L_{G,c}(b) at small b (t in [0,1]) vs s b / ln(1/b), s = ln((c-1)/4); and c = 5 vs its W-form")
    for c in (5.0, 5.5, 6.0, 10.218, 14.5):
        s = log((c - 1)/4)
        for b in (1e-2, 1e-3, 1e-4, 1e-6):
            Lg, tg = legendre(lambda t: LamG(t, c)[0], b, tlo=1e-14, thi=1.0)
            if c == 5.0:
                La, _ = legendre(lambda t: 4*t*t*(W0(5/t)**2 + 2*W0(5/t))/(5*L4), b, tlo=1e-16, thi=1.0)
                print(f"  c=5      b={b:<6}: L={Lg:.5e} (t*={tg:.3e})  W-form {La:.5e}  ratio {Lg/La:.4f}")
            else:
                ref = s*b/log(1/b)
                print(f"  c={c:<6} b={b:<6}: L={Lg:.5e} (t*={tg:.3e})  s b/ln(1/b) = {ref:.5e}  ratio {Lg/ref:.4f}")

    print("\n(6) small budgets: merged family vs G at c = 6 (each in units of its own ln D)")
    for b in (0.01, 0.05, 0.1):
        Lm, _ = legendre(lambda t: Lam_mix(t)/LNB1, b)
        Lg6, _ = legendre(lambda t: LamG(t, 6.0)[0], b, tlo=1e-14, thi=1.0)
        print(f"  b={b}: merged L = {Lm:.4e}   G at c=6 L = {Lg6:.4e}")

    print("\n(7) parametric closed form of the W-form Legendre transform: with Lambda_D = sum_q C_q t^2 (W_q^2 + 2W_q),"
          "\n    b = sum_q 2 C_q t W_q (W_q + 1), L = sum_q C_q t^2 W_q^2 (C_q = lam_q/((q+2) ln b_1), W_q = W(q/t));"
          "\n    single part: L = b^2 / (4 C (1 + W)^2).  Compared with the numerical sup of the W-form and the exact L")
    Cq = {q: LAM[q]/((q + 2)*LNB1) for q in (6, 7)}
    for k in (0.001, 0.01, 0.1, 0.5):
        tt = brentq(lambda t: sum(2*Cq[q]*t*W0(q/t)*(W0(q/t) + 1) for q in (6, 7)) - k, 1e-30, 1.0, xtol=1e-300,
                    rtol=1e-15)
        Lp = sum(Cq[q]*tt*tt*W0(q/tt)**2 for q in (6, 7))
        La, _ = legendre(lambda t: Lam_mix_asym(t)/LNB1, k)
        Le, _ = legendre(lambda t: Lam_mix(t)/LNB1, k)
        Weff = sum(Cq[q]*W0(q/tt) for q in (6, 7))/sum(Cq.values())
        one = k*k/(4*sum(Cq.values())*(1 + Weff)**2)
        print(f"  kappa={k:<6}: t*={tt:.4e}  parametric L={Lp:.6e}  sup of W-form {La:.6e}  exact {Le:.6e}  "
              f"b^2/(4C(1+W_eff)^2) = {one:.6e} (W_eff = {Weff:.3f}, ln(1/kappa) = {log(1/k):.3f})")

    print("\n(8) G just above c = 5: uniform local model (2/ln4) max_x [-s x - (5/8) x^2 + t x ln(4e/x)] vs exact")
    for c in (5.01, 5.1, 5.5):
        s = log((c - 1)/4)
        for t in (1e-4, 1e-3, 0.005, 0.01, 0.02, 0.05):
            e, x = LamG(t, c)
            d = lambda lx: -s - 1.25*exp(lx) + t*log(4/exp(lx))
            if d(-700) < 0:
                print(f"  c={c:<5} t={t:<7}: exact {e:.5e}  local model below 1e-300 (maximiser x < e^-700)")
                continue
            lx = brentq(d, -700, log(4) - 1e-12)
            xx = exp(lx); m = 2*(-s*xx - 0.625*xx*xx + t*xx*log(4*np.e/xx))/L4
            print(f"  c={c:<5} t={t:<7}: exact {e:.5e}  local model {m:.5e}  ratio {e/m if m > 0 else float('nan'):.4f}")

    print("\n(9) G at c > 5, refined small-b form: L ~ s b/(1 + sigma), sigma = ln(A (1 + sigma)/b), A = 2(c-1)/ln4")
    for c in (5.5, 6.0, 10.218, 14.5):
        s = log((c - 1)/4); A = 2*(c - 1)/L4
        for b in (1e-2, 1e-4, 1e-6):
            sg = 1.0
            for _ in range(200):
                sg = log(A*(1 + sg)/b)
            Lg, tg = legendre(lambda t: LamG(t, c)[0], b, tlo=1e-14, thi=1.0)
            print(f"  c={c:<6} b={b:<6}: exact L={Lg:.5e}  s b/(1+sigma) = {s*b/(1 + sg):.5e}  ratio {Lg/(s*b/(1 + sg)):.4f}"
                  f"  (t* = {tg:.3e}, s/(sigma) = {s/sg:.3e})")


if __name__ == "__main__":
    main()


def hybrid():
    """(10) argued obstruction: Kronecker product of merged-family coordinates (weight w) with G-tile units at c > 5
    (weight 1 - w).  Profiles add over factors; per unit: merged coordinate ln K = ln a_1, ln D = ln b_1, Lambda in nats;
    G unit (per m): ln K = g(c), ln D = ln 4, Lambda nats = ln4 * Lambda_{G,D} (exponentially flat for c > 5).
    alpha_hyb = ln D / ln K; constant on the t^2 ln^2 scale in units of ln D: C_D = w C_nat / ln D_hyb."""
    print("\n(10) hybrid merged x G(c): rank exponent alpha_hyb and C_D (t^2 (W^2+2W) scale, units ln D)")
    C_nat = sum(LAM[q]/(q + 2) for q in (6, 7))
    def gfun(c):
        h = -(1/c)*log(1/c) - (1 - 1/c)*log(1 - 1/c)
        return c*h + (c - 1)*L4
    for c in (5.05, 5.5):
        for w in (1.0, 0.9, 0.7, 0.5, 0.3, 0.1, 0.0):
            lnD = w*LNB1 + (1 - w)*L4; lnK = w*LNA1 + (1 - w)*gfun(c)
            print(f"  c={c:<5} w={w:<4}: alpha_hyb={lnD/lnK:.5f}  C_D={w*C_nat/lnD:.5f}  "
                  f"(ratio to merged {w*C_nat/lnD/(C_nat/LNB1):.4f})")


if __name__ == "__main__":
    hybrid()
