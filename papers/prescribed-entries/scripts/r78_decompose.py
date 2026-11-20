"""R78 steps 1-2 (r78.md): decompose the level-1 profile into its four sigma terms, and gamma_D of idealised
profiles with terms removed.

Exact-maximum formula (r74a.md Section 1): per part q, pi = 1/(q+2), z = (u, v, y),
    a = q pi - u + v, b = pi + u, o = pi - v,
    F_q(t; z) = -D + t [ (i) b h(pi/b) + (iv) u h(y/u) + (ii) (u - y) ln q + (iii) a h((v - y)/a) ],
    on P_q = {0 <= v <= pi, 0 <= y <= v, y <= u, u - y <= q pi};  G_q(t) = max_{P_q} F_q.
Lambda per CW coordinate at the mixture P0: L(t) = lam6 G_6(t) + lam7 G_7(t);
gamma_D = max_{t <= 0.3249} ( t/2 - L(t)/ln b_1 ),  ln b_1 = alpha(P0) ln a_1 (r74e.md (1)).
Variants: sigma with a subset of the four terms kept (the polytope P_q unchanged).
(1) step 1 table, (2) step 2 table.  Run: ~/.venv/bin/python r78_decompose.py > r78_decompose_out.txt
"""
import numpy as np
from scipy.optimize import minimize, minimize_scalar

LAM = {6: 7/19, 7: 12/19}
LNA1 = 0.725488559770971
ALPHA = 0.294597647050482
LNB1 = ALPHA*LNA1
TMAX = 0.3249


def ph(s):
    return s*np.log(s) if s > 0 else 0.0


def H2(w, s):            # w h(s/w) = phi(w) - phi(s) - phi(w - s)
    return ph(w) - ph(s) - ph(w - s)


def terms(q, u, v, y):
    pi = 1/(q + 2); a = q*pi - u + v; b = pi + u; o = pi - v
    D = ph(a) - a*np.log(q*pi) + ph(b) - b*np.log(pi) + ph(o) - o*np.log(pi)
    return D, (H2(b, pi), (u - y)*np.log(q), H2(a, v - y), H2(u, y))   # (i), (ii), (iii), (iv)


def G(q, t, keep=(1, 1, 1, 1), starts=None):
    """max of -D + t * sum kept terms over P_q; parametrised so the box is automatic."""
    pi = 1/(q + 2)
    def unpack(p):
        # v in (0, pi), y = v * s1, u = y + (q pi) * s2, s in (0,1) via logistic
        s = 1/(1 + np.exp(-np.asarray(p)))
        v = pi*s[0]; y = v*s[1]; u = y + q*pi*s[2]
        return u, v, y
    def neg(p):
        u, v, y = unpack(p)
        D, T = terms(q, u, v, y)
        return D - t*sum(k*x for k, x in zip(keep, T))
    best = None
    for p0 in (starts or [(-2, -3, -4), (-1, -1, -3), (0, -2, -2), (-3, -5, -6), (1, -1, -1), (-4, -0.5, -5)]):
        r = minimize(neg, p0, method="Nelder-Mead", options=dict(xatol=1e-12, fatol=1e-16, maxiter=20000,
                                                                  maxfev=40000))
        if best is None or r.fun < best.fun:
            best = r
    u, v, y = unpack(best.x)
    return -best.fun, (u, v, y)


def L(t, keep=(1, 1, 1, 1)):
    return sum(LAM[q]*G(q, t, keep)[0] for q in (6, 7))


def gammaD(keep):
    f = lambda t: -(t/2 - L(t, keep)/LNB1)
    ts = np.linspace(0.005, TMAX, 40)
    vals = [f(t) for t in ts]
    i = int(np.argmin(vals))
    lo, hi = ts[max(i - 1, 0)], ts[min(i + 1, len(ts) - 1)]
    r = minimize_scalar(f, bounds=(lo, hi), method="bounded", options=dict(xatol=1e-7))
    return r.x, -r.fun


def main():
    print("(1) step 1: maximiser of F_q(t; u, v, y) and the four sigma terms there (per CW coordinate)")
    print("    columns: t, q, u, v, y, -D, t*(i) pos.entropy b h(pi/b), t*(ii) (u-y) ln q, "
          "t*(iii) a h((v-y)/a), t*(iv) u h(y/u), sum, G_q(t); then shares of t*sigma")
    for t in (0.0196, 0.02, 0.05, 0.1, 0.2, 0.3):
        tot = 0.0
        for q in (6, 7):
            g, (u, v, y) = G(q, t)
            D, T = terms(q, u, v, y)
            s = -D + t*sum(T)
            tot += LAM[q]*g
            sh = [x/sum(T) for x in T]
            print(f"  t={t:.4f} q={q}: u={u:.5f} v={v:.5f} y={y:.2e} | -D={-D:.6f} | "
                  + " ".join(f"{t*x:.6f}" for x in T) + f" | sum={s:.7f} G={g:.7f} | shares "
                  + " ".join(f"{x:.3f}" for x in sh))
        print(f"  t={t:.4f} mixture P0: Lambda per coordinate = {tot:.7f}, per ln a = {tot/LNA1:.7f}, "
              f"t/2 - Lambda/ln b_1 = {t/2 - tot/LNB1:.6f}")

    print("\n(2) step 2: idealised profiles (sigma with terms removed, polytope P_q kept), mixture P0")
    print(f"    ln b_1 = {LNB1:.6f}, t <= {TMAX}; eps*gamma = eps1*gamma, eps1 = 1/(1/alpha + gamma)")
    L01 = L(0.1)
    variants = [("present (i)+(ii)+(iii)+(iv)", (1, 1, 1, 1)),
                ("floor: (i) only", (1, 0, 0, 0)),
                ("(ii) removed", (1, 0, 1, 1)),
                ("(iii) removed", (1, 1, 0, 1)),
                ("(iv) removed", (1, 1, 1, 0)),
                ("(ii),(iii) removed", (1, 0, 0, 1)),
                ("(ii),(iv) removed", (1, 0, 1, 0)),
                ("(iii),(iv) removed", (1, 1, 0, 0))]
    for name, keep in variants:
        l01 = L(0.1, keep)
        tb, gb = gammaD(keep)
        e1 = 1/(1/ALPHA + gb)
        print(f"  {name:30s} Lambda(0.1) = {l01:.6f} ({l01/L01:.3f} of present)  t_opt = {tb:.4f}  "
              f"gamma_D = {gb:.6f}  eps*gamma = {e1*gb:.6f}{'  (t at cap)' if tb > TMAX - 1e-3 else ''}")


if __name__ == "__main__":
    main()
