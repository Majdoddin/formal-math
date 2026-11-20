r"""R150 stage 3a (detection route): best eps*gamma of the characteristic-2 data structure (T4 + P3, r61b.md) in the
form the reductions use, |W| <= N^2/sqrt(D) wanted entries (kappa = 1/2).  Numerical (rate values), except where the
point is an instance of a proved statement (split form: Corollary 3 of r61b.md holds for every c > 4, theta < 3/4).

Model (per level, natural logs; L levels, type p = (p0, p1, p2, pw), d = pw L inner levels, D = 2^d):
  encodings (full, 4^L per band and relabeling):   1/eps = (ln4 - H(p)/2)/(pw ln2) + gamma
      (product type p = ((1-r)^2, r(1-r), r(1-r), r^2): H(p)/2 = H2(r), the band size; deterministic covering Pi_L;
       general type: about f^{-1/2} random relabelings per side, r61b.md 6.2; randomized covering)
  split box count:    gamma_box = theta log2(1/lambda), lambda = pw/min(p0, p1, p2)       (r61b.md Cor. 3)
  exact box count:    gamma_box = -B(p, theta)/(pw ln2), B = max_{v4 <= 1-theta} H(t(v)) - H(p)  (r61b.md 6.4)
  queries:            q(theta) = (H(theta) + theta ln3)/ln2, |W| queries cost N^2 D^{q - 1/2}
  data structure:     gamma = min(gamma_box, 1/2 - q)
  exact leaf count (prescribed W, pruned recursion, no boxes): gamma = -Lam(p)/(pw ln2),
                      Lam(p) = max_v min(pw H(v) - pw ln2/2, H(t(v)) - H(p))                   (r61b.md 6.2)
  t(v) = (p0 + pw v1, p1 + pw v2, p2 + pw v3, pw v4).
Saving of every reduction that keeps the whole saving: eps*gamma (exponent 2 - eps*gamma, 3 - eps*gamma).
Usage: python3 r150d_rates.py > r150d_rates_out.txt
"""
import math
import numpy as np
from scipy.optimize import minimize, brentq, minimize_scalar

LN2, LN3, LN4 = math.log(2), math.log(3), math.log(4)


def Hn(v):
    return -sum(x * math.log(x) for x in v if x > 0)


def H2(x):
    return Hn([x, 1 - x])


def qof(th):
    return (H2(th) + th * LN3) / LN2


def prod_type(r):
    return ((1 - r) ** 2, r * (1 - r), r * (1 - r), r * r)


def eps_of(p, g, Eenc=LN4):
    """encoding range with saving g: 1/eps = (Eenc - H(p)/2)/(pw ln2) + g."""
    return 1.0 / ((Eenc - Hn(p) / 2) / (p[3] * LN2) + g)


# ---------- exact box exponent B(p, theta) by water-filling (closed form) ----------
def waterfill(lows, total):
    """t_i = max(low_i, tau) with sum t_i = total; returns t."""
    lows = sorted(lows)
    # find tau
    k = len(lows)
    for j in range(k + 1):
        # tau >= lows[j-1] and tau <= lows[j]; t = lows[j:] kept, first j raised to tau
        rest = sum(lows[j:])
        tau = (total - rest) / j if j > 0 else None
        if j == 0:
            if rest >= total - 1e-15:
                return None  # infeasible unless equal
            continue
        lo = lows[j - 1]; hi = lows[j] if j < k else float('inf')
        if lo - 1e-15 <= tau <= hi + 1e-15:
            return tau
    return None


def Bexp(p, th):
    """max over v in simplex with v4 <= 1-th of H(t(v)) - H(p)."""
    p0, p1, p2, pw = p
    # unconstrained: t_i = max(p_i, tau) (i = 0,1,2), t_w = tau, sum = 1
    tau = waterfill([p0, p1, p2, 0.0], 1.0)
    if tau <= pw * (1 - th) + 1e-15:
        t = [max(p0, tau), max(p1, tau), max(p2, tau), tau]
    else:
        tw = pw * (1 - th)
        tau2 = waterfill([p0, p1, p2], 1.0 - tw)
        t = [max(p0, tau2), max(p1, tau2), max(p2, tau2), tw]
    return Hn(t) - Hn(p)


def Bexp_check(p, th):
    """SLSQP cross-check of Bexp."""
    p0, p1, p2, pw = p
    hp = Hn(p)
    cons = [{'type': 'eq', 'fun': lambda v: sum(v) - 1}, {'type': 'ineq', 'fun': lambda v: 1 - th - v[3]}]
    best = -1e9
    for start in [np.array([.25] * 4), np.array([.1, .1, .1, .7]), np.array([.3, .3, .3, .1])]:
        r = minimize(lambda v: -(Hn([p0 + pw * v[0], p1 + pw * v[1], p2 + pw * v[2], pw * max(v[3], 0)]) - hp),
                     start, method='SLSQP', bounds=[(0, 1)] * 4, constraints=cons,
                     options={'ftol': 1e-14, 'maxiter': 1000})
        if -r.fun > best:
            best = -r.fun
    return best


# ---------- exact leaf exponent Lam(p) by minimax ----------
def inner_max(p, mu, kappa=0.5):
    """max over the simplex of mu*(pw H(v) - kappa pw ln2) + (1-mu)*(H(t(v)) - H(p)), by KKT:
    mu ln v_i + (1-mu) ln t_i = C for all i."""
    p0, p1, p2, pw = p
    lows = [p0, p1, p2]
    if mu <= 1e-12:
        val = Bexp(p, 0.0)
        return val
    if mu >= 1 - 1e-12:
        return pw * LN4 - kappa * pw * LN2

    lpw = math.log(pw)

    def v_of(C):
        vs = []
        y0 = C - (1 - mu) * lpw  # root for lo = 0; an upper bound of the root for lo > 0
        for lo in lows:
            # solve g(y) = mu y + (1-mu) ln(lo + pw e^y) - C = 0, y = ln v; g convex increasing, g(y0) >= 0:
            # Newton from y0 decreases monotonically to the root
            y = y0
            for _ in range(100):
                ey = math.exp(y)
                s = lo + pw * ey
                g = mu * y + (1 - mu) * math.log(s) - C
                gp = mu + (1 - mu) * pw * ey / s
                step = g / gp
                y -= step
                if abs(step) < 1e-13:
                    break
            vs.append(math.exp(y))
        vs.append(math.exp(y0))
        return vs
    a, b = -60.0, 10.0
    for _ in range(80):
        m = (a + b) / 2
        if sum(v_of(m)) > 1:
            b = m
        else:
            a = m
    v = v_of((a + b) / 2)
    s = sum(v); v = [x / s for x in v]
    t = [p0 + pw * v[0], p1 + pw * v[1], p2 + pw * v[2], pw * v[3]]
    f1 = pw * Hn(v) - kappa * pw * LN2
    f2 = Hn(t) - Hn(p)
    return mu * f1 + (1 - mu) * f2


def Lam(p, kappa=0.5):
    r = minimize_scalar(lambda mu: inner_max(p, mu, kappa), bounds=(0.0, 1.0), method='bounded',
                        options={'xatol': 1e-10})
    return min(r.fun, inner_max(p, 0.0, kappa), inner_max(p, 1.0, kappa))


def Lam_check(p, kappa=0.5):
    """direct: maximise s subject to s <= f1(v), s <= f2(v) (SLSQP)."""
    p0, p1, p2, pw = p
    hp = Hn(p)
    f1 = lambda v: pw * Hn(np.clip(v, 1e-300, None)) - kappa * pw * LN2
    f2 = lambda v: Hn([p0 + pw * v[0], p1 + pw * v[1], p2 + pw * v[2], pw * max(v[3], 0)]) - hp
    best = -1e9
    for start in [np.array([.25] * 4 + [0.]), np.array([.03, .03, .03, .91, 0.]), np.array([.1, .1, .1, .7, 0.])]:
        cons = [{'type': 'eq', 'fun': lambda x: sum(x[:4]) - 1},
                {'type': 'ineq', 'fun': lambda x: f1(x[:4]) - x[4]},
                {'type': 'ineq', 'fun': lambda x: f2(x[:4]) - x[4]}]
        r = minimize(lambda x: -x[4], start, method='SLSQP', bounds=[(1e-12, 1)] * 4 + [(-5, 5)],
                     constraints=cons, options={'ftol': 1e-14, 'maxiter': 2000})
        if r.success and r.x[4] > best:
            best = r.x[4]
    return best


# ---------- saving per model ----------
def gamma_ds(p, exact=True):
    """data structure: max over theta of min(gamma_box(theta), 1/2 - q(theta)); returns (gamma, theta)."""
    pw = p[3]
    if exact:
        gb = lambda th: -Bexp(p, th) / (pw * LN2)
    else:
        lam = pw / min(p[0], p[1], p[2])
        if lam >= 1:
            return 0.0, None
        gb = lambda th: th * math.log2(1 / lam)
    gq = lambda th: 0.5 - qof(th)
    h = lambda th: gb(th) - gq(th)
    thmax = brentq(lambda th: qof(th) - 0.5, 1e-9, 0.5)  # q(theta) = 1/2
    if h(thmax) < 0:
        return max(0.0, gb(thmax)), thmax
    if h(1e-9) >= 0:
        return max(0.0, gq(1e-9)), 1e-9
    th = brentq(h, 1e-9, thmax, xtol=1e-14)
    return max(0.0, gq(th)), th


def gamma_leaf(p):
    lam = Lam(p)
    return max(0.0, -lam / (p[3] * LN2))


def rate(p, model, Eenc=LN4):
    if model == 'split':
        g, th = gamma_ds(p, exact=False)
    elif model == 'box':
        g, th = gamma_ds(p, exact=True)
    else:
        g, th = gamma_leaf(p), None
    if g <= 0:
        return 0.0, 0.0, 0.0, th
    e = eps_of(p, g, Eenc)
    return e * g, e, g, th


def opt_product(model, Eenc=LN4):
    rs = np.linspace(0.15, 0.60, 181)
    vals = [rate(prod_type(r), model, Eenc)[0] for r in rs]
    i = int(np.argmax(vals))
    r = minimize_scalar(lambda x: -rate(prod_type(x), model, Eenc)[0],
                        bounds=(rs[max(i - 1, 0)], rs[min(i + 1, len(rs) - 1)]), method='bounded',
                        options={'xatol': 1e-9})
    return r.x, rate(prod_type(r.x), model, Eenc)


def opt_general(model, Eenc=LN4, start=None):
    """p = (p0, p1, p1, pw), maximise eps*gamma."""
    def neg(y):
        p0, pw = y
        p1 = (1 - p0 - pw) / 2
        if min(p0, pw, p1) <= 1e-4:
            return 1.0
        return -rate((p0, p1, p1, pw), model, Eenc)[0]
    best = (1.0, None)
    if start is None:
        for pw in np.linspace(0.06, 0.30, 25):
            for p0 in np.linspace(0.20, 0.70, 26):
                v = neg((p0, pw))
                if v < best[0]:
                    best = (v, (p0, pw))
        start = best[1]
    r = minimize(neg, np.array(start), method='Nelder-Mead', options={'xatol': 1e-8, 'fatol': 1e-11, 'maxiter': 2000})
    p0, pw = r.x
    p1 = (1 - p0 - pw) / 2
    p = (p0, p1, p1, pw)
    return p, rate(p, model, Eenc)


def main():
    print('R150 stage 3a: characteristic-2 rates eps*gamma in the form |W| <= N^2/sqrt(D) (numerical).\n')
    # cross-checks against r61b
    print('Cross-checks:')
    p = prod_type(0.5)
    print(f'  Lam at rho = 1/2: Lam/(pw ln2) = {Lam(p) / (p[3] * LN2):+.6f} (r61b_range_out: -0.005268); '
          f'SLSQP: {Lam_check(p) / (p[3] * LN2):+.6f}')
    for (r, th) in [(0.5, 0.01), (0.505, 0.05), (0.51, 0.1), (0.4, 0.07), (0.35, 0.06)]:
        p = prod_type(r)
        print(f'  B(rho={r}, theta={th}) = {Bexp(p, th):+.8f}, SLSQP {Bexp_check(p, th):+.8f}')
    for r in [0.3, 0.4, 0.45]:
        p = prod_type(r)
        print(f'  Lam(rho={r}) minimax {Lam(p):+.8f}, SLSQP {Lam_check(p):+.8f}')
    # split form at eps = 1/8 should reproduce r61b's 0.0519 (kappa = 1/2 column): fix eps, max gamma
    def best_gamma_at_eps(eps):
        best = 0.0
        for r in np.linspace(0.25, 0.49, 2401):
            p = prod_type(r)
            g, th = gamma_ds(p, exact=False)
            # largest g' <= g with eps_of(p, g') >= eps
            gmax = 1 / eps - (LN4 - Hn(p) / 2) / (p[3] * LN2)
            best = max(best, min(g, gmax))
        return best
    for inv in [6, 8, 10]:
        print(f'  split form, eps = 1/{inv}: best gamma = {best_gamma_at_eps(1 / inv):.5f} '
              f'(r61b table, kappa = 0.5: {dict([(6, 0.0340), (8, 0.0519), (10, 0.0635)])[inv]})')
    print()
    print('Product types (deterministic covering Pi_L), full encodings:')
    out = {}
    for model in ['split', 'box', 'leaf']:
        r, (eg, e, g, th) = opt_product(model)
        out[model] = (r, eg, e, g, th)
        ths = f', theta = {th:.5f}, q = {qof(th):.5f}' if th else ''
        print(f'  {model:5s}: max eps*gamma = {eg:.7f} at rho = {r:.5f} (c = {1 / r ** 2:.3f}): eps = {e:.6f} '
              f'(1/eps = {1 / e:.4f}), gamma = {g:.6f}{ths}')
    print()
    print('General types p = (p0, p1, p1, pw) (randomized covering by ~f^{-1/2} relabelings per side), full encodings:')
    for model in ['split', 'box', 'leaf']:
        p, (eg, e, g, th) = opt_general(model)
        ths = f', theta = {th:.5f}, q = {qof(th):.5f}' if th else ''
        print(f'  {model:5s}: max eps*gamma = {eg:.7f} at p = ({p[0]:.5f}, {p[1]:.5f}, {p[1]:.5f}, {p[3]:.5f}): '
              f'eps = {e:.6f} (1/eps = {1 / e:.4f}), gamma = {g:.6f}{ths}')
    print()
    # profile over eps for the product box model
    print('Profile (product types, exact box count): eps*gamma along rho')
    for r in [0.25, 0.28, 0.30, 0.32, 0.34, 0.36, 0.38, 0.40, 0.42, 0.45]:
        rows = []
        for model in ['split', 'box', 'leaf']:
            eg, e, g, th = rate(prod_type(r), model)
            rows.append(f'{model} {eg:.6f} (eps {e:.4f}, g {g:.5f})')
        print(f'  rho = {r:.2f}: ' + ';  '.join(rows))


if __name__ == '__main__':
    main()
