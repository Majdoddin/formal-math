r"""R155: shared definitions for the pruned band encoding of T4 + P3 in characteristic 2 (r155-pruned-enc.md).

Letters per level (index 0, 1, 2):  left  s0 = x0, s1 = x1, s2 = p0;   right s0 = y0, s1 = y1, s2 = q0.
P3's level forms in characteristic 2 (r61b.md Section 1), as the sets of letters with coefficient 1:
  left:  term 1 = x0 + x1, term 2 = x0 + p0, term 3 = x1, term 4 = x0
  right: term 1 = y0,      term 2 = y1,      term 3 = y0 + q0, term 4 = y0 + y1
Support of a band's array (r61b.md 4.3): left strings with #(s1, s2) = a (= n2 + d, the row size) and #s2 <= d;
right strings with #(s1, s2) = b (= n1 + d) and #s2 <= d.  Relevant leaves: #1 >= n0, #2 >= n1, #3 >= n2.

E_side(p): the concave program of calc/r150d_prunedenc.py, written once more here, in two forms:
  primal  max Hm(u) + Hm(w) over (pi, pi') >= 0 on compatible (term, letter) pairs, sum pi + sum pi' = 1,
          in-letters of pi and pi' = size, marked letters <= pw, u + u' >= (p0, p1, p2)
          (u = term marginal of pi, u' = term marginal of pi', w = letter marginal of pi');
  dual    min over (nu free, zeta >= 0, eta1..3 >= 0) of
          Phi = nu*size + zeta*pw - eta.(p0,p1,p2) + max(ln sum_t e^{a_t}, ln sum_s e^{b_s}),
          c_ts = eta_t - nu [s in-letter] - zeta [s marked]  (eta_4 = 0),
          a_t = max_{s compatible with t} c_ts,  b_s = max_{t compatible with s} c_ts.
Weak duality (any multipliers give an upper bound) is proved in r155-pruned-enc.md Section 1.4.
"""
import math
from itertools import product
import numpy as np
from scipy.optimize import minimize

LN2 = math.log(2)

# compatible (term, letter) pairs; terms 1..4, letters 0..2
COMP = {
    'left': {1: (0, 1), 2: (0, 2), 3: (1,), 4: (0,)},
    'right': {1: (0,), 2: (1,), 3: (0, 2), 4: (0, 1)},
}
IN_LETTERS = (1, 2)   # x1, p0 / y1, q0
MARKED = 2            # p0 / q0


def pairs(side):
    return [(t, s) for t in (1, 2, 3, 4) for s in COMP[side][t]]


def terms_of_letter(side, s):
    return tuple(t for t in (1, 2, 3, 4) if s in COMP[side][t])


def size_of(cls, side):
    n0, n1, n2, d = cls
    return (n2 + d) if side == 'left' else (n1 + d)


# ---------------- exact objects (small L) ----------------
def support(cls, side):
    """all letter strings of the band support (Sigma)."""
    n0, n1, n2, d = cls
    L = n0 + n1 + n2 + d
    sz = size_of(cls, side)
    out = []
    for u in product((0, 1, 2), repeat=L):
        nin = sum(1 for x in u if x in IN_LETTERS)
        nmk = sum(1 for x in u if x == MARKED)
        if nin == sz and nmk <= d:
            out.append(u)
    return out


def is_relevant(tau, cls):
    n0, n1, n2, d = cls
    return tau.count(1) >= n0 and tau.count(2) >= n1 and tau.count(3) >= n2


def relevant_leaves(cls):
    n0, n1, n2, d = cls
    L = n0 + n1 + n2 + d
    return [tau for tau in product((1, 2, 3, 4), repeat=L) if is_relevant(tau, cls)]


# ---------------- closed-form feasibility of a (prefix term counts c, suffix letter counts w) pair ----------------
def feasible(cls, side, c, w):
    """c = (c1, c2, c3, c4) term counts of the prefix sigma; w = (w0, w1, w2) letter counts of the suffix u'.
    (i)  some prefix letters compatible with sigma complete u' to a support string;
    (ii) some suffix terms compatible with u' complete sigma to a relevant leaf."""
    n0, n1, n2, d = cls
    c1, c2, c3, c4 = c
    w0, w1, w2 = w
    D1, D2, D3 = max(0, n0 - c1), max(0, n1 - c2), max(0, n2 - c3)
    if side == 'left':
        a = n2 + d
        R = a - c3 - w1 - w2           # in-letters still needed from the prefix: j1 (term 1 -> x1) + j2 (term 2 -> p0)
        if w2 > d or R < 0 or R > c1 + min(c2, d - w2):
            return False
        # suffix: p0 -> term 2; x1 -> term 1 or 3; x0 -> term 1, 2 or 4
        if D3 > w1:
            return False
        return max(0, D1 - (w1 - D3)) + max(0, D2 - w2) <= w0
    else:
        b = n1 + d
        R = b - c2 - w1 - w2           # j3 (term 3 -> q0) + j4 (term 4 -> y1)
        if w2 > d or R < 0 or R > c4 + min(c3, d - w2):
            return False
        # suffix: q0 -> term 3; y1 -> term 2 or 4; y0 -> term 1, 3 or 4
        if D2 > w1:
            return False
        return D1 + max(0, D3 - w2) <= w0


def comps(n, parts):
    """all compositions of n into `parts` non-negative parts."""
    if parts == 1:
        yield (n,)
        return
    for i in range(n + 1):
        for rest in comps(n - i, parts - 1):
            yield (i,) + rest


def multinom(n, ks):
    r = math.factorial(n)
    for k in ks:
        r //= math.factorial(k)
    return r


def kept_count_formula(cls, side, k):
    """exact number of kept entries at depth k: sum over feasible (c, w) of multinomials (big integers)."""
    n0, n1, n2, d = cls
    L = n0 + n1 + n2 + d
    tot = 0
    for c in comps(k, 4):
        mc = multinom(k, c)
        for w in comps(L - k, 3):
            if feasible(cls, side, c, w):
                tot += mc * multinom(L - k, w)
    return tot


def log_kept_formula(cls, side, k):
    """ln of the number of kept entries at depth k (floats via lgamma; for larger L)."""
    n0, n1, n2, d = cls
    L = n0 + n1 + n2 + d
    lg = [math.lgamma(i + 1) for i in range(L + 2)]
    terms = []
    for c in comps(k, 4):
        lc = lg[k] - sum(lg[x] for x in c)
        for w in comps(L - k, 3):
            if feasible(cls, side, c, w):
                terms.append(lc + lg[L - k] - sum(lg[x] for x in w))
    if not terms:
        return -math.inf, 0
    m = max(terms)
    return m + math.log(sum(math.exp(t - m) for t in terms)), m


# ---------------- E_side: primal (SLSQP) ----------------
def Hm(x):
    s = sum(x)
    if s <= 0:
        return 0.0
    return -sum(xi * math.log(xi / s) for xi in x if xi > 0)


def side_primal(p, side, starts=4, seed=1):
    p0, p1, p2, pw = p
    P = pairs(side)
    m = len(P)
    size = (p2 + pw) if side == 'left' else (p1 + pw)

    def unpack(x):
        x = np.clip(x, 0, None)
        pre, suf = x[:m], x[m:]
        u = [sum(pre[i] for i in range(m) if P[i][0] == t) for t in (1, 2, 3, 4)]
        us = [sum(suf[i] for i in range(m) if P[i][0] == t) for t in (1, 2, 3, 4)]
        sp = [sum(pre[i] for i in range(m) if P[i][1] == s) for s in (0, 1, 2)]
        w = [sum(suf[i] for i in range(m) if P[i][1] == s) for s in (0, 1, 2)]
        return u, us, sp, w

    def obj(x):
        u, us, sp, w = unpack(x)
        return -(Hm(u) + Hm(w))
    cons = [
        {'type': 'eq', 'fun': lambda x: np.clip(x, 0, None).sum() - 1},
        {'type': 'eq', 'fun': lambda x: (lambda u, us, sp, w: sp[1] + sp[2] + w[1] + w[2] - size)(*unpack(x))},
        {'type': 'ineq', 'fun': lambda x: (lambda u, us, sp, w: pw - sp[2] - w[2])(*unpack(x))},
    ] + [{'type': 'ineq', 'fun': (lambda j: lambda x: (lambda u, us, sp, w: u[j] + us[j] - p[j])(*unpack(x)))(j)}
         for j in range(3)]
    rng = np.random.default_rng(seed)
    best = (-1e9, None)
    for s in range(starts):
        x0 = np.ones(2 * m) if s == 0 else rng.random(2 * m)
        x0 = x0 / x0.sum()
        r = minimize(obj, x0, method='SLSQP', bounds=[(0, 1)] * (2 * m), constraints=cons,
                     options={'ftol': 1e-14, 'maxiter': 3000})
        ok = all((c['fun'](r.x) > -1e-8) if c['type'] == 'ineq' else (abs(c['fun'](r.x)) < 1e-8) for c in cons)
        if ok and -r.fun > best[0]:
            best = (-r.fun, np.clip(r.x, 0, None))
    return best


# ---------------- E_side: dual ----------------
def dual_parts(lam, side):
    """lam = (nu, zeta, eta1, eta2, eta3); returns the vectors a (terms 1..4) and b (letters 0..2)."""
    nu, zeta, e1, e2, e3 = lam
    eta = {1: e1, 2: e2, 3: e3, 4: 0.0}

    def cts(t, s):
        return eta[t] - (nu if s in IN_LETTERS else 0.0) - (zeta if s == MARKED else 0.0)
    a = [max(cts(t, s) for s in COMP[side][t]) for t in (1, 2, 3, 4)]
    b = [max(cts(t, s) for t in terms_of_letter(side, s)) for s in (0, 1, 2)]
    return a, b


def lse(v):
    m = max(v)
    return m + math.log(sum(math.exp(x - m) for x in v))


def dual_value(lam, p, side):
    p0, p1, p2, pw = p
    nu, zeta, e1, e2, e3 = lam
    size = (p2 + pw) if side == 'left' else (p1 + pw)
    a, b = dual_parts(lam, side)
    return nu * size + zeta * pw - e1 * p0 - e2 * p1 - e3 * p2 + max(lse(a), lse(b))


def side_dual(p, side, x0=None):
    """minimise the dual by SLSQP on the smooth epigraph form; returns (value, multipliers).
    Variables: nu, zeta, e1, e2, e3, A1..A4, B0..B2, z (A_t >= c_ts, B_s >= c_ts, z >= LSE(A), z >= LSE(B))."""
    p0, p1, p2, pw = p
    size = (p2 + pw) if side == 'left' else (p1 + pw)
    P = pairs(side)

    def cts(y, t, s):
        nu, zeta, e1, e2, e3 = y[:5]
        eta = (e1, e2, e3, 0.0)[t - 1]
        return eta - (nu if s in IN_LETTERS else 0.0) - (zeta if s == MARKED else 0.0)
    cons = []
    for (t, s) in P:
        cons.append({'type': 'ineq', 'fun': (lambda t, s: lambda y: y[5 + t - 1] - cts(y, t, s))(t, s)})
        cons.append({'type': 'ineq', 'fun': (lambda t, s: lambda y: y[9 + s] - cts(y, t, s))(t, s)})
    cons.append({'type': 'ineq', 'fun': lambda y: y[12] - lse(list(y[5:9]))})
    cons.append({'type': 'ineq', 'fun': lambda y: y[12] - lse(list(y[9:12]))})

    def obj(y):
        return y[0] * size + y[1] * pw - y[2] * p0 - y[3] * p1 - y[4] * p2 + y[12]
    bounds = [(-30, 30), (0, 30), (0, 30), (0, 30), (0, 30)] + [(-60, 60)] * 8
    best = (1e9, None)
    starts = [np.array([0.0, 0.5, 1.0, 1.0, 1.0])] if x0 is None else [np.array(x0)]
    starts += [np.array([0.5, 1.0, 2.0, 2.0, 2.0]), np.array([-0.5, 0.2, 0.5, 0.5, 0.5])]
    for s5 in starts:
        a, b = dual_parts(s5, side)
        y0 = np.concatenate([s5, a, b, [max(lse(a), lse(b)) + 0.01]])
        r = minimize(obj, y0, method='SLSQP', bounds=bounds, constraints=cons,
                     options={'ftol': 1e-15, 'maxiter': 2000})
        lam = list(r.x[:5])
        lam[1] = max(lam[1], 0.0)
        lam[2:] = [max(x, 0.0) for x in lam[2:]]
        v = dual_value(lam, p, side)      # the true dual function at the found multipliers (an upper bound)
        if v < best[0]:
            best = (v, lam)
    return best


def reading_exponent(p, side):
    """(1/L) ln of C(L, a) C(a + d, d) (r61b.md 2.3), upper bound via C(n, k) <= e^{n H2(k/n)}."""
    p0, p1, p2, pw = p
    sz = (p2 + pw) if side == 'left' else (p1 + pw)

    def H2(x):
        return -x * math.log(x) - (1 - x) * math.log(1 - x)
    return H2(sz) + (sz + pw) * H2(pw / (sz + pw))


def E_enc_sides(p):
    """(E_left, E_right) with the reading included: max(E_side, reading) per side (dual values)."""
    eL = side_dual(p, 'left')[0]
    eR = side_dual(p, 'right')[0]
    return max(eL, reading_exponent(p, 'left')), max(eR, reading_exponent(p, 'right'))
