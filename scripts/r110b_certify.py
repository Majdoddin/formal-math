"""R110b: an exact-arithmetic certificate for R110's per-pair SetDisjointness construction at explicit rational
parameters.

What is certified (r110b.md Section 2, Theorem 1): for rational tau, eta0 and a finite chain of rational R14
structures (c_i, theta_i, eps_i) with rational universe exponents d_i, the following inequalities hold, with every
logarithm enclosed rigorously (rational enclosures, series with explicit remainder):
  (T1)  0 < theta_i < 4/5, c_i >= 2, eps_i > 0                                   (r14.md Thm 1 hypotheses)
  (B)   b(theta_i, c_i) < 0                                                       (gamma_i = -b/ln2 > 0)
  (R)   eps_i (A(c_i) - 2 b(theta_i, c_i)) < ln 4,  i.e. eps_i < R'_{c_i}(gamma_i)  (r14.md Thm 1 range)
  (Q)   q(theta_i) d_i <= tau                                                     (query D^q <= N^tau)
  (C2)  d_i/eps_i - gamma_i d_i <= 1 + tau - x                                    (space, one class padded)
  (C3)  2 d_i/eps_i - gamma_i d_i <= 2 - x                                        (space, both classes padded)
  (V)   x - gamma_i d_i <= d_{i-1}  (d_0 := 2 tau),   and d_k >= x               (coverage of all pair classes)
  (S)   1 + 2 tau <= 2 - eta0                                                     (dictionaries, O(N) space)
with x := 2 tau + eta0. Then S T^2 = O~(N^{2 - eta0}) with T = O~(N^tau) (r110b.md Theorem 1).

Two enclosures of each logarithm are used:
  * "tight": ln r = k ln 2 + 2 atanh(y), y = (r - 2^k)/(r + 2^k), the series summed until its tail bound
    2|y|^(2n+1)/((2n+1)(1-y^2)) is below 1e-45, with ln 2 = 2 atanh(1/3) enclosed the same way. This is the
    certificate.
  * "lean": exactly V2Lean's LogBounds.log_mem (logApprox +- logErr with Mathlib's 0.6931471803 <= ln 2 <=
    0.6931471808, error term 2 y^(2n)/(1 - y^2)), with k = round(log2 r) and the smallest n giving series error
    <= 1e-13. This shows whether the existing Lean enclosure lemma is precise enough for each inequality.
Interval arithmetic treats every occurrence independently (no cancellation of shared logarithms), so it is
conservative. Design of the chain (floating point, greedy) is in design(); it only proposes rationals, and nothing
from it is trusted.

Run: ~/.venv/bin/python r110b_certify.py   (single process, about a minute). Output: r110b_certify_out.txt.
"""
from fractions import Fraction as F
from math import log, floor
import numpy as np

# ---------------------------------------------------------------- interval arithmetic over Fractions
ROUND = 10**45


def _down(a):
    return F(floor(a * ROUND), ROUND)


def _up(a):
    return -_down(-a)


class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        assert lo <= hi
        self.lo, self.hi = _down(lo), _up(hi)

    @staticmethod
    def c(v):
        return v if isinstance(v, Iv) else Iv(v)

    def __add__(s, o):
        o = Iv.c(o); return Iv(s.lo + o.lo, s.hi + o.hi)
    __radd__ = __add__

    def __neg__(s):
        return Iv(-s.hi, -s.lo)

    def __sub__(s, o):
        return s + (-Iv.c(o))

    def __rsub__(s, o):
        return Iv.c(o) - s

    def __mul__(s, o):
        o = Iv.c(o)
        p = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return Iv(min(p), max(p))
    __rmul__ = __mul__

    def inv(s):
        assert s.lo > 0 or s.hi < 0, "division by an interval containing 0"
        return Iv(1 / s.hi, 1 / s.lo)

    def __truediv__(s, o):
        return s * Iv.c(o).inv()

    def __rtruediv__(s, o):
        return Iv.c(o) * s.inv()

    def width(s):
        return s.hi - s.lo

    def __repr__(s):
        return f"[{float(s.lo):.15g}, {float(s.hi):.15g}]"


# ---------------------------------------------------------------- logarithms
def atanh_series(y, tol=F(1, 10**45)):
    """2 atanh(y) = 2 sum y^(2i+1)/(2i+1), |y| < 1, with the tail bound 2|y|^(2n+1)/((2n+1)(1-y^2))."""
    y = F(y); s = F(0); n = 0; p = y
    while True:
        tail = 2 * abs(p) / ((2 * n + 1) * (1 - y * y))
        if tail < tol:
            return Iv(2 * s - tail, 2 * s + tail)
        s += p / (2 * n + 1); p *= y * y; n += 1


LN2 = atanh_series(F(1, 3))                       # ln 2 = 2 atanh(1/3)
LN2_LEAN = Iv(F("0.6931471803"), F("0.6931471808"))  # Mathlib's Real.log_two_gt_d9 / log_two_lt_d9
assert LN2_LEAN.lo <= LN2.lo and LN2.hi <= LN2_LEAN.hi


def ln_tight(r):
    r = F(r); assert r > 0
    k = round(log(float(r), 2))
    y = (r - F(2) ** k) / (r + F(2) ** k)
    return k * LN2 + atanh_series(y)


def lean_k_n(r, tol=F(1, 10**13)):
    r = F(r); k = round(log(float(r), 2))
    y = (r - F(2) ** k) / (r + F(2) ** k)
    n = 1
    while 2 * y ** (2 * n) / (1 - y * y) > tol:
        n += 1
    return k, n


def ln_lean(r):
    """V2Lean.LogBounds.log_mem k n r: logApprox k n r +- logErr k n r."""
    r = F(r); k, n = lean_k_n(r)
    y = (r - F(2) ** k) / (r + F(2) ** k)
    mid = (F("0.6931471803") + F("0.6931471808")) / 2
    approx = k * mid + 2 * sum(y ** (2 * i + 1) / (2 * i + 1) for i in range(n))
    err = abs(k) * (F("0.6931471808") - F("0.6931471803")) / 2 + 2 * (y ** (2 * n) / (1 - y * y))
    return Iv(approx - err, approx + err)


# ---------------------------------------------------------------- the R14 quantities on intervals
def r14_quantities(c, th, mode):
    ln = ln_tight if mode == "tight" else ln_lean
    l2 = LN2 if mode == "tight" else LN2_LEAN
    c, th = F(c), F(th)
    lth, lomth, lcth, lcm, lc = ln(th), ln(1 - th), ln(c - 1 + th), ln(c - 1), ln(c)
    l5 = ln(5); l4 = 2 * l2
    b = th * l4 - (1 - th) * lomth - (c - 1 + th) * lcth + (c - 1) * lcm
    gam = (-b) / l2
    H = -(th * lth) - (1 - th) * lomth
    q = (H + th * l4) / l2
    A = 2 * c * l5 - c * lc + (c - 1) * lcm - (c - 1) * l4
    return dict(b=b, gam=gam, q=q, A=A, l4=l4)


def check_chain(tau, eta0, chain, mode):
    """Return a list of (name, structure index, margin interval) with margin = RHS - LHS (>= 0 means holds)."""
    tau, eta0 = F(tau), F(eta0); x = 2 * tau + eta0
    rows = [("S: (2 - eta0) - (1 + 2 tau)", 0, Iv(2 - eta0 - 1 - 2 * tau))]
    prev = 2 * tau
    for i, (c, th, eps, d) in enumerate(chain, 1):
        c, th, eps, d = map(F, (c, th, eps, d))
        assert 0 < th < F(4, 5) and c >= 2 and eps > 0 and d > 0
        Q = r14_quantities(c, th, mode)
        rows.append(("B: -b(theta,c)", i, -Q["b"]))
        rows.append(("R: ln4 - eps (A - 2b)", i, Q["l4"] - eps * (Q["A"] - 2 * Q["b"])))
        rows.append(("Q: tau - q d", i, tau - Q["q"] * d))
        rows.append(("C2: (1+tau-x) - (d/eps - gamma d)", i, (1 + tau - x) - (d / eps - Q["gam"] * d)))
        rows.append(("C3: (2-x) - (2d/eps - gamma d)", i, (2 - x) - (2 * d / eps - Q["gam"] * d)))
        rows.append(("V: d_prev - (x - gamma d)", i, prev - (x - Q["gam"] * d)))
        prev = d
    rows.append(("V: d_k - x", len(chain), Iv(prev - x)))
    return rows


# ---------------------------------------------------------------- design (floating point, untrusted)
LN4f, LN5f = log(4), log(5)


def fl(c, th):
    c = np.asarray(c, float); th = np.asarray(th, float)
    b = th * LN4f - (1 - th) * np.log(1 - th) - (c - 1 + th) * np.log(c - 1 + th) + (c - 1) * np.log(c - 1)
    g = -b / log(2)
    H = -th * np.log(th) - (1 - th) * np.log(1 - th)
    q = (H + th * LN4f) / log(2)
    A = 2 * c * LN5f - c * np.log(c) + (c - 1) * np.log(c - 1) - (c - 1) * LN4f
    return g, q, A


def dmax_fl(c, th, tau, x, se):
    g, q, A = fl(c, th)
    eps = LN4f / (A + g * LN4f) * (1 - se)
    d = np.minimum(np.minimum(tau / q, (1 + tau - x) / (1 / eps - g)), (2 - x) / (2 / eps - g))
    return np.where(g > 0, d, -1.0), g, eps


def best_step(cur, tau, x, slack, se, sd):
    """maximise d over rational grid points (c = k/10^4, theta = j/10^6) with gamma d >= x - cur + slack."""
    need = x - cur + slack
    box = (4.85, 16.0, 0.004, 0.068966)
    stepc, stepth = 0.02, 2e-4
    best = None
    for _ in range(7):
        cs = np.arange(box[0], box[1], stepc); ths = np.arange(box[2], box[3], stepth)
        C, T = np.meshgrid(cs, ths, indexing="ij")
        d, g, _ = dmax_fl(C, T, tau, x, se)
        d = d - sd
        ok = (g * d >= need) & (d > cur)
        if ok.any():
            k = np.unravel_index(np.argmax(np.where(ok, d, -1)), d.shape)
            best = (C[k], T[k])
        else:   # no feasible point yet: refine around the point closest to feasibility
            k = np.unravel_index(np.argmax(np.where(d > cur, g * d - need, -np.inf)), d.shape)
            best = None
        box = (max(2.0, C[k] - 5 * stepc), C[k] + 5 * stepc, max(1e-4, T[k] - 5 * stepth),
               min(0.068966, T[k] + 5 * stepth))
        stepc, stepth = stepc / 5, stepth / 5
    if best is None:
        best = (C[k], T[k])
    # final stage on the rational grid c = i/10^4, theta = j/10^6 (what is certified), exact rounding of eps, d
    ci0, tj0 = round(best[0] * 10**4), round(best[1] * 10**6)
    cand = None
    for ci in range(ci0 - 30, ci0 + 31):
        cs = np.full(61, ci / 1e4); tjs = np.arange(tj0 - 30, tj0 + 31)
        tjs = tjs[(tjs > 0) & (tjs <= 68966)]
        cs = cs[:len(tjs)]
        g, q, A = fl(cs, tjs / 1e6)
        epsf = np.floor(LN4f / (A + g * LN4f) * (1 - se) * 10**9) / 10**9
        d = np.minimum(np.minimum(tau / q, (1 + tau - x) / (1 / epsf - g)), (2 - x) / (2 / epsf - g)) - sd
        d = np.floor(d * 10**9) / 10**9
        ok = (g > 0) & (g * d >= need) & (d > cur)
        if ok.any():
            j = int(np.argmax(np.where(ok, d, -1)))
            if cand is None or d[j] > cand[0]:
                cand = (d[j], ci, int(tjs[j]), epsf[j])
    if cand is None:
        return None
    _, ci, tj, epsf = cand
    c, th = F(ci, 10**4), F(tj, 10**6)
    eps = F(round(epsf * 10**9), 10**9)
    g, q, A = fl(float(c), float(th))
    d = min(tau / q, (1 + tau - x) / (1 / float(eps) - g), (2 - x) / (2 / float(eps) - g)) - sd
    d = F(floor(d * 10**9), 10**9)
    return (c, th, eps, d)


def design(tau, eta0, slack=2e-9, se=1e-7, sd=2e-9, maxlen=12):
    tau_f, x = float(tau), float(2 * F(tau) + F(eta0))
    cur, chain = 2 * tau_f, []
    while cur < x:
        st = best_step(cur, tau_f, x, slack, se, sd)
        if st is None or float(st[3]) <= cur or len(chain) >= maxlen:
            return None
        chain.append(st); cur = float(st[3])
    return chain


# ---------------------------------------------------------------- main
def report(label, tau, eta0, chain, out):
    out.append(f"\n=== {label}: tau = {tau} = {float(tau):.6f}, eta0 = {eta0} = {float(eta0):.7f}, "
               f"x = 2 tau + eta0 = {float(2*F(tau)+F(eta0)):.7f}, {len(chain)} structures")
    for i, (c, th, eps, d) in enumerate(chain, 1):
        g, q, A = fl(float(c), float(th))
        out.append(f"  Pi_{i}: c = {c}, theta = {th}, eps = {eps}, d = {d}   (float: gamma = {g:.7f}, q = {q:.7f},"
                   f" R' = {LN4f/(A+g*LN4f):.9f}, interval [x - gamma d, d] = [{float(2*F(tau)+F(eta0))-g*float(d):.9f},"
                   f" {float(d):.9f}])")
    ok_all = {}
    for mode in ("tight", "lean"):
        rows = check_chain(tau, eta0, chain, mode)
        ok = all(m.lo > 0 for _, _, m in rows)
        ok_all[mode] = ok
        worst = min(rows, key=lambda r: r[2].lo)
        out.append(f"  [{mode}] all {len(rows)} inequalities hold strictly: {ok};  smallest certified margin "
                   f"{float(worst[2].lo):.3e} ({worst[0]}, structure {worst[1]})")
        if mode == "tight":
            for name, i, m in rows:
                out.append(f"    {name:40s} Pi_{i}: margin in {m}  (width {float(m.width()):.1e})")
        else:
            bad = [(n, i, float(m.lo)) for n, i, m in rows if m.lo <= 0]
            if bad:
                out.append(f"    lean-style enclosure too wide for: {bad}")
    return ok_all


def crosscheck(tau, eta0, chain, npts=4001, nal=101):
    """Float cross-check of the cost model on a (p, alpha) grid: for each p in [2 tau, x) the first structure whose
    interval [x - gamma_i d_i, d_i] contains p, with d = d_i, and the exact cost exponent
    max(1 - alpha, d/eps) + max(1 - p + alpha, d/eps) - gamma d of r110.md Section 1 (alpha in [tau, p/2]).
    Returns the largest value of cost - (2 - x) (must be <= 0) and the largest q d - tau."""
    tau, x = float(tau), float(2 * F(tau) + F(eta0))
    par = []
    for c, th, eps, d in chain:
        g, q, A = fl(float(c), float(th)); par.append((float(eps), float(d), float(g), float(q)))
    worst, worstq = -1.0, -1.0
    for p in np.linspace(2 * tau, x, npts, endpoint=False):
        i = next(j for j, (e, d, g, q) in enumerate(par) if x - g * d <= p + 1e-15 and p <= d)
        e, d, g, q = par[i]
        al = np.linspace(tau, p / 2, nal)
        cost = np.maximum(1 - al, d / e) + np.maximum(1 - p + al, d / e) - g * d
        worst = max(worst, float(cost.max() - (2 - x))); worstq = max(worstq, q * d - tau)
    return worst, worstq


def lean_terms(chain):
    """(k, n) arguments of log_mem for each logarithm a Lean certificate needs."""
    res = []
    for c, th, eps, d in chain:
        for r in (th, 1 - th, c - 1 + th, c - 1, c):
            res.append((str(r), *lean_k_n(r)))
    return res


if __name__ == "__main__":
    out = [f"ln 2 tight enclosure {LN2} (width {float(LN2.width()):.1e}); Mathlib's [0.6931471803, 0.6931471808] "
           f"contains it."]
    targets = [("eta0 = 0.0069", F(3279, 100000), F(69, 10000)),
               ("eta0 = 0.00697", F(3279, 100000), F(697, 100000)),
               ("eta0 = 0.006973", F(3275, 100000), F(6973, 1000000))]
    results = {}
    for label, tau, eta0 in targets:
        chain = None
        for sl in (1e-6, 3e-7, 1e-7, 3e-8, 1e-8, 3e-9, 1e-9, 5e-10):   # largest slack that still closes
            chain = design(tau, eta0, slack=sl, sd=sl, se=max(1e-7, sl))
            if chain is not None:
                out.append(f"\n(design slack {sl:.0e})")
                break
        if chain is None:
            out.append(f"\n=== {label}: design failed"); continue
        results[label] = (tau, eta0, chain, report(label, tau, eta0, chain, out))
        w, wq = crosscheck(tau, eta0, chain)
        out.append(f"  float cross-check over a 4001 x 101 grid of pair classes (p, alpha): max cost - (2 - x) = "
                   f"{w:.3e}, max q d - tau = {wq:.3e} (both must be <= 0)")
    out.append("\nlog_mem arguments (r, k, n) a Lean certificate would use, per chain:")
    for label, (tau, eta0, chain, ok) in results.items():
        out.append(f"  {label}: " + "; ".join(f"ln {r}: k={k}, n={n}" for r, k, n in lean_terms(chain)) + "; ln 5")
    txt = "\n".join(out)
    print(txt)
    with open(__file__.replace(".py", "_out.txt"), "w") as f:
        f.write(txt + "\n")
