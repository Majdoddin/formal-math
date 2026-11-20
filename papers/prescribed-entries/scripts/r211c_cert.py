"""R211c: independent re-certification of the batch curve f_cert(kappa) (r79.md Theorem B, r79b.md Lemma 1).

Independent of r74a/r79/r79b code: no import of their scripts, no mpmath.  Trust base: Python's decimal module
(libmpdec), whose ln() is correctly rounded; every operation below is done with directed rounding
(ROUND_FLOOR / ROUND_CEILING) on [lo, hi] intervals, and ln results are widened by one ulp on each side.

What is certified, at the level-1 point P0 = (lam6, u6(q+2), u7(q+2)) = (7/19, 97/100, 979/1000):
  (0) slack(P0) > 0, ln a_1, alpha(P0), c_o = sum_q lam_q c(q)/ln a_1, eps* = ln4/(5 ln5), 2/(c_o + 2);
  (1) G_q(t) <= F_q(t; z0) + sum_i |dF/dz_i (z0)|  (concavity + tangent plane, r74a.md Lemmas 1-3) at an interior
      rational z0 found by my own float search + Newton (analytic Hessian, decimal arithmetic);
      L_t = (lam6 G_6 + lam7 G_7)/ln a_1 >= Lambda(t)  (r74a Lemma 1, every t in (0,1]);
      M_t = max(L_t, t c_o,hi - 2 + 2t) >= Lambda^+(t)  (r79b Lemma 1); M_1 = c_o,hi.
  (2) for each kappa: a rational t chosen by my own float optimisation (not r79's grid), the bottom (direct or the
      paper's data structure with q_A -> 0, eps_A -> eps*), a rational x next to x_min / x_max, the strict condition
      (B1) x M_t + q_A < (1 + alpha x) s, s = min(0, 1 - kappa) + t kappa, checked in intervals with alpha's lower
      end, and the certified lower end of the range (1 + alpha x)/(x + 1/eps_A).
Run: nice -n 19 python3 -I r211c_cert.py > r211c_cert_out.txt
"""
import math
from decimal import Decimal as Dc, Context, ROUND_FLOOR, ROUND_CEILING, ROUND_HALF_EVEN
from fractions import Fraction as Fr

PREC = 60
CF = Context(prec=PREC, rounding=ROUND_FLOOR)
CC = Context(prec=PREC, rounding=ROUND_CEILING)
CN = Context(prec=PREC, rounding=ROUND_HALF_EVEN)


def dlo(fr):
    return CF.divide(Dc(fr.numerator), Dc(fr.denominator))


def dhi(fr):
    return CC.divide(Dc(fr.numerator), Dc(fr.denominator))


class Iv:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi=None):
        if isinstance(lo, Fr):
            self.lo, self.hi = dlo(lo), dhi(lo)
            return
        if isinstance(lo, int):
            lo = Fr(lo); self.lo, self.hi = dlo(lo), dhi(lo); return
        self.lo, self.hi = lo, (lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def c(x):
        return x if isinstance(x, Iv) else Iv(Fr(x))

    def __add__(s, o):
        o = Iv.c(o); return Iv(CF.add(s.lo, o.lo), CC.add(s.hi, o.hi))
    __radd__ = __add__

    def __neg__(s):
        return Iv(-s.hi, -s.lo)

    def __sub__(s, o):
        o = Iv.c(o); return Iv(CF.subtract(s.lo, o.hi), CC.subtract(s.hi, o.lo))

    def __rsub__(s, o):
        return Iv.c(o) - s

    def __mul__(s, o):
        o = Iv.c(o)
        lo = min(CF.multiply(a, b) for a in (s.lo, s.hi) for b in (o.lo, o.hi))
        hi = max(CC.multiply(a, b) for a in (s.lo, s.hi) for b in (o.lo, o.hi))
        return Iv(lo, hi)
    __rmul__ = __mul__

    def __truediv__(s, o):
        o = Iv.c(o)
        assert o.lo > 0 or o.hi < 0, "division by an interval containing 0"
        lo = min(CF.divide(a, b) for a in (s.lo, s.hi) for b in (o.lo, o.hi))
        hi = max(CC.divide(a, b) for a in (s.lo, s.hi) for b in (o.lo, o.hi))
        return Iv(lo, hi)

    def __rtruediv__(s, o):
        return Iv.c(o)/s

    def mag(s):
        return max(abs(s.lo), abs(s.hi))


def ivlog(x):
    x = Iv.c(x)
    assert x.lo > 0
    a = CN.ln(x.lo).next_minus(CF)       # correctly rounded value -> one ulp down is a lower bound
    b = CN.ln(x.hi).next_plus(CC)
    return Iv(a, b)


def phi(s):
    return s*ivlog(s)


def dphi(s):
    return ivlog(s) + 1


# ------------------------------------------------------------------ constants at P0
LAM = {6: Fr(7, 19), 7: Fr(12, 19)}
UF = {6: Fr(97, 100), 7: Fr(979, 1000)}          # u_q (q+2)


def constants():
    lna = Iv(0); lnb = Iv(0); slack = Iv(0); co_num = Iv(0)
    for q in (6, 7):
        w = Fr(1, q + 2); u = UF[q]*w; v = (w - u)/2; p = Fr(q, 2*(q + 2))
        X = [p + w + v, p + u, v]; Z = [u + 2*v, 2*p, w]
        assert Z == [w, q*w, w]
        H = lambda V: -sum((Iv(c)*ivlog(Iv(c)) for c in V), Iv(0))
        slack = slack + Iv(LAM[q])*(H(X) - H(Z))
        lna = lna + Iv(LAM[q]*p)*ivlog(Iv(q))
        lnb = lnb + Iv(LAM[q]*u)*ivlog(Iv(q))
        co_num = co_num + Iv(LAM[q])*(ivlog(Iv(q + 2)) + q*ivlog(Iv(2)))/Iv(q + 2)
    alpha = lnb/lna
    co = co_num/lna
    estar = ivlog(Iv(4))/(5*ivlog(Iv(5)))
    return dict(slack=slack, lna=lna, alpha=alpha, co=co, estar=estar)


# ------------------------------------------------------------------ objective F_q(t; u, v, y) (r74a.md Section 1)
def F_iv(q, t, u, v, y):
    pi = Iv(Fr(1, q + 2)); qpi = Iv(Fr(q, q + 2)); lq = ivlog(Iv(q))
    a = qpi - u + v; b = pi + u; o = pi - v; w = qpi - u + y
    D = phi(a) - a*ivlog(qpi) + phi(b) - b*ivlog(pi) + phi(o) - o*ivlog(pi)
    sig = phi(b) - phi(pi) - phi(y) - phi(u - y) + (u - y)*lq + phi(a) - phi(v - y) - phi(w)
    return -D + t*sig


def G_iv(q, t, u, v, y):
    pi = Iv(Fr(1, q + 2)); qpi = Iv(Fr(q, q + 2)); lq = ivlog(Iv(q))
    a = qpi - u + v; b = pi + u; o = pi - v; w = qpi - u + y
    Du = ivlog(b) - ivlog(a) + lq
    Dv = ivlog(a) - ivlog(o) - lq
    su = dphi(b) - dphi(u - y) + lq - dphi(a) + dphi(w)
    sv = dphi(a) - dphi(v - y)
    sy = -dphi(y) + dphi(u - y) - lq + dphi(v - y) - dphi(w)
    return (-Du + t*su, -Dv + t*sv, t*sy)


# float versions (point search only; validity does not depend on them)
def F_fl(q, t, u, v, y):
    pi = 1/(q + 2); qpi = q/(q + 2); lq = math.log(q)
    a = qpi - u + v; b = pi + u; o = pi - v; w = qpi - u + y
    ph = lambda s: s*math.log(s)
    D = ph(a) - a*math.log(qpi) + ph(b) - b*math.log(pi) + ph(o) - o*math.log(pi)
    sig = ph(b) - ph(pi) - ph(y) - ph(u - y) + (u - y)*lq + ph(a) - ph(v - y) - ph(w)
    return -D + t*sig


def grad_hess_dec(q, t, z, ctx):
    """gradient and Hessian in plain decimal arithmetic (point search only)."""
    u, v, y = z
    one = Dc(1)
    pi = ctx.divide(one, Dc(q + 2)); qpi = ctx.divide(Dc(q), Dc(q + 2)); lq = ctx.ln(Dc(q))
    a = qpi - u + v; b = pi + u; o = pi - v; w = qpi - u + y; uy = u - y; vy = v - y
    L = ctx.ln
    Du = L(b) - L(a) + lq; Dv = L(a) - L(o) - lq
    su = L(b) - L(uy) + lq - L(a) + L(w); sv = L(a) - L(vy)
    sy = -L(y) + L(uy) - lq + L(vy) - L(w)
    g = [-Du + t*su, -Dv + t*sv, t*sy]
    inv = lambda s: ctx.divide(one, s)
    HD = [[inv(b) + inv(a), -inv(a), Dc(0)], [-inv(a), inv(a) + inv(o), Dc(0)], [Dc(0), Dc(0), Dc(0)]]
    Hs = [[inv(b) - inv(uy) + inv(a) - inv(w), -inv(a), inv(uy) + inv(w)],
          [-inv(a), inv(a) - inv(vy), inv(vy)],
          [inv(uy) + inv(w), inv(vy), -inv(y) - inv(uy) - inv(vy) - inv(w)]]
    H = [[-HD[i][j] + t*Hs[i][j] for j in range(3)] for i in range(3)]
    return g, H


def solve3(H, g):
    det = lambda M: (M[0][0]*(M[1][1]*M[2][2] - M[1][2]*M[2][1]) - M[0][1]*(M[1][0]*M[2][2] - M[1][2]*M[2][0])
                     + M[0][2]*(M[1][0]*M[2][1] - M[1][1]*M[2][0]))
    d = det(H); out = []
    for k in range(3):
        M = [[(g[i] if j == k else H[i][j]) for j in range(3)] for i in range(3)]
        out.append(det(M)/d)
    return out


def interior(q, z):
    u, v, y = z
    pi = Fr(1, q + 2)
    return 0 < v < pi and 0 < y < v and y < u and u - y < q*pi


def gh_float(q, t, z):
    u, v, y = z
    pi = 1/(q + 2); qpi = q/(q + 2); lq = math.log(q); L = math.log
    a = qpi - u + v; b = pi + u; o = pi - v; w = qpi - u + y; uy = u - y; vy = v - y
    g = [-(L(b) - L(a) + lq) + t*(L(b) - L(uy) + lq - L(a) + L(w)),
         -(L(a) - L(o) - lq) + t*(L(a) - L(vy)),
         t*(-L(y) + L(uy) - lq + L(vy) - L(w))]
    HD = [[1/b + 1/a, -1/a, 0.0], [-1/a, 1/a + 1/o, 0.0], [0.0, 0.0, 0.0]]
    Hs = [[1/b - 1/uy + 1/a - 1/w, -1/a, 1/uy + 1/w], [-1/a, 1/a - 1/vy, 1/vy],
          [1/uy + 1/w, 1/vy, -1/y - 1/uy - 1/vy - 1/w]]
    H = [[-HD[i][j] + t*Hs[i][j] for j in range(3)] for i in range(3)]
    return g, H


def interior_f(q, z):
    u, v, y = z
    pi = 1/(q + 2)
    return 0 < v < pi and 0 < y < v and y < u and u - y < q*pi


def newton_float(q, t, z):
    z = list(z)
    for _ in range(200):
        g, H = gh_float(q, t, z)
        if max(abs(c) for c in g) < 1e-13:
            break
        dz = solve3(H, g)
        lam = 1.0
        while True:
            zn = [z[i] - lam*dz[i] for i in range(3)]
            if interior_f(q, zn) and F_fl(q, t, *zn) >= F_fl(q, t, *z) - 1e-15:
                break
            lam /= 2
            if lam < 1e-12:
                zn = z; break
        z = zn
    return z


START = {}


def float_argmax(q, t, start=None):
    """float maximiser: Nelder-Mead once per q in log-coordinates, then damped Newton with warm starts."""
    if q not in START:
        from scipy.optimize import minimize
        import numpy as np
        pi = 1/(q + 2)
        def neg(p):
            u, v, y = np.exp(p)
            if not (0 < v < pi and 0 < y < v and y < u and u - y < q*pi):
                return 1e9
            return -F_fl(q, 0.3, u, v, y)
        r = minimize(neg, np.log([0.05, 0.05, 0.005]), method="Nelder-Mead",
                     options=dict(xatol=1e-12, fatol=1e-16, maxiter=20000, maxfev=40000))
        START[q] = {0.3: newton_float(q, 0.3, [float(c) for c in np.exp(r.x)])}
    near = min(START[q], key=lambda s: abs(s - t))
    z = START[q][near]
    # walk from the nearest known t in small steps (keeps Newton in its basin)
    steps = max(1, int(abs(t - near)/0.02))
    for i in range(1, steps + 1):
        z = newton_float(q, near + (t - near)*i/steps, z)
    START[q][t] = z
    return F_fl(q, t, *z), tuple(z)


def refine(q, t, zf):
    """Newton in 60-digit decimal arithmetic with step halving to stay interior; returns rational z0."""
    ctx = Context(prec=PREC)
    tt = ctx.divide(Dc(t.numerator), Dc(t.denominator))
    z = [Dc(repr(float(c))) for c in zf]
    for _ in range(80):
        g, H = grad_hess_dec(q, tt, z, ctx)
        if max(abs(c) for c in g) < Dc(10)**(-52):
            break
        dz = solve3(H, g)
        lam = Dc(1)
        for _h in range(60):
            zn = [z[i] - lam*dz[i] for i in range(3)]
            if interior(q, [Fr(c) for c in zn]):
                break
            lam = lam/2
        z = zn
    z0 = [Fr(c).limit_denominator(10**45) for c in z]
    if not interior(q, z0):
        z0 = [Fr(c) for c in z]
    return z0


def certify_G(q, t, start=None):
    fv, zf = float_argmax(q, float(t), start)
    z0 = refine(q, t, zf)
    assert interior(q, z0), "z0 not interior"
    tI = Iv(t); zI = [Iv(c) for c in z0]
    Fz = F_iv(q, tI, *zI)
    g = G_iv(q, tI, *zI)
    slope = Iv(0)
    for c in g:
        slope = slope + Iv(c.mag())
    ub = (Fz + slope).hi            # G_q(t) <= F(z0) + sum|g_i|  (|z_i - z0_i| <= 1 on P_q, a subset of [0,1]^3)
    return Fr(ub), float(slope.hi), fv, zf


# ------------------------------------------------------------------ the batch curve
def L_and_M(t, K, cache={}):
    if t in cache:
        return cache[t]
    if t == 1:
        res = (K["co"].hi, K["co"].hi, None)
        cache[t] = res
        return res
    G = {}
    sl = []
    for q in (6, 7):
        ub, slope, fv, zf = certify_G(q, t)
        G[q] = ub; sl.append(slope)
    L = (Iv(LAM[6])*Iv(G[6]) + Iv(LAM[7])*Iv(G[7]))/K["lna"]
    pad = Iv(t)*Iv(K["co"].hi) - 2 + Iv(2)*Iv(t)
    M = max(L.hi, pad.hi)
    res = (L.hi, M, max(sl), pad.hi)
    cache[t] = res
    return res


def f_closed(alpha, L, s, estar):
    """float suprema f_dir, f_DS (r79.md Theorem B) at one t."""
    fd = fs = -1.0
    if alpha*s > L and s < 1:
        fd = alpha + (1 - alpha)*(alpha*s - L)/(1 - s + alpha*s - L)
    if L > alpha*s > 0:
        fs = estar*L/(L - (alpha - estar)*s)
    return fd, fs


def s_of(kap, t):
    return min(Fr(0), 1 - kap) + t*kap


LCACHE = {}


def Lfloat(t):
    t = round(t, 6)
    if t not in LCACHE:
        lam6 = 7/19
        G6 = float_argmax(6, t)[0]; G7 = float_argmax(7, t)[0]
        LCACHE[t] = (lam6*G6 + (1 - lam6)*G7)/LNA_F
    return LCACHE[t]


def best_t(kap, alpha, co, estar):
    """float optimisation over t in (0, 1] of max(f_dir, f_DS) with the float profile; plus t = 1."""
    def val(t):
        L = Lfloat(t) if t < 1 else co
        pad = t*co - 2 + 2*t
        M = max(L, pad)
        return max(f_closed(alpha, M, float(s_of(kap, Fr(t).limit_denominator(10**6))), estar))
    grid = [0.002, 0.005, 0.01, 0.02, 0.04, 0.06, 0.08, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4, 0.45, 0.5, 0.55,
            0.6, 0.65, 0.7, 0.75, 0.8, 0.85, 0.9, 0.95, 0.98, 0.995]
    vals = [(val(t), t) for t in grid]
    v0, t0 = max(vals)
    i = grid.index(t0)
    a = grid[max(i - 1, 0)]; b = grid[min(i + 1, len(grid) - 1)]
    gr = (math.sqrt(5) - 1)/2
    c, d = b - gr*(b - a), a + gr*(b - a)
    fc, fdd = val(c), val(d)
    for _ in range(25):
        if fc > fdd:
            b, d, fdd = d, c, fc; c = b - gr*(b - a); fc = val(c)
        else:
            a, c, fc = c, d, fdd; d = a + gr*(b - a); fdd = val(d)
    tb = (a + b)/2
    v1 = val(1.0)
    return (tb, val(tb)) if val(tb) >= v1 else (1.0, v1)


def certify_kappa(kap, t, K):
    """certified lower end of the range at (kappa, t): best of the two bottoms."""
    alpha = K["alpha"]; estar = K["estar"]
    Lhi, Mhi, slope, *_ = L_and_M(t, K)
    s = s_of(kap, t)
    M = Iv(Mhi)
    out = []
    af, Mf, sf = float(alpha.lo), float(Mhi), float(s)
    # direct bottom: q_A = 1, eps_A = 1, x just above x_min = (1 - s)/(alpha s - M)
    if af*sf > Mf and sf < 1:
        xmin = (1 - sf)/(af*sf - Mf)
        for rel in (1e-12, 1e-9, 1e-6):
            x = Fr(repr(xmin*(1 + rel)))
            lhs = Iv(x)*M + 1
            rhs = (1 + Iv(alpha.lo)*Iv(x))*Iv(s)
            if lhs.hi < rhs.lo:
                R = (1 + Iv(alpha.lo)*Iv(x))/(Iv(x) + 1)
                out.append((R.lo, "direct", x)); break
    # data structure, q_A -> 0, eps_A -> eps*: x just below x_max = s/(M - alpha s)
    if Mf > af*sf > 0:
        xmax = sf/(Mf - af*sf)
        for rel in (1e-12, 1e-9, 1e-6):
            x = Fr(repr(xmax*(1 - rel)))
            lhs = Iv(x)*M
            rhs = (1 + Iv(alpha.lo)*Iv(x))*Iv(s)
            if lhs.hi < rhs.lo:
                R = (1 + Iv(alpha.lo)*Iv(x))/(Iv(x) + 1/Iv(estar.lo))
                out.append((R.lo, "DS q_A->0", x)); break
    return max(out) if out else None


def r6(d):
    return f"{math.floor(float(d)*1e6)/1e6:.6f}"


def main():
    import functools, builtins
    global print
    print = functools.partial(builtins.print, flush=True)
    global LNA_F
    K = constants()
    LNA_F = float(K["lna"].lo)
    print("(0) constants at P0 = (7/19, 97/100, 979/1000), decimal interval arithmetic, 60 digits")
    for k in ("slack", "lna", "alpha", "co", "estar"):
        print(f"  {k}: [{K[k].lo:.20E}, {K[k].hi:.20E}]")
    assert K["slack"].lo > 0
    t0 = Iv(2)/(K["co"] + 2)
    tc = Iv(1)/(K["co"] + 2)
    print(f"  2/(c_o + 2) in [{t0.lo:.12E}, {t0.hi:.12E}]  (padding term < 0 below it)")
    print(f"  1/(c_o + 2) in [{tc.lo:.12E}, {tc.hi:.12E}]  (>= 0.3249: {tc.lo >= Dc('0.3249')})")

    print("\n(1) certified M_t at r79b's table values of t (compare r79b.md Section 2 table)")
    print("    t | L_t <= (this script) | pad_hi(t) | M_t | max sum|g_i| | r79b's L_t")
    R79B = {Fr(30, 100): "0.1520406948", Fr(34, 100): "0.1860503300", Fr(40, 100): "0.2418586132",
            Fr(50, 100): "0.3470291246", Fr(60, 100): "0.4666563853", Fr(65, 100): "0.5316852541",
            Fr(70, 100): "0.6000973040", Fr(80, 100): "0.7468068357", Fr(90, 100): "0.9062514226",
            Fr(99, 100): "1.0601700242", Fr(196, 10000): "(r74a: 0.00170915330565)",
            Fr(6, 100): "(r79: 1.1084098e-2)", Fr(3249, 10000): "(r79: 1.7290444e-1)"}
    for t in sorted(R79B):
        Lhi, Mhi, slope, padhi = L_and_M(t, K)
        print(f"  {float(t):.4f} | {Lhi:.12E} | {float(padhi):+.6f} | {Mhi:.12E} | {slope:.1e} | {R79B[t]}")

    print("\n(2) f_cert(kappa): my own choice of t (float optimisation, rounded to a rational), certified (B1) and range")
    print("    kappa | t (rational) | bottom | x | certified: every eps < | r79/r79b printed value")
    PRINTED = {Fr(1, 2): "0.295435", Fr(1): "0.299509", Fr(102, 100): "0.295371", Fr(105, 100): "0.235760",
               Fr(11, 10): "0.212445", Fr(115, 100): "0.204707", Fr(12, 10): "0.200830", Fr(125, 100): "0.198539",
               Fr(13, 10): "0.197066", Fr(14, 10): "0.195402", Fr(15, 10): "0.194637", Fr(16, 10): "0.194351",
               Fr(17, 10): "0.194324", Fr(2): "0.194324"}
    af = float(K["alpha"].lo); cof = float(K["co"].hi); ef = float(K["estar"].lo)
    for kap in sorted(PRINTED):
        tb, vb = best_t(kap, af, cof, ef)
        t = Fr(1) if tb >= 1 else Fr(round(tb*10**4), 10**4)
        res = certify_kappa(kap, t, K)
        if res is None:
            print(f"  {float(kap):.3f} | t = {t} | none certified"); continue
        R, name, x = res
        print(f"  {float(kap):.3f} | {t} | {name} | {float(x):.6g} | {r6(R)} (float sup {vb:.7f}) | {PRINTED[kap]}")

    print("\n(3) the same kappa at r79b's own grid t (cross-check of the closed forms with my certified M_t)")
    GRIDT = {Fr(1, 2): Fr(196, 10000), Fr(1): Fr(6, 100), Fr(11, 10): Fr(24, 100), Fr(115, 100): Fr(34, 100),
             Fr(12, 10): Fr(44, 100), Fr(125, 100): Fr(52, 100), Fr(13, 10): Fr(60, 100), Fr(14, 10): Fr(73, 100),
             Fr(15, 10): Fr(85, 100), Fr(16, 10): Fr(96, 100), Fr(17, 10): Fr(1)}
    for kap, t in sorted(GRIDT.items()):
        res = certify_kappa(kap, t, K)
        R, name, x = res
        print(f"  {float(kap):.3f} | t = {float(t):g} | {name} | certified every eps < {r6(R)} | printed {PRINTED[kap]}")


if __name__ == "__main__":
    main()
