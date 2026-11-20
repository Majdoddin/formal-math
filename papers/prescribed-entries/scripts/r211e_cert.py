"""R211e: certified rational points for the printed thresholds of the CP composites
(R11.1, R23.1 Hyp + hinted OMv, R45.1, R32.1, R77.1 and R77's Q-table).

Own code; imports nothing from earlier R-scripts. Two stages:
 (1) float search (scipy SLSQP) for a good point (lam6, u6, u7) of the level-1 CW mixture q in {6,7};
 (2) rigorous interval arithmetic with exact Fractions at a RATIONAL point: every logarithm is enclosed by the
     artanh series with an explicit tail bound, every operation rounds outward to the grid 2^-200.
Usage: python3 r211e_cert.py   (output: r211e_cert_out.txt beside it)
"""
from fractions import Fraction as F
import math, sys

PREC = 200
SC = 1 << PREC

def rd(x):  # round down to grid
    return F(math.floor(x * SC), SC)
def ru(x):
    return F(math.ceil(x * SC), SC)

class I:
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi=None):
        if hi is None:
            hi = lo
        lo, hi = F(lo), F(hi)
        assert lo <= hi, (lo, hi)
        self.lo, self.hi = lo, hi
    def __add__(s, o):
        o = o if isinstance(o, I) else I(o)
        return I(rd(s.lo + o.lo), ru(s.hi + o.hi))
    __radd__ = __add__
    def __neg__(s):
        return I(-s.hi, -s.lo)
    def __sub__(s, o):
        o = o if isinstance(o, I) else I(o)
        return s + (-o)
    def __rsub__(s, o):
        return I(o) - s
    def __mul__(s, o):
        o = o if isinstance(o, I) else I(o)
        p = [s.lo * o.lo, s.lo * o.hi, s.hi * o.lo, s.hi * o.hi]
        return I(rd(min(p)), ru(max(p)))
    __rmul__ = __mul__
    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        assert o.lo > 0 or o.hi < 0, "division by interval containing 0"
        return s * I(rd(1 / o.hi), ru(1 / o.lo)) if o.lo > 0 else s * I(rd(1 / o.hi), ru(1 / o.lo))
    def __rtruediv__(s, o):
        return I(o) / s
    def mid(s):
        return float((s.lo + s.hi) / 2)
    def __repr__(s):
        return "[%.12f, %.12f]" % (float(s.lo), float(s.hi))

def _ln_reduced(m, K=60):
    """enclosure of ln m for a Fraction m in [1/2, 2] by 2 artanh z, z = (m-1)/(m+1)."""
    z = (m - 1) / (m + 1)
    az = abs(z)
    assert az <= F(1, 3)
    s = F(0)
    zp = z
    z2 = z * z
    for j in range(K):
        s += zp / (2 * j + 1)
        zp *= z2
    s *= 2
    tail = 2 * az ** (2 * K + 1) / ((2 * K + 1) * (1 - az * az))
    return (s, s + tail) if z >= 0 else (s - tail, s)

LN2 = _ln_reduced(F(2))

def ln_point(x):
    x = F(x)
    assert x > 0
    k = round(math.log2(float(x)))
    m = x / F(2) ** k if k >= 0 else x * F(2) ** (-k)
    while m > 2:
        m /= 2; k += 1
    while m < F(1, 2):
        m *= 2; k -= 1
    lo, hi = _ln_reduced(m)
    if k >= 0:
        lo, hi = lo + k * LN2[0], hi + k * LN2[1]
    else:
        lo, hi = lo + k * LN2[1], hi + k * LN2[0]
    return I(rd(lo), ru(hi))

def ln(x):
    if not isinstance(x, I):
        return ln_point(x)
    assert x.lo > 0
    return I(ln_point(x.lo).lo, ln_point(x.hi).hi)

def sqrt_point(x):
    x = F(x)
    m = math.floor(x * 4 ** PREC)
    r = math.isqrt(m)
    return I(F(r, 2 ** PREC), F(r + 1, 2 ** PREC))

def xlnx(z):  # z ln z, z an interval in (0,1]
    return z * ln(z)

def ent(*ps):
    s = I(0)
    for p in ps:
        s = s - xlnx(p)
    return s

def hbin(z):
    return ent(z, 1 - z)

# ---------------- the level-1 model (q in {6,7}) ----------------
QS = (6, 7)
LNQ = {q: ln_point(q) for q in QS}
LNQ2 = {q: ln_point(q + 2) for q in QS}
LN2I = ln_point(2)

def per_q(q, u):
    """per-coordinate quantities of part q at p110 = u (all intervals)."""
    q = F(q); u = I(u)
    w = F(1) / (q + 2)
    p = q / (2 * (q + 2))
    v = (I(w) - u) * F(1, 2)
    hx = ent(I(p) + w + v, I(p) + u, v)          # X-marginal (p+w+v, p+u, v); Y alike
    hz = ent(I(w), I(q * w), I(w))                # Z-marginal (1, q, 1)/(q+2)
    lna = I(p) * LNQ[int(q)]
    lnb = u * LNQ[int(q)]
    lnC = (LNQ2[int(q)] + q * LN2I) / (q + 2)     # coverage of a uniform-type output
    lnU = I(p) * ln_point(2 * (q + 1)) + LNQ2[int(q)] / (q + 2)   # column union (r32 Sec. 1)
    return dict(slack=hx - hz, lna=lna, lnb=lnb, lnC=lnC, lnU=lnU)

def g_typ(q):
    """max_Y (1/(q+2)) [h(Y) + (1-Y) ln q + q h((1-Y)/q)] (r45 l. 110 with Y = y(q+2)); the function is concave
    in Y, its stationary point is the root of (q-1)Y^2 + (q^2-q+2)Y - 1 = 0 in (0,1), Y* = 2/(B + sqrt(B^2+4(q-1)))."""
    B = q * q - q + 2
    s = sqrt_point(B * B + 4 * (q - 1))
    Y = 2 / (s + B)
    val = (hbin(Y) + (1 - Y) * LNQ[q] + q * hbin((1 - Y) / q)) / (q + 2)
    return val, Y

GT = {q: g_typ(q) for q in QS}
EPS = ln_point(4) / (5 * ln_point(5))

def point(l6, u6, u7):
    lam = {6: F(l6), 7: 1 - F(l6)}
    uu = {6: F(u6), 7: F(u7)}
    d = {q: per_q(q, uu[q]) for q in QS}
    S = lambda key: sum((lam[q] * d[q][key] for q in QS), I(0))
    la = S("lna")
    out = dict(slack=S("slack"), alpha=S("lnb") / la, co=S("lnC") / la, ccol=S("lnU") / la)
    out["cg"] = sum((lam[q] * GT[q][0] for q in QS), I(0)) / la
    out["cprime"] = out["ccol"] - 1
    return out

def rangeF(a, c, e):          # 2 c e/(e + 2c - alpha): Hyp / single entry q < 1/2
    return 2 * c * e / (e + 2 * c - a)
def rangeQ(a, c, e, Q):       # c e/(Q e + c - Q alpha): per-entry query exponent below Q
    return c * e / (Q * e + c - Q * a)
def colF(a, c, e):            # c' e/(e + c' - alpha): column cost N D^Q, Q < 1
    return c * e / (e + c - a)

# ---------------- float search ----------------
def fl(v):
    return v.mid()

def ffun(l6, u6, u7, kind):
    import numpy as np
    lam = {6: l6, 7: 1 - l6}; uu = {6: u6, 7: u7}
    la = lb = lc = lu = sl = cg = 0.0
    for q in QS:
        w = 1 / (q + 2); p = q / (2 * (q + 2)); v = (w - uu[q]) / 2
        H = lambda *ps: -sum(x * math.log(x) for x in ps if x > 0)
        sl += lam[q] * (H(p + w + v, p + uu[q], v) - H(w, q * w, w))
        la += lam[q] * p * math.log(q); lb += lam[q] * uu[q] * math.log(q)
        lc += lam[q] * (math.log(q + 2) + q * math.log(2)) / (q + 2)
        lu += lam[q] * (p * math.log(2 * (q + 1)) + math.log(q + 2) / (q + 2))
        cg += lam[q] * fl(GT[q][0])
    a, co, cc, cgv, e = lb / la, lc / la, lu / la - 1, cg / la, math.log(4) / (5 * math.log(5))
    val = {"hyp": 2 * co * e / (e + 2 * co - a), "omv": co * e / (e + co - a),
           "r45": 2 * cgv * e / (e + 2 * cgv - a), "col": cc * e / (e + cc - a)}[kind]
    return val, sl

def search(kind):
    from scipy.optimize import minimize
    best = None
    for x0 in [(0.19, 0.995 / 8, 0.999 / 9), (0.25, 0.9 / 8, 0.99 / 9), (0.15, 0.999 / 8, 0.9999 / 9)]:
        r = minimize(lambda z: -ffun(*z, kind)[0], x0, method="SLSQP",
                     bounds=[(0.01, 0.99), (0.05, 1 / 8 - 1e-9), (0.05, 1 / 9 - 1e-9)],
                     constraints=[{"type": "ineq", "fun": lambda z: ffun(*z, kind)[1]}],
                     options={"ftol": 1e-15, "maxiter": 500})
        if best is None or -r.fun > best[0]:
            best = (-r.fun, r.x)
    return best

def main():
    out = []
    P = lambda *a: out.append(" ".join(str(x) for x in a))
    P("R211e certification (exact Fractions, outward rounding to 2^-200, ln by artanh series with tail bound)")
    P("eps* = ln4/(5 ln5) in", EPS)
    for q in QS:
        P("q=%d: g_typ (max_Y) in %s, Y* in %s, c_g(q) = g/(p ln q) in %s" % (
            q, GT[q][0], GT[q][1], GT[q][0] / (F(q, 2 * (q + 2)) * LNQ[q])))
    # R11.1
    r11 = rangeF(I(F(321334, 10 ** 6)), I(2), EPS)
    P("\nR11.1: 4 eps*/(eps* + 4 - 0.321334) in", r11, " > 0.178938:", r11.lo > F(178938, 10 ** 6),
      " > 0.178939:", r11.lo > F(178939, 10 ** 6))
    for a, name in [(F(31389, 10 ** 5), "LGU 0.31389"), (F(1, 2), "alpha 1/2 (preprints)")]:
        P("   at %s:" % name, rangeF(I(a), I(2), EPS))
    # float searches
    targets = {"hyp": F(182773, 10 ** 6), "omv": F(194639, 10 ** 6), "r45": F(187824, 10 ** 6),
               "col": F(204684, 10 ** 6)}
    names = {"hyp": "R23.1 Hyp / R77.1 OSD: 2 c_o e/(e + 2 c_o - alpha)",
             "omv": "R23.1 hinted OMv per entry / 5.12 first region: c_o e/(e + c_o - alpha)",
             "r45": "R45.1 shared queries: 2 c_g e/(e + 2 c_g - alpha)",
             "col": "R32.1 column: c' e/(e + c' - alpha)"}
    for kind in ["hyp", "omv", "r45", "col"]:
        v, x = search(kind)
        P("\n%s\n  float optimum %.9f at lam6=%.7f u6(q+2)=%.7f u7(q+2)=%.7f" % (names[kind], v, x[0], x[1] * 8, x[2] * 9))
        # rational point: round, then lower u slightly until the certified slack is > 0 and value > target
        found = False
        for den in [10 ** 6, 10 ** 7, 10 ** 8]:
            l6 = F(round(x[0] * den), den)
            for back in [0, 1, 2, 5, 10, 20, 50, 100, 200, 500]:
                u6 = F(round(x[1] * 8 * den) - back, den) / 8
                u7 = F(round(x[2] * 9 * den) - back, den) / 9
                if u6 >= F(1, 8):
                    u6 = F(den - 1 - back, den) / 8
                if u7 >= F(1, 9):
                    u7 = F(den - 1 - back, den) / 9
                d = point(l6, u6, u7)
                val = {"hyp": lambda: rangeF(d["alpha"], d["co"], EPS), "omv": lambda: colF(d["alpha"], d["co"], EPS),
                       "r45": lambda: rangeF(d["alpha"], d["cg"], EPS), "col": lambda: colF(d["alpha"], d["cprime"], EPS)}[kind]()
                if d["slack"].lo > 0 and val.lo > targets[kind]:
                    P("  CERTIFIED point lam6 = %s, u6 = %s (u6(q+2) = %s), u7 = %s (u7(q+2) = %s)" % (
                        l6, u6, u6 * 8, u7, u7 * 9))
                    P("    slack in", d["slack"], "(> 0: admissible)")
                    P("    alpha in", d["alpha"], " c_o in", d["co"], " c_g in", d["cg"], " c' in", d["cprime"])
                    P("    value in", val, " > %s: True (margin %.3e)" % (float(targets[kind]), float(val.lo - targets[kind])))
                    found = True
                    break
            if found:
                break
        if not found:
            P("  NOT certified at the printed value", float(targets[kind]))
    # Lean's points, recomputed with this code (cross-check)
    P("\nCross-check at Lean's points:")
    d = point(F(1973, 10000), F(9976, 10000) / 8, F(99873, 100000) / 9)
    P("  P1 (Numbers.lean): slack", d["slack"], "alpha", d["alpha"], "c_o", d["co"],
      "Hyp value", rangeF(d["alpha"], d["co"], EPS), "OMv per-entry value", colF(d["alpha"], d["co"], EPS))
    P("  R77 Q-table at P1 (c_o e/(Q e + c_o - Q alpha)):")
    for Q, pr in [(F(1, 10), "0.174273"), (F(3, 10), "0.178422"), (F(4, 10), "0.180571"), (F(49, 100), "0.182550"),
                  (F(1, 2), "0.182773"), (F(75, 100), "0.188520"), (F(1), "0.194639")]:
        v = rangeQ(d["alpha"], d["co"], EPS, Q)
        P("    Q = %s: %s  printed %s  value > printed: %s" % (Q, v, pr, v.lo > F(pr)))
    d2 = point(F(375691, 2000000), F(62443, 500000), F(111059, 1000000))
    P("  P2 (R32Number.lean): slack", d2["slack"], "alpha", d2["alpha"], "c'", d2["cprime"],
      "column value", colF(d2["alpha"], d2["cprime"], EPS))
    d3 = point(F(1830, 10000), F(99978, 100000) / 8, F(9999, 10000) / 9)
    P("  r45 printed point lam6 = 0.1830, u(q+2) = (0.99978, 0.9999): slack", d3["slack"], "value",
      rangeF(d3["alpha"], d3["cg"], EPS))
    txt = "\n".join(out)
    print(txt)
    with open(__file__.replace(".py", "_out.txt"), "w") as f:
        f.write(txt + "\n")

if __name__ == "__main__":
    main()
