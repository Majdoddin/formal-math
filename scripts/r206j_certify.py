"""R206j: independent certificate of R114a's thresholds (column-degree cut), q = 1 and q = 1/2.

Untrusted search in Python's decimal (60 digits); every claim printed as CERTIFIED is re-checked with the rigorous
interval logarithms of r206j_iv.py on exact rationals.

Notation (r114a.md:72-77): F(x,c) = x ln4 - (1-x)ln(1-x) - (c-1+x)ln(c-1+x) + (c-1)ln(c-1),
G(x,c) = (c-1+x)ln(c-1+x) - x ln x - (c-1)ln(c-1),
h1 = F + t(G - x ln2), h2 = F + tG (both concave in x on [0,1]),
ln4 * Lambda_col(t,c) = max h1 + max h2,  A(c) = 2c ln5 - c ln c + (c-1)ln(c-1) - (c-1)ln4,
g1 = H(x) + x ln2, g2 = H(x) + x ln4.
Lower side at (c0,t0): ln4*Lambda_col(t0,c0) < t0 q ln4  => L_col(q;c0) > 0 => eps^col_q >= ln4/A(c0).
Upper side at (c1,x1,x2): g1(x1)+g2(x2) > q ln4 and F(x1,c1)+F(x2,c1) > 0 => ln4*Lambda_col(t,c1) > t q ln4 for
all t in [0,1] => L_col(q;c1) < 0 => c*_q >= c1 => eps^col_q <= ln4/A(c1).
"""
import sys
from decimal import Decimal as Dc, getcontext
from fractions import Fraction as Fr
import r206j_iv as iv

getcontext().prec = 60
D = Dc
LN2d = D(2).ln()
LN4d = 2 * LN2d


def Fd(x, c):
    return x * LN4d - (1 - x) * (1 - x).ln() - (c - 1 + x) * (c - 1 + x).ln() + (c - 1) * (c - 1).ln()


def Gd(x, c):
    return (c - 1 + x) * (c - 1 + x).ln() - x * x.ln() - (c - 1) * (c - 1).ln()


def dh_d(x, c, t, half):
    v = LN4d + (1 - x).ln() - (1 - t) * (c - 1 + x).ln() - t * x.ln()
    return v - t * LN2d if half == 1 else v


def argmax_d(c, t, half):
    lo, hi = D("1e-40"), 1 - D("1e-40")
    for _ in range(190):
        mid = (lo + hi) / 2
        if dh_d(mid, c, t, half) > 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def hval_d(x, c, t, half):
    v = Fd(x, c) + t * Gd(x, c)
    return v - t * x * LN2d if half == 1 else v


def Lam_d(t, c):
    x1, x2 = argmax_d(c, t, 1), argmax_d(c, t, 2)
    return (hval_d(x1, c, t, 1) + hval_d(x2, c, t, 2)) / LN4d, x1, x2


def best_t(c, q):
    # maximise t q - Lam(t,c): concave in t; derivative q - dLam/dt, dLam/dt = (G1 - x1 ln2 + G2)/ln4 (envelope)
    lo, hi = D(0), D(1)
    for _ in range(80):
        mid = (lo + hi) / 2
        _, x1, x2 = Lam_d(mid, c)
        slope = q - (Gd(x1, c) - x1 * LN2d + Gd(x2, c)) / LN4d
        if slope > 0:
            lo = mid
        else:
            hi = mid
    t = (lo + hi) / 2
    lam, x1, x2 = Lam_d(t, c)
    return t, t * q - lam, x1, x2


def cstar(q, clo=D("4.3"), chi=D("4.95"), steps=75):
    for _ in range(steps):
        mid = (clo + chi) / 2
        if best_t(mid, q)[1] > 0:
            chi = mid
        else:
            clo = mid
    return (clo + chi) / 2


def A_d(c):
    return 2 * c * D(5).ln() - c * c.ln() + (c - 1) * (c - 1).ln() - (c - 1) * LN4d


# ---------------- rigorous part ----------------
L2 = iv.LN2
L4 = iv.scale(2, L2)
L5 = iv.ln(5)


def h_iv(x, c, t, half):
    x, c, t = Fr(x), Fr(c), Fr(t)
    terms = [(x, L4), (-(1 - x), iv.ln(1 - x)), (-(1 - t) * (c - 1 + x), iv.ln(c - 1 + x)),
             ((1 - t) * (c - 1), iv.ln(c - 1)), (-t * x, iv.ln(x))]
    if half == 1:
        terms.append((-t * x, L2))
    return iv.lin(*terms)


def dh_iv(x, c, t, half):
    x, c, t = Fr(x), Fr(c), Fr(t)
    terms = [(1, L4), (1, iv.ln(1 - x)), (-(1 - t), iv.ln(c - 1 + x)), (-t, iv.ln(x))]
    if half == 1:
        terms.append((-t, L2))
    return iv.lin(*terms)


def F_iv(x, c):
    x, c = Fr(x), Fr(c)
    return iv.lin((x, L4), (-(1 - x), iv.ln(1 - x)), (-(c - 1 + x), iv.ln(c - 1 + x)), (c - 1, iv.ln(c - 1)))


def g_iv(x, half):
    x = Fr(x)
    return iv.lin((-x, iv.ln(x)), (-(1 - x), iv.ln(1 - x)), (x, L2 if half == 1 else L4))


def A_iv(c):
    c = Fr(c)
    return iv.lin((2 * c, L5), (-c, iv.ln(c)), (c - 1, iv.ln(c - 1)), (-(c - 1), L4))


def max_upper(c, t, half, xstar, delta=Fr(1, 10 ** 24)):
    """Rigorous upper bound on max_{[0,1]} h_half(., c, t) for concave h, from a bracket a < x* < b."""
    xs = Fr(str(xstar))
    a, b = xs - delta, xs + delta
    da, db = dh_iv(a, c, t, half), dh_iv(b, c, t, half)
    assert da[0] > 0 and db[1] < 0, "bracket not certified"
    ha, hb = h_iv(a, c, t, half), h_iv(b, c, t, half)
    u1 = ha[1] + da[1] * (b - a)          # tangent at a, evaluated at b (x* <= b, tangent increasing)
    u2 = hb[1] + (-db[0]) * (b - a)       # tangent at b, evaluated at a
    return min(u1, u2), a, b


def lower_side(q, c0, t0, label):
    q, c0, t0 = Fr(q), Fr(c0), Fr(t0)
    cd, td = D(c0.numerator) / D(c0.denominator), D(t0.numerator) / D(t0.denominator)
    x1, x2 = argmax_d(cd, td, 1), argmax_d(cd, td, 2)
    U1, a1, b1 = max_upper(c0, t0, 1, x1)
    U2, a2, b2 = max_upper(c0, t0, 2, x2)
    rhs_lo = t0 * q * L4[0]
    marg = rhs_lo - (U1 + U2)
    Ahi = A_iv(c0)[1]
    eps_lo = L4[0] / Ahi
    gam_lo = marg / L4[1]
    ok = marg > 0 and 0 <= t0 <= 1 and c0 > 3
    print(f"[{label}] lower side q={q} c0={float(c0):.12f} ({c0}) t0={float(t0):.12f}")
    print(f"    maximisers x1 in [{float(a1):.15f}, {float(b1):.15f}], x2 in [{float(a2):.15f}, {float(b2):.15f}]")
    print(f"    upper bound ln4*Lambda_col(t0,c0) <= {float(U1 + U2):.13e}   t0*q*ln4 >= {float(rhs_lo):.13e}")
    print(f"    margin (nats) >= {float(marg):.6e};  gamma = t0 q - Lambda_col >= {float(gam_lo):.6e} (units of ln D)")
    print(f"    eps^col_q >= ln4/A(c0) >= {eps_lo:.0f}" if False else
          f"    eps^col_q >= ln4/A(c0) >= {float(eps_lo):.13f}   (exact lower bound {str(eps_lo)[:0]}as rational kept)")
    print(f"    CERTIFIED: {ok}")
    return ok, eps_lo, gam_lo


def upper_side(q, c1, x1, x2, label):
    q, c1, x1, x2 = Fr(q), Fr(c1), Fr(x1), Fr(x2)
    gsum = iv.add(g_iv(x1, 1), g_iv(x2, 2))
    gmarg = gsum[0] - q * L4[1]
    Fs = iv.add(F_iv(x1, c1), F_iv(x2, c1))
    eps_hi = L4[1] / A_iv(c1)[0]
    ok = gmarg > 0 and Fs[0] > 0
    print(f"[{label}] upper side q={q} c1={float(c1):.12f} x1={float(x1)} x2={float(x2)}")
    print(f"    g1(x1)+g2(x2) - q ln4 >= {float(gmarg):.6e};  F(x1,c1)+F(x2,c1) >= {float(Fs[0]):.6e} (<= {float(Fs[1]):.6e})")
    print(f"    eps^col_q <= ln4/A(c1) <= {float(eps_hi):.13f}")
    print(f"    CERTIFIED: {ok}")
    return ok, eps_hi


def primal_point(q, c, nudge=D("1e-22")):
    """At c < c*_q: tilted maximisers at the t where g1+g2 = q ln4 (KKT), nudged up so the strict inequality holds."""
    lo, hi = D(0), D(1)
    for _ in range(90):
        mid = (lo + hi) / 2
        x1, x2 = argmax_d(c, mid, 1), argmax_d(c, mid, 2)
        gs = -x1 * x1.ln() - (1 - x1) * (1 - x1).ln() + x1 * LN2d - x2 * x2.ln() - (1 - x2) * (1 - x2).ln() + x2 * LN4d
        if gs < q * LN4d:
            lo = mid
        else:
            hi = mid
    t = hi
    x1, x2 = argmax_d(c, t, 1), argmax_d(c, t, 2)
    return x1 + nudge, x2 + nudge, t


def main():
    out = []
    print("# R206j certificate of R114a's two thresholds (own code; decimal search, rigorous check)")
    ok_all = True
    # 1. R114a's own points (r114a.md:230-231)
    r114 = {
        1: dict(c0="4.5108852936", t0="0.0523815335", c1="4.5108848936", x1="0.18220", x2="0.20276"),
        Fr(1, 2): dict(c0="4.8104012867", t0="0.0137180889", c1="4.8104008867", x1="0.07220", x2="0.07847"),
    }
    for q, p in r114.items():
        ok, e_lo, _ = lower_side(q, Fr(p["c0"]), Fr(p["t0"]), "r114a point")
        ok_all &= ok
        ok, e_hi = upper_side(q, Fr(p["c1"]), Fr(p["x1"]), Fr(p["x2"]), "r114a point, printed digits")
        if not ok:
            cd = D(p["c1"])
            x1, x2, t = primal_point(D(1) if q == 1 else D("0.5"), cd)
            print(f"    printed (x1,x2) does not certify; KKT point at c1: x1={x1:.25f} x2={x2:.25f} (t={t:.12f})")
            ok, e_hi = upper_side(q, Fr(p["c1"]), Fr(str(x1)), Fr(str(x2)), "r114a c1, own KKT point")
        ok_all &= ok
    # 2. own tighter enclosure around the float zero c*_q
    for q in (1, Fr(1, 2)):
        qd = D(1) if q == 1 else D("0.5")
        cs = cstar(qd)
        t, L, x1, x2 = best_t(cs, qd)
        print(f"[float] q={q}: c*_q = {cs:.18f}, t* = {t:.12f}, x1* = {x1:.12f}, x2* = {x2:.12f}, "
              f"eps = ln4/A(c*) = {LN4d / A_d(cs):.15f}")
        delta = D("1e-11")
        c0 = cs + delta
        t0, L0, _, _ = best_t(c0, qd)
        c0f = Fr(str(c0.quantize(D("1e-20"))))
        t0f = Fr(str(t0.quantize(D("1e-16"))))
        ok, e_lo, g_lo = lower_side(q, c0f, t0f, "own tight point")
        ok_all &= ok
        c1 = cs - delta
        c1f = Fr(str(c1.quantize(D("1e-20"))))
        x1u, x2u, tu = primal_point(qd, D(c1f.numerator) / D(c1f.denominator))
        ok, e_hi = upper_side(q, c1f, Fr(str(x1u)), Fr(str(x2u)), "own tight point")
        ok_all &= ok
        print(f"    => CERTIFIED enclosure q={q}: c*_q in ({float(c1f):.13f}, {float(c0f):.13f}),"
              f" eps^col_q in ({float(e_lo):.13f}, {float(e_hi):.13f})")
    print("ALL CERTIFIED:", ok_all)


if __name__ == "__main__":
    main()
