"""R211b (2026-11-18): independent re-certification of r74a, R74(e) and R117 printed values (CP part B1).

Library: r211b_lib.py (own interval arithmetic over Fractions; no mpmath interval, no r74a/r117 code).
Run: nice -n 19 ~/.venv/bin/python3 r211b_cert.py > r211b_cert_out.txt
Every "certified" number below is an outward-rounded enclosure; floats are printed only as labels.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import r211b_lib as L
from r211b_lib import I, ln, rup, rdn
import mpmath as mp

W = sys.stdout.write


def dn(x, d=12):
    """decimal string <= x (floor at d decimals)"""
    x = Fr(x)
    if x < 0:
        return '-' + dn_ceil(-x, d)
    n = (x.numerator * 10 ** d) // x.denominator
    return f"{n // 10 ** d}.{n % 10 ** d:0{d}d}"


def up(x, d=12):
    return '-' + dn(-Fr(x), d) if Fr(x) < 0 else dn_ceil(x, d)


def dn_ceil(x, d):
    x = Fr(x)
    if x < 0:
        return '-' + dn(-x, d)
    n = -((-x.numerator * 10 ** d) // x.denominator)
    return f"{n // 10 ** d}.{n % 10 ** d:0{d}d}"


def iv(x, d=12):
    return f"[{dn(x.lo, d)}, {dn_ceil(x.hi, d)}]"


def claim(ok, text):
    W(("  CHECK OK    " if ok else "  CHECK FAILS ") + text + "\n")
    return ok


# ---------------------------------------------------------------- (0) self-tests
def selftest():
    W("(0) self-tests\n")
    mp.mp.dps = 60
    worst = 0
    for x in [Fr(2), Fr(3), Fr(7, 19), Fr(10), Fr(1, 7), Fr(979, 9000), Fr(123456789, 1000), Fr(1, 10 ** 9)]:
        r = ln(x)
        m = mp.log(mp.mpf(x.numerator) / x.denominator)
        ok = mp.mpf(r.lo.numerator) / r.lo.denominator <= m + mp.mpf(10) ** -55 and \
            m - mp.mpf(10) ** -55 <= mp.mpf(r.hi.numerator) / r.hi.denominator
        worst = max(worst, float(r.width()))
        claim(ok, f"ln({x}) enclosure {iv(r, 20)} contains mpmath's 60-digit value (width {float(r.width()):.1e})")
    # mpmath interval arithmetic as a second trust base, for the two r74a G-values below (section 1 repeats them)
    W(f"  largest enclosure width {worst:.1e}\n")
    # second trust base: mpmath interval arithmetic (iv) for F_6, F_7 at the rational z0 used in (1)
    from mpmath import iv as miv
    miv.dps = 50
    t = Fr(49, 2500)
    for q in (6, 7):
        b, F, g, z0 = L.Gq_auto(q, t)
        u, v, y = (miv.mpf(c.numerator) / c.denominator for c in z0)
        tt = miv.mpf(49) / 2500
        pi = miv.mpf(1) / (q + 2)
        a = q * pi - u + v; bb = pi + u; o = pi - v; w = q * pi - u + y
        ph = lambda s: s * miv.log(s)
        D = ph(a) - a * miv.log(q * pi) + ph(bb) - bb * miv.log(pi) + ph(o) - o * miv.log(pi)
        sg = ph(bb) - ph(pi) - ph(y) - ph(u - y) + (u - y) * miv.log(q) + ph(a) - ph(v - y) - ph(w)
        Fm = -D + tt * sg
        lo_ok = mp.mpf(F.lo.numerator) / F.lo.denominator <= Fm.b + mp.mpf(10) ** -45
        hi_ok = Fm.a - mp.mpf(10) ** -45 <= mp.mpf(F.hi.numerator) / F.hi.denominator
        claim(lo_ok and hi_ok, f"F_{q}(49/2500; z0): own enclosure {iv(F, 22)} overlaps mpmath iv {Fm}")


# ---------------------------------------------------------------- helpers
def show_point(name, parts):
    P = L.point(parts)
    W(f"  {name}: parts {[(q, str(Fr(l)), str(Fr(f))) for q, l, f in parts]}\n")
    W(f"    slack {iv(P['slack'], 12)}  alpha {iv(P['alpha'], 13)}  ln a_1 {iv(P['lna'], 13)}  "
      f"ln b_1 {iv(P['lnb'], 13)}  cbar {iv(P['cbar'], 9)}\n")
    claim(P['slack'].lo > 0, "slack(P) > 0 (P admissible)")
    return P


def gamma_level1(P, parts, t, verbose=True):
    """gamma_inf = t/2 - sum_q lam_q G_q(t)/ln b_1 (Theorem D, x -> infinity), certified lower bound"""
    t = Fr(t)
    tot = I(0)
    for q, lam, f in parts:
        b, F, g, z0 = L.Gq_auto(q, t)
        if verbose:
            W(f"    G_{q}({t}) <= {dn_ceil(b, 22)}  (z0 = {[f'{float(c):.7e}' for c in z0]}, "
              f"max|g_i| = {max(float(x.absmax()) for x in g):.1e})\n")
        tot = tot + I(b) * Fr(lam)
    Lam_cert = tot / P['lna']
    gam = I(t / 2) - tot / P['lnb']
    return gam, Lam_cert


def eps1_of(alpha, a_mix, gam_lo):
    """largest eps (lower bound) with 1/eps - a_mix >= gam_lo: eps1 = 1/(a_mix + gam_lo)"""
    return (cvI(a_mix) + gam_lo).inv().lo


def cvI(x):
    return x if isinstance(x, I) else I(x)


def tcheck(P, t):
    lim = (P['cbar'] + 2).inv()
    return claim(Fr(t) <= lim.lo, f"t = {t} <= 1/(cbar + 2) (>= {dn(lim.lo, 4)})")


# ---------------------------------------------------------------- (1) r74a at P0
def part1():
    W("\n(1) r74a: Theorem D at the level-1 point P0, t = 49/2500\n")
    parts = [(6, Fr(7, 19), Fr(97, 100)), (7, Fr(12, 19), Fr(979, 1000))]
    P = show_point("P0", parts)
    claim(Fr(2945976, 10 ** 7) < P['alpha'].lo and P['alpha'].hi < Fr(2945977, 10 ** 7), "0.2945976 < alpha(P0) < 0.2945977")
    claim(P['cbar'].hi <= Fr(1077861, 10 ** 6), "cbar(P0) <= 1.077861")
    t = Fr(49, 2500)
    tcheck(P, t)
    gam, Lc = gamma_level1(P, parts, t)
    W(f"    Lambda_cert(t) in {iv(Lc, 15)};  gamma_inf in {iv(gam, 15)}\n")
    claim(Lc.hi <= Fr(170915331, 10 ** 11), "Lambda_cert(49/2500) <= 0.00170915331 (r74a.md:5)")
    claim(gam.lo >= Fr(39983470, 10 ** 10), "gamma_inf >= 0.0039983470 (r74a.md:8)")
    claim(gam.lo >= Fr(399834705824, 10 ** 14), "gamma_inf >= 0.00399834705824 (r74a.md:103)")
    e1 = eps1_of(None, P['alpha'].inv(), gam.lo)
    W(f"    eps1 = 1/(1/alpha + gamma_inf) >= {dn(e1, 12)};  eps1*gamma_inf >= {dn(e1 * gam.lo, 15)}\n")
    claim(e1 >= Fr(2942510, 10 ** 7), "eps1 >= 0.2942510 (r74a.md:8)")
    claim(e1 * gam.lo >= Fr(1176517811, 10 ** 12), "eps1*gamma_inf >= 1.176517811e-3 (r74a.md:109)")
    g = Fr(3998, 10 ** 6); e = Fr(29425, 10 ** 5)
    enc = (I(1 / e) - P['alpha'].inv()).lo
    claim(g < gam.lo and g < enc, f"Hyp(eps, 0.003998) for every eps <= 0.29425: 0.003998 < gamma_inf and "
          f"0.003998 < 1/0.29425 - 1/alpha (>= {dn(enc, 9)})")
    # other tilts of r74a.md:105-107
    W("    other tilts (r74a.md:105-107):\n")
    for tt, pr in [(Fr(15, 1000), Fr(38136, 10 ** 7)), (Fr(18, 1000), Fr(39770, 10 ** 7)), (Fr(19, 1000), Fr(399556, 10 ** 8)),
                   (Fr(195, 10000), Fr(399831, 10 ** 8)), (Fr(197, 10000), Fr(399821, 10 ** 8)), (Fr(20, 1000), Fr(399678, 10 ** 8)),
                   (Fr(21, 1000), Fr(398101, 10 ** 8)), (Fr(25, 1000), Fr(37542, 10 ** 7))]:
        g2, _ = gamma_level1(P, parts, tt, verbose=False)
        claim(g2.lo >= pr, f"t = {tt}: gamma_inf >= {dn(g2.lo, 10)} vs printed lower bound {float(pr):.6g}")
    return P


# ---------------------------------------------------------------- (2) R74(e) rows
R74E = [  # (label, parts, t, printed gamma_inf, printed eps bound)
    ("q 13/14", [(13, Fr(33, 50), Fr(999999, 10 ** 6)), (14, Fr(17, 50), Fr(999999, 10 ** 6))], Fr(23, 1000), Fr(4790512, 10 ** 9), Fr(149908, 10 ** 6)),
    ("q 11/12", [(11, Fr(73, 200), Fr(999999, 10 ** 6)), (12, Fr(127, 200), Fr(999999, 10 ** 6))], Fr(1133, 50000), Fr(4699696, 10 ** 9), Fr(171889, 10 ** 6)),
    ("q 10", [(10, Fr(1), Fr(999999, 10 ** 6))], Fr(2221, 100000), Fr(4584163, 10 ** 9), Fr(199817, 10 ** 6)),
    ("q 8", [(8, Fr(1), Fr(999999, 10 ** 6))], Fr(1067, 50000), Fr(4372342, 10 ** 9), Fr(249727, 10 ** 6)),
    ("q 6/7", [(6, Fr(41, 400), Fr(999999, 10 ** 6)), (7, Fr(359, 400), Fr(999999, 10 ** 6))], Fr(2051, 100000), Fr(4199120, 10 ** 9), Fr(289745, 10 ** 6)),
]


def part2():
    W("\n(2) R74(e): certified level-1 points (r74e.md:207-213)\n")
    out = {}
    for lab, parts, t, pg, pe in R74E:
        P = show_point(lab, parts)
        tcheck(P, t)
        gam, Lc = gamma_level1(P, parts, t)
        e1 = eps1_of(None, P['alpha'].inv(), gam.lo)
        W(f"    gamma_inf in {iv(gam, 12)};  eps1 >= {dn(e1, 8)};  eps1*gamma >= {dn(e1 * gam.lo, 10)}\n")
        claim(gam.lo >= pg, f"gamma_inf >= printed {float(pg):.7g}")
        claim(e1 >= pe, f"eps1 >= printed {float(pe):.6f}, so Hyp(eps, {float(pg):.7g}) for every eps <= {float(pe):.6f}")
        out[lab] = (gam, e1)
    return out


# ---------------------------------------------------------------- (3) R117 products CW(6/7) x G(c)
R117 = [  # (label, parts, c, t, f, profile, printed Qc, printed eps1)
    ("0.172", Fr(603, 100), Fr(53, 1000), Fr(663, 1000), 'sharp', Fr(14247718, 10 ** 9), Fr(1716089, 10 ** 7)),
    ("0.20", Fr(146, 25), Fr(79, 2000), Fr(187, 400), 'sharp', Fr(93078383, 10 ** 10), Fr(1996354, 10 ** 7)),
    ("0.25", Fr(563, 100), Fr(1313, 50000), Fr(3, 16), 'sharp', Fr(55504155, 10 ** 10), Fr(2494767, 10 ** 7)),
    ("0.29", Fr(553, 100), Fr(13, 625), Fr(31, 2500), 'sharp', Fr(42557500, 10 ** 10), Fr(2894198, 10 ** 7)),
    ("0.20pr", Fr(2519, 500), Fr(143, 100000), Fr(653, 1000), 'crude', Fr(32709421, 10 ** 11), Fr(1999748, 10 ** 7)),
    ("0.18pr", Fr(101, 20), Fr(83, 20000), Fr(1749, 2000), 'crude', Fr(99104972, 10 ** 11), Fr(1799804, 10 ** 7)),
]
P117S = [(6, Fr(9, 50), Fr(999999, 10 ** 6)), (7, Fr(41, 50), Fr(999999, 10 ** 6))]
P117C = [(6, Fr(21, 100), Fr(9957, 10000)), (7, Fr(79, 100), Fr(4987, 5000))]


def product_point(parts, P, c, t, f, profile, verbose=True):
    t, c, f = Fr(t), Fr(c), Fr(f)
    tot = I(0)
    for q, lam, _ in parts:
        if profile == 'sharp':
            b, F, g, z0 = L.Gq_auto(q, t)
            bI = I(b)
        else:
            bI = L.Lpr_iv(q, t)
            b = bI.hi
        if verbose:
            W(f"    CW part q = {q}: {'G_q' if profile == 'sharp' else 't^2 ln^2(4eq/t)'}({t}) <= {dn_ceil(b, 15)}\n")
        tot = tot + bI * lam
    LamCW = tot / P['lnb']           # Lambda/alpha per ln D of the CW share
    LG, x0 = L.LamG_auto(t, c)
    Ac = L.A_iv(c) / ln(4)
    Qc = I(t / 2) - LamCW * (1 - f) - LG * f
    amix = P['alpha'].inv() * (1 - f) + Ac * f
    e1 = (amix + I(Qc.lo)).inv().lo
    if verbose:
        W(f"    Lambda_CW/alpha <= {dn_ceil(LamCW.hi, 12)};  Lambda_G({t}, {c}) <= {dn_ceil(LG.hi, 12)} (x0 = {float(x0):.6e});"
          f"  A(c)/ln4 in {iv(Ac, 10)}\n")
        W(f"    query term Q >= {dn(Qc.lo, 12)};  encoding sum f_i a_i <= {dn_ceil(amix.hi, 10)};  "
          f"eps1 = 1/(sum f_i a_i + Q) >= {dn(e1, 9)};  eps1*Q >= {dn(e1 * Qc.lo, 9)}\n")
    return Qc, amix, e1


def part3():
    W("\n(3) R117: certified product points (r117.md:91-96, :101-103), Theorem D_x with f_dir = 0\n")
    PS = show_point("P (sharp rows)", P117S)
    PC = show_point("P (closed-form rows)", P117C)
    for lab, c, t, f, prof, pq, pe in R117:
        P, parts = (PS, P117S) if prof == 'sharp' else (PC, P117C)
        W(f"  row eps~{lab}: c = {c}, t = {t}, f_G = {f}, CW profile {prof}\n")
        tcheck(P, t)
        Qc, amix, e1 = product_point(parts, P, c, t, f, prof)
        claim(Qc.lo >= pq, f"Q >= printed {float(pq):.8g}")
        claim(e1 >= pe, f"eps1 >= printed {float(pe):.7f}: Hyp(eps, gamma) for every gamma < {float(pq):.8g} and every eps < {float(pe):.7f}")


if __name__ == "__main__":
    selftest()
    part1()
    part2()
    part3()
    W("\nDONE\n")
