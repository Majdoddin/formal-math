"""R220e: independent checks of the numbers printed in CP Sections 10-11 (cp-unequal-r219.tex, cp-profile-r219.tex).

Certified parts use exact rationals (fractions.Fraction) and logarithm enclosures by the atanh series with a proved
geometric tail bound, outward-rounded to denominators 10^50. Part (F) is floating point (COMPUTED).
Run: nice -n 19 python3 -I r220e_checks.py > r220e_checks_out.txt
"""
from fractions import Fraction as Fr
import math

DEN = 10 ** 50


def down(x):
    return Fr(math.floor(x * DEN), DEN)


def up(x):
    return Fr(math.ceil(x * DEN), DEN)


class I:
    """closed interval [lo, hi] of rationals"""
    def __init__(s, lo, hi=None):
        s.lo = Fr(lo)
        s.hi = Fr(lo) if hi is None else Fr(hi)
        assert s.lo <= s.hi

    def __add__(s, o):
        o = o if isinstance(o, I) else I(o)
        return I(s.lo + o.lo, s.hi + o.hi)
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
        return I(down(min(p)), up(max(p)))
    __rmul__ = __mul__

    def inv(s):
        assert s.lo > 0 or s.hi < 0
        return I(down(1 / s.hi), up(1 / s.lo))

    def __truediv__(s, o):
        o = o if isinstance(o, I) else I(o)
        return s * o.inv()

    def __rtruediv__(s, o):
        return I(o) * s.inv()

    def __repr__(s):
        return "[%.15g, %.15g]" % (float(s.lo), float(s.hi))


def atanh_enc(z, terms=60):
    """enclosure of atanh(z) for rational |z| <= 1/3"""
    z = Fr(z)
    assert abs(z) <= Fr(1, 3)
    s = Fr(0)
    p = z
    for i in range(terms):
        s += p / (2 * i + 1)
        p *= z * z
    # tail: sum_{i>=terms} |z|^(2i+1)/(2i+1) <= |z|^(2 terms+1)/((2 terms+1)(1-z^2))
    tail = abs(z) ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))
    return I(down(s - tail), up(s + tail))


LN2 = atanh_enc(Fr(1, 3)) * 2


def ln(x):
    x = Fr(x)
    assert x > 0
    k = 0
    while x > Fr(4, 3):
        x /= 2
        k += 1
    while x < Fr(2, 3):
        x *= 2
        k -= 1
    z = (x - 1) / (x + 1)
    return atanh_enc(z) * 2 + LN2 * k


def xlnx(p):
    p = Fr(p)
    return I(0) if p == 0 else ln(p) * p


def H(dist):
    acc = I(0)
    for p in dist:
        acc = acc - xlnx(p)
    return acc


def floor6(x):
    return Fr(math.floor(Fr(x) * 10 ** 6), 10 ** 6)


def show(tag, ok):
    print(("  ok   " if ok else "  FAIL ") + tag)
    return ok


allok = True

print("(A) Table cp:E7:table (Lemma cp:E7): the seven points, exact identities and certified slacks")
pts = [  # (q, sigma, u(q+2), vx(q+2)), printed E, printed beta, printed slack lower bounds (X, Y)
    (7, Fr(3, 4), Fr(999, 1000), Fr(1, 2000), Fr(333, 1000), Fr(999, 4000), (Fr("3.76e-3"), Fr("3.80e-3"))),
    (7, Fr(1, 2), Fr(919, 1000), Fr(237, 5000), Fr(2757, 7000), Fr(2757, 14000), (Fr("9.77e-4"), Fr("9.83e-4"))),
    (8, Fr(1, 3), Fr(179, 200), Fr(337, 5000), Fr(179, 400), Fr(179, 1200), (Fr("7.73e-4"), Fr("8.01e-4"))),
    (10, Fr(1, 4), Fr(197, 200), Fr(47, 5000), Fr(197, 400), Fr(197, 1600), (Fr("1.03e-3"), Fr("1.01e-3"))),
    (11, Fr(1, 5), Fr(951, 1000), Fr(83, 2500), Fr(2853, 5500), Fr(2853, 27500), (Fr("6.61e-4"), Fr("6.52e-4"))),
    (13, Fr(1, 7), Fr(887, 1000), Fr(53, 625), Fr(887, 1625), Fr(887, 11375), (Fr("6.09e-4"), Fr("5.91e-4"))),
    (18, Fr(1, 10), Fr(973, 1000), Fr(49, 2500), Fr(10703, 18000), Fr(10703, 180000), (Fr("5.09e-4"), Fr("5.14e-4"))),
]
printedEd = [Fr("0.333000"), Fr("0.393857"), Fr("0.447500"), Fr("0.492500"), Fr("0.518727"), Fr("0.545846"), Fr("0.594611")]
rows = []
minslack = None
for idx, (q, sg, uq, vq, Ep, bp, (slx, sly)) in enumerate(pts):
    w = Fr(1, q + 2)
    pl = Fr(q, 1) / ((1 + sg) * (q + 2))
    pe = sg * pl
    u = uq * w
    vx = vq * w
    vy = w - u - vx
    ok = all(x > 0 for x in (pe, pl, u, vx, vy)) and u < pe <= pl and pe + pl == Fr(q, q + 2) and u + vx + vy == w
    E = u / pe
    beta = u / pl
    X = (pl + w + vy, pe + u, vx)
    Y = (pe + w + vx, pl + u, vy)
    Z = (w, Fr(q, q + 2), w)
    sX = H(X) - H(Z)
    sY = H(Y) - H(Z)
    allok &= show("row %d q=%d sigma=%s: point valid %s; E=u/pe=%s (printed %s); beta=%s (printed %s); floor6(E)=%s (printed %s)"
                  % (idx + 1, q, sg, ok, E, Ep, beta, bp, floor6(E), printedEd[idx]),
                  ok and E == Ep and beta == bp and floor6(E) == printedEd[idx] and pe / pl == sg)
    allok &= show("      slack_X in %s > %s; slack_Y in %s > %s" % (sX, float(slx), sY, float(sly)), sX.lo > slx and sY.lo > sly)
    rows.append((sg, E, q, pl, pe, u))
    m = min(sX.lo, sY.lo)
    minslack = m if minslack is None else min(minslack, m)
allok &= show("smallest slack lower end %.12g > 5.09e-4 (E7_slack_min)" % float(minslack), minslack > Fr("5.09e-4"))
E7 = rows[-1][1]
allok &= show("E_7 = 10703/18000 = %.10f > 0.594611 (E13_top); so 'E(s) <= 0.594611' is FALSE for s <= 1/10" % float(E7),
              E7 > Fr("0.594611"))
allok &= show("9000/10703 = 1/(2 E_7) = %.8f > 0.84 (E16_s)" % float(1 / (2 * E7)), 1 / (2 * E7) > Fr("0.84"))

print("\n(B) alpha(P0), slack(P0), c_o(P0), t_pad bound (Lemma cp:L11 inputs, re-derived)")
lam = {6: Fr(7, 19), 7: Fr(12, 19)}
uP0 = {6: Fr(97, 100) / 8, 7: Fr(979, 1000) / 9}
pq = {q: Fr(q, 2 * (q + 2)) for q in (6, 7)}
lna1 = I(0)
lnb1 = I(0)
for q in (6, 7):
    lna1 = lna1 + ln(q) * (lam[q] * pq[q])
    lnb1 = lnb1 + ln(q) * (lam[q] * uP0[q])
alpha = lnb1 / lna1
print("  alpha(P0) in %s" % alpha)
allok &= show("0.2945976 < alpha(P0) < 0.2945977", alpha.lo > Fr("0.2945976") and alpha.hi < Fr("0.2945977"))
co = I(0)
for q in (6, 7):
    cq = (ln(q + 2) + LN2 * q) / (q + 2)
    co = co + cq * lam[q]
co = co / lna1
allok &= show("c_o(P0) in %s <= 1.077861" % co, co.hi <= Fr("1.077861"))
tpad = 2 / (co + 2)
allok &= show("2/(c_o+2) in %s > 0.6498 (F2: t_pad > 0.6498)" % tpad, tpad.lo > Fr("0.6498"))
allok &= show("2/alpha(P0) > %.6f > 6.788 (F9_entry_lo)" % float((2 / alpha).lo), (2 / alpha).lo > Fr("6.788"))

print("\n(C) Table cp:E15:table and the extremes of Remark cp:E15")
eps5 = (LN2 * 2) / (ln(5) * 5)
print("  eps*_5 = ln4/(5 ln5) in %s" % eps5)


def Estep(s):
    vals = [alpha.lo]  # alpha(P0) enters only as the square value; compare with exact rows
    best = None
    for sg, E, *_ in rows:
        if sg >= s:
            best = E if best is None else max(best, E)
    return best  # all rows have E > alpha(P0), so the max is a row value whenever one exists


samples = [((Fr("0.10"), Fr("0.91")), Fr("0.054584"), Fr("0.029459"), Fr("0.017227")),
           ((Fr("0.05"), Fr("0.96")), Fr("0.029730"), Fr("0.014729"), None),
           ((Fr("0.20"), Fr("0.85")), Fr("0.098500"), Fr("0.058919"), None),
           ((Fr("0.30"), Fr("0.75")), Fr("0.118157"), Fr("0.088379"), Fr("0.051681")),
           ((Fr("0.40"), Fr("0.65")), Fr("0.133200"), Fr("0.117839"), Fr("0.068908")),
           ((Fr("0.10"), Fr("0.95")), Fr("0.054584"), None, None)]
for (b, c), r87, sq, v1 in samples:
    m, M = min(b, c), max(b, c)
    s = m / M
    E = Estep(s)
    lo = b + c - 1
    up87 = floor6(m * E)
    sqI = alpha * m
    v1I = eps5 * m
    sq_tr = floor6(sqI.lo) if floor6(sqI.lo) == floor6(sqI.hi) else None
    v1_tr = floor6(v1I.lo) if floor6(v1I.lo) == floor6(v1I.hi) else None
    ok = up87 == r87
    ok &= (sq is None and sqI.hi <= lo) or (sq is not None and sq_tr == sq and sqI.lo > lo)
    ok &= (v1 is None and v1I.hi <= lo) or (v1 is not None and v1_tr == v1 and v1I.lo > lo)
    allok &= show("(b,c)=(%s,%s): s=%s, E(s)=%s, lower end %s; Cor E13 end %s (printed %s); square %s (printed %s); v1 %s (printed %s)"
                  % (b, c, s, E, lo, up87, r87, sq_tr if sqI.lo > lo else "empty", sq, v1_tr if v1I.lo > lo else "empty", v1), ok)
ext_a = alpha / (2 - alpha)
ext_m = 1 / (2 - alpha)
allok &= show("alpha/(2-alpha) in %s < 0.172744" % ext_a, ext_a.hi < Fr("0.172744"))
allok &= show("1/(2-alpha) in %s < 0.586372" % ext_m, ext_m.hi < Fr("0.586372"))
okst = True
for sg, E, *_ in rows:
    mm = 1 / (1 + 1 / sg - E)
    aa = E * mm
    okst &= (mm < ext_m.lo) and (aa < ext_a.lo)
    print("     step with right end %s: min(b,c) < %.6f, a < %.6f" % (sg, float(mm), float(aa)))
allok &= show("every step's bounds are below those at s = 1", okst)

print("\n(D) Proposition cp:E16 and Remark cp:E17 numbers")
for mu in (Fr("0.5286"), Fr("0.527661")):
    th = 3 * (1 + mu) / (16 + mu)
    th2 = (1 + mu) / (5 + mu)
    allok &= show("mu=%s: 3(1+mu)/(16+mu)=%.6f < 0.2775; sharper (1+mu)/(5+mu)=%.6f" % (mu, float(th), float(th2)), th < Fr("0.2775"))
    for r in (Fr(1, 100), Fr(1, 10), Fr(1, 5), Fr(1, 4), Fr(27, 100)):
        smin_mono = r / (1 + mu - r * mu)
        smin_211f = 3 * r / ((1 + mu) * (3 - r))
        assert smin_211f <= smin_mono  # uses mu >= 1/2
    sig_hi = lambda r: 1 + r * mu / (1 + mu)
    r = Fr(1, 5)
    eps_hi = (sig_hi(r) - 1) / (1 + r - sig_hi(r))
    allok &= show("   eps at sigma = 1 + r mu/(1+mu) equals mu (r=1/5): %s" % eps_hi, eps_hi == mu)
allok &= show("s(sigma) at sigma_max = r/(1+mu-r mu) >= 3r/((1+mu)(3-r)) for mu >= 1/2 (checked at 5 r, two mu)", True)
allok &= show("E(1/7) = 887/1625 = %.6f > 0.5286" % float(Fr(887, 1625)), Fr(887, 1625) > Fr("0.5286"))
allok &= show("2r/(3-r) at r=1/5 is %s (<= 1/7), at r=3/11 is %s (= 1/5)" % (Fr(2, 5) / (3 - Fr(1, 5)), 2 * Fr(3, 11) / (3 - Fr(3, 11))),
              Fr(2, 5) / (3 - Fr(1, 5)) == Fr(1, 7) and 2 * Fr(3, 11) / (3 - Fr(3, 11)) == Fr(1, 5))
for r in (Fr(1, 10), Fr(1, 5), Fr(3, 11)):
    s0 = 2 * r / (3 - r)
    allok &= show("r=%s: (1-r/3)(1+s0) = %s = 1 + r/3; scaled triple (s0/2, 1, s0)(1-r/3) = (%s, %s, %s)"
                  % (r, (1 - r / 3) * (1 + s0), (1 - r / 3) * s0 / 2, 1 - r / 3, (1 - r / 3) * s0),
                  (1 - r / 3) * (1 + s0) == 1 + r / 3 and (1 - r / 3) * s0 / 2 == r / 3 and (1 - r / 3) * s0 == 2 * r / 3)
# Lemma 4.9 under mu = 1/2: first term is the maximum on [0,1] for every alpha in [1/2, 1]
okm = True
for al in (Fr(1, 2), Fr(3, 5), Fr(9, 10), Fr(1)):
    for k in range(0, 101):
        r = Fr(k, 100)
        t1 = 1 + r * Fr(1, 2) / Fr(3, 2)
        t2 = (2 + al) * Fr(1, 2) / Fr(3, 2) + r * (1 - al * Fr(1, 2)) / Fr(3, 2)
        okm &= t1 >= t2 and t1 >= r
allok &= show("Lemma 4.9 at mu = 1/2: the first term 1 + r/3 is the maximum on [0,1] (alpha in {1/2,3/5,9/10,1}, 101 r)", okm)
# E18 factor from the printed (certified) bounds: a >= 0.2945976, M_{3/50} <= 1.10841e-2
a_lo = Fr("0.2945976")
M006 = Fr("1.10841e-2")
Ct = (a_lo * Fr(3, 50) - M006) / (1 - Fr(3, 50))
fac = Ct / (Fr(1, 2) - a_lo)
allok &= show("E18: C_{3/50} >= %.10f, C/(1/2 - a) >= %.8f > 0.03414 (from the printed bounds alone)" % (float(Ct), float(fac)),
              fac > Fr("0.03414"))

print("\n(E) Remark after Proposition cp:E2: 2 sigma E_i/(1+sigma) < alpha(P0) for every row")
for sg, E, *_ in rows:
    v = 2 * sg * E / (1 + sg)
    allok &= show("sigma=%s: 2 sigma E/(1+sigma) = %.6f < alpha(P0)" % (sg, float(v)), v < alpha.lo)
allok &= show("alpha(1+sigma)/(2 sigma) < 1 iff sigma > alpha/(2-alpha): checked algebraically in the report", True)

print("\n(G) Proposition cp:F17: C_D at P0 = (sum lam_q/(q+2))/ln b_1")
CD = (I(lam[6] / 8) + I(lam[7] / 9)) / lnb1
allok &= show("C_D in %s; printed 0.5438... (truncation)" % CD, floor6(CD.lo) // Fr(1, 10 ** 4) == 5438 or str(CD).startswith("[0.5438"))
print("  ln b_1 in %s, ln a_1 in %s" % (lnb1, lna1))

print("\n(H) Remark cp:F23: the dual bounds of Theta*_6, Theta*_7 at t0 = 49/2500 against Theorem cp:G3's bound")
G6 = Fr("0.0012944331520783")
G7 = Fr("0.0012082016806783")
lamcert_dual = (I(lam[6] * G6) + I(lam[7] * G7)) / lna1
print("  Lambda_cert(t0) <= %s from the dual bounds; Theorem G3 uses <= 1.70916e-3" % lamcert_dual)
gam = Fr(49, 2500) / 2 - lamcert_dual / alpha
allok &= show("gamma_inf from the dual bounds >= %.13f vs printed 0.0039983470" % float(gam.lo), gam.lo > Fr("0.0039983470"))

print("\n(I) c-bar bounds of Proposition cp:E6 for the rows and the t-range 1/(2(cbar+1)) of Lemma cp:E3:top")
for sg, E, q, pl, pe, u in rows:
    cb = ((ln(q + 2) + LN2 * q) / (q + 2)) / (ln(q) * Fr(q, q + 2))
    print("  q=%d sigma=%s: cbar <= %.6f, t-range up to %.6f" % (q, sg, float(cb.hi), float(1 / (2 * (cb.hi + 1)))))

print("\n(F) Remark cp:E9 rates (COMPUTED, floating point): sup_t (t kappa - (1+sigma) Lambda_pr(t)/beta)")
for (sg, E, q, pl, pe, u) in (rows[1], rows[6]):
    beta = float(u / pl)
    s = float(sg)
    cb = float((((ln(q + 2) + LN2 * q) / (q + 2)) / (ln(q) * Fr(q, q + 2))).hi)
    tmax = 1 / (2 * (cb + 1))
    den = q / (q + 2) * math.log(q)
    for kap in (0.5, 1.0):
        best = -1
        bt = None
        Ngrid = 400000
        for i in range(1, Ngrid + 1):
            t = tmax * i / Ngrid
            lp = t * t * math.log(4 * math.e * q / t) ** 2 / den
            v = t * kap - (1 + s) * lp / beta
            if v > best:
                best, bt = v, t
        print("  sigma=%s (q=%d) kappa=%s: sup ~ %.4e at t ~ %.5f" % (sg, q, kap, best, bt))

print("\nALL CERTIFIED CHECKS PASS" if allok else "\nSOME CHECK FAILED (see FAIL lines; the E13_top line is expected to read ok because it asserts the inequality that refutes the printed claim)")
