"""R79: certified upper bounds L_t >= Lambda(t) at a grid of t in (0, 0.3249] and at t = 1, at the level-1 point
P0 = (7/19, 97/100, 979/1000) (r79.md Section 2; method of r74a.md, functions imported read-only from
r74a_certify.py).

For each t: G_q(t) <= F(z0) + sum |grad F(z0)| (R74a Lemma 3, concavity), interval arithmetic (mpmath iv, 60 digits);
Lambda(t) <= Lambda_cert(t) = (lam6 G_6 + lam7 G_7)/ln a_1 (R74a Lemma 1).
t = 1: Lambda(1) <= c_o = sum_q lam_q c(q)/ln a_1, c(q) = (ln(q+2) + q ln 2)/(q+2) (r79.md Lemma 2.1).
Also: cbar <= c_o, and 1/(cbar + 2) >= 3249/10000 (the t-range of P1-Corollary 4.1), certified.
Writes r79_certify.json: exact rational upper bounds (as "p/q" strings of the binary interval endpoints).
Run: ~/.venv/bin/python r79_certify.py > r79_certify_out.txt
"""
import sys, os, json, time
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r74a_certify as C            # read-only import (functions only); sets up mpmath from the user site
from mpmath import iv, mp
import mpmath

HERE = os.path.dirname(os.path.abspath(__file__))
TGRID = [Fr(1, 10000), Fr(3, 10000), Fr(8, 10000), Fr(2, 1000), Fr(4, 1000), Fr(74, 10000), Fr(12, 1000),
         Fr(196, 10000), Fr(28, 1000), Fr(36, 1000), Fr(48, 1000), Fr(6, 100), Fr(7, 100), Fr(85, 1000),
         Fr(1, 10), Fr(12, 100), Fr(145, 1000), Fr(17, 100), Fr(2, 10), Fr(24, 100), Fr(28, 100),
         Fr(3249, 10000)]


def mpf_to_fr(x):
    """exact rational value of a binary mpf."""
    man, exp = mp.mpf(x).man_exp
    return Fr(man)*Fr(2)**exp if exp >= 0 else Fr(man, 2**(-exp))


def up(x):        # exact rational >= the interval x
    return mpf_to_fr(mp.make_mpf(x._mpi_[1]))


def dn(x):        # exact rational <= the interval x
    return mpf_to_fr(mp.make_mpf(x._mpi_[0]))


def I(fr):
    return iv.mpf(fr.numerator)/fr.denominator


def main():
    t00 = time.time()
    slack, lna, alpha = C.point_P0()
    assert slack.a > 0
    print("(0) P0 = (7/19, 97/100, 979/1000), interval arithmetic, 60 digits")
    print(f"  slack in [{C.lo(slack)}, {C.hi(slack)}]; ln a_1 in [{C.lo(lna)}, {C.hi(lna)}]; "
          f"alpha(P0) in [{C.lo(alpha)}, {C.hi(alpha)}]")
    # coverage exponent c_o = cbar (level 1: C_M is exactly prod over coordinates, L1-2.2 (H4))
    co = iv.mpf(0)
    for q, lam in ((6, C.LAM6), (7, 1 - C.LAM6)):
        co += I(lam)*(iv.log(q + 2) + q*iv.log(2))/(q + 2)
    co = co/lna
    print(f"  c_o = cbar = sum_q lam_q c(q)/ln a_1 in [{C.lo(co)}, {C.hi(co)}]")
    tmax = 1/(co + 2)
    print(f"  1/(cbar + 2) in [{C.lo(tmax)}, {C.hi(tmax)}];  >= 3249/10000: {bool(dn(tmax) >= Fr(3249, 10000))}")
    assert dn(tmax) >= Fr(3249, 10000)

    print("\n(1) certified G_q(t) and Lambda_cert(t) = (lam6 G_6 + lam7 G_7)/ln a_1, and gamma-type numbers")
    print("    t | G_6(t) <= | G_7(t) <= | max sum|g_i| | Lambda_cert(t) <= | t/2 - L/alpha >= (Theorem D, kappa = 1/2)")
    out = dict(alpha_lo=str(dn(alpha)), alpha_hi=str(up(alpha)), lna_lo=str(dn(lna)), lna_hi=str(up(lna)),
               co_hi=str(up(co)), co_lo=str(dn(co)), points=[])
    for t in TGRID:
        Gs = {}; slopes = []
        for q in (6, 7):
            z0, Fz, g, ub, fv = C.certify_G(q, t)
            slope = max(max(abs(c.a), abs(c.b)) for c in g)
            slopes.append(float(slope))
            assert slope < mp.mpf(10)**(-20), (q, t, slope)
            Gs[q] = ub
        Gsum = I(C.LAM6)*iv.mpf(Gs[6]) + I(1 - C.LAM6)*iv.mpf(Gs[7])
        Lc = Gsum/lna
        gD = I(t)/2 - Lc/alpha
        out["points"].append(dict(t=str(t), G6_hi=str(mpf_to_fr(Gs[6])), G7_hi=str(mpf_to_fr(Gs[7])),
                                  L_hi=str(up(Lc))))
        print(f"  {float(t):.4f} | {float(mpf_to_fr(Gs[6])):.12e} | {float(mpf_to_fr(Gs[7])):.12e} | {max(slopes):.1e} | "
              f"{C.hi(Lc, 12)} | {C.lo(gD, 8)}")
    out["points"].append(dict(t="1", L_hi=str(up(co))))
    print(f"  1.0000 | (c(6) = 9 ln2/8) | (c(7)) | exact | {C.hi(co, 12)} (= c_o) |")
    with open(os.path.join(HERE, "r79_certify.json"), "w") as f:
        json.dump(out, f, indent=1)

    print("\n(2) comparison with the numerical profile of r76_lamtable.json (floats, linear interpolation)")
    try:
        import numpy as np
        tab = json.load(open(os.path.join(HERE, "r76_lamtable.json")))
        TG = np.array(tab["t"]); lam6 = 7/19
        L6, L7 = np.array(tab["Lam"]["6"]), np.array(tab["Lam"]["7"])
        lna_f = float(lna.a)
        for p in out["points"][:-1]:
            t = float(Fr(p["t"]))
            num = (lam6*np.interp(t, TG, L6) + (1 - lam6)*np.interp(t, TG, L7))/lna_f
            print(f"  t = {t:.4f}: certified {float(Fr(p['L_hi'])):.8e}, numerical (interp.) {num:.8e}")
    except Exception as ex:
        print("  skipped:", ex)
    print(f"\nrun time {time.time() - t00:.1f} s")


if __name__ == "__main__":
    main()
