"""R79b: certified upper bounds M_t >= max(Lambda(t), t c_o - 2 + 2t) at a grid of t in [0.25, 1), at the
level-1 point P0 = (7/19, 97/100, 979/1000) (r79b.md Lemma 1; method of r74a.md / r79_certify.py, functions imported
read-only from r74a_certify.py).

For each t: G_q(t) <= F(z0) + sum |grad F(z0)| (R74a Lemma 3, concavity), interval arithmetic (mpmath iv, 60 digits);
Lambda(t) <= L_t = (lam6 G_6 + lam7 G_7)/ln a_1 (R74a Lemma 1, valid for t in (0, 1]).
Padding term (P1-Lemma 4, limit along the level-1 family): pad(t) = t c_o - 2 + 2t with c_o's upper end.
M_t := max(L_t, pad_hi(t)) (certified either way); the script reports which of the two is larger.
Writes r79b_certify.json: the r79 grid (t <= 0.3249, where pad <= -1 < 0 <= Lambda, so M_t = L_t) plus the new grid 0.25 ... 0.99 (step 0.01),
plus t = 1 (M_1 = c_o), as exact rationals ("p/q").
Run: ~/.venv/bin/python r79b_certify.py > r79b_certify_out.txt
"""
import sys, os, json, time
from fractions import Fraction as Fr
from multiprocessing import Pool
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r74a_certify as C            # read-only import (functions only); sets up mpmath from the user site
from mpmath import iv, mp

HERE = os.path.dirname(os.path.abspath(__file__))
NEW_T = [Fr(k, 100) for k in range(25, 100) if k != 28]     # 0.25, 0.26, ..., 0.99 (0.28 is on r79's grid)


def mpf_to_fr(x):
    man, exp = mp.mpf(x).man_exp
    return Fr(man)*Fr(2)**exp if exp >= 0 else Fr(man, 2**(-exp))


def up(x):
    return mpf_to_fr(mp.make_mpf(x._mpi_[1]))


def dn(x):
    return mpf_to_fr(mp.make_mpf(x._mpi_[0]))


def I(fr):
    return iv.mpf(fr.numerator)/fr.denominator


def one_t(t):
    """certified upper bound on G_q(t), q = 6, 7, as Fractions, plus the gradient sizes."""
    res = {}
    for q in (6, 7):
        z0, Fz, g, ub, fv = C.certify_G(q, t)
        slope = max(max(abs(c.a), abs(c.b)) for c in g)
        assert slope < mp.mpf(10)**(-20), (q, t, slope)
        res[q] = (mpf_to_fr(ub), float(slope), fv)
    return t, res


def main():
    t00 = time.time()
    slack, lna, alpha = C.point_P0()
    co = iv.mpf(0)
    for q, lam in ((6, C.LAM6), (7, 1 - C.LAM6)):
        co += I(lam)*(iv.log(q + 2) + q*iv.log(2))/(q + 2)
    co = co/lna
    co_hi = up(co)
    print("(0) P0 = (7/19, 97/100, 979/1000), interval arithmetic, 60 digits")
    print(f"  alpha(P0) in [{C.lo(alpha)}, {C.hi(alpha)}];  c_o in [{C.lo(co)}, {C.hi(co)}]")
    t0 = 2/(co + 2)
    print(f"  pad(t) = t c_o - 2 + 2t < 0 exactly for t < 2/(c_o + 2) in [{C.lo(t0)}, {C.hi(t0)}]")

    old = json.load(open(os.path.join(HERE, "r79_certify.json")))
    with Pool(2) as P:
        results = P.map(one_t, NEW_T)

    print("\n(1) new grid: certified L_t >= Lambda(t), pad_hi(t) = t c_o,hi - 2 + 2t, M_t = max(L_t, pad_hi)")
    print("    t | G_6(t) <= | G_7(t) <= | max|g_i| | L_t <= | pad(t) <= | M_t (certified) | binding")
    pts = []
    for p in old["points"]:
        t = Fr(p["t"])
        if t == 1:
            continue
        assert t not in NEW_T
        pts.append(dict(t=p["t"], L_hi=p["L_hi"], pad_hi=str(t*co_hi - 2 + 2*t), M_hi=p["L_hi"], src="r79"))
    for t, res in results:
        G = I(C.LAM6)*I(res[6][0]) + I(1 - C.LAM6)*I(res[7][0])
        Lc = G/lna
        L_hi = up(Lc)
        pad_hi = t*co_hi - 2 + 2*t
        M = max(L_hi, pad_hi)
        pts.append(dict(t=str(t), L_hi=str(L_hi), pad_hi=str(pad_hi), M_hi=str(M), src="r79b"))
        print(f"  {float(t):.2f} | {float(res[6][0]):.12e} | {float(res[7][0]):.12e} | "
              f"{max(res[6][1], res[7][1]):.1e} | {float(L_hi):.10f} | {float(pad_hi):+.10f} | {float(M):.10f} | "
              f"{'Lambda' if L_hi >= pad_hi else 'PADDING'}")
    pts.append(dict(t="1", L_hi=str(co_hi), pad_hi=str(co_hi), M_hi=str(co_hi), src="r79 Lemma 2.1"))
    print(f"  1.00 | (c(6)) | (c(7)) | exact | {float(co_hi):.10f} | {float(co_hi):+.10f} | {float(co_hi):.10f} | both")
    out = dict(alpha_lo=old["alpha_lo"], alpha_hi=old["alpha_hi"], co_hi=str(co_hi), co_lo=old["co_lo"], points=pts)
    with open(os.path.join(HERE, "r79b_certify.json"), "w") as f:
        json.dump(out, f, indent=1)

    print("\n(2) margins: min over the new grid of L_t - pad_hi(t) (positive: the padding term never binds on the grid)")
    mg = min((Fr(p["L_hi"]) - Fr(p["pad_hi"]), p["t"]) for p in pts if p["src"] == "r79b")
    print(f"  min L_t - pad_hi = {float(mg[0]):.6f} at t = {float(Fr(mg[1]))}")

    print("\n(3) comparison with the numerical profile of r76_lamtable.json (floats, linear interpolation)")
    import numpy as np
    tab = json.load(open(os.path.join(HERE, "r76_lamtable.json")))
    TG = np.array(tab["t"]); lam6 = 7/19
    L6, L7 = np.array(tab["Lam"]["6"]), np.array(tab["Lam"]["7"])
    lna_f = float(lna.a)
    for t, res in results:
        num = (lam6*np.interp(float(t), TG, L6) + (1 - lam6)*np.interp(float(t), TG, L7))/lna_f
        fl = (lam6*res[6][2] + (1 - lam6)*res[7][2])/lna_f
        print(f"  t = {float(t):.2f}: float max {fl:.8e}, numerical table (interp.) {num:.8e}")
    print(f"\nrun time {time.time() - t00:.1f} s")


if __name__ == "__main__":
    main()
