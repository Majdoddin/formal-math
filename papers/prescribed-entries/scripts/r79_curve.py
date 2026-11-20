"""R79: the certified batch curve f_cert(kappa), Theorem D_kappa's gamma and excess, at P0 (r79.md Section 2).

Inputs: r79_certify.json (certified L_t >= Lambda(t) at a grid of t <= 0.3249, and L_1 = c_o at t = 1; alpha(P0)
enclosure).  Range formula (r76.md (3.1), r79.md Theorem B): with s = min(0, 1 - kappa) + t kappa,
    x L_t + q_A < (1 + alpha x) s,      eps < R(x) = (1 + alpha x)/(x + 1/eps_A).
Bottoms: direct inner products (q_A = 1, eps_A = 1); the paper's data structure with q_A -> 0, eps_A -> eps*
(main.tex Theorem m:thm:general); the data structure at a fixed theta (R14 Theorem 1/2: q_A > q(theta),
eps_A < eps(theta) = ln4/A(c_min(theta))).
For each kappa: float optimisation over (t, bottom, x) -> a rational point x near the optimum -> interval check of the
strict constraint with the certified L_t, alpha_lo, q_A upper and eps_A lower ends -> certified lower end of R(x).
So every printed "certified" value v satisfies: Theorem B holds for every eps < v.
Comparison: r76's numerical f at P0 (r76_curve.f_spread, numerical profile, all t / t <= 0.3249 or t = 1).
Run: ~/.venv/bin/python r79_curve.py > r79_curve_out.txt
"""
import sys, os, json
from fractions import Fraction as Fr
from math import log, inf
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mpmath
from mpmath import iv, mp
import r20_rates as R20            # read-only import (functions only): q1, cmin, eps_of, A, b

iv.dps = 50; mp.dps = 50
HERE = os.path.dirname(os.path.abspath(__file__))
J = json.load(open(os.path.join(HERE, "r79_certify.json")))
ALO, AHI = Fr(J["alpha_lo"]), Fr(J["alpha_hi"])
PTS = [(Fr(p["t"]), Fr(p["L_hi"])) for p in J["points"]]       # includes t = 1 (L = c_o)
ALF = float(ALO)
E_STAR = log(4)/(5*log(5))


def I(fr):
    return iv.mpf(fr.numerator)/fr.denominator


def lo(x):
    return float(mp.make_mpf(x._mpi_[0]))


# ------------------------------------------------------------------ bottoms
THETAS = [Fr(1, 1000), Fr(3, 1000), Fr(1, 100), Fr(3, 100), Fr(1, 10), Fr(2, 10)]
BOT = [("direct", 1.0, 1.0, None), ("DS q_A->0", 0.0, E_STAR, None)]
for th in THETAS:
    BOT.append((f"DS theta={th}", R20.q1(float(th)), R20.eps_of(float(th)), th))


def ivH(x):
    return -x*iv.log(x) - (1 - x)*iv.log(1 - x)


def cert_bottom(name, th):
    """interval (q_A upper end, eps_A lower end) of a bottom."""
    if name == "direct":
        return iv.mpf(1), iv.mpf(1)
    if th is None:   # q_A -> 0, eps_A -> eps*: sup values (any eps below is reached with q_A > 0, eps_A < eps*)
        return iv.mpf(0), iv.log(4)/(5*iv.log(5))
    tI = I(th)
    qA = (ivH(tI) + tI*iv.log(4))/iv.log(2)
    c_hi = Fr(repr(R20.cmin(float(th))*(1 + 1e-9)))
    cI = I(c_hi)
    xlx = lambda z: z*iv.log(z)
    bval = tI*iv.log(4) - xlx(1 - tI) - xlx(cI - 1 + tI) + xlx(cI - 1)
    assert mp.make_mpf(bval._mpi_[1]) < 0, "b(theta, c_hi) not < 0"
    Ac = 2*cI*iv.log(5) - cI*ivH(1/cI) - (cI - 1)*iv.log(4)
    return qA, iv.log(4)/Ac


CB = {name: cert_bottom(name, th) for name, _, _, th in BOT}


# ------------------------------------------------------------------ sup over x (float) and certification
def sup_x(a, L, s, qA, eA):
    """(sup of R over feasible x, x at which it is approached, side) for x L + qA < (1 + a x) s."""
    A = L - a*s; Bc = s - qA
    R = lambda x: (1 + a*x)/(x + 1/eA)
    if eA > a:                      # R decreasing in x: smallest feasible x
        if A < 0 and Bc < 0:
            x0 = Bc/A; return R(x0), x0, "above"
        if Bc > 0 and A <= 0:
            return eA, 0.0, "zero"
        if Bc > 0 and A > 0:
            return eA, 0.0, "zero"
        return -inf, None, None
    else:                           # R increasing in x: largest feasible x
        if A > 0:
            if Bc <= 0: return -inf, None, None
            x0 = Bc/A; return R(x0), x0, "below"
        if A <= 0 and (Bc > 0 or A < 0):
            return a, inf, "inf"
        return -inf, None, None


def s_of(kap, t):
    return min(Fr(0), 1 - kap) + t*kap


def f_float(kap, tmax=Fr(1)):
    best = (-inf, None)
    for t, L in PTS:
        if t > tmax: continue
        s = float(s_of(kap, t))
        for name, qA, eA, th in BOT:
            v, x0, side = sup_x(ALF, float(L), s, qA, eA)
            if v > best[0]:
                best = (v, (t, name, x0, side))
    return best


def certify(kap, t, L, name, x0, side):
    """certified lower end of R at a rational x next to x0 (strict constraint checked in intervals)."""
    if side not in ("above", "below"):
        return None
    for rel in (Fr(1, 10**12), Fr(1, 10**9), Fr(1, 10**6)):
        x = Fr(repr(x0))*(1 + rel if side == "above" else 1 - rel)
        qA, eA = CB[name]
        s = s_of(kap, t)
        xI, sI = I(x), I(s)
        lhs = xI*I(L) + qA
        rhs = (1 + I(ALO)*xI)*sI          # s > 0 here; alpha_lo gives the smaller right side
        if mp.make_mpf(lhs._mpi_[1]) < mp.make_mpf(rhs._mpi_[0]):
            Rv = (1 + I(ALO)*xI)/(xI + 1/eA)
            return lo(Rv), x
    return None


def fl6(v):
    from math import floor
    return f"{floor(v*1e6)/1e6:.6f}"


def main():
    print(f"alpha(P0) in [{float(ALO):.15f}, {float(AHI):.15f}]; certified t-grid (L_t >= Lambda(t)):")
    print("  " + ", ".join(f"{float(t):g}" for t, _ in PTS))
    for name in CB:
        qA, eA = CB[name]
        print(f"  bottom {name}: q_A <= {float(mp.make_mpf(qA._mpi_[1])):.6f}, eps_A >= {lo(eA):.6f}")

    # r76 numerical comparison
    try:
        from r76_curve import point, f_spread
        P0 = point(7/19, us=[0.97/8, 0.979/9])
        def r76f(k, tmax=1.0):
            m = "hyp" if k < 1 else "lit"
            v = f_spread(P0, k, measure=m, tmax=tmax)[0]
            if tmax < 1:
                from r76_curve import t1_only
                v = max(v, t1_only(P0, k)) if k >= 1 else v
            return v
    except Exception as ex:
        print("r76 comparison unavailable:", ex); r76f = None

    print("\n(1) f_cert(kappa) (Theorem B; kappa <= 1: Hyp measure, target N^2; kappa >= 1: target |B| D)")
    print("    (certified column rounded down to 6 digits)")
    print("    kappa | f_cert (sup, float) | certified: every eps < | optimum (t, bottom, x) | r76 numerical: all t | t<=0.3249 or t=1")
    KAP = [Fr(1, 100), Fr(5, 100), Fr(1, 10), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1), Fr(1005, 1000), Fr(101, 100),
           Fr(1015, 1000), Fr(102, 100), Fr(1025, 1000), Fr(103, 100), Fr(104, 100), Fr(105, 100), Fr(107, 100),
           Fr(11, 10), Fr(115, 100), Fr(12, 10), Fr(125, 100), Fr(127, 100), Fr(13, 10), Fr(15, 10), Fr(17, 10), Fr(2), Fr(3), Fr(5)]
    rows = []
    for k in KAP:
        v, (t, name, x0, side) = f_float(k)
        c = certify(k, t, dict(PTS)[t], name, x0, side)
        cv = c[0] if c else None
        alpha_floor = (k <= 1)
        shown = max(cv or -inf, float(ALO) if alpha_floor else -inf)
        note = "" if not alpha_floor or (cv and cv > float(ALO)) else " (= alpha(P0) by Theorem D_kappa)"
        r1 = r76f(float(k)) if r76f else float("nan")
        r2 = r76f(float(k), 0.3249) if r76f else float("nan")
        rows.append((k, v, shown))
        xs = f"{x0:.4g}" if x0 not in (None, inf) else str(x0)
        print(f"  {float(k):6.3f} | {v:.6f} | {fl6(shown)}{note} | (t={float(t):g}, {name}, x={xs}) | {r1:.6f} | {r2:.6f}")

    print("\n(2) end of the plateau f_cert > alpha(P0) (direct bottom, x -> x_min): largest kappa with some grid t "
          "and alpha (t kappa + min(0, 1-kappa)) > L_t")
    def above(k):
        return any(float(ALO)*float(s_of(k, t)) > float(L) and float(s_of(k, t)) < 1 for t, L in PTS)
    lo_k, hi_k = Fr(1), Fr(2)
    for _ in range(40):
        m = (lo_k + hi_k)/2
        lo_k, hi_k = (m, hi_k) if above(m) else (lo_k, m)
    kc = Fr(int(lo_k*10**6), 10**6)
    v, (t, name, x0, side) = f_float(kc)
    c = certify(kc, t, dict(PTS)[t], name, x0, side)
    print(f"  kappa*_cert = {float(lo_k):.6f} (float); at kappa = {float(kc)}: f_cert = {v:.7f}, certified "
          f"{c[0] if c else None} at t = {float(t)} ({name})")

    print("\n(3) Theorem D_kappa: gamma_D(kappa) >= max_t (t kappa - L_t/alpha_lo) over the certified grid "
          "(t <= 0.3249), for eps <= eps1(kappa) = 1/(1/alpha + gamma); and the certified excess above alpha(P0)")
    for k in (Fr(1, 100), Fr(2, 100), Fr(5, 100), Fr(1, 10), Fr(2, 10), Fr(1, 2), Fr(1)):
        best = None
        for t, L in PTS:
            if t > Fr(3249, 10000): continue
            g = I(t)*I(k) - I(L)/I(ALO)
            if best is None or lo(g) > best[0]:
                best = (lo(g), t)
        v, (t2, name, x0, side) = f_float(k)
        exc = None
        if name == "direct" and side == "above":
            c = certify(k, t2, dict(PTS)[t2], name, x0, side)
            exc = c[0] - float(AHI) if c else None
        exs = f"{exc:.3e} (t = {float(t2):g})" if exc and exc > 0 else "none on the grid"
        print(f"  kappa = {float(k):5.2f}: gamma_D >= {best[0]:.4e} (t = {float(best[1]):g});  certified excess "
              f"f_cert - alpha(P0) >= {exs}")


if __name__ == "__main__":
    main()
