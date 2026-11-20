"""R79b: the certified batch curve over the extended t-grid (r79b.md Section 3).

Same method as r79_curve.py (functions imported read-only from it): for each kappa, float optimisation over
(t, bottom, x) on the certified grid, then a rational x next to the optimum, the strict condition (B1)
x M_t + q_A < (1 + alpha x) s checked in interval arithmetic with the certified M_t, alpha's lower end and the bottom's
q_A upper / eps_A lower ends, and the certified lower end of the range (1 + alpha x)/(x + 1/eps_A).
The only change: the grid is r79b_certify.json (r79's 22 values t <= 0.3249, 74 new values 0.25 ... 0.99 in steps of 0.01, and t = 1),
and the bound used is M_t = max(L_t, t c_o - 2 + 2t) (r79b.md Lemma 1); on r79's grid M_t = L_t.
Columns: certified new value; r79's f_cert (old grid, recomputed); r76's numerical "all t" value.
Run: ~/.venv/bin/python r79b_curve.py > r79b_curve_out.txt
"""
import sys, os, json
from fractions import Fraction as Fr
from math import inf
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import r79_curve as R              # read-only import (functions only); loads r79_certify.json as R.PTS

HERE = os.path.dirname(os.path.abspath(__file__))
J = json.load(open(os.path.join(HERE, "r79b_certify.json")))
assert Fr(J["alpha_lo"]) == R.ALO
NEW = sorted((Fr(p["t"]), Fr(p["M_hi"])) for p in J["points"])
OLD = list(R.PTS)


def best_and_cert(k, pts):
    R.PTS = pts
    v, (t, name, x0, side) = R.f_float(k)
    c = R.certify(k, t, dict(pts)[t], name, x0, side)
    return v, (c[0] if c else None), t, name, x0


def main():
    from r76_curve import point, f_spread
    P0 = point(7/19, us=[0.97/8, 0.979/9])
    print("grid: r79 (t <= 0.3249) + new t = " + ", ".join(f"{float(t):g}" for t, _ in NEW if t > Fr(3249, 10000)))
    print("\n(1) kappa | new f_cert (float sup) | new certified: every eps < | optimum (t, bottom, x) | "
          "r79 f_cert (old grid) | r76 numerical all t | gain over r79")
    KAP = [Fr(1100 + 5*i, 1000) for i in range(141)]          # 1.100, 1.105, ..., 1.800
    rows = []
    for k in KAP:
        v, cv, t, name, x0 = best_and_cert(k, NEW)
        vo, co, _, _, _ = best_and_cert(k, OLD)
        r76 = f_spread(P0, float(k), measure="lit", tmax=1.0)[0]
        assert cv is not None and co is not None
        rows.append((k, cv, co, r76, t, name))
        xs = f"{x0:.4g}" if x0 not in (None, inf) else str(x0)
        print(f"  {float(k):.3f} | {v:.6f} | {R.fl6(cv)} | (t={float(t):g}, {name}, x={xs}) | {R.fl6(co)} | "
              f"{r76:.6f} | {cv - co:+.6f}")
    print("\n(2) summary")
    g = max(rows, key=lambda r: r[1] - r[2])
    print(f"  largest gain over r79: {g[1] - g[2]:.6f} at kappa = {float(g[0]):.3f}")
    d = max(rows, key=lambda r: r[3] - r[1])
    print(f"  largest shortfall against r76 all-t: {d[3] - d[1]:.2e} at kappa = {float(d[0]):.3f}")
    t1 = [r for r in rows if r[4] == 1]
    print(f"  first kappa on the grid where the optimum is t = 1 (R23's 0.194324): "
          f"{float(t1[0][0]) if t1 else 'none'}")
    binding = [r for r in rows if r[4] > Fr(3249, 10000) and r[4] < 1]
    print(f"  kappa with optimal t in the new range (0.3249, 1): {float(binding[0][0]):.3f} ... "
          f"{float(binding[-1][0]):.3f}" if binding else "  none")


if __name__ == "__main__":
    main()
