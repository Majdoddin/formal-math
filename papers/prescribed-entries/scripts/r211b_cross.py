"""R211b (2026-11-18): certified values of both curves at the computed crossing eps = 0.171511 (r74e.md:179).
Level-1 Theorem D (pair 11/12, x -> infinity) and pure tile (Theorem D_x with f_G = 1), parameters taken from
calc/r211b_curve_out.txt (1) and nudged so that the certified eps bound covers 0.171511.
Run: nice -n 19 ~/.venv/bin/python3 r211b_cross.py > r211b_cross_out.txt
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
import r211b_curve as C

E0 = Fr(171511, 10 ** 6)
for lam in (Fr(340, 1000), Fr(341, 1000), Fr(342, 1000)):
    parts = [(11, lam, Fr(999999, 10 ** 6)), (12, 1 - lam, Fr(999999, 10 ** 6))]
    gl, e1, P, _ = C.cert_level1(parts, Fr(1133, 50000))
    print(f"level-1 11/12, lam_11 = {lam}, t = 1133/50000: gamma < {C.dn(gl, 10)} for every eps <= {C.dn(e1, 7)}"
          f"  covers 0.171511: {e1 >= E0}", flush=True)
for c in (Fr(501800, 100000), Fr(501790, 100000), Fr(501780, 100000)):
    for t in (Fr(449, 20000),):
        gq, e2 = C.cert_tile(c, t)
        print(f"pure tile c = {c}, t = {t}: gamma < {C.dn(gq, 10)} for every eps < {C.dn(e2, 7)}"
              f"  covers 0.171511: {e2 > E0}", flush=True)
print("DONE")
