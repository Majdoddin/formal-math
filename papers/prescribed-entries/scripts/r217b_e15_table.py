# R217b: print-format check for the E15 sample table of CP Section 10 (r211f Section 7.3 samples).
# Exact rational arithmetic (fractions) only. No new mathematics: each upper end is min(b,c) times a printed
# exact or certified value; the script truncates (rounds down) to 6 decimals and checks the emptiness of intervals.
# Inputs: E_i of the seven certified rows (r211f:401-407, exact fractions u/pe), alpha(P0) > 0.2945976
# (calc/r211a_p0_certify_out.txt:8-9), v1's range ln4/(5 ln5) > 0.1722706 (v1 main.tex l. 178).
from fractions import Fraction as F
import math

rows = [  # (sigma_i, E_i)
    (F(3,4), F(333,1000)), (F(1,2), F(2757,7000)), (F(1,3), F(179,400)), (F(1,4), F(197,400)),
    (F(1,5), F(2853,5500)), (F(1,7), F(887,1625)), (F(1,10), F(10703,18000))]
alpha_lo = F(2945976, 10**7)   # certified lower bound of alpha(P0)
alpha_hi = F(2945977, 10**7)
es_lo = F(1722706, 10**7)      # ln4/(5 ln5) = 0.17227062...
assert abs(math.log(4)/(5*math.log(5)) - 0.1722706) < 1e-7 and math.log(4)/(5*math.log(5)) > 0.1722706

def E(s):
    vals = [Ei for (si, Ei) in rows if si >= s]
    return max(vals) if vals else None  # None: s > 3/4, E = alpha(P0)

def trunc6(x):
    return F(math.floor(x * 10**6), 10**6)

samples = [(F(10,100), F(91,100)), (F(5,100), F(96,100)), (F(20,100), F(85,100)),
           (F(30,100), F(75,100)), (F(40,100), F(65,100)), (F(10,100), F(95,100))]
for (b, c) in samples:
    m, M = min(b, c), max(b, c)
    s = m / M
    Es = E(s)
    lower = b + c - 1
    up87 = m * (Es if Es is not None else alpha_lo)
    upsq_lo, upsq_hi = m * alpha_lo, m * alpha_hi
    upv1 = m * es_lo
    def show(up, name):
        if up <= lower:
            return name + " empty (" + str(float(up)) + " <= " + str(float(lower)) + ")"
        return name + " (" + str(float(lower)) + ", " + "%.6f" % float(trunc6(up)) + ")"
    print("(b,c) = (%s, %s): s = %s = %.6f, E(s) = %s = %.6f" % (b, c, s, float(s), Es, float(Es)))
    print("   " + show(up87, "R87.2") + " | " + show(upsq_lo, "square(alpha_lo)") +
          " [hi end " + "%.7f" % float(upsq_hi) + "] | " + show(upv1, "v1"))
# extremes on the step s = 1 (E = alpha(P0)): min(b,c) < 1/(2 - E), a < E/(2 - E); lower bounds from alpha_lo
print("extremes at s = 1 (alpha_lo): min(b,c) < %.7f, a < %.7f" % (float(1/(2-alpha_lo)), float(alpha_lo/(2-alpha_lo))))
print("extremes at s = 1 (alpha_hi): min(b,c) < %.7f, a < %.7f" % (float(1/(2-alpha_hi)), float(alpha_hi/(2-alpha_hi))))
# E16 threshold 3(1+mu)/(16+mu) at mu = 0.5286 (increasing in mu)
mu = F(5286, 10000)
print("3(1+mu)/(16+mu) at mu = 0.5286: %.7f < 0.2775: %s" % (float(3*(1+mu)/(16+mu)), 3*(1+mu)/(16+mu) < F(2775,10000)))
for (si, Ei) in rows:
    print("row sigma = %s: E = %s = %.7f, decimal floor6 = %.6f" % (si, Ei, float(Ei), float(trunc6(Ei))))
