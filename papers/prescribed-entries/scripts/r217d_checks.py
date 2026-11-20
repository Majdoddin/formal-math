# r217d_checks.py -- R217d (CP drafting run 2, unit U9): arithmetic checks of the numbers printed in cp-transfer-r217.tex.
# Standard library only (decimal at 60 digits, fractions). Output: r217d_checks_out.txt (written by redirection).
# Every printed value is compared with the value macro of cp-values.tex and with its rounding direction.
from decimal import Decimal as Dm, getcontext
from fractions import Fraction as Fr
getcontext().prec = 60
ln = lambda x: Dm(x).ln()

print("(1) copy size of VXXZ's family (r59-part3b Prop. 4.1; r211d row 19)")
h13 = -(Dm(1)/3)*ln(Dm(1)/3) - (Dm(2)/3)*ln(Dm(2)/3)
hstar_hi = h13 + (Dm(2)/3)*ln(6)
bound = (ln(7) - hstar_hi)/2
print("  h(1/3)                  =", h13)
print("  h(1/3) + (2/3) ln 6     =", hstar_hi, "(upper bound on h*)")
print("  ln 7                    =", ln(7))
print("  (ln 7 - that)/2         =", bound)
print("  >= 0.0574 ?", bound >= Dm("0.0574"), "  >= 0.0575 ?", bound >= Dm("0.0575"))

print("(2) structural c_g of the standard decomposition on any (T1),(T3),(T4) family of CW_5 with Q = e^{o(M)}")
ktyp5 = 6*ln(2)/7
Amax = ln(7)/2
print("  kappa_typ(5) = 6 ln2/7  =", ktyp5)
print("  A <= ln7/2              =", Amax)
print("  ratio 12 ln2/(7 ln7)    =", ktyp5/Amax, " >= 0.6106 ?", ktyp5/Amax >= Dm("0.6106"))
print("  kappa_0/2 (0.321334/2)  =", Dm("0.321334")/2)

print("(3) kappa_typ(q) for the standard decomposition, closed form")
def ktyp(q):
    q = Dm(q)
    x = ((q+1) - (q*q - 2*q + 5).sqrt())/(2*(q-1))
    return x, (-2*ln(x) - (q-1)*ln(1-x))/(q+2)
for q in (5, 6, 7, 8):
    x, k = ktyp(q)
    A = Dm(q)*ln(q)/(2*(q+2))
    print("  q=%d  x_q=%s  kappa_typ=%s  A_q=%s  ratio=%s" % (q, str(x)[:14], str(k)[:14], str(A)[:14], str(k/A)[:14]))
x5, k5 = ktyp(5)
print("  q=5 identity: kappa_typ(5) - 6 ln2/7 =", k5 - ktyp5)
x7, k7 = ktyp(7)
A7 = 7*ln(7)/18
cg7 = k7/A7
print("  c_g(std, q=7) =", cg7, "; /6 =", cg7/6, "; 1/7 =", Dm(1)/7, "; /6 < 1/7 ?", cg7/6 < Dm(1)/7)

print("(4) Proposition 4.1 instance (r211d row 8), exact rationals")
aC, aB, c = Fr("0.2945976"), Fr("0.321334"), Fr(2)
th = aC/(2*c - aB + aC)
f = aC + th*(aB - aC)
print("  theta* =", Dm(th.numerator)/Dm(th.denominator))
print("  range  =", Dm(f.numerator)/Dm(f.denominator), " > 0.296579 ?", f > Fr("0.296579"), " > 0.296580 ?", f > Fr("0.296580"))

print("(5) slack of the single-q point q = 7, u = w = 1/9 (alpha = 2/7): H_X = ln 2 > H_Z = ln 9 - (7/9) ln 7")
print("  2^9 7^7 =", 2**9 * 7**7, " 3^18 =", 3**18, " 2^9 7^7 > 3^18 ?", 2**9 * 7**7 > 3**18)
print("  H_X - H_Z =", ln(2) - (ln(9) - Dm(7)/9*ln(7)))
print("  alpha = u/p = (1/9)/(7/18) =", Fr(1, 9)/Fr(7, 18))

print("(6) window constant c = 3^(2^(l*-1)) 3^(l*) at l* = 3:", 3**4 * 3**3)

print("(7) Example C13: c_g = kappa_typ(7)/(6 A_7) < 1/7  <=>  -2 ln x - 6 ln(1-x) < 3 ln 7  <=>  x^2 (1-x)^6 > 7^-3,")
print("    x = x_7 = (4 - sqrt 10)/6; exact rational check with sqrt 10 enclosed in [31622/10^4, 31623/10^4]")
s_lo, s_hi = Fr(31622, 10**4), Fr(31623, 10**4)
assert s_lo**2 < 10 < s_hi**2
x_lo, x_hi = (4 - s_hi)/6, (4 - s_lo)/6           # x = (4 - sqrt 10)/6 lies in [x_lo, x_hi]
lower = x_lo**2 * (1 - x_hi)**6                    # x^2 increasing, (1-x)^6 decreasing on [x_lo, x_hi]
print("  x_7 in [%s, %s]" % (float(x_lo), float(x_hi)))
print("  x^2 (1-x)^6 >= %.6f ; 7^-3 = %.6f ; certified > ? %s" % (float(lower), 1/343, lower > Fr(1, 343)))
print("  check of the root: (q-1)x^2-(q+1)x+1 at q=7 for x=(4-sqrt10)/6 is 0 since 6x^2-8x+1=0 <=> x=(8-sqrt40)/12")

print("(8) Remark C21: 12 ln 2/(7 ln 7) > 0.6106  <=>  2^(120000) > 7^(42742)  (exact integers)")
print("  ", 2**120000 > 7**(7*6106))

print("(9) copy size: h(1/3) + (2/3) ln 6 = (5/3) ln 3, so the bound is (1/6) ln(343/243);  >= 0.0574 <=> 343/243 > exp(0.3444)")
print("  (5/3) ln 3 - [h(1/3) + (2/3) ln 6] =", (Dm(5)/3)*ln(3) - hstar_hi)
print("  (1/6) ln(343/243) =", ln(Dm(343)/243)/6)
xx = Fr(3444, 10**4)
term, ssum, k = Fr(1), Fr(1), 0
while True:
    k += 1
    term = term*xx/k
    ssum += term
    if term < Fr(1, 10**30):
        break
exp_hi = ssum + 2*term*xx/(k+1)                    # tail of the series bounded by twice the next term (x < 1)
print("  exp(0.3444) <= %.12f ; 343/243 = %.12f ; certified > ? %s" % (float(exp_hi), 343/243, Fr(343, 243) > exp_hi))
