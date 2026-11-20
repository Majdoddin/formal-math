"""Ancillary file of arXiv:2610.17420, version 2: the two witness checks of Theorem 8.2 (fixed query exponent),
in interval arithmetic (mpmath.iv, 50 digits).

With Hh(x) = -x ln x - (1-x) ln(1-x), q(theta) = (Hh(theta) + theta ln 4)/ln 2,
b(theta, c) = theta ln 4 - (1-theta) ln(1-theta) - (c-1+theta) ln(c-1+theta) + (c-1) ln(c-1),
A(c) = 2c ln 5 - c Hh(1/c) - (c-1) ln 4 and R'_c(gamma) = ln 4/(A(c) + gamma ln 4), the proof of Theorem 8.2 uses only:
  at (theta, c) = (0.068967, 4.826866): q(theta) < 1/2, b(theta, c) < 0, R'_c(-b(theta, c)/ln 2) > 0.17843;
  at (theta, c) = (0.17053, 4.56877):   q(theta) < 1,   b(theta, c) < 0, R'_c(-b(theta, c)/ln 2) > 0.18840.
Every quantity is an interval that contains the exact value; a check passes when the whole interval is on the
required side. Run: python3 r14_witness_check.py   (needs mpmath; recorded output r14_witness_check_out.txt)."""
from mpmath import iv
iv.dps = 50
LN2, LN4, LN5 = iv.log(2), iv.log(4), iv.log(5)

def Hh(x):
    return -x * iv.log(x) - (1 - x) * iv.log(1 - x)

def check(theta_s, c_s, q_bound, eps_bound):
    th, c = iv.mpf(theta_s), iv.mpf(c_s)
    q = (Hh(th) + th * LN4) / LN2
    b = th * LN4 - (1 - th) * iv.log(1 - th) - (c - 1 + th) * iv.log(c - 1 + th) + (c - 1) * iv.log(c - 1)
    gamma = -b / LN2
    A = 2 * c * LN5 - c * Hh(1 / c) - (c - 1) * LN4
    R = LN4 / (A + gamma * LN4)
    ok = [q.b < q_bound, b.b < 0, R.a > iv.mpf(eps_bound).b]
    print('(theta, c) = (%s, %s):' % (theta_s, c_s))
    print('  q(theta)       = %s  < %s: %s' % (iv.nstr(q, 15), q_bound, ok[0]))
    print('  b(theta, c)    = %s  < 0: %s' % (iv.nstr(b, 15), ok[1]))
    print('  R\'_c(-b/ln 2) = %s  > %s: %s (margin %s)' % (iv.nstr(R, 15), eps_bound, ok[2], iv.nstr(R - iv.mpf(eps_bound), 3)))
    return all(ok)

if __name__ == '__main__':
    r = [check('0.068967', '4.826866', 0.5, '0.17843'), check('0.17053', '4.56877', 1, '0.18840')]
    print('ALL CHECKS PASS' if all(r) else 'A CHECK FAILED')
