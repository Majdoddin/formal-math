r"""R61b (D), Section 6.4: rigorous certificates for the fixed-q data structure (exact box count per type) at product
types beyond rho = 1/2.

Boxes at switching order t = theta d are at most poly * M * exp(L B(p, theta)) with
    B(p, theta) = max_{v in P_theta} G(v) - H(p),   G(v) = H(p0 + pw v1, p1 + pw v2, p2 + pw v3, pw v4),
    P_theta = {v in simplex_4 : v4 <= 1 - theta}  (vertices e1, e2, e3 and theta e_i + (1-theta) e4).
G is concave, so for any v* in P_theta: max G <= G(v*) + max_{vertex u} grad G(v*).(u - v*).  We take v* on the face
v4 = 1 - theta with t1 = t2 = t3 (water filling) and evaluate the bound in interval arithmetic (mpmath.iv).
The query exponent is q(theta) = (H(theta) + theta ln 3)/ln 2; the encoding range at rho is rho^2 ln2/(ln4 - H2(rho)).
Run with the system python (mpmath): /usr/bin/python3 r61b_certify2.py > r61b_certify2_out.txt
"""
from fractions import Fraction
import math
from mpmath import iv, mp

iv.dps = 50
mp.dps = 30


def Hiv(v):
    return -sum(x * iv.log(x) for x in v)


def cert(rho, theta):
    rho = Fraction(rho); theta = Fraction(theta)
    p = [(1 - rho) ** 2, rho * (1 - rho), rho * (1 - rho), rho ** 2]
    pw = p[3]
    # water filling on the face v4 = 1 - theta
    T = (p[0] + p[1] + p[2] + pw * theta) / 3
    v = [(T - p[i]) / pw for i in range(3)] + [1 - theta]
    assert all(x >= 0 for x in v) and sum(v) == 1
    P = [iv.mpf(x.numerator) / x.denominator for x in p]
    V = [iv.mpf(x.numerator) / x.denominator for x in v]
    PW = P[3]
    t = [P[0] + PW * V[0], P[1] + PW * V[1], P[2] + PW * V[2], PW * V[3]]
    G = Hiv(t)
    grad = [-PW * (iv.log(t[i]) + 1) for i in range(4)]
    th = iv.mpf(theta.numerator) / theta.denominator
    verts = []
    for i in range(3):
        u = [0, 0, 0, 0]; u[i] = 1; verts.append(u)
        u = [0, 0, 0, 0]; u[i] = th; u[3] = 1 - th; verts.append(u)
    lin = [sum(grad[k] * (iv.mpf(u[k]) - V[k]) for k in range(4)) for u in verts]
    upper = G.b + max(x.b for x in lin) - Hiv(P).a
    q = (-(float(theta)) * math.log(float(theta)) - (1 - float(theta)) * math.log(1 - float(theta))
         + float(theta) * math.log(3)) / math.log(2)
    r = float(rho)
    eps = r * r * math.log(2) / (math.log(4) - (-r * math.log(r) - (1 - r) * math.log(1 - r)))
    return upper, q, eps


if __name__ == '__main__':
    print('B(p, theta) <= U (interval upper bound); U < 0 certifies that the boxes decay at query exponent q(theta)')
    for rho, theta in [(Fraction(1, 2), Fraction(1, 100)), (Fraction(101, 200), Fraction(1, 20)),
                       (Fraction(51, 100), Fraction(1, 10)), (Fraction(13, 25), Fraction(3, 20)),
                       (Fraction(261, 500), Fraction(37, 200)), (Fraction(523, 1000), Fraction(189, 1000)),
                       (Fraction(5235, 10000), Fraction(1892, 10000))]:
        U, q, eps = cert(rho, theta)
        print(f'rho = {rho} ({float(rho):.4f}), theta = {theta} ({float(theta):.4f}): U = {mp.nstr(U, 8)} '
              f'({"certified" if U < 0 else "NOT certified"}); q(theta) = {q:.6f}; eps(rho) = {eps:.6f}')
