"""R154(c) reviewer: independent interval certificates of r155's points (P), (U), (S) unfolded and (Pf), (Uf), (Sf)
folded (system python, mpmath interval arithmetic; no r155/r156 code).

Method (different from r155's tangent plane):
 Lam(p) <= max_v g_mu(v), g_mu = mu f1 + (1-mu) f2 (weak duality, any mu in [0,1]);
 g_mu(v) = K + sum_i phi_i(v_i) is separable; for every real C,
   max_{simplex} g_mu <= K + C + sum_i sup_{v >= 0} (phi_i(v) - C v);
 each sup is attained in a bracket [lo, hi] with F'(lo) > 0 > F'(hi) (checked in intervals; F concave), so it is at
 most the upper end of the interval extension of F over [lo, hi].
 E_side^side(p) <= Phi(lambda; p) (r155 1.4 weak duality, re-derived), evaluated in intervals at float multipliers
 (any multipliers are admissible: nu real, zeta, eta >= 0); at the general points lambda0 of Prop. 1.5.
 reading exponents rd_side in intervals; E_side' := max(E_side bound, rd).
Conditions (r155 Theorems P, G; folded: Theorem P/G applied at eps' with 1/eps' = 1/e0 + 1/4):
 (Lf) UB_Lam + gamma0 pw ln2 < 0
 (En) rate + gamma0 pw ln2 < pw ln2 / eps'     rate per covering (product / unsplit rows relabeled / split xi = 0)
 (Tf) max(H2r, H2c) < pw ln2 / eps'
 (Sc) randomized: H2r + H2c - H < (1/2 - gamma0) pw ln2
 (Hy) 0 < eps', gamma0 <= 1/2
Usage: /usr/bin/python3 r154c_cert.py r154c_cert_out.txt   (reads r154c_certdata.json for mu, C, multipliers)
"""
import json, sys
from fractions import Fraction as Fr
import mpmath
from mpmath import iv, mpf

iv.prec = 240
mpmath.mp.prec = 240

out = open(sys.argv[1], 'w') if len(sys.argv) > 1 else sys.stdout
log = lambda s: print(s, file=out, flush=True)


def I(x):
    """exact rational or float -> point interval (rational: enclosing interval)."""
    if isinstance(x, Fr):
        return iv.mpf(x.numerator) / iv.mpf(x.denominator)
    return iv.mpf(x)


LN2 = iv.log(iv.mpf(2))


def ent(ps):
    s = iv.mpf(0)
    for x in ps:
        s -= x * iv.log(x)
    return s


def H2(x):
    return ent([x, 1 - x])


def hi(x):
    return mpf(x.b) if isinstance(x, iv.mpf) else mpf(x)   # exact: endpoints are representable at this precision


def lo(x):
    return mpf(x.a) if isinstance(x, iv.mpf) else mpf(x)


# ----- Lam upper bound -----
def phi_parts(p, mu, i):
    p0, p1, p2, pw = p
    q = [p0, p1, p2, iv.mpf(0)][i]
    def F(v, C):
        t = q + pw * v
        return -mu * pw * v * iv.log(v) - (1 - mu) * t * iv.log(t) - C * v
    def dF(v, C):
        t = q + pw * v
        return -mu * pw * (iv.log(v) + 1) - (1 - mu) * pw * (iv.log(t) + 1) - C
    return F, dF


def stationary_float(p, mu, C, i):
    """float (mp) root of dF via bisection in log v."""
    p0, p1, p2, pw = [mpf(Fr_to_mp(x)) for x in p]
    q = [p0, p1, p2, mpf(0)][i]
    def d(lv):
        v = mpmath.exp(lv)
        return -mu * pw * (lv + 1) - (1 - mu) * pw * (mpmath.log(q + pw * v) + 1) - C
    a, b = mpf(-300), mpf(10)
    for _ in range(400):
        m = (a + b) / 2
        if d(m) > 0:
            a = m
        else:
            b = m
    return mpmath.exp(a), mpmath.exp(b)


def Fr_to_mp(x):
    return mpf(x.numerator) / mpf(x.denominator)


def lam_upper(pr, mu_f, C_f):
    p = [I(x) for x in pr]
    mu = iv.mpf(mpf(mu_f))
    C = iv.mpf(mpf(C_f))
    p0, p1, p2, pw = p
    Hp = ent(p)
    K = -mu * pw * LN2 / 2 - (1 - mu) * Hp
    total = K + C
    vs = []
    for i in range(4):
        F, dF = phi_parts(p, mu, i)
        a, b = stationary_float(pr, mpf(mu_f), mpf(C_f), i)
        # widen slightly
        a = a * (1 - mpf(10) ** -40)
        b = b * (1 + mpf(10) ** -40)
        va, vb = iv.mpf(a), iv.mpf(b)
        assert lo(dF(va, C)) > 0, ('bracket lo', i)
        assert hi(dF(vb, C)) < 0, ('bracket hi', i)
        total += F(iv.mpf([a, b]), C)
        vs.append((a + b) / 2)
    sv = sum(vs)
    return total, [x / sv for x in vs]  # upper end of total is the rigorous bound; vs: the g_mu maximiser


def lam_lower(pr, v_f):
    """rigorous LOWER bound: min(f1, f2) at an explicit point of the simplex (tightness)."""
    p = [I(x) for x in pr]
    p0, p1, p2, pw = p
    v = [iv.mpf(mpf(x)) for x in v_f[:3]]
    v.append(1 - v[0] - v[1] - v[2])
    f1 = pw * ent(v) - pw * LN2 / 2
    t = [p0 + pw * v[0], p1 + pw * v[1], p2 + pw * v[2], pw * v[3]]
    f2 = ent(t) - ent(p)
    return min(lo(f1), lo(f2))


# ----- E_side bound -----
CL = {1: (0, 1), 2: (0, 2), 3: (1,), 4: (0,)}
CR = {1: (0,), 2: (1,), 3: (0, 2), 4: (0, 1)}


def ivmax(xs):
    m = xs[0]
    for x in xs[1:]:
        m = iv.mpf([max(lo(m), lo(x)), max(hi(m), hi(x))])
    return m


def Phi_iv(lam, pr, side):
    p = [I(x) for x in pr]
    p0, p1, p2, pw = p
    nu, zeta, e1, e2, e3 = lam
    if not isinstance(e1, iv.mpf):
        assert zeta >= 0 and e1 >= 0 and e2 >= 0 and e3 >= 0
    nu, zeta, e1, e2, e3 = [iv.mpf(mpf(x)) if not isinstance(x, iv.mpf) else x for x in (nu, zeta, e1, e2, e3)]
    eta = {1: e1, 2: e2, 3: e3, 4: iv.mpf(0)}
    Cs = CL if side == 'L' else CR
    size = (p2 + pw) if side == 'L' else (p1 + pw)
    def c(t, s):
        return eta[t] - nu * (1 if s != 0 else 0) - zeta * (1 if s == 2 else 0)
    a = [ivmax([c(t, s) for s in Cs[t]]) for t in (1, 2, 3, 4)]
    b = [ivmax([c(t, s) for t in (1, 2, 3, 4) if s in Cs[t]]) for s in (0, 1, 2)]
    A = iv.log(sum(iv.exp(x) for x in a))
    B = iv.log(sum(iv.exp(x) for x in b))
    return nu * size + zeta * pw - e1 * p0 - e2 * p1 - e3 * p2 + ivmax([A, B])


def rd_iv(pr, side):
    p = [I(x) for x in pr]
    p0, p1, p2, pw = p
    s = (p2 + pw) if side == 'L' else (p1 + pw)
    return H2(s) + (s + pw) * H2(pw / (s + pw))


def side_bound(pr, side, lam_f):
    p0, p1, p2, pw = pr
    B = (max(p0, p1) + max(p0, p2) + p1) if side == 'L' else (max(p0, p2) + p1 + p2)
    prop = (pw <= min(p0, p1, p2)) and (B <= 1)
    pI = [I(x) for x in pr]
    if prop:
        # lambda0 of Prop 1.5, evaluated in intervals (gives H(p) + ln max(1, B) = H(p))
        lam0 = (iv.mpf(0), iv.mpf(0), iv.log(pI[0] / pI[3]), iv.log(pI[1] / pI[3]), iv.log(pI[2] / pI[3]))
        val = Phi_iv(lam0, pr, side)
        how = 'lambda0 (Prop 1.5 applies: pw <= min p_i, B_side = %.6f <= 1, exact rational check)' % float(B)
    else:
        val = Phi_iv(tuple(lam_f), pr, side)
        how = 'float multipliers %s (B_side = %.6f > 1)' % (tuple(round(x, 10) for x in lam_f), float(B))
    rd = rd_iv(pr, side)
    return ivmax([val, rd]), val, rd, how


# ----- points -----
def prod(r):
    return [(1 - r) ** 2, r * (1 - r), r * (1 - r), r * r]


PTS = [
    # name, covering, p (rationals), (eps0 or e0), gamma0, folded
    ('P', 'product', prod(Fr(1373, 4000)), Fr(62457, 500000), Fr(68459, 1000000), False),
    ('U', 'unsplit_rows', [Fr(3073, 10000), Fr(5579, 20000), Fr(5923, 20000), Fr(147, 1250)], Fr(120191, 1000000), Fr(81093, 1000000), False),
    ('S', 'split', [Fr(30697, 100000), Fr(23, 80), Fr(23, 80), Fr(11803, 100000)], Fr(7573, 62500), Fr(2023, 25000), False),
    ('Pf', 'product', prod(Fr(3465, 10000)), Fr(13121, 100000), Fr(33647, 500000), True),
    ('Uf', 'unsplit_rows', [Fr(15299, 50000), Fr(13911, 50000), Fr(29581, 100000), Fr(11999, 100000)], Fr(126377, 1000000), Fr(4971, 62500), True),
    ('Sf', 'split', [Fr(15281, 50000), Fr(3587, 12500), Fr(3587, 12500), Fr(6023, 50000)], Fr(31867, 250000), Fr(79347, 1000000), True),
    # full encodings (4^L per band): sanity against the reviewed r150 (C1), (C2) and r156's folded (C1f), (C2f), (C3f)
    ('C1', 'product', prod(Fr(1843, 5000)), Fr(3209, 25000), Fr(11859, 200000), False, 'full'),
    ('C2', 'unsplit_cols', [Fr(1487, 5000), Fr(1487, 5000), Fr(1383, 5000), Fr(643, 5000)], Fr(6127, 50000), Fr(74073, 1000000), False, 'full'),
    ('C1f', 'product', prod(Fr(3721, 10000)), Fr(13559, 100000), Fr(29007, 500000), True, 'full'),
    ('C2f', 'unsplit_cols', [Fr(741, 2500), Fr(741, 2500), Fr(2763, 10000), Fr(1309, 10000)], Fr(25791, 200000), Fr(18159, 250000), True, 'full'),
    ('C3f', 'split', [Fr(2901, 10000), Fr(2901, 10000), Fr(2901, 10000), Fr(1297, 10000)], Fr(128527, 1000000), Fr(73597, 1000000), True, 'full'),
]


def main():
    data = json.load(open('r154c_certdata.json'))
    data.update(json.load(open('r154c_certdata_full.json')))
    log("R154(c) independent interval certificates (mpmath iv, 240 bits); separable Lagrange bound for Lam,")
    log("weak dual Phi for E_side; conditions of r155 Theorems P/G (folded: at 1/eps' = 1/e0 + 1/4).")
    allok = True
    for entry in PTS:
        name, cov, pr, e0, g0, folded = entry[:6]
        enc = entry[6] if len(entry) > 6 else 'pruned'
        assert sum(pr) == 1 and min(pr) > 0
        d = data[name]
        p = [I(x) for x in pr]
        p0, p1, p2, pw = p
        Hp = ent(p)
        H2r, H2c = H2(p2 + pw), H2(p1 + pw)
        UB, vmax = lam_upper(pr, d['mu'], d['C'])
        LB = lam_lower(pr, vmax)
        if enc == 'pruned':
            EL, ELs, rdL, howL = side_bound(pr, 'L', d['lamL'])
            ER, ERs, rdR, howR = side_bound(pr, 'R', d['lamR'])
        else:
            # full encoding: 4^L per band; reading C(L,a)C(a+d,d) <= 4^L needs a + d <= L (checked)
            assert pr[2] + 2 * pr[3] <= 1 and pr[1] + 2 * pr[3] <= 1
            EL = ER = ELs = ERs = 2 * LN2
            rdL, rdR = rd_iv(pr, 'L'), rd_iv(pr, 'R')
            assert hi(rdL) <= lo(EL) and hi(rdR) <= lo(ER)
            howL = howR = 'full encoding ln 4'
        g0I = I(g0)
        e0I = I(e0)
        inv_eps = (1 / e0I + iv.mpf(1) / 4) if folded else 1 / e0I
        nu = pw * LN2 * inv_eps
        gp = g0I * pw * LN2
        if cov == 'product':
            rate = ivmax([EL, ER]) - H2r
        elif cov == 'unsplit_rows':
            rate = ivmax([ER - H2c, EL + H2c - Hp])
        elif cov == 'unsplit_cols':
            rate = ivmax([EL - H2r, ER + H2r - Hp])
        else:
            rate = ivmax([EL + (H2c - H2r - Hp) / 2, ER + (H2r - H2c - Hp) / 2])
        m_Lf = UB + gp
        m_En = rate + gp - nu
        m_Tf = ivmax([H2r, H2c]) - nu
        m_Sc = (H2r + H2c - Hp) - (iv.mpf(1) / 2 - g0I) * pw * LN2
        X = (H2r + H2c - Hp) / 2
        checks = {'Lf': hi(m_Lf) < 0, 'En': hi(m_En) < 0, 'Tf': hi(m_Tf) < 0,
                  'Hy': (1 / inv_eps).b <= 0.5 and g0 <= Fr(1, 2) and g0 > 0}
        if cov != 'product':
            checks['Sc'] = hi(m_Sc) < 0
            checks['X>=0'] = lo(X) >= 0
        ok = all(checks.values())
        allok &= ok
        s0 = e0 * g0
        log(f"\n[{name}] covering {cov}, {enc} encodings, {'FOLDED' if folded else 'unfolded'}; p = ({', '.join(str(x) for x in pr)})")
        log(f"   ({'e0' if folded else 'eps0'}, gamma0) = ({e0}, {g0}) = ({float(e0):.6f}, {float(g0):.6f}); s0 = {s0} = {float(s0):.10f}"
            f"; APSP exponent 3 - s0 = {float(3 - s0):.10f}")
        log(f"   Lam <= UB = {mpmath.nstr(hi(UB), 12)} (mu = {d['mu']:.10f}, C = {d['C']:.10f})"
            + (f"; LB = {mpmath.nstr(LB, 12)} at the float maximiser, gap {mpmath.nstr(hi(UB) - LB, 3)}" if LB is not None else ''))
        log(f"   leaf bound on gamma: -UB/(pw ln2) >= {mpmath.nstr(lo(-UB / (pw * LN2)), 12)}  (gamma0 = {float(g0):.8f})")
        log(f"   H(p) in [{mpmath.nstr(lo(Hp), 13)}, {mpmath.nstr(hi(Hp), 13)}]; H2r = {mpmath.nstr(hi(H2r), 12)}, H2c = {mpmath.nstr(hi(H2c), 12)}")
        log(f"   E_side^L <= {mpmath.nstr(hi(ELs), 13)} via {howL}; rd_L = {mpmath.nstr(hi(rdL), 8)}")
        log(f"   E_side^R <= {mpmath.nstr(hi(ERs), 13)} via {howR}; rd_R = {mpmath.nstr(hi(rdR), 8)}")
        log(f"   1/eps' = {mpmath.nstr(hi(inv_eps), 12)}; E = rate/(pw ln2) <= {mpmath.nstr(hi(rate / (pw * LN2)), 12)}; "
            f"T = max(H2r,H2c)/(pw ln2) <= {mpmath.nstr(hi(ivmax([H2r, H2c]) / (pw * LN2)), 12)}")
        log(f"   margins (upper ends; all must be < 0): Lf {mpmath.nstr(hi(m_Lf), 4)}, En {mpmath.nstr(hi(m_En), 4)}, "
            f"Tf {mpmath.nstr(hi(m_Tf), 4)}" + (f", Sc {mpmath.nstr(hi(m_Sc), 4)}" if cov != 'product' else ''))
        log(f"   checks {checks}  ->  {'CERTIFIED' if ok else 'NOT CERTIFIED'}")
    log(f"\nALL CERTIFIED: {allok}")


if __name__ == '__main__':
    main()
