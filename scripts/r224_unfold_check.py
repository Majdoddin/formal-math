"""R224 (2026-11-19): unfolded check of the folded certificates of r155_fold.py (v2 Table t:tab:cert; item 19 / 47 of
arxiv/v2-draft/char2-part-sources.md). For each folded point (Pf), (Uf), (Sf) it takes e0 and gamma0 from
r155_fold.certify_fold, puts eps_f := 1/(1/e0 + 1/4) = 4 e0/(4 + e0), and evaluates r155_cert's own unfolded inequalities
at (eps_f, gamma0) in the same exact interval arithmetic:
    (Lf) U + ln2 pw gamma0 < 0,  (En) rate + ln2 pw gamma0 - ln2 pw/eps_f < 0,  (Tf) max(h2r, h2c) - ln2 pw/eps_f < 0,
    (Sc) h2r + h2c - H - ln2 pw (1/2 - gamma0) < 0 (split and unsplit coverings),
so Hyp_2(eps_f, gamma0) (Hyp_2^LV for the random coverings) holds by r155_cert's argument, with no folding in the
check; the folded saving s0 = e0 gamma0 equals eps_f gamma0/(1 - eps_f/4) exactly (black-box folding,
r156-shr26-levers.md 3.1). (En) and (Tf) at eps_f are r155_fold's (EnF) and (TfF) multiplied by 1/e0.
Usage: python3 r224_unfold_check.py > r224_unfold_check_out.txt"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
import r155_cert as C
import r155_fold as Fo

def unfold(name, pq, cover, xi=None):
    r = Fo.certify_fold(pq, cover, xi=xi)
    c, e0, g0 = r['c'], r['e0'], r['c']['gamma0']
    pwl2 = C.LN2() * pq[3]
    ef = 1 / (1 / e0 + F(1, 4))
    chk = {'Lf': c['chk']['Lf'],
           'En': (c['rate'] + pwl2 * g0 - pwl2 / ef).hi,
           'Tf': (C.imax(c['h2r'], c['h2c']) - pwl2 / ef).hi}
    if 'Sc' in c['chk']:
        chk['Sc'] = c['chk']['Sc']
    ok = all(v < 0 for v in chk.values()) and 0 < ef <= F(1, 2) and 0 < g0 <= F(1, 2)
    same = e0 * g0 == ef * g0 / (1 - ef / 4)
    print(f'{name} {cover}: e0 = {e0}, gamma0 = {g0}, eps_f = 4 e0/(4 + e0) = {ef} = {float(ef):.9f}')
    print('    unfolded checks at (eps_f, gamma0): ' + ', '.join(f'{k} {float(v):.3e}' for k, v in chk.items())
          + f'  -> {"CERTIFIED" if ok else "FAILED"}')
    print(f'    e0 gamma0 = eps_f gamma0/(1 - eps_f/4) exactly: {same}; s0 = {float(e0 * g0):.8f}; '
          f'folded run of r155_fold ok: {r["ok"]}')
    return ok and same and r['ok']

def main():
    print('R224 unfolded check of the folded certificates of r155_fold.py (Table t:tab:cert)')
    rr = F(3465, 10000)
    res = [unfold('(Pf)', ((1 - rr) ** 2, rr * (1 - rr), rr * (1 - rr), rr * rr), 'product'),
           unfold('(Uf)', (F(30598, 100000), F(27822, 100000), F(29581, 100000), F(11999, 100000)), 'unsplit'),
           unfold('(Sf)', (F(30562, 100000), F(28696, 100000), F(28696, 100000), F(12046, 100000)), 'split', xi=F(0))]
    print('ALL CERTIFIED' if all(res) else 'NOT ALL CERTIFIED')

if __name__ == '__main__':
    main()
