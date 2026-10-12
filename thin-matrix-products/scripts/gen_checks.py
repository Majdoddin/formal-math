#!/usr/bin/env python3
"""Writes Checks.lean: for every statement `def X : Prop` of Statements.lean whose proof
`theorem x : X` exists in ThinMatrixProducts/, one line `theorem x : X := ThinMatrixProducts.x`.
Prints the statements that have no proof yet."""
import re, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
stm = (root / 'Statements.lean').read_text()
names = re.findall(r'^def (\w+) : Prop', stm, re.M)
proofs = {}
for f in (root / 'ThinMatrixProducts').rglob('*.lean'):
    for m in re.finditer(r'^theorem (\w+) : (\w+)\b', f.read_text(), re.M):
        proofs[m.group(2)] = m.group(1)
lines = ['/-', 'For every statement of `Statements.lean`, a theorem which says that it holds. The proofs are',
         'in `ThinMatrixProducts/`; this file only names them. Written by `scripts/gen_checks.py`.', '-/',
         'import ThinMatrixProducts', '', 'namespace ThinMatrixProducts.Checks', 'open ThinMatrixProducts', '']
missing = []
for n in names:
    if n in proofs:
        lines.append(f'theorem {proofs[n]} : {n} := ThinMatrixProducts.{proofs[n]}')
    else:
        missing.append(n)
lines += ['', 'end ThinMatrixProducts.Checks', '']
(root / 'Checks.lean').write_text('\n'.join(lines))
print('statements:', len(names), 'proved:', len(names) - len(missing))
for n in missing: print('MISSING', n)
