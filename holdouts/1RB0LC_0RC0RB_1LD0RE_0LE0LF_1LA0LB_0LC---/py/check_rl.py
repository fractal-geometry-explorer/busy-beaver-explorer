"""Check the run-length simulator c/rl.c: the same tape at every sweep end as with its shift rules turned off, and
(first group) as the plain simulator c/direct.c.  usage: python3 check_rl.py MACHINE [STEPS]  (default 1e8)"""
import sys
from sim import rl, direct, orientation

M = sys.argv[1]
steps = sys.argv[2] if len(sys.argv) > 2 else '1e8'
a = [x for x in rl(M, steps) if x.startswith('S')]
b = [x for x in rl(M, steps, nocross=True) if x.startswith('S')]
n = min(len(a), len(b))
assert n > 100 and a[:n] == b[:n], 'rl.c differs from rl.c without shift rules'
msg = f'{M}: {n} sweep ends up to {float(steps):.0e} steps agree with the run without shift rules'
if orientation(M)[0] == 'R':
    c = [x for x in direct(M, steps) if x.startswith('S')]
    m = min(n, len(c))
    assert a[:m] == c[:m], 'rl.c differs from the plain simulator'
    msg += f' and with the plain simulator ({m})'
print(msg)
