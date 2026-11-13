"""Which block runs out first in the real run?  (input for the ratio assumptions of search.py)

Follows the exact accelerated run from the blank tape (py/accel.py) and, for every jump of at least KMIN periods,
records the delta signature of the phase (the non-zero count changes per period), which of the shrinking blocks
limits the phase, and by how much: slack = (periods the next shrinking block would have lasted) / (periods done).
Jumps where another shrinking block has fewer than KMIN copies left afterwards are listed separately.

usage (from the repo root): python3 holdouts/<M>/py/closure2/witness.py MACHINE MAXSTEPS OUT.json [KMIN]
"""
import json
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import accel  # noqa: E402


def main():
    M = sys.argv[1]
    mx = int(float(sys.argv[2]))
    kmin = int(sys.argv[4]) if len(sys.argv) > 4 else 1000
    S = accel.Sim(M)
    tab = {}

    def oj(rule, k):
        if k < kmin:
            return
        d = rule[2]
        rs = accel.reps(S.c)
        before = [z.n - k * x for z, x in zip(rs, d)]
        sh = [i for i, x in enumerate(d) if x < 0]
        life = [Fraction(before[i], -d[i]) for i in sh]
        j = min(range(len(sh)), key=lambda t: life[t])
        sig = ','.join(str(x) for x in d if x)
        e = tab.setdefault(sig, {'shrinking': len(sh), 'first': {}, 'minslack': None, 'jumps': 0, 'firststep': float(S.c.steps)})
        e['jumps'] += 1
        e['first'][str(j)] = e['first'].get(str(j), 0) + 1
        if len(sh) > 1:
            sl = float(min(life[t] for t in range(len(sh)) if t != j) / life[j])
            if e['minslack'] is None or sl < e['minslack']:
                e['minslack'] = sl
        nblocks = sum(1 for z in rs if z.n >= kmin)
        e['maxblocks'] = max(e.get('maxblocks', 0), nblocks)
    S.on_jump = oj
    try:
        S.run(mx)
    except accel.Halted as h:
        print('HALT', h)
    print('end %.6e' % S.c.steps)
    for sig, e in sorted(tab.items(), key=lambda x: -x[1]['jumps']):
        print('%-28s jumps %6d  shrinking blocks %d  first to run out %s  least slack %s  long blocks <= %d' %
              (sig, e['jumps'], e['shrinking'], e['first'], e['minslack'], e['maxblocks']))
    json.dump({'machine': M, 'maxsteps': mx, 'kmin': kmin, 'signatures': tab}, open(sys.argv[3], 'w'), indent=1)


if __name__ == '__main__':
    main()
