"""Witnesses in the frozen word at crossing turns with blank end (lean/Race.lean).

The list machine (`listmachine.py`) can fail in case 1 only at a crossing turn T2 N O p s with blank end (r = 0), and
only if the right sweep reads (sx true N).reverse ++ 1 ++ s without stopping and ends in F.  A witness in s is a 0
followed by an odd run of 1s that is followed by 0 or by the end of s; with one, case 1 cannot happen
(`astep_T2_witness`).  This counts the crossing turns with blank end that have a witness and prints those that do not,
with the number of bounces since the last time E read the last 1 (an EO turn).

  python3 race.py K     run K list steps (40,000 take about 25 minutes)
"""
import re, sys
from collections import Counter
from listmachine import step1, canon


def bits(s): return ''.join('01'[x] for x in s)


def witness(s):
    return any(m.start() > 0 and len(m.group()) % 2 for m in re.finditer(r'1+', bits(s)))


def race(K):
    st = ('EO', (True, False), ('pre', 1)); C = Counter(); k = None; i = 0
    while i < K:
        if st[0] == 'V': st = st[1]
        pre = canon(st)
        if pre[0] == 'EO':
            print('after list step', i, 'EO, crossing' if pre[2][0] == 'o' else 'EO, no crossing', 'zone length', len(pre[1]))
            k = 0
        st = step1(st)
        if st[0] != 'V': i += 1
        c = canon(st[1] if st[0] == 'V' else st)
        if c[0] == 'T2' and not c[5]:
            if k is not None: k += 1
            w = witness(c[4]); C[w] += 1
            if not w: print('  no witness after list step', i, 'at', 'bounce', k, 'after the EO turn, s =', bits(c[4]) or 'empty')
    print('crossing turns with blank end:', C[True] + C[False], 'with a witness:', C[True])


if __name__ == '__main__':
    race(int(float(sys.argv[1])) if len(sys.argv) > 1 else 12000)
