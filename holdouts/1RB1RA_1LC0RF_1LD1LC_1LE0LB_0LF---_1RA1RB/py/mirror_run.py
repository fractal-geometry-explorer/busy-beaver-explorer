"""The list machine of the Pascal machine (lean/End.lean there) from the first right turn of the Pascal table started
in another state: D for 1RB1RA_1LC0RF_1LD1LC_1LE0LB_0LF---_1RA1RB, C for 1RB1RC_1RC1RB_1LD0RA_1LE1LD_1LF0LC_0LA---
(lean/Mirror.lean: each of them is that run in a mirror).  Uses py/listmachine.py and py/race.py of
holdouts/1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF.

  python3 mirror_run.py first Q          the first right turn of the Pascal table started in Q, as a list state
  python3 mirror_run.py lockstep Q N     the list machine against every right turn of the first N steps
  python3 mirror_run.py run Q K          K list steps alone: no failure (astep = none), far parts clean, and the
                                         crossing turns with blank end that lack a witness (lean/Race.lean)
"""
import os
import re
import sys
import time
from collections import Counter

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF", "py"))
import listmachine as LM  # noqa: E402
from turnshape import T, tok_left, tok_right  # noqa: E402
from race import witness, bits  # noqa: E402


def first(q):
    """Run the Pascal table from blank tape in state q to its first right turn; return (step, list state)."""
    tape, h, st, lo, hi, mv = {}, 0, q, 0, 0, 0
    for t in range(10 ** 4):
        a = T[(st, tape.get(h, 0))]
        if st == 'E' and mv == 1 and a[1] == -1:
            L, R = tok_left(tape, h, lo), tok_right(tape, h, hi)
            assert R == 'o' and '?' not in L and 'o' not in L[1:], (L, R)   # E on the last 1, a plain zone
            p = 1 if L.startswith('o') else 0
            w = tuple(x == 'b' for x in reversed(L[p:]))
            return t, ('EO', w, ('pre', p))
        tape[h] = a[0]; h += a[1]; mv = a[1]; st = a[2]; lo = min(lo, h); hi = max(hi, h)
    raise RuntimeError('no right turn')


def lockstep(q, N):
    src = open(LM.__file__).read()
    code = "def lockstep(N):" + src.split("def lockstep(N):")[1].split("\ndef run(")[0]
    code = code.replace("tape,h,st,lo,hi,mv={},0,'A',0,0,0", "tape,h,st,lo,hi,mv={},0,START,0,0,0")
    g = dict(vars(LM)); g['START'] = q
    exec(code, g)
    g['lockstep'](N)


def run(q, K, every=5000):
    clean = re.compile(r'^y(x(xx)*y)*x(xx)*$')
    t0, st = first(q)
    print('start', q, 'first right turn at step', t0, st, flush=True)
    kinds = Counter(); unclean = 0; zone = 0; wit = Counter(); k = None; i = 0; t = time.time()
    while i < K:
        if st[0] == 'V': st = st[1]
        pre = LM.canon(st)
        if pre[0] == 'EO':
            print('after list step', i, 'EO,', 'crossing' if pre[2][0] == 'o' else 'no crossing', 'zone', len(pre[1]))
            k = 0
        try:
            st = LM.step1(st)
        except LM.Danger as d:
            print('FAILS after list step', i, d); return
        if st[0] == 'V': continue
        i += 1
        c = LM.canon(st); kinds[c[0]] += 1
        if c[0] == 'T2':
            if not clean.match(''.join('xy'[b] for b in c[2])): unclean += 1
            zone = max(zone, len(c[1]) + len(c[2]))
            if not c[5]:
                if k is not None: k += 1
                w = witness(c[4]); wit[w] += 1
                if not w: print('  no witness after list step', i, 'bounce', k, 'after the EO turn, s =', bits(c[4]) or 'empty')
        else:
            zone = max(zone, len(c[1]))
        if i % every == 0 or i == K:
            print(i, 'list steps', dict(kinds), 'unclean far parts', unclean, 'largest zone', zone,
                  'blank-end crossing turns', wit[True] + wit[False], 'with witness', wit[True],
                  '%.0fs' % (time.time() - t), flush=True)


if __name__ == '__main__':
    cmd, q = sys.argv[1], sys.argv[2]
    if cmd == 'first': print(first(q))
    elif cmd == 'lockstep': lockstep(q, int(float(sys.argv[3])))
    else: run(q, int(float(sys.argv[3])))
