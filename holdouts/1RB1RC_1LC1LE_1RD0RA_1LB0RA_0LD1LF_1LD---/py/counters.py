"""The counter-list rule of 1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---, complete (every case met in the run), with
the exact step count of each visit, and its checks against the machine.

At each visit (A at the right end, on blank) the tape is  0^inf (10)^c0 s0 (10)^c1 s1 ... (10)^c(m-1) A>  with
separators s in {0, 1}.  A counter may be 0 (a zero slot): in the run it only appears between two 0 separators
(the tape shows 00, or 000 for two slots), or as the prefix c0 = 0, s0 = 1 (the tape starts with a lone 1).

The carry starts at the last counter, i = m-1:
  * s(i-1) = 1: that separator becomes 0, and the target is c(i) if c(i) is even, c(i-1) if c(i) is odd;
  * s(i-1) = 0 and c(i) even: the target is c(i-1);
  * s(i-1) = 0 and c(i) odd: go on with i - 1;
  * i = 0 (the carry passes the first counter): REBUILD at the front (below).
If the target is >= 1 it loses 1 and the last counter gains 3 (an ordinary visit).  If the target is a zero slot:
  * the counter x left of the slot >= 1: x loses 1, the slot disappears, x and the counter y right of it are joined by
    a separator 1, and the tail from y is REBUILT;
  * x is also a slot: the counters left of x and right of the target merge (their sum), the two slots disappear, and
    the tail from the merged counter is REBUILT;
  * the target is the prefix (c0 = 0, s0 = 1, reached from c1 odd): the prefix disappears and the tail from c1 is
    REBUILT, with c1 gaining one more.
REBUILD from y: every separator from y to the end becomes 1, y gains 1, the last counter gains 1 (2 if it is y), and
a new last counter 2 is appended after a separator 0.  At the front: c0 even: rebuild from c0; c0 odd: a new
counter 0 is put in front with separator 1 and the rebuild is from it (so it becomes 1).
Normal form: a leading zero counter with separator 0 is blank tape and is dropped; a zero counter between a
separator 1 and a separator 0 is the same tape as its two neighbours merged plus 1 ((10)^a 1 0 (10)^b = (10)^(a+b+1)).

Steps of the visit (S = c(i) + ... + c(m-1), n = m - i, u = number of separators 1 among s(i-1)...):
ordinary, s(i-1) = 0: 6S + 6n + 12;  s(i-1) = 1, c(i) odd: 6S + 6n + 5u + 5;  c(i) even: 6S + 6n + 4u + 4;
rebuild at the front: 6S + 28 (S the sum of all counters);  at a slot: 6S + 28;  at the prefix: 6S + 10u + 20.

usage:
  python3 counters.py random N           compare with the machine on N random lists (with slots and the prefix)
  python3 counters.py visits FILE        compare with every visit printed by ../c/tokvisits (blocks and steps)
"""
import random
import sys

M = "1RB1RC_1LC1LE_1RD0RA_1LB0RA_0LD1LF_1LD---"


LAST = {}   # details of the last event: the counter x left of a zero slot, its index


class Unknown(Exception):
    """A shape the rule does not cover (never met in the run from blank tape)."""


def rebuild_tail(cs, ss, y):
    for k in range(y, len(ss)):
        ss[k] = '1'
    cs[y] += 1
    cs[-1] += 1
    cs.append(2)
    ss.append('0')


def norm(cs, ss):
    while len(cs) > 1 and cs[0] == 0 and ss[0] == '0':
        cs.pop(0); ss.pop(0)
    k = 1
    while k < len(cs) - 1:
        if cs[k] == 0 and ss[k - 1] == '1':
            if ss[k] != '0':
                raise Unknown('slot between two separators 1')
            cs[k - 1] += cs[k + 1] + 1
            del cs[k:k + 2]; del ss[k - 1:k + 1]
            continue
        if cs[k] == 0 and ss[k] == '1':
            raise Unknown('slot followed by a separator 1')
        k += 1
    return cs, ss


def step(cs, ss):
    """(cs', ss', steps, kind) for the next visit."""
    cs, ss = list(cs), list(ss)
    m = len(cs)
    i = m - 1
    pref = cs[0] == 0 and len(ss) > 0 and ss[0] == '1'
    while True:
        if i == 0:
            if cs[0] == 0:
                raise Unknown('front 0 passed')
            steps = 6 * sum(cs) + 28
            if cs[0] % 2 == 0:
                rebuild_tail(cs, ss, 0)
            else:
                cs.insert(0, 0); ss.insert(0, '1')
                rebuild_tail(cs, ss, 0)
            cs, ss = norm(cs, ss)
            return cs, ss, steps, 'front'
        if ss[i - 1] == '1':
            if cs[i] == 0:
                raise Unknown('slot with a separator 1 on its left')
            j = i if cs[i] % 2 == 0 else i - 1
            u = sum(1 for x in ss[i - 1:] if x == '1')
            S, n = sum(cs[i:]), m - i
            steps = 6 * S + 6 * n + (4 * u + 4 if j == i else 5 * u + 5)
            ss[i - 1] = '0'
            break
        if cs[i] % 2 == 0:
            j = i - 1
            S, n = sum(cs[i:]), m - i
            steps = 6 * S + 6 * n + 12
            u = 0
            break
        i -= 1
    if cs[j] >= 1:
        cs[j] -= 1
        cs[-1] += 3
        cs, ss = norm(cs, ss)
        return cs, ss, steps, 'ordinary'
    if j == 0:
        if not pref:
            raise Unknown('front slot')
        steps = 6 * S + 10 * u + 20
        del cs[0]; del ss[0]
        rebuild_tail(cs, ss, 0)
        cs[0] += 1
        cs, ss = norm(cs, ss)
        return cs, ss, steps, 'prefix'
    if ss[j] == '1':
        raise Unknown('slot with a separator 1 on its right')
    steps = 6 * S + 28
    x = cs[j - 1]
    LAST.clear(); LAST.update(j=j, x=x, left=cs[max(0, j - 3):j], right=cs[j + 1:j + 3])
    if x >= 1:
        cs[j - 1] -= 1
        del cs[j]; del ss[j - 1]
        ss[j - 1] = '1'
        rebuild_tail(cs, ss, j)
        cs, ss = norm(cs, ss)
        return cs, ss, steps, 'slot'
    if j - 2 < 0 or (ss[j - 2] == '1' and not (j - 2 == 0 and pref)):
        raise Unknown('merge at the front or across a separator 1')
    cs[j - 2] += cs[j + 1]
    del cs[j - 1:j + 2]; del ss[j - 2:j + 1]
    rebuild_tail(cs, ss, j - 2)
    cs, ss = norm(cs, ss)
    return cs, ss, steps, 'merge'


def tape(cs, ss):
    s = ''
    for i, c in enumerate(cs):
        if i:
            s += ss[i - 1]
        s += '10' * c
    return s.lstrip('0')


def parse(toks):
    """the format of ../c/tokvisits: '|' or a prefix '1', then counter, separator string, counter, ..."""
    cs, ss = [], []
    if toks[0] == '|':
        toks = toks[1:]
    else:
        assert toks[0] == '1', toks[:3]
        cs.append(0); ss.append('1'); toks = toks[1:]
    cs.append(int(toks[0]))
    k = 1
    while k < len(toks):
        sp = toks[k]
        if sp == '1':
            ss.append('1')
        else:
            assert set(sp) == {'0'}, sp
            for _ in range(len(sp) - 1):
                ss.append('0'); cs.append(0)
            ss.append('0')
        cs.append(int(toks[k + 1])); k += 2
    return cs, ss


TABLE = {}
for _i, _g in enumerate(M.split('_')):
    for _r in range(2):
        _t = _g[3 * _r:3 * _r + 3]
        TABLE[(_i, _r)] = None if _t[0] == '-' else (int(_t[0]), 1 if _t[1] == 'R' else -1, ord(_t[2]) - 65)


def machine_next(t, maxs=10 ** 6):
    """run the machine from tape t (string) with A at the right end on blank to the next such visit"""
    tp = dict(enumerate(map(int, t)))
    pos, st, steps, hi = len(t), 0, 0, len(t)
    while steps < maxs:
        tr = TABLE[(st, tp.get(pos, 0))]
        if tr is None:
            return 'HALT', steps
        tp[pos] = tr[0]; pos += tr[1]; st = tr[2]; steps += 1
        hi = max(hi, pos)
        if st == 0 and pos >= hi and tp.get(pos, 0) == 0:
            lo = min(k for k, v in tp.items() if v == 1)
            return ''.join(str(tp.get(k, 0)) for k in range(lo, pos)), steps
    return 'TIMEOUT', steps


def main():
    what = sys.argv[1]
    if what == 'random':
        N = int(sys.argv[2])
        rnd = random.Random(1)
        from collections import Counter
        kinds, bad, unk = Counter(), 0, 0
        for _ in range(N):
            m = rnd.randint(2, 6)
            cs = [rnd.randint(1, 9) for _ in range(m)]
            ss = [rnd.choice('01') for _ in range(m - 1)]
            if m >= 3 and rnd.random() < 0.6:
                for _ in range(rnd.randint(1, 2)):
                    z = rnd.randint(1, m - 2); cs[z] = 0; ss[z - 1] = '0'; ss[z] = '0'
            if rnd.random() < 0.3:
                cs = [0] + cs; ss = ['1'] + ss
            try:
                cs, ss = norm(cs, ss)
                c2, s2, st, kind = step(cs, ss)
            except Unknown:
                unk += 1
                continue
            out, steps = machine_next(tape(cs, ss))
            kinds[kind] += 1
            if out != tape(c2, s2) or steps != st:
                bad += 1
                print('MISMATCH', cs, ss, out, tape(c2, s2), steps, st)
        print('random lists: %d checked (%s), %d outside the rule, %d mismatches' % (sum(kinds.values()), dict(kinds), unk, bad))
    elif what == 'visits':
        from collections import Counter
        prev = None; n = 0; kinds = Counter()
        for line in open(sys.argv[2]):
            p = line.split()
            if p[0] == 'HALT':
                print(line); break
            cur = parse(p[2:]); s = int(p[1])
            if prev is not None:
                c2, s2, st, kind = step(*prev)
                if (c2, s2) != cur or ps + st != s:
                    print('MISMATCH at visit', p[0]); return
                n += 1; kinds[kind] += 1
            prev, ps = cur, s
        print('%d consecutive visits up to step %d: counters and step counts agree (%s)' % (n, ps, dict(kinds)))


if __name__ == '__main__':
    main()
