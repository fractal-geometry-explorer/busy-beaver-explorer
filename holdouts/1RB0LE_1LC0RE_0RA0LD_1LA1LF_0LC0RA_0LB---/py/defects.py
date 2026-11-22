"""Chains with defects (the siblings with E1 = 0RE): the defect law, a checker and a simulator that uses it.

A defect is one erased cell (a 1 turned to 0) in a separator of the chain of wordchain.py:

    after Z      d = 11   ->  c = 01   (first cell erased)     also seen: a = 10, ad, zd, ac (laws not decoded)
    after a W    c = 01   ->  z = 00
    after a U    ad = 1011 -> ac = 1001 (third cell erased)

**The defect law (checked, see below).**  Carries follow the chain law of wordchain.py (each wrap sends 3 to the
next word; an empty word passes 3 times what it got).  When a carry of c > 0 reaches a defect (one of the three
erasures in the table, the after-Z `c` included), the separator is restored and the carry goes on as c - 3: the
defect takes exactly one unit.  So between two defects the law is the chain law, and a defect only delays the carry
by one unit, once.  Not decoded: the separator after Z read as `a` (and the rarer ad, zd, ac there).  When a carry
meets it the words after it are read again with W and U swapped, as at a change of era.

usage (from the repository root):
  python3 .../py/defects.py MACHINE check STEPS      every pair of consecutive full events of a plain run
  python3 .../py/defects.py MACHINE run DIGITS [SPOT]
      follows the run until about 10^DIGITS events: jumps by the chain law on the words up to the first defect,
      applies the defect law at each crossing without running it, and runs cell by cell only the events the law
      does not cover (a carry leaving the chain, or reaching an undecoded defect); where the chain is not in this
      grammar at all it falls back to prefixjump.py (the chain law on the longest grammar prefix, tail kept).  It checks itself: SPOT random
      events per jump and a fifth of the crossings are rebuilt and run cell by cell against the law.
"""
import random
import re
import sys

from prefixjump import parse_prefix
from wordchain import S_of, Sim, add_n, bits, decode, jump, ptab, tape_left, tape_right, val

ZD = r'((?:za|aa)+)'
WD = r'((?:zc|cc)*)'
UD = r'((?:az|aa)*)'
RZ = re.compile(ZD + '(zd|ad|ac|d|c|a)')
RWU = re.compile(WD + '(c|z|)' + UD)
RAD = re.compile('(ad|ac|zd)')
HEAL = {0: {'c': 'd'}, 1: {'z': 'c'}, 2: {'ac': 'ad'}}
CELLS = {'z': '00', 'a': '10', 'c': '01', 'd': '11'}


def kind(i):
    return 0 if i == 0 else (1 if i % 2 else 2)


def healthy(i):
    return ('d', 'c', 'ad')[kind(i)]


def parse(tok):
    """(words, separators) of a token string, separators[i] after word i (None after the last), or None."""
    m = RZ.match(tok)
    if not m:
        return None
    words, seps, pos = [bits(m.group(1), 'aa')], [m.group(2)], m.end()
    while True:
        m = RWU.match(tok, pos)
        if not m:
            return None
        words += [bits(m.group(1), 'cc'), bits(m.group(3), 'aa')]
        seps.append(m.group(2))
        pos = m.end()
        if pos >= len(tok):
            seps.append(None)
            return words, seps
        m = RAD.match(tok, pos)
        if not m:
            return None
        seps.append(m.group(1))
        pos = m.end()


def tape(words, seps):
    D = (('0010', '1010'), ('0001', '0101'), ('1000', '1010'))
    s = '0'
    for i, w in enumerate(words):
        s += ''.join(D[kind(i)][b] for b in w)
        if seps[i] is not None:
            s += ''.join(CELLS[t] for t in seps[i])
    return s


def step(words, seps):
    """The next event by the chain law and the defect law, or None when the law does not cover it."""
    w = [list(x) for x in words]
    sp = list(seps)
    carry = 1
    for i in range(len(w)):
        k = len(w[i])
        v = val(w[i]) + carry
        out = v >> k
        v &= (1 << k) - 1
        w[i] = [(v >> j) & 1 for j in range(k)]
        carry = 3 * out
        if carry == 0:
            return w, sp
        if sp[i] is None:
            return None
        if sp[i] != healthy(i):
            if sp[i] not in HEAL[kind(i)]:
                return None
            sp[i] = HEAL[kind(i)][sp[i]]
            carry -= 3
            if carry == 0:
                return w, sp
    return None


def first_defect(seps):
    for i, x in enumerate(seps):
        if x is not None and x != healthy(i):
            return i
    return None


def advance(words, seps, e):
    """The words e events on, if no carry reaches the first defect (or leaves the chain) before."""
    k = first_defect(seps)
    pre = words if k is None else words[:k + 1]
    d = decode(S_of(pre) + e * 3 ** (len(pre) - 1), [len(x) for x in pre])
    if d is None:
        return None
    return d + ([list(x) for x in words[k + 1:]] if k is not None else [])


def longest(words, seps):
    """The largest e such that advance(words, seps, e) is defined."""
    k = first_defect(seps)
    pre = words if k is None else words[:k + 1]
    j, _ = jump(pre)
    return j


def check(M, steps):
    s = Sim(ptab(M))
    total = 0
    prev = None
    tally = {}
    while total < steps:
        e, k = s.run_to_event(steps - total)
        total += k
        if e in (None, 'HALT'):
            break
        r = parse(e[2])
        if prev and r:
            p = step(*prev)
            crossing = p is not None and p[1] != prev[1]
            if p is None:
                key = 'not covered (a carry leaves the chain or meets an undecoded defect)'
            elif (p[0], p[1]) == (r[0], r[1]):
                key = 'by the law, crossing a defect' if crossing else 'by the law'
            else:
                key = 'MISMATCH'
            tally[key] = tally.get(key, 0) + 1
        prev = r
    print('%d steps of %s: %s' % (total, M, tally))


def run(M, digits, nspot):
    tr = ptab(M)
    rng = random.Random(1)
    s = Sim(tr)
    e, _ = s.run_to_event(10 ** 9)
    events = 1
    stats = {'jumps': 0, 'crossings by the defect law': 0, 'events run cell by cell': 0}
    checks = [0, 0]
    end = 'no halt'
    while len(str(events)) - 1 < digits:
        if e in ('HALT', None):
            end = 'HALT' if e == 'HALT' else 'stopped: no full event within 10^8 steps'
            break
        n, nw, tok = e
        r = parse(tok)
        if r is not None:
            words, seps = r
            while True:
                j = longest(words, seps)
                if j > 0:
                    for _ in range(nspot):
                        e0 = rng.randrange(0, j)
                        ww = advance(words, seps, e0)
                        ex = step(ww, seps)
                        if ex is None:
                            continue
                        t = Sim(tr, 1 << 18)
                        nn, nnw = add_n(n, nw, e0)
                        t.load(tape_left(nn, nnw), tape(ww, seps))
                        ee, _ = t.run_to_event(10 ** 7)
                        if ee is None:
                            continue  # one event longer than the budget: no verdict
                        rr = parse(ee[2]) if ee != 'HALT' else None
                        checks[0] += 1
                        if rr is None or (rr[0], rr[1]) != (ex[0], ex[1]) or (ee[0], ee[1]) != add_n(nn, nnw, 1):
                            checks[1] += 1
                    words = advance(words, seps, j)
                    n, nw = add_n(n, nw, j)
                    events += j
                    stats['jumps'] += 1
                st = step(words, seps)
                if st is None:
                    break
                if rng.random() < 0.2:
                    t = Sim(tr, 1 << 18)
                    t.load(tape_left(n, nw), tape(words, seps))
                    ee, _ = t.run_to_event(10 ** 7)
                    if ee is not None:
                        rr = parse(ee[2]) if ee != 'HALT' else None
                        checks[0] += 1
                        if rr is None or (rr[0], rr[1]) != (st[0], st[1]):
                            checks[1] += 1
                words, seps = st
                n, nw = add_n(n, nw, 1)
                events += 1
                stats['crossings by the defect law'] += 1
            s.load(tape_left(n, nw), tape(words, seps))
        else:
            p = parse_prefix(tok)  # not in the defect grammar: the chain law on the grammar prefix, tail kept
            if p is not None:
                j, w2 = jump(p[0])
                if j > 0:
                    n, nw = add_n(n, nw, j)
                    events += j
                    stats['jumps'] += 1
                    s.load(tape_left(n, nw), tape_right(w2) + p[1])
        e, _ = s.run_to_event(10 ** 8)
        events += 1
        stats['events run cell by cell'] += 1
        if stats['events run cell by cell'] % 100 == 0:
            print('about 10^%d events, %s, checks %s' % (len(str(events)) - 1, stats, checks))
            sys.stdout.flush()
    print('%s: about 10^%d events from blank tape (so at least that many steps), %s; %s; self-checks: %d events, '
          '%d mismatches' % (M, len(str(events)) - 1, end, stats, checks[0], checks[1]))


if __name__ == '__main__':
    M, mode = sys.argv[1], sys.argv[2]
    if mode == 'check':
        check(M, int(sys.argv[3]))
    else:
        run(M, int(sys.argv[3]), int(sys.argv[4]) if len(sys.argv) > 4 else 2)
