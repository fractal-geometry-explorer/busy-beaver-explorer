"""Right turns of 1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF in the 2-cell letters of lean/Wall.lean.

A right turn is E reading 1 and stepping left, just after a right move.  Left of the head we read 2-cell letters
outwards: a = 11, b = 01 (nearest cell first), and o = a lone 1 that shifts the letter grid by one cell.  Right of the
head (starting at the head) the letters are a = 11, c = 01, and o.

Checks, for the first N steps (default 2*10^7; the README quotes 2*10^8):
  1. every right turn is  [o] Z [o Z]  |E on a|  Z' [o]   with Z in {a,b}*, Z' in {a,c}*: the zone has at most one
     interior o (the leading o is the prefix p = 1 of Wall.lean), the frozen side at most one trailing o; or, at the
     start of some crossings, E on a lone 1 at the right end of the tape;
  2. at every right turn with no interior o (Wall.lean's `Turn w p s R`), `nxt w p s` either predicts the next such
     turn exactly, with the same R, or is `none` (the sweep runs into R); `none` starts a crossing;
  3. the start of a crossing does not decide its outcome: for zone words W of up to 12 letters, the turn the machine
     reaches from <zl2 W (pre p), R, F or E> (R blank or a single 1) is not determined by any number j <= 8 of letters
     of W next to the head.

Usage: python3 turnshape.py [N]
"""
import re
import sys
import itertools
from collections import Counter

T = {('A', 0): (1, 1, 'B'), ('A', 1): (0, 1, 'E'), ('B', 0): (0, 1, 'C'), ('B', 1): None,
     ('C', 0): (1, -1, 'D'), ('C', 1): (1, -1, 'E'), ('D', 0): (1, -1, 'E'), ('D', 1): (1, -1, 'D'),
     ('E', 0): (1, 1, 'F'), ('E', 1): (0, -1, 'C'), ('F', 0): (1, 1, 'A'), ('F', 1): (1, 1, 'F')}


def tok_left(tape, h, lo):
    out, i = '', h - 1
    while True:
        c = (tape.get(i, 0), tape.get(i - 1, 0))
        if c == (1, 1): out += 'a'; i -= 2
        elif c == (0, 1): out += 'b'; i -= 2
        elif c == (1, 0): out += 'o'; i -= 1
        else:
            if any(tape.get(j, 0) for j in range(lo, i + 1)): out += '?'
            return out[::-1]          # far to near


def tok_right(tape, i, hi):
    out = ''
    while True:
        c = (tape.get(i, 0), tape.get(i + 1, 0))
        if c == (1, 1): out += 'a'; i += 2
        elif c == (0, 1): out += 'c'; i += 2
        elif c == (1, 0): out += 'o'; i += 1
        else:
            if any(tape.get(j, 0) for j in range(i, hi + 2)): out += '?'
            return out                # near to far


# Wall.lean on lists (letters: False = a, True = b or c; words nearest the head first)
def sx(q, ws):
    out = []
    for a in ws:
        q ^= a; out.append(q)
    return out


def par(q, ws):
    for a in ws: q ^= a
    return q


def rswL(e, W, xs):
    W = list(W)
    for i, x in enumerate(xs):
        if e and not x: return W, e, xs[i + 1:]
        e ^= x; W = [e] + W
    return W, e, None


def nxt(w, p, s):
    W, e, r = rswL(0, [0], list(reversed(sx(1, w))) + [1] + list(s))
    return None if r is None else (tuple(W), p ^ par(1, w), tuple(r))


LEFT = re.compile(r'^o?[ab]*(o[ab]*)?$')
RIGHT = re.compile(r'^(a[ac]*o?|o)$')


def check_run(N):
    tape, h, st, lo, hi, mv = {}, 0, 'A', 0, 0, 0
    shapes, bad = Counter(), 0
    prev, stats = None, Counter()
    for t in range(N):
        a = T[(st, tape.get(h, 0))]
        if a is None:
            print('halt at', t); return
        if st == 'E' and mv == 1 and a[1] == -1:
            L, R = tok_left(tape, h, lo), tok_right(tape, h, hi)
            ok = LEFT.match(L) and RIGHT.match(R)
            if not ok: bad += 1
            inner = 'o' in L[1:]
            cur = None
            if R == 'o':
                shapes[('E on the last cell, a lone 1',)] += 1
            else:
                shapes[('interior o' if inner else 'no interior o', 'trailing o' if R.endswith('o') else 'no trailing o')] += 1
                if not inner:
                    p = 1 if L.startswith('o') else 0
                    w = tuple(x == 'b' for x in reversed(L.lstrip('o')))
                    s = tuple(x == 'c' for x in R[1:].rstrip('o'))
                    cur = (w, p, s, R.endswith('o'))
            if prev is not None:
                if prev[4] is None: stats['nxt = none (a crossing starts)'] += 1
                elif cur is not None and prev[4] == cur[:3] and prev[3] == cur[3]: stats['nxt exact'] += 1
                else: stats['nxt wrong'] += 1
            prev = None if cur is None else cur + (nxt(*cur[:3]),)
        tape[h] = a[0]; h += a[1]; mv = a[1]; st = a[2]; lo = min(lo, h); hi = max(hi, h)
    print(f'{N} steps: {sum(shapes.values())} right turns, {bad} outside the shape')
    for k, v in sorted(shapes.items()): print('  ', k, v)
    print('  turns with no interior o, compared with the next right turn:', dict(stats))


def end_event(W, p, e, r, maxs=10 ** 5):
    tape, i = {}, -1
    for x in W:
        tape[i], tape[i - 1] = (0, 1) if x else (1, 1); i -= 2
    if p: tape[i] = 1
    if r: tape[0] = 1
    h, st, mv, lo, hi = 0, 'E' if e else 'F', 0, min(tape, default=0), 0
    for t in range(maxs):
        a = T[(st, tape.get(h, 0))]
        if a is None: return 'halt'
        if st == 'E' and mv == 1 and a[1] == -1 and t > 0:
            return tok_left(tape, h, lo) + '|' + tok_right(tape, h, hi)
        tape[h] = a[0]; h += a[1]; mv = a[1]; st = a[2]; lo = min(lo, h); hi = max(hi, h)
    return 'timeout'


def check_locality(n=12):
    out = {}
    for m in range(n + 1):
        for W in itertools.product([0, 1], repeat=m):
            for p, e, r in itertools.product([0, 1], repeat=3):
                o = end_event(W, p, e, r)
                ok = '|' in o and LEFT.match(o.split('|')[0]) and RIGHT.match(o.split('|')[1])
                out[(W, p, e, r)] = 'shape' if ok else o if o in ('halt', 'timeout') else 'other'
    print('crossing starts, W up to', n, 'letters:', dict(Counter(out.values())))
    for j in range(9):
        cls = {}
        for (W, p, e, r), k in out.items():
            if len(W) >= j: cls.setdefault((W[:j], e, r), set()).add(k)
        print(f'   {j} letters next to the head: {sum(len(v) > 1 for v in cls.values())} of {len(cls)} classes undecided')


if __name__ == '__main__':
    check_run(int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 * 10 ** 7)
    check_locality()
