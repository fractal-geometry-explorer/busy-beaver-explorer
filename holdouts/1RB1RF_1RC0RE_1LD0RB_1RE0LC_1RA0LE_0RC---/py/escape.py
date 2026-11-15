"""Tapes of the block form that halt: 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---.

The run from blank tape keeps the form "blocks a^k (a = 01) separated by b = 00110, single cursor cells 0 or 1".
This searches small tapes that contain a cursor stopped half way across a separator (`0 a 1 1 a b`) followed by a
second cursor, and prints the one that halts soonest, visit by visit.  The last tape before the halt is the one of
lean/Escape.lean.

usage: python3 escape.py            # about 20 s
       python3 escape.py "1 a b a^5 0 a^3 b a^6 0" 5     # the visits of the right end from any tape of the form
"""
import itertools
import sys

M = "1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---"
T = {}
for i, row in enumerate(M.split('_')):
    for s in range(2):
        t = row[3 * s:3 * s + 3]
        T[(i, s)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
WORDS = {'a': '01', 'b': '00110'}


def expand(s):
    """'1 a b a^2 0' -> cells"""
    out = ''
    for t in s.split():
        w, n = (t.split('^') + ['1'])[:2]
        out += WORDS.get(w, w) * int(n)
    return out


def show(cells):
    out = []; i = 0
    while i < len(cells):
        for name in ('b', 'a'):
            w = WORDS[name]
            if cells.startswith(w, i):
                if out and out[-1][0] == name: out[-1][1] += 1
                else: out.append([name, 1])
                i += len(w); break
        else:
            if out and out[-1][0] == cells[i]: out[-1][1] += 1
            else: out.append([cells[i], 1])
            i += 1
    return ' '.join(n + ('^%d' % c if c > 1 else '') for n, c in out)


def visit(cells, maxs=10 ** 7):
    """cells: the tape (blank beyond), head in state B on the blank cell right of it.  Runs to the next time state B
    steps onto a new cell at the right end; returns the new tape, or ('HALT', steps)."""
    pad = len(cells) + 50
    tape = [0] * pad + [int(c) for c in cells] + [0] * 8
    pos = pad + len(cells); hi = pos; s = 1; n = 0; lo = pad
    while True:
        tr = T[(s, tape[pos])]
        if tr is None: return ('HALT', n)
        tape[pos] = tr[0]; pos += tr[1]; s = tr[2]; n += 1
        lo = min(lo, pos)
        if pos > hi:
            if s == 1: return ''.join(map(str, tape[lo:pos]))
            hi = pos
            if hi >= len(tape) - 1: tape += [0] * 8
        if n > maxs: return ('LONG', n)


def run(start, nmax):
    w = expand(start); hist = [w]
    for _ in range(nmax):
        w = visit(w)
        if not isinstance(w, str): return hist, w
        hist.append(w)
    return hist, None


if __name__ == "__main__":
    if len(sys.argv) > 1:
        hist, end = run(sys.argv[1], int(sys.argv[2]))
        for h in hist: print(show(h))
        if end: print(end[0], 'after', end[1], 'more steps')
        sys.exit()
    best = None; nhalt = ntot = 0
    for p, x, y, z in itertools.product(range(1, 5), range(0, 7), range(0, 9), range(0, 9)):
        for cur in '01':
            for form in ("1 a b a^%d 0 a 1 1 a b a^%d %s a^%d 0", "1 a b a^%d 0 a 1 1 a b a^%d %s a^%d b a^%d 0"):
                if form.count('%') == 4 and z: continue
                s = form % ((p, x, cur, y) if form.count('%') == 4 else (p, x, cur, y, z))
                hist, end = run(s, 60); ntot += 1
                if end and end[0] == 'HALT':
                    nhalt += 1
                    if best is None or (len(hist), len(hist[0])) < (len(best[1]), len(best[1][0])): best = (s, hist, end)
    print('%d of %d tapes halt within 60 visits; the soonest:' % (nhalt, ntot))
    s, hist, end = best
    for h in hist: print('  ', show(h))
    print('   HALT after', end[1], 'more steps')
