#!/usr/bin/env python3
"""Bit model of 1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA, and its check against the machine.

At a left-end turn (state D on the leftmost visited cell, about to step right) the tape is  w0 1 w1 1 ... wm 1  with
w0 = 0: every second cell is 1 and the others spell a bit word w.  One round trip maps w to

    g(w) + [1, 0]      if the pass ends in state P
    g(w) + [1, 1, 0]   if the pass ends in state Y
    HALT               if the pass ends in state X or Q

where g keeps w0 and reads w1, w2, ... with a 4-state automaton started in X:

    state  read 0        read 1        mode
    X      write 1, P    write 0, X    invert
    P      write 1, X    write 0, Y    invert
    Y      write 0, X    write 1, Q    copy
    Q      write 0, Y    write 1, Y    copy

Equivalently, parse w1 w2 ... into tokens.  Invert mode: 1 -> 0, 00 -> 11, 01 -> 10 and switch to copy mode.
Copy mode: 10 -> 10, 11 -> 11, 0 -> 0 and switch to invert mode.  X and Y are token boundaries, P and Q are inside
a token.

This script checks the model, it proves nothing:
  python3 bitmodel.py run STEPS      follow the machine from blank tape and compare every lap with the model
  python3 bitmodel.py random N       N random words: one machine lap from the word against the model
  python3 bitmodel.py start          print the bit word at lap 3 (input for c/model.c)
"""
import random, sys

MACHINE = '1RB0RE_1RC1RE_1LD1LC_0RB0LC_1RF0RB_---1RA'
DELTA = {'X': 'PX', 'P': 'XY', 'Y': 'XQ', 'Q': 'YY'}
INVERT = {'X': 1, 'P': 1, 'Y': 0, 'Q': 0}

def table():
    T = {}
    for s, part in enumerate(MACHINE.split('_')):
        for b in (0, 1):
            t = part[3*b:3*b+3]
            T[(s, b)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T

def model(w):
    """One lap of the model.  Returns the new word, or None for a halt."""
    s = 'X'; out = [w[0]]
    for b in w[1:]:
        out.append(b ^ INVERT[s]); s = DELTA[s][b]
    if s == 'P': return out + [1, 0]
    if s == 'Y': return out + [1, 1, 0]
    return None

def lap(T, cells, q):
    """One machine lap: cells[0] is the leftmost visited cell, head on it in state q, about to step right.
    Ends the next time the head is on the leftmost visited cell and about to step right, after reaching the right end.
    Returns (cells, state, steps) or None on a halt."""
    tape = dict(enumerate(cells)); p = 0; lo = 0; hi = len(cells) - 1; far = hi; s = q; n = 0; reached = False
    while True:
        tr = T[(s, tape.get(p, 0))]
        if tr is None: return None
        if p == lo and tr[1] == 1 and n > 0 and reached: break
        tape[p] = tr[0]; p += tr[1]; s = tr[2]; n += 1
        lo = min(lo, p); hi = max(hi, p)
        if p >= far: reached = True
    return [tape.get(i, 0) for i in range(lo, hi + 1)], s, n

def first(T):
    tape = {}; p = lo = hi = 0; s = 0; n = 0
    while True:
        tr = T[(s, tape.get(p, 0))]
        if p == lo and tr[1] == 1: break
        tape[p] = tr[0]; p += tr[1]; s = tr[2]; n += 1; lo = min(lo, p); hi = max(hi, p)
    return [tape.get(i, 0) for i in range(lo, hi + 1)], s, n

def word(cells):
    return cells[0::2] if len(cells) % 2 == 0 and all(x == 1 for x in cells[1::2]) else None

def cells_of(w):
    return [x for b in w for x in (b, 1)]

def main():
    T = table(); cmd = sys.argv[1] if len(sys.argv) > 1 else 'run'
    if cmd in ('run', 'start'):
        limit = int(sys.argv[2]) if len(sys.argv) > 2 else 3000000
        cells, q, steps = first(T); n = 0; good_from = None
        while steps < limit:
            n += 1; old = word(cells) if q == 3 else None
            r = lap(T, cells, q)
            if r is None: print('machine halts in lap', n); return
            cells, q, st = r
            ok = old is not None and q == 3 and model(old) == word(cells)
            if ok and good_from is None:
                good_from = n
                if cmd == 'start': print(''.join(map(str, old))); return
            if not ok: good_from = None
            steps += st
        print('laps followed: %d (%d steps); model exact from lap %s on' % (n, steps, good_from))
    elif cmd == 'random':
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
        random.seed(7); bad = 0; halts = 0
        for _ in range(N):
            w = [0] + [random.randrange(2) for _ in range(random.randrange(3, 40))]
            want = model(w); r = lap(T, cells_of(w), 3)
            if want is None:
                halts += 1; bad += r is not None
            else:
                bad += r is None or r[1] != 3 or word(r[0]) != want
        print('%d random words, %d disagreements (%d of the words halt, in both)' % (N, bad, halts))

if __name__ == '__main__':
    main()
