"""What the end of the wall does with a carry (an experiment on made-up walls, 24 November 2026).

In the run the carries have not yet passed digit 14 of the 46 (by 2*10^10 steps); at 3/8 per digit they reach the
end of the wall only after about 10^19 to 10^20 trips.  To see what the 139-cell end E does with a carry, this
script takes the real wall at step 3*10^9, sets digit 0 to 01110 and digits 1..45 to 11111 (for each of them carry
X gives 00001 and passes X on: so the first trip carries all the way through), runs the machine for one sweep, puts
the 46 digits back to the same values, and repeats.  The walls are made up (in the run the digits will not all
be 11111 when the carry arrives), so this shows what E does with a stream of X carries, not what the run does.

Seen (400 sweeps, no halt):
  * the first carry turns cell 0 of E from 0 to 1 and nothing else: E is more counter, in a form not used yet
    (its cells 0, 4, 8 count in binary like a b c of a digit: 1, then 0 1, then 1 1, ...);
  * at the 56th carry E is rewritten as a whole: it is 8 cells shorter, two more words 10001101 stand at the right
    end, and the right end of the tape moves 8 cells right (the far-end crossing far_B of lean/FarEnd.lean);
  * after that the sweeps go on with the longer tail, and E keeps counting.

usage: python3 endregion.py [SWEEPS]     (default 400, about a second)
"""
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import carry  # noqa: E402


def sweep(w, n=3):
    """One sweep of the machine from C>0 (01101)^n W; returns the new wall (it may be longer) or 'HALT'."""
    T = carry.tm_table()
    tape = collections.defaultdict(int)
    s = '0' + '01101' * n + w
    for i, c in enumerate(s):
        tape[i] = int(c)
    hi0 = len(s) - 1
    h, st, steps, lo, mx = 0, 2, 0, 0, hi0
    while True:
        a = T[(st, tape[h])]
        if a is None:
            return 'HALT', steps
        tape[h] = a[0]
        h += a[1]
        st = a[2]
        steps += 1
        lo, mx = min(lo, h), max(mx, h)
        if st == 2 and h == lo and steps > 10:
            L = len(w) + mx - hi0
            return ''.join(str(tape[k]) for k in range(mx - L + 1, mx + 1)), steps


def setdig(w, i, v):
    x = list(w)
    for k, j in enumerate(carry.FREE):
        x[44 + 25 * i + j] = v[k]
    return ''.join(x)


def short(s):
    return re.sub(r'(?:10001101){2,}', lambda m: f' (10001101)^{len(m.group()) // 8}', s)


def main(n):
    *_, (s, w) = carry.walls(3e9)
    E = w[1194:]
    print(f'E at the start: {short(E)}')
    for it in range(n):
        x = setdig(w[:1194] + E, 0, '01110')
        for i in range(1, 46):
            x = setdig(x, i, '11111')
        w2, steps = sweep(x)
        if w2 == 'HALT':
            print(f'carry {it + 1}: HALT after {steps} steps')
            return 1
        E2 = w2[1194:]
        grow = len(E2) - len(E)
        if it < 8 or grow or it + 1 == n:
            diff = ''.join('.' if a == b else b for a, b in zip(E, E2)) if not grow else short(E2)
            print(f'carry {it + 1:3d}: {steps:6d} steps' + (f', right end +{grow} cells: ' if grow else ', E: ')
                  + diff[:150])
        E = E2
    print(f'{n} carries, no halt')
    return 0


if __name__ == '__main__':
    sys.exit(main(int(float(sys.argv[1])) if len(sys.argv) > 1 else 400))
