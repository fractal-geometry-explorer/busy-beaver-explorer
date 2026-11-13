"""The digits of the wall of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE.

At each visit of the head, in state C, to the left end of the tape where the tape is C>0 (01101)^n W with W of
exactly 1,573 cells (once per sweep, from step 2*10^7 on), cut W after its first 44 cells into 25-cell digits.
The script checks, on every sweep of the run:

  * every one of the first 40 digits has the form  x110 x110 x011 0011 0x11 0x11 0  (x free): five free cells
    a b c d e at cells 0, 4, 8, 17 and 21 of the digit;
  * the first k digits, taken together, come back to the same contents after exactly 8^k sweeps (k = 1, 2, 3),
    and take 8^k different values;
  * how deep the changes of one sweep reach.

It prints the first digits of the first sweeps and the three checks.  Observations of one run, not proofs.

usage: python3 digits.py [STEPS]   (default 3e8: 2,819 sweeps, a few seconds)
"""
import os
import subprocess
import sys
import tempfile
from collections import Counter

M = '1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE'
HERE = os.path.dirname(os.path.abspath(__file__))
FREE = (0, 4, 8, 17, 21)
SKEL = 'x110x110x01100110x110x110'


def walls(steps):
    exe = os.path.join(tempfile.gettempdir(), 'walldump_m6')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '../c/walldump.c')], check=True)
    out = subprocess.run([exe, M, str(int(steps)), 'C', '01101', '1573', '1000000000', '20000000'],
                         stdout=subprocess.PIPE, text=True).stdout
    return [line.split() for line in out.splitlines()]


def digits(w, count=40):
    return [w[44 + 25 * i:69 + 25 * i] for i in range(count)]


def main(steps):
    ws = walls(steps)
    D = [digits(w) for _, w in ws]
    skel = Counter(''.join('x' if j in FREE else r[j] for j in range(25)) for d in D for r in d)
    bits = [[''.join(r[j] for j in FREE) for r in d] for d in D]
    print(f'{len(ws)} sweeps from step {ws[0][0]} to step {ws[-1][0]}')
    print('forms of the first 40 digits:', dict(skel))
    ok = set(skel) == {SKEL}
    for row in bits[:10]:
        print('  ', ' '.join(row[:6]))
    for k in (1, 2, 3):
        seq = [tuple(b[:k]) for b in bits]
        per = 8 ** k
        periodic = all(seq[t] == seq[t + per] for t in range(len(seq) - per))
        distinct = len(set(seq[:per]))
        print(f'first {k} digit(s): period {per} holds for all {len(seq) - per} pairs: {periodic}; '
              f'{distinct} different values in one period')
        ok = ok and periodic and distinct == per
    deep = Counter()
    for a, b in zip(ws, ws[1:]):
        d = [j for j in range(1573) if a[1][j] != b[1][j]]
        deep[(d[-1] - 44) // 25 if d else -1] += 1
    print('deepest digit changed by a sweep -> number of sweeps:', dict(sorted(deep.items())))
    print('ALL CHECKS PASS' if ok else 'A CHECK FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(float(sys.argv[1]) if len(sys.argv) > 1 else 3e8))
