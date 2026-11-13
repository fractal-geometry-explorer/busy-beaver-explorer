#!/usr/bin/env python3
"""What happens at the end of the regime of bmap.py (P_14, near 2.6e18 steps), seen on reduced configurations.

The law of bmap.py is right-anchored: how much a segment loses per event depends only on the number of segments to
its right.  So the right end of the real P_13 is the right end of a configuration with only the m oldest segments
y_13(m-1), ..., y_13(0) and the generator segment g = 2*3^(m+4) - 28 that goes with m segments (this is itself P_n of
a shorter history).  This script builds that configuration (as cells), runs the macro simulator c/msim.c from it, and
prints the list at each new cell on the right.  Comparing m = 3, 4, 5 shows which part of the result depends on m
(the young, left part) and which does not (the right end).

usage: python3 bcollapse.py [b1|b2] [m] [steps]      (default b1 5 1e14)
"""
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bmap import MACH, build
from m2runs import convert, fmt


def config(c0, m, n=13):
    g = 2 * 3 ** (m + 4) - 28
    ys = [3 ** (j + 2) * (17 - n + j) - 27 for j in range(m - 1, -1, -1)]
    runs = [2, *[3] * 16, 5, 3, 5, *[3] * g]
    for y in ys:
        runs += [5] + [3] * y
    runs += [5] + [3] * (c0 - 2 * n) + [1]
    cells = '0' * 8 + '0'.join('1' * r for r in runs)
    return 'D %d %s0\n' % (len(cells), cells), g, ys, c0 - 2 * n


if __name__ == '__main__':
    name = sys.argv[1] if len(sys.argv) > 1 else 'b1'
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    steps = sys.argv[3] if len(sys.argv) > 3 else '1e14'
    mach, c0 = MACH[name]
    text, g, ys, c = config(c0, m)
    print(f'{name}, reduced P_13 with m = {m}: [{g}, {", ".join(map(str, ys))}, {c}]')
    cfg = os.path.join(tempfile.gettempdir(), f'g01_{name}_{m}.cfg')
    open(cfg, 'w').write(text)
    out = subprocess.run([build('msim'), mach, '4', steps, cfg, '1'], capture_output=True, text=True, check=True).stdout
    last = None
    for line in out.split('\n'):
        f = line.split()
        if len(f) < 3 or '|' not in f:
            continue
        i = f.index('|')
        toks = f[2:i] + f[i + 1:]
        while toks and set(toks[0].split('^')[0]) == {'0'}: toks.pop(0)
        while toks and set(toks[-1].split('^')[0]) == {'0'}: toks.pop()
        s = fmt(convert(toks))
        if f[0] == 'HALT':
            print('HALT', s); break
        body = ' '.join(t for t in s.split() if t.startswith('3') or t == '5' or t.startswith('5'))
        if body != last:
            print(f[0], s[:200])
            last = body
