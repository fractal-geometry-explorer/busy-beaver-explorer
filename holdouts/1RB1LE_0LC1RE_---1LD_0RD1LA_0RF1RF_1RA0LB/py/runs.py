"""Prints the tape at every EVERY-th visit of the right end (A on the blank right of the tape) as the lengths of its
runs of 1s (single 0s between runs dropped, 9*k = k runs of length 9), using the exact simulator blocksim.py.

usage: python3 runs.py SECONDS EVERY [TAIL]
"""
import os, re, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from blocksim import BlockSim
from bbtools.symtm import Halted
M = "1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB"
W = "1111111010"


def group(r):
    out, prev, cnt = [], None, 0
    for x in r + [None]:
        if x == prev:
            cnt += 1; continue
        if prev is not None:
            out.append(prev if cnt == 1 else '%s*%d' % (prev, cnt))
        prev, cnt = x, 1
    return out


secs, every = float(sys.argv[1]), int(sys.argv[2])
tail = int(sys.argv[3]) if len(sys.argv) > 3 else 0
b = BlockSim(M, W, 'A', 'R'); T = time.time(); n = 0
while time.time() - T < secs:
    try:
        b.next_visit()
    except Halted as e:
        print('HALT', e, b.steps); break
    n += 1
    if n % every == 0:
        items = b.norm.merge(b.norm.flatten(b.cfg.left[1:] + b.cfg.right[:-1]))
        s = ''.join(x if isinstance(x, str) else W * x for x in items)
        toks = [str(len(g)) if g[0] == '1' else '.' * (len(g) - 1) for g in re.findall(r'1+|0+', s)]
        out = ' '.join(group([t for t in toks if t]))
        print(n, b.steps, len(s), out[-tail:] if tail else out, flush=True)
print('visits', n, 'steps', b.steps)
