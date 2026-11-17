"""Check a pclosure_list.py search output against a plain cell-by-cell simulator and plain regular expressions.

For every leaf that runs to a node (or halts), at x = 0 and at a few random values of its variables:
  1. write out the class with the leaf's start counts, run the plain machine from the event state at the left end
     until the next event, and compare the tape cell by cell with the node the leaf predicts;
  2. check, with a regular expression made from each class ((w){lo,} for a repeat), that the predicted node's cells
     are in the language of some class of the set (the cover check, done without the matcher).

usage: BBM=... BBEV=... BBMIRROR=... python3 vlist.py OUT.json [POINTS] [MAXSTEPS]
"""
import json
import os
import random
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paccel_inner as A  # noqa: E402
from vinner import parse_form, ev, run  # noqa: E402


def class_cells(items, counts):
    out, it = [], iter(counts)
    for t in items:
        if isinstance(t, int):
            out.append(t)
        else:
            out.extend(t[0] * next(it))
    return out


def node_cells(nodej, x):
    out = []
    for t in nodej:
        if isinstance(t, int):
            out.append(t)
        else:
            k, c = t[1]
            out.extend(t[0] * (k + sum(a * x.get(int(v), 0) for v, a in c.items())))
    return out


def regex(items):
    r = ''
    for t in items:
        if isinstance(t, int):
            r += str(t)
        else:
            r += '(?:%s){%d,}' % (''.join(map(str, t[0])), t[1])
    return re.compile(r + '0*$')


def main():
    data = json.load(open(sys.argv[1]))
    npts = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    maxsteps = int(float(sys.argv[3])) if len(sys.argv) > 3 else 10 ** 7
    random.seed(1)
    regs = [regex(c['items']) for c in data['classes']]
    ok = bad = skip = uncov = 0
    for c in data['classes']:
        for lf in c['leaves']:
            if lf['kind'] not in ('node', 'halt'):
                continue
            start = [parse_form(s) for s in lf['start']]
            vs = sorted({v for f in start for v in f[1]})
            pts = [{v: 0 for v in vs}] + [{v: random.randint(0, 12) for v in vs} for _ in range(npts - 1)]
            for x in pts:
                r = run(class_cells(c['items'], [ev(f, x) for f in start]), maxsteps)
                if r is None:
                    skip += 1
                    continue
                if lf['kind'] == 'halt':
                    good = r[0] == 'halt'
                else:
                    want = node_cells(lf['nodej'], x)
                    got = r[1] if r[0] == 'node' else None
                    while got and got[-1] == 0:
                        got.pop()
                    while want and want[-1] == 0:
                        want.pop()
                    good = got == want
                    s = ''.join(map(str, want))
                    if not any(g.match(s) for g in regs):
                        uncov += 1
                        print('UNCOVERED', c['key'], lf['node'], x)
                if good:
                    ok += 1
                else:
                    bad += 1
                    print('MISMATCH', c['key'], lf['start'], x, lf.get('node'), r[0])
    print('checked %d, mismatches %d, uncovered %d, too long %d' % (ok + bad, bad, uncov, skip))


if __name__ == '__main__':
    main()
