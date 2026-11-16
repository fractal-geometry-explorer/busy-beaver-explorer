"""Check the leaves of a pclosure_inner.py search against a plain cell-by-cell simulator (no shift rules, no cycle
rules, no symbolic counts).

For every leaf that runs to a node (or halts), at x = 0 and at a few random values of its variables: write out the
start tape, run the plain machine from the event state at the left end until the next event (the event state arriving
at the left end of the visited tape) and compare the tape, cell by cell, with the node the leaf predicts.

usage: BBM=... BBEV=... BBMIRROR=... [BBBIG=...] python3 vinner.py OUT.json [POINTS] [MAXSTEPS]
"""
import json
import os
import random
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paccel_inner as A  # noqa: E402

T = A.T
EV = A.EVSTATE


def parse_form(s):
    k, c = 0, {}
    for part in s.split('+'):
        if '*x' in part:
            a, v = part.split('*x')
            c[int(v)] = int(a)
        else:
            k = int(part)
    return k, c


def ev(form, x):
    k, c = form
    return k + sum(a * x.get(v, 0) for v, a in c.items())


def cells(text, counts):
    out, it = [], iter(counts)
    for part in text.split():
        if part.startswith('('):
            out.extend(int(ch) for ch in part[1:part.index(')')] * next(it))
        else:
            out.extend(int(ch) for ch in part)
    return out


def run(tape, maxsteps):
    """Plain run from state EV on cell 0 (nothing to the left).  Returns ('node', cells from the head) or ('halt',)
    or None (no event within maxsteps)."""
    t = dict(enumerate(tape))
    p, st, lo = 0, EV, 0
    for _ in range(maxsteps):
        tr = T[(st, t.get(p, 0))]
        if tr is None:
            return ('halt',)
        w, m, st = tr
        t[p] = w
        p += m
        if m == -1 and st == EV and p <= lo:
            lo = p
            hi = max(k for k, v in t.items() if v) if any(t.values()) else p
            return ('node', [t.get(i, 0) for i in range(p, hi + 1)])
    return None


def main():
    data = json.load(open(sys.argv[1]))
    npts = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    maxsteps = int(float(sys.argv[3])) if len(sys.argv) > 3 else 10 ** 7
    random.seed(1)
    ok = bad = skip = 0
    for text, res, leaves in data['classes']:
        for lf in leaves:
            if lf['kind'] not in ('node', 'halt'):
                continue
            start = [parse_form(s) for s in lf['start']]
            vs = sorted({v for f in start for v in f[1]})
            pts = [{v: 0 for v in vs}] + [{v: random.randint(0, 12) for v in vs} for _ in range(npts - 1)]
            for x in pts:
                r = run(cells(text, [ev(f, x) for f in start]), maxsteps)
                if r is None:
                    skip += 1
                    continue
                if lf['kind'] == 'halt':
                    good = r[0] == 'halt'
                else:
                    want = cells(lf['to'], [ev(parse_form(c), x) for c in lf['counts']])
                    got = r[1] if r[0] == 'node' else None
                    while got and got[-1] == 0:
                        got.pop()
                    while want and want[-1] == 0:
                        want.pop()
                    good = got == want
                if good:
                    ok += 1
                else:
                    bad += 1
                    print('MISMATCH', text, lf['start'], x, lf.get('to'), lf.get('counts'), r[0])
    print('checked %d, mismatches %d, too long %d' % (ok + bad, bad, skip))


if __name__ == '__main__':
    main()
