"""Iterate the exact round map (roundmap.nxt) from the first left-end tape of the blank-tape run, [0, 0, 2] at
step 50, and optionally compare with the left-end tapes printed by run.py (which skips single-block tapes).

usage: python3 orbit.py ROUNDS [rounds.txt]          python3 orbit.py test [N]   (random lists against direct.py)
"""
import os, random, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from roundmap import nxt, closed, _cache
from direct import rnd


def load(fn):
    """The left-end tapes of run.py's output as lists of blocks."""
    rows = []
    for line in open(fn):
        p = line.split()
        if len(p) < 3 or p[1] != 'E' or p[2] != '1':
            continue
        blocks, buf, ok = [0], '', True
        for t in p[3:] + ['$']:
            if t in ('0', '1'):
                buf += t
                continue
            while buf and ok:
                if buf.startswith('01'):
                    blocks[-1] += 1; buf = buf[2:]
                elif buf.startswith('110'):
                    blocks.append(0); buf = buf[3:]
                else:
                    ok = False
            if t == 'a':
                blocks[-1] += 1
            elif t.startswith('a^'):
                blocks[-1] += int(t[2:])
            elif t != '$':
                ok = False
        if ok:
            rows.append(blocks)
    return rows


def test(n):
    random.seed(5)
    bad = ncl = 0
    for _ in range(n):
        bl = [random.choice([random.randint(0, 8), random.randint(0, 70)]) for _ in range(random.randint(1, 6))]
        v = rnd(bl, 10 ** 8)[0]
        try:
            m = nxt(bl)
        except ValueError:
            m = None
        if (m != v) if (isinstance(v, list) or v == 'halt') else (m is not None):
            bad += 1; print('BAD', bl, v, m)
        c = closed(bl)
        if c is not None:
            ncl += 1
            if c != v:
                bad += 1; print('BAD closed', bl, v, c)
    print(n, 'random lists,', ncl, 'in the closed-form domain,', bad, 'mismatches')


def main():
    if sys.argv[1] == 'test':
        return test(int(sys.argv[2]) if len(sys.argv) > 2 else 2000)
    n = int(sys.argv[1])
    ref, ri = None, 0
    if len(sys.argv) > 2:
        ref = load(sys.argv[2])
        ri = ref.index([0, 0, 2])
    bl = [0, 0, 2]
    t0 = time.time()
    ncl = matched = maxlen = single = 0
    for i in range(n):
        if ref is not None and ri < len(ref) and len(bl) > 1:
            assert ref[ri] == bl, (i, ref[ri], bl)
            ri += 1; matched += 1
        maxlen = max(maxlen, len(bl))
        single += len(bl) == 1
        c = closed(bl)
        r = nxt(bl)
        if r == 'halt':
            print('HALT in round', i, bl[:3]); return
        if c is not None:
            ncl += 1
            assert c == r
        bl = r
        if i % max(1, n // 10) == 0:
            print(i, 'blocks', len(bl), 'bits of x0', bl[0].bit_length(), 'bits of total', sum(bl).bit_length(),
                  round(time.time() - t0, 1), flush=True)
    print('rounds', n, 'no halt; closed-form rounds', ncl, 'single-block rounds', single, 'max blocks', maxlen,
          'cut-down tapes', len(_cache), 'matched run.py tapes', matched, 'bits of total', sum(bl).bit_length())


main()
