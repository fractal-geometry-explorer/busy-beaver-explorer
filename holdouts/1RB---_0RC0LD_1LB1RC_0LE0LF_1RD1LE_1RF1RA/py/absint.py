"""An abstract model of the block map of 1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA: does it close without a critical frame?

Values are exact below T, or "at least k" (k <= T).  A block list is pre ++ mid ++ suf: `pre` (up to K blocks next to
the head) and `suf` (up to K2 blocks at the far end) are kept exactly, and `mid` stands for any number of blocks of at
least some bound.  A zigzag on a block of at least T cells is taken in one step (as `zig` of lean/Series.lean), with
lower bounds for what it adds to its neighbours.  The successor function over-approximates `next` of
lean/Blocks.lean.  Starting from a real frame (abstracted), a breadth-first search either closes (an invariant: no
critical frame is ever reached) or finds an abstract path to a critical frame, which it prints.

With T = 30 and K = K2 = 8, started from the frames 2·10^6 and 10^8 of the run, it finds a path in under a second: a block of "at least k"
cells at the right end becomes an exact small value, and a few small blocks next to each other then sweep into the
critical frame.  The real run never has small blocks next to each other away from the left end, but the
model cannot see why: what keeps the blocks large is how large they are, not a finite pattern.

usage: python3 py/absint.py T K K2 START_FILE [TRACE_LINES]
  START_FILE: three lines, the state letter, the left list and the right list (nearest block first), e.g. from
  `python3 py/blockmap.py show` or a C dump of the run.
"""
import sys, collections
T = int(sys.argv[1]); K = int(sys.argv[2]); K2 = int(sys.argv[3])
MIDMIN = 4
ZIG = 1
def g(k): return ('G', min(k, T))
def isg(v): return isinstance(v, tuple)
def norm(v): return g(v) if (not isg(v) and v >= T) else v
def lo(v): return v[1] if isg(v) else v
def add(v, c): return g(v[1] + c) if isg(v) else norm(v + c)
def split(v, cut):
    """refine abstract v into exact values < cut and G(>=cut) part."""
    if not isg(v): return [v]
    k = v[1]
    if k >= cut: return [v]
    return list(range(k, cut)) + [g(cut)]
def sub(v, c):
    if isg(v):
        assert v[1] >= c, (v, c)
        return g(v[1] - c)
    assert v >= c; return v - c

class Overflow(Exception): pass

def pop(l):
    pre, mid, suf = l
    if pre: return [(pre[0], (pre[1:], mid, suf))]
    # mid may be exhausted
    out = []
    if mid is not None: out.append((g(mid), ((), mid, suf)))
    if suf: out.append((suf[0], ((), None, suf[1:])))
    else: out.append((0, ((), None, ())))
    return out

def push(x, l):
    pre, mid, suf = l
    pre = (x,) + pre
    if len(pre) > K:
        last = pre[-1]; pre = pre[:-1]
        if mid is None and len(suf) < K2: suf = (last,) + suf
        else:
            b = lo(last)
            if b < MIDMIN: raise Overflow((x, l))
            mid = b if mid is None else min(mid, b)
    return (pre, mid, suf)

def pushes(xs, l):
    for x in reversed(xs): l = push(x, l)
    return l

def popsplit(l, cut):
    out = []
    for v, l1 in pop(l):
        for w in split(v, cut): out.append((w, l1))
    return out

def succ(f):
    q, L, R = f
    out = []
    if q == 'E':
        for i, L1 in pop(L):
            for m, R1 in popsplit(R, T if ZIG else 3):
                if isg(m) and ZIG:
                    # m >= k >= 8 ; check next block is 0
                    for z, R2 in pop(R1):
                        if z == 0:
                            for j, R3 in pop(R2):
                                k = m[1]
                                for r in (2, 3, 4):
                                    t0 = max(1, -(-(k - r) // 3))
                                    out.append(('E', push(g(lo(i) + 2 * t0), L1),
                                                pushes([r, 0, g(lo(j) + t0)], R3)))
                        else:
                            out.append(('C', pushes([sub(m, 2), add(i, 2)], L1), push(z, R2)))
                    continue
                if m == 0: out.append(('E', L1, push(add(i, 1), R1)))
                elif m == 1:
                    for r, R2 in pop(R1): out.append(('C', pushes([r, add(i, 2)], L1), R2))
                else: out.append(('C', pushes([sub(m, 2), add(i, 2)], L1), R1))
    elif q == 'C':
        for a, L1 in popsplit(L, 3):
            for r, R1 in popsplit(R, 1):
                if a == 0: out.append(('C', push(add(r, 1), L1), R1))
                elif a == 1:
                    for b, L2 in pop(L1): out.append(('E', L2, pushes([b, 0, add(r, 1)], R1)))
                elif a == 2:
                    if r != 0: out.append('HALT')
                    else:
                        for b, L2 in pop(L1): out.append(('B', push(add(b, 5), L2), R1))
                else: out.append(('C', pushes([add(r, 1), sub(a, 1)], L1), R1))
    elif q == 'B':
        for a, L1 in popsplit(L, 2):
            for r, R1 in popsplit(R, 3):
                if r == 0:
                    for s, R2 in pop(R1): out.append(('C', pushes([s, a], L1), R2))
                elif a == 0:
                    for b, L2 in pop(L1): out.append(('E', L2, pushes([b, 0, sub(r, 1)], R1)))
                elif a == 1:
                    for b, L2 in pop(L1):
                        if r == 1: out.append(('F', push(add(b, 4), L2), R1))
                        elif r == 2: out.append(('B', push(add(b, 5), L2), R1))
                        else: out.append('HALT')
                else: out.append(('C', pushes([sub(r, 1), a], L1), R1))
    else:
        for a, L1 in pop(L):
            for r, R1 in popsplit(R, 2):
                if r == 0: out.append(('F', push(add(a, 1), L1), R1))
                elif r == 1: out.append(('B', push(add(a, 2), L1), R1))
                else: out.append('HALT')
    return out

def absl(lst):
    v = [norm(x) for x in lst]
    if len(v) > K + K2: raise Overflow('start too long')
    return (tuple(v[:K]), None, tuple(v[K:]))

def show(s):
    def f(v): return ('>=%d' % v[1]) if isg(v) else str(v)
    def fl(l): return '[' + ' '.join(map(f, l[0])) + ((' ~>=%d*~ ' % l[1]) if l[1] is not None else ' | ') + ' '.join(map(f, l[2])) + ']'
    return s[0] + ' L' + fl(s[1]) + ' R' + fl(s[2])

if __name__ == '__main__':
    ls = open(sys.argv[4]).read().split('\n')
    f = (ls[0].strip(), tuple(int(x) for x in ls[1].split()), tuple(int(x) for x in ls[2].split()))
    s0 = (f[0], absl(f[1]), absl(f[2]))
    seen = {s0: None}; dq = collections.deque([s0]); n = 0
    def trace(s):
        tr = []
        while s is not None: tr.append(s); s = seen[s]
        tr.reverse(); print('trace length', len(tr))
        for x in tr[-int(sys.argv[5]) if len(sys.argv)>5 else -100:]: print('  ', show(x))
    while dq:
        s = dq.popleft(); n += 1
        try: nx = succ(s)
        except Overflow as e:
            print('OVERFLOW at', show(s), e); trace(s); sys.exit(1)
        for t in nx:
            if t == 'HALT':
                print('ABSTRACT HALT from', show(s)); trace(s); sys.exit(2)
            if t not in seen: seen[t] = s; dq.append(t)
        if n % 200000 == 0: print('states', n, len(seen), flush=True)
    print('CLOSED: no abstract halt; states', len(seen))
