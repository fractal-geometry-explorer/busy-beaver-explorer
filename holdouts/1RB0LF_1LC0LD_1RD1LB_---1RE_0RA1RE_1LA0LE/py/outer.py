"""The outer orbit of 1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE: the configurations O(N) = 1^N F>0 0 1^3.

The tape right of the gap is kept as a list of blocks (1^n 0), stored as runs [[n, count], ...] with the block
nearest the head at the end.  Rounds against one block are done all at once (the rule of `mstep` iterated), and
the inner epochs (README, "Inner epochs") are jumped over with the closed form found numerically:
X = 24*2^j - 3 becomes 24*2^(j+1) - 3 and the units in front of the stored block drop by j + 4, at a cost of
1152*4^j - 216*2^j + 10 steps.  Anything else is run on the machine itself, cell by cell.

  python3 outer.py K [notime]     the first K outer configurations from blank tape (N, its parity, the step)

The jump is a heuristic acceleration (checked against the unaccelerated run for j < 400), so the outer values
past the eighth rest on it.
"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../tools/py"))
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)
from bbtools.machine import Machine, Run, Tape

M = Machine.parse("1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE")
F = 5
TIME = True


def norm(r):
    while r and r[-1] == 0:
        r.pop()
    return r


def concrete(X, r, maxsteps=10**8):
    """run the machine from 0^inf 1^X F>0 0 blocks(r) to the next such configuration (X != 1)"""
    c = [1] * X + [0, 0]
    head = X
    for b in r:
        c += [1] * b + [0]
    t = Tape()
    for i, v in enumerate(c):
        t.set(i, v)
    t.lo, t.hi = 0, len(c) - 1
    run = Run(M, F, t, head)
    while run.steps < maxsteps:
        if not run.step():
            return 'halt', run.steps, None
        if run.state == F and t.get(run.head) == 0:
            h = run.head
            j = h - 1
            while t.get(j) == 1:
                j -= 1
            if all(t.get(q) == 0 for q in range(min(t.lo, j) - 1, j + 1)) and t.get(h + 1) == 0:
                X2 = h - 1 - j
                if X2 == 1:
                    continue
                rr, n = [], 0
                for q in range(h + 2, t.hi + 2):
                    if t.get(q):
                        n += 1
                    else:
                        rr.append(n)
                        n = 0
                return X2, norm(rr), run.steps
    raise RuntimeError('no macro configuration')


def expand(rr):
    out = []
    for v, c in reversed(rr):
        out += [v] * c
    return out


def compress(r):
    rr = []
    for v in reversed(r):
        if rr and rr[-1][0] == v:
            rr[-1][1] += 1
        else:
            rr.append([v, 1])
    return rr


def push(rr, v, c=1):
    if c > 0:
        if rr and rr[-1][0] == v:
            rr[-1][1] += c
        else:
            rr.append([v, c])


def pop1(rr):
    v, c = rr[-1]
    if c == 1:
        rr.pop()
    else:
        rr[-1][1] -= 1
    return v


def top(rr, i=0):
    j = len(rr) - 1
    while j >= 0:
        v, c = rr[j]
        if i < c:
            return v
        i -= c
        j -= 1
    return None


def trim(rr):
    while rr and rr[0][0] == 0:
        rr.pop(0)


class Sim:
    def __init__(s, X, r, t):
        s.X, s.rr, s.t = X, compress(norm(list(r))), t

    def add(s, n):
        if TIME:
            s.t += n

    def macro(s):
        X, rr = s.X, s.rr
        k = rr[-1][1] if rr and rr[-1][0] == 1 else 0
        if k:
            rr.pop()
        Y = top(rr)
        if Y is not None and Y >= 2:
            if X >= 3:
                j = min(Y // 2, (X - 1) // 2)
                s.add(j * (6 * k + 18) + 6 * j * (j - 1))
                X -= 2 * j; Y -= 2 * j; pop1(rr); push(rr, Y); push(rr, 1, k + 2 * j)
                if X == 1:
                    X = 0; s.add(2); push(rr, 1)
                s.X = X; trim(rr); return 'round'
            if X == 0:
                j = Y // 2
                s.add(j * (6 * k + 14) + 6 * j * (j - 1))
                Y -= 2 * j; pop1(rr); push(rr, Y); push(rr, 1, k + 2 * j)
                trim(rr); return 'round'
        elif Y is None or Y == 0:
            if Y == 0:
                pop1(rr)
            Z = top(rr) if Y == 0 else None
            if X >= 5:
                z = 0
                if Z is not None:
                    z = Z; pop1(rr)
                s.add(6 * k + 20); X -= 4; push(rr, 2 * k + z + 5)
                if X == 1:
                    X = 0; s.add(2); push(rr, 1)
                s.X = X; trim(rr); return 'merge'
            if X == 0 and Z is not None:
                W = top(rr, 1)
                if W is not None and W >= 1:
                    pop1(rr); pop1(rr); push(rr, W - 1)
                    s.add(8 * k + Z + 19); s.X = 2 * k + Z + 6; trim(rr); return 'restart'
            if X == 0 and (Z is None or top(rr, 1) is None):
                z = 0
                if Z is not None:
                    z = Z; pop1(rr)
                s.add(8 * k + z + 27); s.X = 2 * k + z + 4; push(rr, 3); trim(rr); return 'outer'
            if Y == 0:
                push(rr, 0)
        if k:
            push(rr, 1, k)
        if X == 2 and k >= 1:
            pop1(rr); push(rr, 0); s.X = 5; s.add(15); return 'two'
        X2, r2, cost = concrete(X, expand(rr))
        if X2 == 'halt':
            s.add(r2); s.X = 'halt'; return 'halt'
        s.X = X2; s.rr = compress(r2); s.add(cost)
        return 'machine'


def run_outer(s):
    """run to the next outer configuration (or a halt), jumping over inner epochs"""
    jumps = 0
    while True:
        kd = s.macro()
        if kd in ('halt', 'outer'):
            return kd, jumps
        if kd == 'restart' and len(s.rr) == 3 and s.rr[2] == [0, 1] and s.rr[1][0] == 1 and s.rr[0][1] == 1:
            u, X = s.rr[1][1], s.X
            q, rem = divmod(X + 3, 24)
            if rem == 0 and q & (q - 1) == 0:
                j = q.bit_length() - 1
                ok = lambda m: m * (j + 4) + m * (m - 1) // 2 + (j + m + 68) <= u
                lo, hi = 0, 1
                while ok(hi):
                    hi *= 2
                while hi - lo > 1:
                    mid = (lo + hi) // 2
                    lo, hi = (mid, hi) if ok(mid) else (lo, mid)
                m = lo
                if m > 0:
                    if TIME:   # sum over i = j .. j+m-1 of 1152*4^i - 216*2^i + 10
                        s.t += 384 * (4 ** (j + m) - 4 ** j) - 216 * (2 ** (j + m) - 2 ** j) + 10 * m
                    s.X = 24 * 2 ** (j + m) - 3
                    s.rr[1][1] = u - (m * (j + 4) + m * (m - 1) // 2)
                    jumps += m


def in_H(N):
    n = max(N.bit_length() - 6, 0)
    return any(N == 2 ** (m + 4) - 2 * m - 10 for m in range(n, n + 4))


if __name__ == "__main__":
    K = int(sys.argv[1])
    TIME = 'notime' not in sys.argv
    s = Sim(10, [3], 102)   # O(10) at step 102 (`init_cfg` in Reduce.lean)
    print("outer 0: N = 10, step 102")
    for i in range(K):
        kd, j = run_outer(s)
        if kd == 'halt':
            print('halt', 'step', s.t if TIME else '?')
            break
        N = s.X
        Ns = str(N) if N.bit_length() < 64 else f'({N.bit_length()} bits)'
        st = (f'{float(s.t):.3e}' if s.t > 10**12 else s.t) if TIME else '?'
        print(f'outer {i + 1}: N = {Ns}, N mod 2 = {N % 2}, in H: {in_H(N)}, step {st}, epochs jumped {j}', flush=True)
