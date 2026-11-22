"""endbfs.py: can the last blocks of the word alone exclude the dangerous junk?  (They cannot.)

The word pass of lean/Word.lean and c/wordrun.c, restricted to the last K cells of the word.  A state is the last K
cells and the block starts of the round that wrote them; the input of a round is where the pass enters the window
(1 or 2 cells into a block of the previous round, the PR59 phase rule) and the count it brings.  Counts are of the
form 2^a - d (at depth 48 the run has d in {0,...,34}, mostly 0, 1, 2, 4).  Breadth-first search from the word end
after ROUND0 rounds of the real run, over every input of that form, for a round that meets 1111 (halt) or 11100
(no proved rule; for 1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA--- every 111 halts).

usage: python3 endbfs.py [K [ROUND0 [D [AMIN AMAX]]]]
  D: the allowed deficits d, e.g. "0" or "0,1,2" (default 0); AMIN..AMAX: the exponents a (default 6..18, the
  range of nearly all counts the run brings to depth 48)
"""
import sys
from collections import deque


def pass_word(T, p, n):
    """n visits from cell p on the list T (zeros after the end are added as needed), the rules of c/wordrun.c for
    1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---.  Returns (result, block starts); result 'ok', 'halt' or 'stuck'."""
    starts = []
    while n > 0:
        if len(T) <= p + 8:
            T.extend([0] * 64)
        w = T
        if w[p] == 0:
            w[p] = 1; n -= 1
        elif w[p + 2] == 0:                       # 100, 110: a digit block
            starts.append(p); m = n - 1; w[p] = m & 1; w[p + 1] = 0; n = 1 + m // 2; p += 3
        elif w[p + 1] == 0 and w[p + 3] == 0:     # 1010: a doubler
            starts.append(p); n *= 2; p += 4
        elif w[p + 1] == 0:                       # 1011 -> 0001
            starts.append(p); w[p] = 0; w[p + 2] = 0; w[p + 3] = 1; n -= 1
        else:                                     # 111
            if w[p + 3] == 1:
                return 'halt', starts
            if w[p + 4] == 1:
                starts.append(p); w[p + 1] = 0; n -= 1
            else:
                return 'stuck', starts
    return 'ok', starts


def strip(T):
    e = len(T)
    while e > 0 and T[e - 1] == 0:
        e -= 1
    return e


def real_state(K, rounds):
    """The word end after `rounds` rounds of the exact pass (round: put 1 0 in front, one visit)."""
    T = [1]
    for _ in range(rounds):
        T = [1, 0] + T
        res, starts = pass_word(T, 0, 1)
        assert res == 'ok'
    e = strip(T)
    lo = e - K
    return tuple(T[lo:e]), tuple(b - lo for b in starts if b - lo >= -4)


def step(state, o, n, K):
    win, st = state
    T = list(win) + [0] * 64
    res, starts = pass_word(T, o, n)
    if res != 'ok':
        return res, None
    e = max(strip(T), K)
    lo = e - K
    return 'ok', (tuple(T[lo:e]), tuple(b - lo for b in starts if b - lo >= -4))


def main():
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 48
    r0 = int(sys.argv[2]) if len(sys.argv) > 2 else 11
    D = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [0]
    amin = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    amax = int(sys.argv[5]) if len(sys.argv) > 5 else 18
    counts = sorted({(1 << a) - d for a in range(amin, amax + 1) for d in D if (1 << a) > d})
    s0 = real_state(K, r0)
    par = {s0: None}
    q = deque([s0])
    while q:
        s = q.popleft()
        win, st = s
        for o in sorted({b + d for b in st for d in (1, 2) if 0 <= b + d <= 3}):
            for n in counts:
                res, t = step(s, o, n, K)
                if res != 'ok':
                    path = [(s, o, n)]
                    while par[path[-1][0]] is not None:
                        path.append(par[path[-1][0]])
                    print(f'{res.upper()} after {len(path)} rounds from the word end of round {r0} (K = {K}, counts 2^a - d, a in {amin}..{amax}, d in {D}):')
                    for (w, _), oo, nn in reversed(path):
                        print('  window', ''.join(map(str, w)), f' enter at {oo} with {nn} visits')
                    print(f'states explored: {len(par)}')
                    return
                if t not in par:
                    par[t] = (s, o, n)
                    q.append(t)
        if len(par) > 2_000_000:
            print('state cap reached'); return
    print(f'no danger reachable; {len(par)} states')


if __name__ == '__main__':
    main()
