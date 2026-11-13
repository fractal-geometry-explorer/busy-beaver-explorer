"""The marker map of 1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC (fitted; checked against the machine, not proved).

With a = 10 and b = 110, the moments the head extends the tape to the left in state B have the tape

    P[k0, k1, ..., kn] = B> 0 0 a^k0 b a^k1 b ... b a^kn 1          (blank tape on both sides)

`F` is the map from one such moment to the next, for the lists the run meets: two blocks [k, m] or three blocks
[k, m, n] with n odd.  A single block [N] halts (lean/Halt.lean, `single_halts`).

    [k, m]      m >= k+2          ->  [2k+3, m-k-2]                     the marker doubles
                m = k+1           ->  [1, 2k+3, 1]
                m = k             ->  [2k+3]  ->  HALT
                m < k, k-m odd    ->  [k-m, 2m+3]
                m < k, k-m even   ->  [1, k-m-1, 2m+3]
    [k, m, n]   m >= k+2          ->  [2k+3, m-k-2, n]
    (n odd)     m <= k            ->  [1, 2k+n+4]
                m = k+1           ->  [1, 4k+n+10]

So the machine halts from blank tape iff the orbit of [1, 1, 1] (reached at step 72, lean/Halt.lean) meets a
two-block list [k, k].

    python3 py/map.py table            the formulas against a direct run of the machine, small lists (incl. n even)
    python3 py/map.py check STEPS      the machine from blank tape for STEPS steps against the orbit of the map
    python3 py/map.py far ITERATIONS   iterate the map (exact integers), looking for [k, k]
"""
import re
import sys
import time

TABLE = "1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC"
TR = {}
for _i, _row in enumerate(TABLE.split('_')):
    for _b in range(2):
        _c = _row[3 * _b:3 * _b + 3]
        TR[(chr(65 + _i), _b)] = None if _c[0] == '-' else (int(_c[0]), 1 if _c[1] == 'R' else -1, _c[2])

START = [1, 1, 1]


def F(G):
    """The fitted map; 'HALT', or None for a list it does not cover (n even is covered too, see `table`)."""
    if len(G) == 1:
        return 'HALT'
    k, m, rest = G[0], G[1], G[2:]
    if len(G) > 3:
        return None
    if m >= k + 2:
        return [2 * k + 3, m - k - 2] + rest
    if len(G) == 2:
        if m == k + 1:
            return [1, 2 * k + 3, 1]
        if m == k:
            return [2 * k + 3]
        i = k - m
        return [i, 2 * m + 3] if i % 2 else [1, i - 1, 2 * m + 3]
    n = G[2]
    if n % 2 == 1:
        return [1, 2 * k + n + 4] if m <= k else [1, 4 * k + n + 10]
    if m == k + 1:
        return [1, 2 * k + 3, n + 3]
    if m == k:
        return [2 * k + 5 + n]
    i = k - m
    return [i, 2 * m + 5 + n] if i % 2 else [1, i - 1, 2 * m + 5 + n]


PAT = re.compile(r'^00((?:10)*(?:110(?:10)*)*)1$')


def parse(s):
    m = PAT.match(s)
    if not m:
        return None
    return [len(p) // 2 for p in m.group(1).split('110')]


def enc(G):
    return '00' + '110'.join('10' * k for k in G) + '1'


def p_moments(tape, pos, st, maxsteps):
    """The moments the head, in B, is left of everything visited so far and the tape is a P[...]: (step, list);
    ('HALT', step) if the machine halts."""
    lo = pos
    for t in range(1, maxsteps + 1):
        r = TR[(st, 1 if pos in tape else 0)]
        if r is None:
            yield t, 'HALT'
            return
        if r[0]:
            tape[pos] = 1
        else:
            tape.pop(pos, None)
        pos += r[1]
        st = r[2]
        if pos < lo:
            lo = pos
            if st == 'B' and tape:
                g = parse(''.join('1' if i in tape else '0' for i in range(pos, max(tape) + 1)))
                if g is not None:
                    yield t, g


def machine_next(G, maxsteps=10 ** 7):
    tape = {i: 1 for i, c in enumerate(enc(G)) if c == '1'}
    for t, g in p_moments(tape, 0, 'B', maxsteps):
        return g
    return 'TIMEOUT'


def table():
    tot = 0
    for k in range(9):
        for m in range(13):
            for rest in [[]] + [[n] for n in range(8)]:
                G = [k, m] + rest
                got = machine_next(G)
                if got != F(G):
                    print('MISMATCH', G, F(G), got)
                    return
                tot += 1
    for N in range(40):
        if machine_next([N]) != 'HALT':
            print('MISMATCH', [N])
            return
    print('the formulas agree with the machine on', tot, 'lists [k, m] and [k, m, n]; [N] halts for N < 40')


def check(steps):
    prev, n, t = None, 0, 0
    for t, g in p_moments({}, 0, 'A', steps):
        if prev is None:
            print('first marker configuration: step', t, g)
        elif F(prev) != g:
            print('MISMATCH at step', t, prev, F(prev), g)
            return
        else:
            n += 1
        prev = g
    print('the machine follows the map for', n, 'consecutive marker configurations; the last one, at step', t, 'is', prev)


def far(iterations):
    G, t0 = list(START), time.time()
    for it in range(1, iterations + 1):
        H = F(G)
        if H is None or (H != 'HALT' and (len(H) == 3 and H[2] % 2 == 0)):
            print('outside the map at iteration', it)
            return
        if H == 'HALT' or len(H) == 1:
            print('HALT: [k, k] at iteration', it, G if len(str(G)) < 200 else '(large)')
            return
        G = H
        if it % max(1, iterations // 10) == 0:
            print('iteration', it, 'blocks of', [x.bit_length() for x in G], 'bits', round(time.time() - t0, 1), 's')
            sys.stdout.flush()
    print('no halt in', iterations, 'iterations of the map')


if __name__ == '__main__':
    if sys.argv[1] == 'table':
        table()
    elif sys.argv[1] == 'check':
        check(int(float(sys.argv[2])))
    else:
        far(int(float(sys.argv[2])))
