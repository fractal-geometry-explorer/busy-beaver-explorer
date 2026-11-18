"""Check the left-end map (emap.step) of 1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB against the plain machine.

`plain(s, n, k)` builds the state (head in state A two cells, or D three cells, left of 1^n (01)^k 111, or of 1^n
when k = 0), runs the machine cell by cell to the next state of that form and returns it (or 'HALT').

usage: python3 leftcheck.py [NMAX KMAX]    every state with n < NMAX, k < KMAX (default 70, 50), 300 random larger
                                           ones, the run from blank tape, and the epoch map f(N) for N <= 150
       python3 leftcheck.py rules          the rule table with step counts (`steps`) against direct simulation
"""
import os, random, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from emap import step, jump

M = '1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB'
T = {}
for i, g in enumerate(M.split('_')):
    for b in (0, 1):
        s = g[3 * b:3 * b + 3]
        T[(i, b)] = None if s[0] == '-' else (int(s[0]), 1 if s[1] == 'R' else -1, ord(s[2]) - 65)
PAT = re.compile(r'^(1*)((?:01)*)(1*)$')
TR = bytes.maketrans(b'\x00\x01', b'01')


def run(tape, base, h, q, hi, maxst=10 ** 9):
    """Run to the next left-end state; (state, steps) with state = (s, n, k), 'HALT' or ('?', ...)."""
    lo, steps = base, 0
    while steps < maxst:
        tr = T[(q, tape[h])]
        if tr is None:
            return 'HALT', steps + 1
        w, d, q = tr
        tape[h] = w
        if w and h < lo:
            lo = h
        if w and h > hi:
            hi = h
        h += d
        steps += 1
        if d < 0 and h < lo:
            while not tape[lo]:
                lo += 1
            if (q == 0 and lo - h == 2) or (q == 3 and lo - h == 3):
                x = bytes(tape[lo:hi + 1]).translate(TR).decode().rstrip('0')
                m = PAT.match(x)
                if not m or (m.group(2) and len(m.group(3)) != 3):
                    return ('?', 'ABCDEF'[q], x[:60]), steps
                k = len(m.group(2)) // 2
                return ('ABCDEF'[q], len(m.group(1)) + (len(m.group(3)) if k == 0 else 0), k), steps
    return 'max', steps


def plain(s, n, k):
    cells = '1' * n + '01' * k + ('111' if k else '')
    L = 5 * len(cells) + 200
    tape = bytearray(2 * L + len(cells))
    for i, c in enumerate(cells):
        tape[L + i] = int(c)
    return run(tape, L, L - (2 if s == 'A' else 3), 'ABCDEF'.index(s), L + len(cells) - 1)[0]


def main():
    nmax, kmax = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (70, 50)
    random.seed(3)
    todo = [(s, n, k) for s in 'AD' for n in range(nmax) for k in range(kmax)]
    todo += [(random.choice('AD'), random.randint(0, 400), random.randint(0, 300)) for _ in range(300)]
    bad = 0
    for x in todo:
        if plain(*x) != step(*x):
            bad += 1; print('BAD', x, plain(*x), step(*x))
    print(len(todo), 'states,', bad, 'mismatches')
    # from blank tape
    tape = bytearray(40000)
    st, n0 = run(tape, 20000, 20000, 0, 20000)
    print('blank tape: first left-end state', st, 'after', n0, 'steps')
    x, cnt = st, 0
    for _ in range(170):
        y = plain(*x)
        assert y == step(*x), (x, y)
        x = y; cnt += 1
    print(cnt, 'states of the blank-tape run follow the map; now', x)
    # epochs: from D(N, 0) to the next D(N', 0) or a halt
    halts = []
    for N in range(1, 151):
        x = ('D', N, 0)
        while True:
            y = plain(*x)
            assert y == step(*x), (x, y)
            x = y
            if x == 'HALT':
                halts.append(N); break
            if x[0] == 'D' and x[2] == 0:
                break
    print('epochs N = 1..150 follow the map; halting N:', halts)


def steps(s, n, k):
    """Machine steps from the left-end state s(n, k) to the next one, or to the halt (counting the halting step)."""
    if n % 2 == 0:
        return 3 * n + 11
    if k == 0:
        return 3 * n + (23 if s == 'A' else 28)
    if k == 1:
        return n + (8 if s == 'A' else 9)
    if 2 * k >= n + 5:
        return (3 * n * n + 24 * n + (47 if s == 'A' else 61)) // 2
    return 6 * k * k + 3 * n + 36


def run_states(maxsteps):
    """The run from blank tape: (step, left-end state) at every left-end state of the first maxsteps steps."""
    N = 1 << 16
    tape = bytearray(N)
    h = lo = hi = N // 2
    q, lo_set = 0, False
    for t in range(maxsteps):
        tr = T[(q, tape[h])]
        if tr is None:
            yield t + 1, 'HALT'
            return
        w, d, q = tr
        tape[h] = w
        if w and (not lo_set or h < lo):
            lo, lo_set = h, True
        if w and h > hi:
            hi = h
        h += d
        if d < 0 and lo_set and h < lo:
            while not tape[lo]:
                lo += 1
            if (q == 0 and lo - h == 2) or (q == 3 and lo - h == 3):
                x = bytes(tape[lo:hi + 1]).translate(TR).decode().rstrip('0')
                m = PAT.match(x)
                if m and (not m.group(2) or len(m.group(3)) == 3):
                    k = len(m.group(2)) // 2
                    yield t + 1, ('ABCDEF'[q], len(m.group(1)) + (len(m.group(3)) if k == 0 else 0), k)


def check_rules():
    bad = cnt = halts = 0
    for s in 'AD':
        for n in range(80):
            for k in range(60):
                cells = '1' * n + '01' * k + ('111' if k else '')
                L = 5 * len(cells) + 200
                tape = bytearray(2 * L + len(cells))
                for i, c in enumerate(cells):
                    tape[L + i] = int(c)
                y, m = run(tape, L, L - (2 if s == 'A' else 3), 'ABCDEF'.index(s), L + len(cells) - 1)
                cnt += 1; halts += y == 'HALT'
                if y != step(s, n, k) or m != steps(s, n, k):
                    bad += 1; print('differs at', (s, n, k), y, m, step(s, n, k), steps(s, n, k))
    print(f'rules grid: {cnt} left-end states ({halts} halting), {bad} failures')
    MAX = 10 ** 7
    x, acc, nv = ('D', 3, 0), 11, 0
    for t, y in run_states(MAX):
        if nv:
            acc += steps(*x); x = step(*x)
        nv += 1
        if y != x or t != acc:
            bad += 1; print('run differs at step', t, y, x, acc); x, acc = y, t
    print(f'rules run: {nv} left-end states in the first {MAX:.0e} steps, the last at step {acc}, '
          f"{'all at the predicted step' if not bad else 'FAILED'}")
    return bad


if __name__ == '__main__':
    if sys.argv[1:2] == ['rules']:
        sys.exit(1 if check_rules() else 0)
    main()
