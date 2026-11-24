"""The digit carry rule of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE (24 November 2026).

The wall.  From step 2*10^7 on, at each visit of the head in state C to the left end of the tape, the tape is
C>0 (01101)^n W with W exactly 1,573 cells:

    W = H  D_0 D_1 ... D_45  E  (10001101)^30
    H   = 01100011000110001100110011010110011011100110      44 cells, the same at every sweep
    D_j = a110 b110 c011 0011 0d11 0e11 0                     25 cells, a digit; five free cells a b c d e
    E   = 139 cells, the same at every sweep so far

A digit is written here as its five free cells, 'abcde'.

The sweep.  Between two visits to the left end the head goes from H into the digits and back to H exactly 15
times (15 trips).  At the start of trip p (p = 0..14) the cells of H are the same at every sweep, and trip p
feeds the carry Y into digit 0 if p is 1, 6 or 11, and the carry X otherwise.  A carry c reaching digit j
rewrites it and passes a carry on (or stops) by the table TABLE below: TABLE[c][d] = (d', c'), c' = '' for
"stops".  Five carries occur: X, Y, P, Q, R.  The table has 73 entries, and no others are ever needed:

  * it reproduces every trip of the first 1,200 sweeps (trip by trip, simulating the machine), and every sweep
    from step 2*10^7 to 2*10^10 (29,299 sweeps, from the walls dumped by c/walldump.c);
  * run as a model for 10^6 sweeps from the wall at 2*10^10, it never meets a pair (carry, digit) outside the
    table, and the carries never pass digit 17;
  * closure: the digit strings with first digit in FIRST[p] and every two neighbouring digits in PAIRS are
    mapped by trip p into the strings with first digit in FIRST[p+1] and neighbours in PAIRS, and no trip meets a
    pair (carry, digit) outside the table.  lean/Carry.lean proves this by decide, for strings of every length,
    for the model.  Its link to the machine is the two checks above (simulation, not proof).

A in TABLE['X'] is binary counting in a, b, c (a lowest): X sets the lowest 0 among a, b, c and clears the 1s
below it; when a = b = c = 1 the digit overflows, and d e steps from 11 to 01 (passing X on) or from 01 to 10
(passing Y on).  Deeper digits are rare: a trip changes at least 2 digits in 1/4 of all trips, and each further
digit is reached by 3/8 of the trips that reach the one before (the counts below), so the carries first reach the
end of the 46 digits after roughly 10^19 to 10^20 trips.

usage: python3 carry.py check [STEPS]     sweeps predicted by the table vs the dumped walls (default 2e10)
       python3 carry.py trips [SWEEPS]    trip by trip, machine vs table (default 300 sweeps)
       python3 carry.py far [SWEEPS]      the model alone from the wall at the end of the dump (default 1e6)
       python3 carry.py closure           the closure check above
       python3 carry.py lean > ../lean/CarryData.lean    the table, the pairs and the certificate for Lean
"""
import collections
import os
import subprocess
import sys
import tempfile

M = '1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE'
HERE = os.path.dirname(os.path.abspath(__file__))
H = '01100011000110001100110011010110011011100110'
FREE = (0, 4, 8, 17, 21)
SKEL = 'x110x110x01100110x110x110'
ND = 46
YPH = (1, 6, 11)

_SPEC = """
X 00001>10001 00010>10010 00011>10011 00100>10100 00101>10101 00110>10110 01000>11000 01001>11001 01011>11011
  01101>11101 01110>11110 01111>11111 10000>01000 10001>01001 10010>01010 10011>01011 10100>01100 10101>01101
  10110>01110 10111>01111 11000>00100 11010>00110 11011>00111 11101>00010:Y 11111>00001:X
Y 00001>01001 00010>11111:P 00110>01110 00111>11010:P 01000>00100 01010>10000:X 01100>10111:Y 01111>00001:X
  10001>00101 10011>11011 10100>00011:Y 10101>11101 11000>10100 11001>01101 11101>10010:Y 11110>01000:X
P 00001>00101 00011>11011 00100>00011:Y 00101>11101 01000>10100 01001>01101 01101>10010:Y 01110>01000:X
  10000>00100 10010>10000:X 10100>10111:Y 10111>00001:X 11010>01110 11011>11010:P 11101>11111:Q 11111>01001:X
Q 00001>01101 00110>01000:X 01000>00011:Y 01111>00101:X 10011>11010:P 10101>11111:Q 11000>10111:Y 11101>10000:R
R 00001>11001 00110>11110 01000>10100 01111>10001:X 10011>00111 10101>00010:Y 11000>01100 11101>01010:Y
"""


def _table():
    t, c = {}, None
    for tok in _SPEC.split():
        if len(tok) == 1:
            c = tok
            t[c] = {}
            continue
        d, rest = tok.split('>')
        d2, _, c2 = rest.partition(':')
        t[c][d] = (d2, c2)
    return t


TABLE = _table()
CARRIES = 'XYPQR'


def digits(w):
    """The 46 digits of a wall, each as its five free cells; checks the fixed cells."""
    assert w[:44] == H, 'head part changed'
    out = []
    for i in range(ND):
        d = w[44 + 25 * i:69 + 25 * i]
        assert all(SKEL[j] == 'x' or SKEL[j] == d[j] for j in range(25)), ('digit form', i, d)
        out.append(''.join(d[j] for j in FREE))
    return out


def trip(d, c):
    """One trip of the model: carry c into digit 0 of the list d (changed in place).  Returns the number of digits
    changed, or raises KeyError on a pair outside the table and IndexError if the carry passes the last digit."""
    j = 0
    while c:
        d[j], c = TABLE[c][d[j]]
        j += 1
    return j


def sweep(d):
    deep = 0
    for p in range(15):
        deep = max(deep, trip(d, 'Y' if p in YPH else 'X'))
    return deep


def dump(steps, path):
    exe = os.path.join(tempfile.gettempdir(), 'walldump_30773')
    subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, '../c/walldump.c')], check=True)
    with open(path, 'w') as f:
        subprocess.run([exe, M, str(int(steps)), 'C', '01101', '1573', '1000000000', '20000000'], stdout=f,
                       check=True)


def walls(steps):
    path = os.path.join(tempfile.gettempdir(), f'walls_30773_{int(steps)}.txt')
    if not os.path.exists(path):
        dump(steps, path)
    with open(path) as f:
        for line in f:
            s, w = line.split()
            yield int(s), w


def check(steps):
    prev, ok, deep = None, 0, collections.Counter()
    for s, w in walls(steps):
        if prev is not None:
            d = digits(prev)
            k = sweep(d)
            assert d == digits(w) and w[1194:] == prev[1194:], f'sweep ending at step {s} not predicted'
            ok += 1
            deep[k] += 1
        prev = w
    print(f'{ok} sweeps from step 2e7 to {steps:.0e}: every one predicted by the table')
    print('digits changed by the sweep (deepest trip) -> sweeps:', dict(sorted(deep.items())))
    return 0


def tm_table():
    t = {}
    for i, p in enumerate(M.split('_')):
        for r in (0, 1):
            x = p[3 * r:3 * r + 3]
            t[(i, r)] = None if x[2] == '-' else (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65)
    return t


def machine_trips(w, n=3):
    """Run the machine from C>0 (01101)^n W to the next visit to the left end in state C; return the digits after
    each trip (a trip ends when the head comes back to cell 12 of H after a visit to the digits), the cells of H
    at those moments, and the wall at the end.  n does not matter (the pass over the block is uniform)."""
    T = tm_table()
    tape = collections.defaultdict(int)
    for i, c in enumerate('0' + '01101' * n + w):
        tape[i] = int(c)
    base = 1 + 5 * n + 44
    h, st, steps, lo, inside, out = 0, 2, 0, 0, False, []
    while True:
        a = T[(st, tape[h])]
        assert a is not None, 'halt'
        tape[h] = a[0]
        h += a[1]
        st = a[2]
        steps += 1
        lo = min(lo, h)
        r = h - base
        if r >= 0:
            inside = True
        if r == -12 and inside:
            inside = False
            dd = ''.join(str(tape[base + k]) for k in range(25 * ND))
            out.append(([''.join(dd[25 * i + j] for j in FREE) for i in range(ND)],
                        ''.join(str(tape[k]) for k in range(base - 44, base))))
        if st == 2 and h == lo and steps > 10:
            hi = 1 + 5 * n + len(w) - 1
            return out, ''.join(str(tape[k]) for k in range(hi - len(w) + 1, hi + 1))


def trips(nsweeps):
    heads, used, n = None, set(), 0
    for t, (s, w) in enumerate(walls(3e9)):
        if t >= nsweeps:
            break
        tr, w2 = machine_trips(w)
        assert len(tr) == 15, 'not 15 trips'
        hs = [x[1] for x in tr]
        heads = heads or hs
        assert hs == heads, 'H differs between sweeps'
        d = digits(w)
        for p, (dm, _) in enumerate(tr):
            c, j = 'Y' if p in YPH else 'X', 0
            while c:
                used.add((c, d[j]))
                d[j], c = TABLE[c][d[j]]
                j += 1
            assert d == dm, f'trip {p} of sweep {t}'
            n += 1
    print(f'{n} trips of {nsweeps} sweeps: each one is the table; H is the same at the start of each trip '
          f'number p in every sweep; {len(used)} table entries used')
    return 0


def far(nsweeps):
    *_, (s, w) = walls(2e10)
    d = digits(w)
    deep, used, first = collections.Counter(), set(), {}
    for t in range(int(nsweeps)):
        for p in range(15):
            c, j = 'Y' if p in YPH else 'X', 0
            while c:
                used.add((c, d[j]))
                d[j], c = TABLE[c][d[j]]
                j += 1
            deep[j] += 1
            first.setdefault(j, t)
    tot = sum(deep.values())
    print(f'model, {int(nsweeps)} sweeps from the wall at step {s}: {len(used)} of 73 entries used, none missing')
    ge = tot
    for k in sorted(deep):
        print(f'  trips changing {k:2d} digits: {deep[k]:9d}   at least {k}: {ge / tot:.6f}'
              + (f'  ratio to {k - 1}: {prev / ge:.4f}' if k > 1 else ''))
        prev, ge = ge, ge - deep[k]
    return 0


def first_sets():
    """FIRST[p]: digit 0 at the start of trip p (from the sweep-start set, closed under the trips)."""
    *_, (s, w) = walls(3e9)
    F = [set() for _ in range(15)]
    F[0] = {'01110', '11101', '00100', '10100', '01001', '11011', '00001', '10010'}
    for _ in range(2):
        for p in range(15):
            c = 'Y' if p in YPH else 'X'
            F[(p + 1) % 15] |= {TABLE[c][x][0] for x in F[p]}
    return F


def closure():
    """The smallest sets PAIRS (neighbouring digits) and THETA (carry, digit, right neighbour) that contain the
    pairs of the walls of the first 50 sweeps and are closed under every trip; fails on a pair outside the table."""
    W = [w for _, (s, w) in zip(range(50), walls(3e9))]
    F = first_sets()
    pairs = {(d[j], d[j + 1]) for w in W for d in [digits(w)] for j in range(ND - 1)}
    theta = set()
    changed = True
    while changed:
        changed = False
        work = [('Y' if p in YPH else 'X', x, y) for p in range(15) for x in F[p] for (a, y) in pairs if a == x]
        while work:
            c, x, y = work.pop()
            if (c, x, y) in theta:
                continue
            theta.add((c, x, y))
            x2, c2 = TABLE[c][x]
            if not c2:
                new = [(x2, y)]
            else:
                y2, _ = TABLE[c2][y]
                new = [(x2, y2)]
                work += [(c2, y, z) for (a, z) in pairs if a == y]
            for q in new:
                if q not in pairs:
                    pairs.add(q)
                    changed = True
    return F, pairs, theta


def show_closure():
    F, pairs, theta = closure()
    print(f'closed: {len(pairs)} neighbour pairs, {len(theta)} (carry, digit, neighbour) triples, first-digit sets of '
          f'sizes {[len(f) for f in F]}; no pair (carry, digit) outside the table')
    return 0


def lean():
    """lean/CarryData.lean: the table as tab[carry][digit], and the sets FIRST and PAIRS as bit masks."""
    F, pairs, theta = closure()
    code = lambda d: int(d, 2)
    cnum = {c: i + 1 for i, c in enumerate(CARRIES)}
    cnum[''] = 0
    rows = [['none'] * 32 for _ in range(6)]
    for c in CARRIES:
        for d, (d2, c2) in TABLE[c].items():
            rows[cnum[c]][code(d)] = f'some ({code(d2)}, {cnum[c2]})'
    pm = [0] * 32
    for a, b in pairs:
        pm[code(a)] |= 1 << code(b)
    fm = [sum(1 << code(x) for x in f) for f in F]
    w0 = next(iter(walls(3e9)))[1]
    print('/-! Generated by `python3 py/carry.py lean`; do not edit by hand.  The carry table of')
    print('1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE (see `Carry.lean`).  A digit is its five free cells a b c d e read')
    print('as a binary number, a highest; the carries are 0 (none), 1 X, 2 Y, 3 P, 4 Q, 5 R. -/')
    print('\nnamespace H30773.Carry\n')
    print('/-- `tab[c][d]` = (new digit, carry passed on) when carry c reaches digit d: the 73 entries. -/')
    print('def tab : List (List (Option (Nat × Nat))) := [')
    print(',\n'.join('  [' + ', '.join(r) + ']' for r in rows) + ']\n')
    print(f'/-- Bit y of `pmask[x]`: digit y may stand right of digit x ({len(pairs)} pairs). -/')
    print('def pmask : List Nat := [' + ', '.join(map(str, pm)) + ']\n')
    print('/-- Bit x of `fmask[p]`: digit 0 may be x at the start of trip p. -/')
    print('def fmask : List Nat := [' + ', '.join(map(str, fm)) + ']\n')
    print('/-- The 46 digits of the wall at step 20,018,306 (the first sweep of `py/carry.py check`). -/')
    print('def wall0 : List Nat := [' + ', '.join(str(code(x)) for x in digits(w0)) + ']\n')
    print('end H30773.Carry')
    return 0


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'check'
    arg = float(sys.argv[2]) if len(sys.argv) > 2 else None
    if cmd == 'check':
        sys.exit(check(arg or 2e10))
    if cmd == 'trips':
        sys.exit(trips(int(arg or 300)))
    if cmd == 'far':
        sys.exit(far(arg or 1e6))
    if cmd == 'closure':
        sys.exit(show_closure())
    if cmd == 'lean':
        sys.exit(lean())
    print(__doc__)
