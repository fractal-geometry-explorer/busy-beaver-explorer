"""The phase map of 1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE (the same cases as `lean/Phases.lean`), with the step count of each case.

usage (from the repository root):
  python3 holdouts/1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE/py/phasemap.py run [K]      iterate K phases from the start (default 10^6): steps reached, all-ones phases
  python3 holdouts/1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE/py/phasemap.py check [N]    compare every case with parameters < N (default 9) against the machine
  python3 holdouts/1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE/py/phasemap.py fatal [N]    the all-ones lengths below N (default 2000) that halt before an Even
                                                   phase or another all-ones tape (the list `fatalLen` of Phases.lean)

Phases: ('e', x, z) = E>0 (10)^x 1^z;  ('r', x, y) = (10)^x 1^y C>0;  ('q', m, k, t) = (10)^m 1 A>0 0 (10)^k 1^t.
"""
M = "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE"
RS, RPRE, QS, QW = "C", [], "A", 1

def nxt(p):
    if p[0] == 'e':
        x, z = p[1:]
        if z <= 1: return None
        return ('q', x, 0, z - 2), 2 * x + 3
    if p[0] == 'q':
        m, k, t = p[1:]
        if m >= 1 and t >= 3:
            b = min(m, (t - 1) // 2); s = 4 * (b * k + b * (b - 1)) + 10 * b
            return ('q', m - b, k + 2 * b, t - 2 * b), s
        if m == 0 and t >= 5: return ('e', k + 4, t - 4), 8 * k + 27
        if m == 0 and t == 4: return ('r', 0, 2 * k + 10), 6 * k + 20
        if m == 0 and t == 3: return ('r', 0, 2 * k + 8), 6 * k + 18
        return ('r', m, 2 * k + 3 + 2 * t), 2 * k + 2 + 2 * t
    x, y = p[1:]
    if x == 0: return (('e', 0, 1), 2) if y == 0 else (('e', 0, y + 1), y - 1 + 3)
    if x == 1: return {0: (('r', 0, 4), 7), 1: (('r', 0, 6), 10)}.get(y, (('e', 2, y - 1), y - 2 + 14))
    return (('q', x - 2, 1, 0), 3) if y == 0 else (('q', x - 2, 0, y + 1), y - 1 + 4)
INIT, INIT_STEPS = ('r', 0, 2), 2
def ones(p): return p[0] == 'r' and p[1] == 0
def even(p):
    if p[0] == 'e': return p[2] % 2 == 0 and p[2] >= 2
    if p[0] == 'r': return p[1] >= 1 and p[2] % 2 == 1
    return p[3] % 2 == 0


# ---------------------------------------------------------------- tools
import itertools
import sys

T = {}
for _i, _s in enumerate(M.split('_')):
    for _b in (0, 1):
        _w = _s[3 * _b:3 * _b + 3]
        T[(_i, _b)] = None if _w[0] == '-' else (int(_w[0]), 1 if _w[1] == 'R' else -1, ord(_w[2]) - 65)


def build(p):
    """The finite tape (cells, head, state) of a phase."""
    if p[0] == 'e':
        x, z = p[1:]
        return [0] + [1, 0] * x + [1] * z, 0, 4
    if p[0] in ('r', 'a'):
        x, y = p[1:]
        c = [1, 0] * x + [1] * y + RPRE
        return c + [0], len(c), ord(RS) - 65
    m, k, t = p[1:]
    c = [1, 0] * m + [1]
    return c + [0, 0] + [1, 0] * (QW * k) + [1] * t, len(c), ord(QS) - 65


def norm(cells, pos, st):
    ks = [i for i, v in enumerate(cells) if v] + [pos]
    lo, hi = min(ks), max(ks)
    return tuple(cells[i] if 0 <= i < len(cells) else 0 for i in range(lo, hi + 1)), pos - lo, st


def simulate(cells, pos, st, n):
    tape = dict(enumerate(cells))
    for _ in range(n):
        tr = T[(st, tape.get(pos, 0))]
        if tr is None:
            return None
        w, d, st = tr
        tape[pos] = w
        pos += d
    lo = min(list(tape) + [pos])
    hi = max(list(tape) + [pos])
    return norm([tape.get(i, 0) for i in range(lo, hi + 1)], pos - lo, st)


def check(n=9):
    """Run every phase with parameters < n for the step count of `nxt` and compare with the predicted phase."""
    bad = cnt = 0
    for kind, ar in (('e', 2), (INIT[0], 2), ('q', 3)):
        for args in itertools.product(range(n), repeat=ar):
            p = (kind,) + args
            r = nxt(p)
            if r is None:
                continue
            cnt += 1
            if simulate(*build(p), r[1]) != norm(*build(r[0])):
                bad += 1
                print('MISMATCH', p, r)
    print(f'{cnt} phases checked against the machine, {bad} mismatches')


def run(k):
    """Iterate the map k times from the start; print the step count reached and every all-ones phase."""
    p, t, seen = INIT, INIT_STEPS, []
    for i in range(k):
        if ones(p):
            seen.append((p[2], t))
        r = nxt(p)
        if r is None:
            print('halts at phase', i, p, 'step', t)
            return
        p, s = r
        t += s
    print(f'{k} phases, {t} steps ({t:.4e}), now {p}')
    print('all-ones phases (n, step):', [(n, f'{s:.3e}') for n, s in seen])


def fate(p, fuel=1000):
    for i in range(fuel):
        r = nxt(p)
        if r is None:
            return True
        p = r[0]
        if even(p) or ones(p):
            return False
    return None


def fatal(n):
    """The all-ones lengths below n whose run halts before an Even phase or another all-ones tape."""
    print([k for k in range(n) if fate((INIT[0], 0, k))])


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'run'
    arg = int(sys.argv[2]) if len(sys.argv) > 2 else None
    if cmd == 'check':
        check(arg or 9)
    elif cmd == 'fatal':
        fatal(arg or 2000)
    else:
        run(arg or 10 ** 6)
