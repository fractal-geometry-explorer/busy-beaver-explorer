"""The rules of a round with exact step counts (lean/Rules.lean, lean/Macro.lean), checked against direct simulation.

    R(n, m)     := 0^inf A> 0 11 (01)^n 0 11 (01)^m 0^inf       (round start with a counter)
    Z(k)        := 0^inf A> 0 11 (01)^k 0^inf                   (round start, counter used up)
    X_m(k, j)   := 0^inf C> (01)^k 0 11 (01)^j 0 11 (01)^m 0^inf (inside a round; X(k, j) without the counter)

usage: python3 py/exact.py          # every rule on a grid of tapes, and the run from blank tape
"""
import re
import sys

TM = "1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA"

# ---- direct simulation (independent of the rules) ----

def table(tm):
    """'1RB0RE_...' -> {(state, read): (write, move, next state) or None}."""
    T = {}
    for i, part in enumerate(tm.split('_')):
        for r in (0, 1):
            t = part[3 * r:3 * r + 3]
            T[('ABCDEF'[i], r)] = None if t[2] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, t[2])
    return T


def canon(cells, pos, st):
    """A configuration as (state, word, head offset), the word with the blanks at both ends stripped."""
    ks = [k for k, v in cells.items() if v]
    if not ks:
        return (st, '', 0)
    lo, hi = min(ks), max(ks)
    return (st, ''.join(str(cells.get(k, 0)) for k in range(lo, hi + 1)), pos - lo)


def cfg(left, st, right):
    """The configuration 0^inf left S> right 0^inf (head on the first symbol of right)."""
    cells = {i: int(c) for i, c in enumerate(left + right)}
    return cells, len(left), st


def run(T, c, n):
    """Run n steps from c = (cells, pos, st). Returns ('ok', c) or ('halt', k) if the k-th step (k <= n) is a halt."""
    cells, pos, st = dict(c[0]), c[1], c[2]
    for k in range(1, n + 1):
        t = T[(st, cells.get(pos, 0))]
        if t is None:
            return 'halt', k
        cells[pos] = t[0]; pos += t[1]; st = t[2]
    return 'ok', (cells, pos, st)


def R(n, m):
    return cfg('', 'A', '011' + '01' * n + '011' + '01' * m)


def Z(k):
    return cfg('', 'A', '011' + '01' * k)


def X(k, j, m=None):
    return cfg('', 'C', '01' * k + '011' + '01' * j + ('' if m is None else '011' + '01' * m))


def tape(s):
    return {'R': R, 'Z': Z, 'X': X}[s[0]](*s[1:])


def micro(s):
    """The rules of lean/Rules.lean: (name, next configuration or 'halt', steps). s = ('R', n, m), ('Z', k) or
    ('X', k, j, m) with m = None for no counter."""
    if s[0] == 'R':
        return 'entry', ('X', 1, s[1], s[2]), 4
    if s[0] == 'Z':
        return 'entry', ('X', 1, s[1], None), 4
    _, k, j, m = s
    if j >= 2:
        return 'pass', ('X', k + 3, j - 2, m), 4 * k + 22
    if m is None:
        return ('zOdd', ('R', k + 1, 1), 4 * k + 26) if j == 1 else ('zEven', 'halt', 2 * k + 5)
    if j == 0:
        return 'endEven', ('R', k + 1, m + 2), 4 * k + 4 * m + 30
    return ('endOdd', ('R', k + 4, m - 1), 8 * k + 46) if m >= 1 else ('endOdd0', ('Z', k + 5), 8 * k + 46)


def nxt(s):
    """One round, the map `next` of lean/Macro.lean, with its number of steps."""
    if s[0] == 'R':
        _, n, m = s
        p = n // 2
        if n % 2 == 0:
            return 'even', ('R', 3 * p + 2, m + 2), 6 * p * p + 32 * p + 4 * m + 38
        if m >= 1:
            return 'odd', ('R', 3 * p + 5, m - 1), 6 * p * p + 44 * p + 58
        return 'odd, m = 0', ('Z', 3 * p + 6), 6 * p * p + 44 * p + 58
    p = s[1] // 2
    if s[1] % 2:
        return 'Z odd', ('R', 3 * p + 2, 1), 6 * p * p + 32 * p + 34
    return 'Z even: halt', 'halt', 6 * p * p + 26 * p + 11   # the last step is the halting one


def shape(cells, pos, st):
    """The R, Z or X configuration this is (head at the left end), or None."""
    if st not in 'AC' or any(v for i, v in cells.items() if i < pos):
        return None
    hi = max([i for i, v in cells.items() if v] + [pos])
    w = ''.join(str(cells.get(i, 0)) for i in range(pos, hi + 1))
    if st == 'A':
        x = re.fullmatch(r'011((?:01)*)011((?:01)*)', w)
        if x:
            return ('R', len(x.group(1)) // 2, len(x.group(2)) // 2)
        x = re.fullmatch(r'011((?:01)*)', w)
        return x and ('Z', len(x.group(1)) // 2)
    x = re.fullmatch(r'((?:01)*)011((?:01)*)011((?:01)*)', w)
    if x:
        return ('X', len(x.group(1)) // 2, len(x.group(2)) // 2, len(x.group(3)) // 2)
    x = re.fullmatch(r'((?:01)*)011((?:01)*)', w)
    return x and ('X', len(x.group(1)) // 2, len(x.group(2)) // 2, None)


def first(T, c, n, kinds):
    """Steps from c to the first configuration of the given kinds, or to the halt (at most n steps)."""
    cells, pos, st = dict(c[0]), c[1], c[2]
    lo = min([i for i, v in cells.items() if v] + [pos])
    for k in range(1, n + 1):
        t = T[(st, cells.get(pos, 0))]
        if t is None:
            return 'halt', k
        cells[pos] = t[0]; pos += t[1]; st = t[2]
        if t[0]:
            lo = min(lo, pos - t[1])
        if pos <= lo and st in 'AC':
            s = shape(cells, pos, st)
            if s and s[0] in kinds:
                return s, k
    return '?', n


def main():
    T = table(TM)
    bad = n = 0
    counts = {}

    def check(name, got, want):
        nonlocal bad, n
        n += 1
        counts[name] = counts.get(name, 0) + 1
        if got != want:
            bad += 1
            print("differs:", name, got, want)

    starts = [('R', a, m) for a in range(0, 40) for m in range(0, 8)] + [('Z', k) for k in range(0, 40)]
    xs = [('X', k, j, m) for k in range(0, 25) for j in range(0, 20) for m in list(range(0, 6)) + [None]]
    for s in starts + xs:
        name, t, N = micro(s)
        check(name, first(T, tape(s), N, 'RZX'), (t, N))
    for s in starts:
        name, t, N = nxt(s)
        check('round: ' + name, first(T, tape(s), N, 'RZ'), (t, N))
    print(f"grid: {n} tapes, each run to its first R, Z or X configuration (the rules of Rules.lean) or its "
          f"first R or Z (a round), or to the halt")
    for k, v in sorted(counts.items()):
        print(f"    {k}: {v}")
    print(f"    failures: {bad}")
    LIMIT = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
    cells, pos, st = {}, 0, 'A'
    s, at, k, nv, nr, runbad = ('Z', 1), 10, 0, 0, 0, 0
    rounds = []
    while at <= LIMIT:
        while k < at:
            t = T[(st, cells.get(pos, 0))]
            cells[pos] = t[0]; pos += t[1]; st = t[2]; k += 1
        nv += 1
        if canon(cells, pos, st) != canon(*tape(s)):
            runbad = 1
            print("run differs at step", at, s)
            break
        if s[0] in 'RZ':
            rounds.append((at, s))
        _, s, N = micro(s)
        at += N
    t, x, ok = 10, ('Z', 1), True
    for at_, s_ in rounds:
        ok = ok and (at_, s_) == (t, x)
        _, x, N = nxt(x)
        t += N
    print(f"run from blank: {nv} configurations R, Z, X up to step {LIMIT:,} at the predicted steps "
          f"({'ok' if not runbad else 'FAILED'}); the {len(rounds)} round starts among them are where the round "
          f"map puts them: {ok}")
    print("    first rounds:", ", ".join(f"{s_[0]}({', '.join(map(str, s_[1:]))}) at {a:,}" for a, s_ in rounds[:7]), "...")
    s, tot, path = ('R', 9, 2), 0, []
    while s != 'halt':
        name, s, N = nxt(s)
        tot += N; path.append(N)
    print(f"R(9, 2) -> halt: {' + '.join(map(str, path))} = {tot} steps by the rounds,", run(T, R(9, 2), 10 ** 6),
          "by simulation")
    return bad + runbad + (not ok)


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
