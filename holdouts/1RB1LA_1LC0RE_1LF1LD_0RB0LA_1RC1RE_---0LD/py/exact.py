"""mxdys's rules with exact step counts, checked against direct simulation.

    X(b, c) := 0^inf A> 0 1^b 0 0 1^c 0^inf

The rules are `even_rule`, `odd_rule`, `zero_rule`, `halt_rule` of lean/Macro.lean (proved there with Reach1, i.e.
without step counts); the step counts below are checked here against direct simulation only.

usage: python3 py/exact.py          # every rule on a grid of tapes, and the run from blank tape
"""
import re
import sys

TM = "1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD"

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


def X(b, c):
    return cfg('', 'A', '0' + '1' * b + '00' + '1' * c)


def rule(b, c):
    """(name, next (b, c) or 'halt', steps): the map g of lean/Macro.lean, with the steps it takes."""
    if b == 0:
        return 'zero_rule', (c + 2, 1), 2 * c + 33          # c >= 1
    if b == 1:
        return 'halt_rule', 'halt', 13                      # 12 steps to F on a 0, then the halting step
    if b % 2 == 0:
        k = (b - 2) // 2
        return 'even_rule', (5 * k + c + 7, 1), 3 * k ** 3 + 29 * k * k + 95 * k + 102 + 2 * c
    k = (b - 3) // 2
    return 'odd_rule', (k, k + c + 4), 2 * k * k + 12 * k + 19


def is_x(cells, pos, st):
    """Is the configuration of the shape X(b, c): A on a 0 with blank to its left, then 1^b 0 0 1^c and blank?"""
    if st != 'A' or cells.get(pos, 0) or any(v for i, v in cells.items() if i < pos):
        return False
    hi = max([i for i, v in cells.items() if v] + [pos])
    return re.fullmatch(r'1*001*', ''.join(str(cells.get(i, 0)) for i in range(pos + 1, hi + 1))) is not None


def first_x(T, c, n):
    """Steps from c to the first configuration of the shape X(b, c) or the halt, looking at most n steps."""
    cells, pos, st = dict(c[0]), c[1], c[2]
    for k in range(1, n + 1):
        t = T[(st, cells.get(pos, 0))]
        if t is None:
            return 'halt', k
        cells[pos] = t[0]; pos += t[1]; st = t[2]
        if st == 'A' and cells.get(pos, 0) == 0 and is_x(cells, pos, st):
            return canon(cells, pos, st), k
    return '?', n


def main():
    T = table(TM)
    bad = n = 0
    counts = {}
    for b in range(0, 41):
        for c in range(1 if b == 0 else 0, 31):
            name, t, N = rule(b, c)
            r, k = first_x(T, X(b, c), N + 1)
            ok = (r == 'halt' and k == N) if t == 'halt' else (r == canon(*X(*t)) and k == N)
            n += 1
            counts[name] = counts.get(name, 0) + 1
            if not ok:
                bad += 1
                print("differs:", (b, c), name, t, N, r, k)
    grid_bad = bad
    print(f"grid: {n} tapes, each run to its first X(b', c') or the halt "
          f"({', '.join(f'{k} {v}' for k, v in sorted(counts.items()))}), {bad} failures")
    LIMIT = int(float(sys.argv[1])) if len(sys.argv) > 1 else 2 * 10 ** 7
    cells, pos, st = {}, 0, 'A'
    s, at, nv, k = (3, 1), 45, 0, 0
    while at <= LIMIT:
        while k < at:
            t = T[(st, cells.get(pos, 0))]
            cells[pos] = t[0]; pos += t[1]; st = t[2]; k += 1
        nv += 1
        if canon(cells, pos, st) != canon(*X(*s)):
            bad += 1; grid_bad = -1
            print("run differs at step", at, s)
            break
        last = s
        _, s, N = rule(*s)
        at += N
    print(f"run from blank: {nv} configurations X(b, c) at their predicted step counts up to step {LIMIT:,} "
          f"(the last X{last} at step {k:,}), {'ok' if grid_bad >= 0 else 'FAILED'}")
    s, tot = (2, 6), 0
    while s != 'halt':
        tot += rule(*s)[2]; s = rule(*s)[1]
    print("X(2, 6) -> halt:", tot, "steps by the rules,", run(T, X(2, 6), 10 ** 5), "by simulation")
    return bad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
