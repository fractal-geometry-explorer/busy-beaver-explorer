"""Antihydra's recursion with exact step counts, as on the bbchallenge wiki, checked against direct simulation.

    A(a, b)    := 0^inf 1^a 0 1^b E> 0^inf               (the wiki's family)
    Q(p, a, b) := 0^inf 1^p 0 1^a 0 1^b B> 0^inf         (lean/Macro.lean; A(a, b + 1) is Q(a, b, 2) four steps later)

usage: python3 py/exact.py          # every rule on a grid of tapes, and the run from blank tape
"""
import re
import sys

TM = "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

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


def A(a, b):
    return cfg('1' * a + '0' + '1' * b, 'E', '')


def Q(p, a, b):
    return cfg('1' * p + '0' + '1' * a + '0' + '1' * b, 'B', '')


def tape(s):
    return A(*s[1:]) if s[0] == 'A' else Q(*s[1:])


def wiki_rule(a, b):
    """The wiki's rules on A(a, b), b >= 2: (name, next ('A', a', b') or 'halt', steps)."""
    if b % 2 == 0:
        j = b // 2
        return 'even', ('A', a + 2, 3 * j + 2), 2 * a + 3 * j * j + 12 * j + 11
    j = (b - 1) // 2
    if a == 0:
        return 'halt', 'halt', 3 * j * j + 9 * j            # 3j^2 + 9j - 1 steps to F on a 0, then the halting step
    return 'odd', ('A', a - 1, 3 * j + 3), 3 * j * j + 12 * j + 5


def lean_rule(s):
    """The rules of lean/Rules.lean on Q(p, a, b) (b >= 2), with their step counts."""
    _, p, a, b = s
    c = b - 2
    if a >= 3:
        return 'sweep (inner)', ('Q', p, a - 2, b + 3), 2 * (b - 1) + 13
    if a == 1:
        return 'odd end (odd_a + odd_b, odd0)', ('Q', p + 2, c + 4, 2), 2 * c + 2 * p + 26
    if p >= 1:
        return 'even end (even)', ('Q', p - 1, c + 5, 2), 2 * c + 20
    return 'halt (halt0)', 'halt', c + 8                   # c + 7 steps to F on a 0, then the halting step


def shape(cells, pos, st, kind):
    """The A or Q configuration this is (head at the right end, right of everything), or None."""
    if st != ('E' if kind == 'A' else 'B') or any(v for i, v in cells.items() if i >= pos):
        return None
    lo = min([i for i, v in cells.items() if v] + [pos])
    w = ''.join(str(cells.get(i, 0)) for i in range(lo, pos))
    if kind == 'A':
        x = re.fullmatch(r'0*?(1*)0(1*)', '0' + w)
        return x and ('A', len(x.group(1)), len(x.group(2)))
    x = re.fullmatch(r'0*?(1*)0(1*)0(1*)', '0' + w)
    return x and ('Q', len(x.group(1)), len(x.group(2)), len(x.group(3)))


def first(T, c, n, kind):
    """Steps from c to the first configuration of the given family, or to the halt (at most n steps)."""
    cells, pos, st = dict(c[0]), c[1], c[2]
    for k in range(1, n + 1):
        t = T[(st, cells.get(pos, 0))]
        if t is None:
            return 'halt', k
        cells[pos] = t[0]; pos += t[1]; st = t[2]
        f = shape(cells, pos, st, kind)
        if f:
            return f, k
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

    for a in range(0, 30):
        for b in range(2, 50):
            name, t, N = wiki_rule(a, b)
            check('A ' + name, first(T, A(a, b), N, 'A'), (t, N))
            check('A -> Q', first(T, A(a, b), 4, 'Q'), (('Q', a, b - 1, 2), 4))
    for p in range(0, 20):
        for a in range(1, 30):
            for b in range(2, 14):
                name, t, N = lean_rule(('Q', p, a, b))
                check('Q ' + name, first(T, Q(p, a, b), N, 'Q'), (t, N))
    print(f"grid: {n} tapes, each run to its first configuration of the same family or the halt")
    for k, v in sorted(counts.items()):
        print(f"    {k}: {v}")
    print(f"    failures: {bad}")
    # the run from blank tape: every A configuration (the wiki's rules) at its predicted step
    LIMIT = 10 ** 7
    cells, pos, st = {}, 0, 'A'
    s, at, nv, k, runbad = ('A', 0, 4), 11, 0, 0, 0
    seen = []
    while at <= LIMIT:
        while k < at:
            t = T[(st, cells.get(pos, 0))]
            cells[pos] = t[0]; pos += t[1]; st = t[2]; k += 1
            f = shape(cells, pos, st, 'A')
            if f and k < at:
                runbad = 1
                print("run: an A configuration the rules skip, at step", k, f)
        nv += 1
        if canon(cells, pos, st) != canon(*tape(s)):
            runbad = 1
            print("run differs at step", at, s)
            break
        seen.append((at, s[1], s[2]))
        _, s, N = wiki_rule(s[1], s[2])
        at += N
    print(f"run from blank: all {nv} configurations A(a, b) up to step {LIMIT:,} come at the predicted steps, "
          f"and no others: {'ok' if not runbad else 'FAILED'}")
    print("    first:", ", ".join(f"A{x[1:]} at {x[0]}" for x in seen[:6]), "...", f"A{seen[-1][1:]} at {seen[-1][0]:,}")
    for s in [('A', 2, 5)]:
        tot, cur, path = 0, s, []
        while cur != 'halt':
            name, nx, N = wiki_rule(cur[1], cur[2])
            tot += N; path.append(N); cur = nx
        print(f"A{s[1:]} -> halt: {' + '.join(map(str, path))} = {tot} steps by the rules,",
              run(T, A(*s[1:]), 10 ** 5), "by simulation")
    return bad + runbad


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
