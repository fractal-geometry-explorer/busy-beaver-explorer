"""The pass map of 1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LA---, exact (tape and step count).

Sample the run each time the head arrives at the left end of the tape in state A (and, during a rebuild, in E).
Write `a` for the word 10.  At such a moment the tape is

    a 0 a^c  1^k1 a^n1  1^k2 a^n2  ...  1^kr a^nr          (c >= 0)

(blank on both sides; for c = -1 the head is `a 1 a 1^k1 ...`).  The state of the run is the counter c and the list of
pairs P = [(k1, n1), ..., (kr, nr)] (k in 1..3).  A normal tape alternates separators (2,1) = `1 1 0` and blocks
(1, m) = `1 (10)^m`, ending with the end marker (2,1); the block (2,1)(1,m) is the leftward-pass encoding of the
right-end block (10)^(m+2) 1.  The first place where this alternation breaks is the *frontier*, and one pass (left end
to left end) rewrites the tape only there (and at the counter):

  a   counter phase   c, [(1,q) ...]  q >= 1          ->  c+3, [(1,q-1) ...]                 6c + 36 steps
  b   counter ends    c, [(3,1),(1,m) ...]            ->  c-1, [(2,1),(1,4),(1,m-1) ...]       6c + 54
  c   block grows     (1,p),(1,q)  q >= 1             ->  (1,p+4),(1,q-1)                     6c + 20F + 6M + 6p + 56
  d   next block      (1,p),(3,1),(1,m)               ->  (1,p),(2,1),(1,4),(1,m-1)            6c + 20F + 6M + 54
  e   block at end    (1,p),(3,1) END                 ->  (1,p),(2,1),(1,2),(2,1) END          6c + 20F + 6M + 50
  g   timer           ... (2,1) END, no frontier      ->  ... (2,1),(1,1),(2,1) END            6c + 20F + 6M + 44
  f   carry G         (2,q),(2,1),(1,m)  (q != 1)     ->  (2,1),(1,q+3),(2,m)                  6c + 20F + 6M + 8q + 48
  f1  carry G(1)      ... (1,x),(2,1),(2,1),(1,m)     ->  ... (1,x),(2,1),(1,4),(2,m)          6c + 20F + 6M + 56
  h   G(1) at end     ... (1,x),(2,1),(2,1) END       ->  ... (1,x),(2,1),(1,4),(1,0)
  i   tail            ... (1,p),(1,0) END             ->  ... (1,p+3),(2,1) END
  f2  G meets X       (2,q),(1,x) ...                 ->  (2,1),(1,x+3) ... and the pass goes on to the end (rule g)

and a pair (1,0) merges into the next pair: (1,0),(k,n) = (k+1,n).  F and M are the number and the sum of the m of
the blocks (2,1)(1,m) left of the frontier.  When c = -1 (the timer ran out) the next two passes are a rebuild:
the first applies the frontier rule as if c were 0 (4 steps fewer than at c = 0, seen for rules d, g), the second (70 steps) turns the first
block (2,1)(1,m1) into the counter phase:  c = 5, P = [(1, m1-2)] + rest.

Rules h, i, f1, f2 and their costs are rare (seen 1 to 5 times up to 1.1e9 steps); the others are seen thousands of
times.  `check` compares every pass with the plain machine (c/lt1.c output) tape and step count.

usage: python3 passes.py check SAMPLES     SAMPLES = output of  lt1 MACHINE STEPS  (left-end arrivals)
"""
import sys


class NoRule(Exception):
    pass


def merge(P):
    i = 0
    while i < len(P) - 1:
        k, n = P[i]
        if n == 0:
            k2, n2 = P[i + 1]
            P = P[:i] + [(k + k2, n2)] + P[i + 2:]
            continue
        i += 1
    return P


def frontier(P):
    """Index of the first pair that breaks the alternation (2,1),(1,m),(2,1),...,(2,1)END; len(P)-1 if none."""
    for j, (k, n) in enumerate(P):
        if j % 2 == 0:
            if (k, n) != (2, 1) or j == len(P) - 1:
                return j
        else:
            if k != 1 or (j + 1 < len(P) and P[j + 1][0] == 1):
                return j
    return len(P)


def prefix(P, j):
    Fm = [P[i + 1][1] for i in range(0, j - 1, 2)]
    return len(Fm), sum(Fm)


def step(c, P):
    """One pass: (c', P', rule, steps)."""
    P = list(P)
    if c == -1:
        c2, P2, r, s = step(0, P)
        s = None if s is None else s - 4
        assert P2[0] == (2, 1) and P2[1][0] == 1
        return 5, [(1, P2[1][1] - 2)] + P2[2:], 'R' + r, None if s is None else s + 70
    if P[0][0] == 1:
        q = P[0][1]
        P[0] = (1, q - 1)
        return c + 3, merge(P), 'a', 6 * c + 36
    if P[0] == (3, 1):
        m = P[1][1]
        P[0:2] = [(2, 1), (1, 4), (1, m - 1)]
        return c - 1, merge(P), 'b', 6 * c + 54
    j = frontier(P)
    F, M = prefix(P, j)
    base = 6 * c + 20 * F + 6 * M
    k, n = P[j]
    if j % 2 == 0 and j == len(P) - 1 and P[j] == (2, 1):
        P[j:j + 1] = [(2, 1), (1, 1), (2, 1)]
        return c - 1, P, 'g', base + 44
    if j % 2 == 1 and k == 1 and j + 2 == len(P) and P[j + 1] == (1, 0):
        P[j:j + 2] = [(1, n + 3), (2, 1)]
        return c - 1, P, 'i', None
    if j % 2 == 1 and k == 1 and P[j + 1][0] == 1 and P[j + 1][1] >= 1:
        p, q = n, P[j + 1][1]
        P[j:j + 2] = [(1, p + 4), (1, q - 1)]
        return c - 1, merge(P), 'c', base + 6 * p + 56
    if j % 2 == 0 and (k, n) == (3, 1):
        if j == len(P) - 1:
            P[j:j + 1] = [(2, 1), (1, 2), (2, 1)]
            return c - 1, P, 'e', base + 50
        if P[j + 1][0] == 1:
            m = P[j + 1][1]
            P[j:j + 2] = [(2, 1), (1, 4), (1, m - 1)]
            return c - 1, merge(P), 'd', base + 54
    if j % 2 == 0 and k == 2 and n != 1:
        q = n
        if j + 2 < len(P) and P[j + 1] == (2, 1) and P[j + 2][0] == 1:
            m = P[j + 2][1]
            P[j:j + 3] = [(2, 1), (1, q + 3), (2, m)]
            return c - 1, P, 'f', base + 8 * q + 48
        if j + 1 < len(P) and P[j + 1][0] == 1:
            x = P[j + 1][1]
            P[j:j + 2] = [(2, 1), (1, x + 3)]
            P = merge(P)
            j2 = frontier(P)
            if j2 == len(P) - 1 and P[j2] == (2, 1):
                P[j2:j2 + 1] = [(2, 1), (1, 1), (2, 1)]
                return c - 1, P, 'f2', None
    if j % 2 == 1 and (k, n) == (2, 1):
        if j + 1 < len(P) and P[j + 1][0] == 1:
            m = P[j + 1][1]
            P[j:j + 2] = [(1, 4), (2, m)]
            return c - 1, P, 'f1', base + 56
        if j == len(P) - 1:
            P[j:j + 1] = [(1, 4), (1, 0)]
            return c - 1, P, 'h', None
    raise NoRule(f'c={c} frontier {j}: {P[max(0, j - 3):j + 4]}')


def sample(fields):
    """The (c, P) of one left-end sample, as printed by lt1 (tokens a^k, 0, 1^k)."""
    t = []
    for f in fields:
        s, _, k = f.partition('^')
        t.append((s, int(k) if k else 1))
    if t[0] == ('a', 1) and t[1] == ('0', 1):
        c, rest = (t[2][1], t[3:]) if t[2][0] == 'a' else (0, t[2:])
    elif t[:3] == [('a', 1), ('1', 1), ('a', 1)]:
        c, rest = -1, [('1', 2), ('a', 1)] + t[3:]
    else:
        raise ValueError(f'not a sample: {t[:4]}')
    P, i = [], 0
    while i < len(rest):
        s, k = rest[i]
        assert s == '1'
        if i + 1 < len(rest):
            P.append((k, rest[i + 1][1]))
            i += 2
        else:
            P.append((k, 0))
            i += 1
    return c, P


def check(path, start=440):
    prev, ok, unc, used = None, 0, 0, {}
    for line in open(path):
        f = line.split()
        if f[1] != 'A' or int(f[0]) < start:
            continue
        c, P = sample(f[2:])
        s = int(f[0])
        if prev:
            pc, pP, ps = prev
            c2, P2, r, st = step(pc, pP)
            if (c2, P2) != (c, P):
                raise SystemExit(f'pass from step {ps}: rule {r} predicts {c2} {P2[:12]}, run has {c} {P[:12]}')
            if st is not None and st != s - ps:
                raise SystemExit(f'pass from step {ps}: rule {r} predicts {st} steps, run took {s - ps}')
            if st is None:
                unc += 1
            ok += 1
            used[r] = used.get(r, 0) + 1
        prev = (c, P, s)
    print(f'{ok} passes from step {start} to {prev[2]} follow the rules ({unc} of them with no step formula); rules used: {used}')


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check(sys.argv[2])
