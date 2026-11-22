"""Which gaps a jump of a `10` defect can turn into the danger pattern (1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB).

lean/Gaps.lean proves: at a jump over y^j x^(a+1) with rest C (L = j + a + 2), the run of y words at the next jump
covers the first r coefficients (defect included) iff C agrees with mask L there, mask L [k] = 1 iff k & L == 0
(`next_jump_run`).  This script checks that statement with the jump map of py/fmap.py, counts how few gaps can reach the
danger pattern in one jump, and reads the real run (output of c/turns.c, as for py/defect_life.py).

usage: python3 jump_gaps.py [turns.txt]
"""
import itertools
import sys


def mask(L, n):
    return [1 if k & L == 0 else 0 for k in range(n)]


def times(C, L):  # multiply by (1 + z)^L, truncated to len(C)
    for _ in range(L):
        C = [C[0]] + [C[i] ^ C[i - 1] for i in range(1, len(C))]
    return C


def run(W):  # length of the leading run of 1s
    r = 0
    while r < len(W) and W[r]:
        r += 1
    return r


def agree(u, v):
    r = 0
    while r < len(u) and r < len(v) and u[r] == v[r]:
        r += 1
    return r


def exhaustive():
    bad = n = 0
    for N in range(1, 13):
        for L in range(1, 41):
            for t in itertools.product([0, 1], repeat=N - 1):
                C = [1] + list(t)
                n += 1
                bad += run(times(C, L)) != agree(C, mask(L, N))
    print(f"next run = agreement of C with mask L: {n} cases (|C| <= 12, L <= 40), mismatches {bad}")


def counts():
    print("gaps of n words (after the defect) that are dangerous at the next jump, of 2^n:")
    for n in range(4, 21, 4):
        tot = 0
        for j in range(n):
            for a in range(n - j):
                L = j + a + 2
                if L <= n:  # C non-empty: one C per (j, a) makes the next gap all y
                    tot += 1
        print(f"  n = {n:2}: {tot} of {2 ** n}")


def data(path):
    sys.path.insert(0, __file__.rsplit('/', 1)[0])
    from defect_life import deep_sweeps
    rows = deep_sweeps(path)
    out = []
    ev, cur = [], []
    for r in rows:
        if r is None:
            if cur:
                ev.append(cur)
            cur = []
            continue
        k, P, G = r
        if P[-1] == 'y':
            j = run([c == 'y' for c in G])
            a = run([c == 'x' for c in G[j:]])
            cur.append((k, j, a, len(G), [int(c == 'y') for c in G[j + a:]]))
    if cur:
        ev.append(cur)
    ok = tot = 0
    for life in ev:
        for (k, j, a, g, C), (k2, j2, _, g2, _) in zip(life, life[1:]):
            L = j + a + 1
            ag = agree(C, mask(L, len(C)))
            tot += 1
            ok += ag == j2 + 1 or (ag >= len(C) and j2 + 1 >= len(C))
            out.append(f"  step {k}: j={j} L={L} gap {g}: C={''.join('y' if c else 'x' for c in C)} "
                       f"mask={''.join('y' if c else 'x' for c in mask(L, len(C)))} agree {ag} -> next run {j2} "
                       f"(needs {g2} for danger)")
    print(f"real run: {ok} of {tot} next-jump runs equal (agreement of C with mask L) - 1")
    print('\n'.join(out))


if __name__ == '__main__':
    exhaustive()
    counts()
    if len(sys.argv) > 1:
        data(sys.argv[1])
