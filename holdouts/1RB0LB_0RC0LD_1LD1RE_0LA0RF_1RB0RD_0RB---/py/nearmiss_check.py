"""nearmiss_check.py ROUND DELTA [DEPTH [H]]: an exact, whole-word check of one near miss found by c/nearmiss.c.
Runs the exact pass (Python integers) for ROUND-1 rounds; in round ROUND adds DELTA visits to the count at the first
block start at least DEPTH cells before the word end (DELTA = 'x2' doubles it, '/2' halves it); then runs H more
whole rounds on the changed word and reports the first 1111 / 11100 / 111."""
import sys
from endbfs import strip


def rnd(T, inject=None):
    """one round on the whole word T (list, modified in place); inject = (depth, f) changes the count once."""
    T[:0] = [1, 0]
    E = strip(T)
    p, n, done, met111 = 0, 1, inject is None, None
    while n > 0:
        if len(T) <= p + 8:
            T.extend([0] * 64)
        w = T
        if w[p] != 0 and not done and p >= E - inject[0]:
            done = True; n0 = n; n = inject[1](n); print(f'  count at cell {p} ({E - p} before the end): {n0} -> {n}')
        if w[p] == 0:
            w[p] = 1; n -= 1
        elif w[p + 2] == 0:
            m = n - 1; w[p] = m & 1; w[p + 1] = 0; n = 1 + m // 2; p += 3
        elif w[p + 1] == 0 and w[p + 3] == 0:
            n *= 2; p += 4
        elif w[p + 1] == 0:
            w[p] = 0; w[p + 2] = 0; w[p + 3] = 1; n -= 1
        else:
            met111 = (p, E - p, ''.join(map(str, T[p:p + 6])))
            if w[p + 3] == 1:
                return 'halt (1111)', met111
            if w[p + 4] == 1:
                w[p + 1] = 0; n -= 1
            else:
                return 'stuck (11100)', met111
    return ('ok, met 111 (11101 rule)' if met111 else 'ok'), met111


def main():
    R = int(sys.argv[1]); d = sys.argv[2]
    depth = int(sys.argv[3]) if len(sys.argv) > 3 else 60
    H = int(sys.argv[4]) if len(sys.argv) > 4 else 6
    f = (lambda n: 2 * n) if d == 'x2' else (lambda n: n // 2) if d == '/2' else (lambda n: n + int(d))
    T = [1]
    for _ in range(R - 1):
        res, _m = rnd(T)
        assert res == 'ok'
    print(f'round {R}, changed:')
    res, m = rnd(T, (depth, f)); print('  ', res, m or '')
    for j in range(1, H + 1):
        res, m = rnd(T); print(f'round {R + j}:', res, m or '')
        if not res.startswith('ok'):
            break


if __name__ == '__main__':
    main()
