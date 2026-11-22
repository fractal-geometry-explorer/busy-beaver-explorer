"""The fuel a round's defect needs, and the doubler heights behind it (see "Seventh pass" in the README).

usage: python3 py/fuel.py ROUNDS [RANDOM_TRIALS=20000]      the run, with the token rules of py/tokz.py
       python3 py/fuel.py --dump DUMP                     one round-start tape written by c/toksim.cpp

nx W is the number of visits of A after which the tape x W has no defect left (lean/Fuel.lean: nx, ne, n0, and
the theorem `fuel` that they are enough). A round tape is L^m x U (or L^m z U), and the round's single visit of A
reaches the defect as 2^m visits, so the defect dies iff nx U <= 2^m. Printed: nx U and the margin m - log2(nx U).

Heights: h(p) = (number of L) - (number of digits) before token p. The script also checks, for every round k of
the run and for random tapes L^m x W, that two rounds never lower the height at any token index p up to where the
first round's defect died: h_{k+2}(p) >= h_k(p).
"""
import random
import sys

sys.setrecursionlimit(1000000)
import tokz
from tokz import T


def need(W):
    """nx, ne, n0 of every suffix of the clean token list W (lean/Fuel.lean), as lists indexed by start position."""
    n = len(W)
    nx, ne, n0 = [0] * (n + 1), [0] * (n + 1), [0] * (n + 1)
    nx[n] = 1
    for i in range(n - 1, -1, -1):
        t = W[i]
        if t == 'O':
            nx[i], ne[i], n0[i] = 2 * nx[i + 1] + 1, 2 * ne[i + 1] + 1, 0
        elif t == 'L':
            nx[i], ne[i], n0[i] = (nx[i + 1] + 1) // 2, (ne[i + 1] + 1) // 2, 2 * (nx[i + 1] - 1)
        elif t == 'I':
            nx[i], ne[i], n0[i] = ne[i + 1] + 1, n0[i + 1], 2 * (2 * ne[i + 1] + 1)
        else:
            raise ValueError('not a clean tape: ' + t)
    return nx, ne, n0


def heights(s):
    b, hs = 0, []
    for t in s:
        hs.append(b)
        b += 1 if t == 'L' else (-1 if t in 'OI' else 0)
    return hs


def round_need(s):
    """For a round-start tape L^m d U: (m, need of d U in visits arriving at d)."""
    m = 0
    while s[m] == 'L': m += 1
    d, U = s[m], s[m + 1:]
    nx, ne, _ = need(U)
    if d == 'x': return m, nx[0]
    if d == 'z': return m, 1 + 2 * ne[0] + 1     # z W: one visit makes it 1 W, which needs 2 ne W + 1
    if d == '1': return m, 2 * ne[0] + 1
    raise ValueError(d)


def one_round(s):
    T[:] = s
    tokz.stats['die'] = []
    tokz.An(1, 0)
    d = tokz.stats['die']
    K = d[-1][2] if d else None
    T.insert(0, 'x'); tokz.norm()
    while T and T[-1] == 'O': T.pop()
    return list(T), K


def run(R):
    s = list('LLLzLLOLOI')          # round 6, as in py/tokz.py
    hist = {}
    worst_margin = None
    for k in range(6, R + 1):
        if k >= 9:
            m, nd = round_need(s)
            margin = m - (nd.bit_length() - 1)
            if nd > 2 ** m: print('round', k, ': the defect needs', nd, 'visits and gets 2^%d' % m)
            if k >= 12 and (worst_margin is None or margin < worst_margin[1]): worst_margin = (k, margin)
            if k % 500 == 0 or k <= 14: print('round %6d: m = %5d, need nx U = %d, margin m - log2(need) = %d' % (k, m, nd, margin))
        s2, K = one_round(s)
        hist[k] = (s, K)
        s = s2
    print('smallest margin from round 12 on: %d (round %d)' % (worst_margin[1], worst_margin[0]))
    bad = 0
    for k in range(40, R - 1):
        (a, K), (b, _) = hist[k], hist[k + 2]
        ha, hb = heights(a), heights(b)
        if min(hb[p] - ha[p] for p in range(1, min(K, len(hb)))) < 0: bad += 1
    print('rounds 40..%d: rounds k with h_{k+2}(p) < h_k(p) somewhere before the death point: %d' % (R - 2, bad))


def random_check(N, seed=2):
    random.seed(seed)
    gens = ['OIL', 'OOIIL', 'LLLOI', 'OL', 'IL', 'OI']
    bad = tot = 0
    for _ in range(N):
        m = random.randint(25, 60)
        g = random.choice(gens)
        s = ['L'] * m + ['x'] + [random.choice(g) for _ in range(random.randint(5, 120))]
        try:
            s1, K = one_round(s)
            if K is None: continue
            s2, _ = one_round(s1)
        except Exception:
            continue                # two defects met, or the defect did not die: not a test case
        h, h2 = heights(s), heights(s2)
        tot += 1
        if min(h2[p] - h[p] for p in range(m, min(K, len(h2)))) < 0: bad += 1
    print('random tapes L^m x W: %d of %d with a height lowered in two rounds' % (bad, tot))


if __name__ == '__main__':
    if sys.argv[1] == '--dump':
        s = list(open(sys.argv[2]).read().strip())
        m, nd = round_need(s)
        print('m = %d, need = %d (log2 %d), margin %d' % (m, nd, nd.bit_length() - 1, m - (nd.bit_length() - 1)))
    else:
        run(int(sys.argv[1]))
        random_check(int(sys.argv[2]) if len(sys.argv) > 2 else 20000)
