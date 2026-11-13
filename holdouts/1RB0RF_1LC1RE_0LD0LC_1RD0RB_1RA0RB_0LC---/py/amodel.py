"""The macro map of 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC--- in Python: the same map as `astep` in lean/Full.lean,
with the word in reading order.  A Q configuration is (W, a, G): the tape  W 0 1^(3a) B>0 0^g1 1 0^g2 1 ...  with W
the blocks of the word, a >= 1 the counter's low part, G the raw gap lengths.

astep(W, a, G) returns (kind, W', a', G') for the next Q configuration, or (None, reason) where no rule applies.
kinds: wide, unit, unitB (regular steps), anom1, anom2, anomU, anomUB (anomalies), coll (collision).

`python3 amodel.py race` prints, for a one-block word of B bits and a low part a, whether the first collision
comes before the word runs out again (C) or not (A), with the number of regular steps before it.
"""
import sys

# (t parity, g, U) -> (last blocks appended after 3s ones, new low part, new first gap minus (old gap - 5))
TAB = {
    (0, 0, '0'): ([3], '1', 0), (0, 1, '0'): ([3], '1', 1), (0, 0, '1'): ([5], '1', 1), (0, 1, '1'): ([5], '1', 2),
    (0, 0, '2'): ([7], '1', 2), (0, 0, 'u+3'): ([7], 'u+2', 2), (0, 1, 'u+2'): ([5], 'u+2', 2),
    (1, 0, '0'): ([1, 1, 1], '1', 1), (1, 1, '0'): ([1, 1, 1], '1', 2), (1, 0, '1'): ([1, 1, 3], '1', 2),
    (1, 1, '1'): ([1, 1, 1], '2', 2), (1, 0, 'u+2'): ([1, 1, 3], 'u+2', 2), (1, 1, 'u+2'): ([1, 1, 1], 'u+3', 2),
}


def phi(W):
    W = list(W)
    b = W.pop()
    W[-1] += 2
    return W + [1] * ((b - 1) // 2)


def lead2(G):
    t = 0
    while t < len(G) and G[t] == 2:
        t += 1
    return t


def astep(W, a, G):
    if len(W) == 1:
        if W[0] % 2 or W[0] < 2:
            return (None, 'bad word')
        return ('anom1', [2] + [1] * ((W[0] - 2) // 2), 1, [3 * (a - 1)] + G)
    if len(W) == 2 and W[1] == 1:
        new = [2] + [1] * ((W[0] - 2) // 2)
        if a >= 2:
            return ('anom2', new + [3], 1, [3 * (a - 2) + 1] + G)
        t = lead2(G)
        R = G[t:]
        if not R:
            return ('anomUB', new + [5], t + 1, [])
        if R[0] >= 3:
            return ('anomU', new + [5], t + 1, [R[0] - 3] + R[1:])
        return (None, 'anomaly with a short gap %s' % G[:3])
    W2 = phi(phi(W))
    if a >= 2:
        return ('wide', W2, 1, [3 * a - 4] + G)
    t = lead2(G)
    R = G[t:]
    if not R:
        return ('unitB', W2, t + 2, [])
    if R[0] >= 3:
        return ('unit', W2, t + 2, [R[0] - 3] + R[1:])
    g, R2 = R[0], R[1:]
    U = lead2(R2)
    R3 = R2[U:]
    if R3 and R3[0] < 5:
        return (None, 'collision, next gap %d' % R3[0])
    key = None
    for k in TAB:
        if k[0] == t % 2 and k[1] == g and k[2].isdigit() and int(k[2]) == U:
            key = k
    if key is None:
        for k in TAB:
            if k[0] == t % 2 and k[1] == g and not k[2].isdigit() and U >= int(k[2].split('+')[1]):
                key = k
    C, ap, d = TAB[key]
    u = U - int(key[2].split('+')[1]) if not key[2].isdigit() else 0
    W3 = list(W2)
    W3[-1] += 2
    W3 += [1] * (3 * (t // 2)) + C
    return ('coll', W3, eval(ap, {'u': u}), ([R3[0] - 5 + d] + R3[1:]) if R3 else [])


def race():
    for c in range(2, 9):
        row = []
        for a in range(1, 10):
            cur = list(astep([2 * c + 2], a, [5, 8, 11])[1:])
            n = 0
            while True:
                r = astep(*cur)
                if r[0] is None or r[0] == 'coll' or r[0].startswith('anom'):
                    break
                cur = list(r[1:])
                n += 1
            row.append(('C' if r[0] == 'coll' else 'A' if r[0] else '?') + str(n))
        print('B =', c, ' a = 1..9:', ' '.join(row))


if __name__ == "__main__":
    if sys.argv[1:] == ['race']:
        race()
