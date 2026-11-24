"""The neighbour invariants of the two wall counters (24 November 2026).

1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA (walls W0..W3, phase 0..3): for three neighbouring digits w y x,
    Q = run(x) + h(x) + g(y) + 4*phase(w) mod 16,   h = (0, 1, 3, 3), g = (0, 0, 2, 2)
1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC--- (walls S0..S3): for two neighbouring digits y x,
    K = phase(y) + run(x) + [x is S2 or S3] mod 4
Both are unchanged by every sweep while the digits live (lean/Invariant.lean of each machine proves it for the
abstract carry rules).  At a merge (x an S1 / W1 whose left run is used up) the twin's left neighbour is in phase K;
for this machine y is W0 (Q = 1 mod 4) or W2 (Q = 3 mod 4), and w is in phase (Q - 1 - g(y)) / 4.

    python3 invariant.py check SWEEPS [twin]    over digits.py sweeps from 3e6 steps, count the neighbour tuples
                                                whose invariant changed in plain sweeps (expected: none)
    python3 invariant.py states                 the invariant's values in the saved deep states
"""
import collections
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
M1 = '1RB0LF_1LC0RC_1RA1LD_0RB0LE_1LC0LB_---1LA'
M2 = '1RB1LA_0LC0RE_1LD1LB_1RE1LF_1RC0RA_0RC---'
H = (0, 1, 3, 3)
G = (0, 0, 2, 2)


def phases(prefix):
    return {prefix + str(i): i for i in range(4)}


def inv_main(D):
    P = phases('W')
    return [(r + H[P[x]] + G[P[y]] + 4 * P[w]) % 16 if all(t in P for t in (w, y, x)) else None
            for (w, _), (y, _), (x, r) in zip(D, D[1:], D[2:])]


def inv_twin(D):
    P = phases('S')
    return [(P[y] + r + (P[x] >= 2)) % 4 if y in P and x in P else None for (y, _), (x, r) in zip(D, D[1:])]


def check(sweeps, twin):
    m = M2 if twin else M1
    sys.path.insert(0, os.path.join(HERE, '..', '..', m, 'py'))
    import digits
    sp = digits.SPEC
    carry = ('S3',) if twin else ('W3',)
    f = inv_twin if twin else inv_main
    st = None
    for step, cells in digits.direct_samples(sp, 3e6):
        a = sp.parse_cells(cells)
        if a:
            st = (a[0], list(a[1]), a[2], a[3])
    n = changed = other = 0
    for _ in range(sweeps):
        r = sp.sweep(st, carry=carry)
        if r[0] != 'ok':
            print('STOP', r[0])
            return
        new = r[1]
        P = phases('S' if twin else 'W')
        top = 1 if st[1][0][0] not in P else 0  # the twin's leading S is not a phase wall
        plain = len(new[1]) == len(st[1]) and all(
            x in P and y in P and (P[y] - P[x]) % 4 in (0, 1) for (x, _), (y, _) in zip(st[1][top:], new[1][top:]))
        if plain:
            for a, b in zip(f(st[1]), f(new[1])):
                if a is not None and b is not None:
                    n += 1
                    changed += a != b
        else:
            other += 1
        st = new
    print(f"{sweeps} sweeps, {sweeps - other} plain (every digit a phase wall, stepping by 0 or 1): "
          f"{n} neighbour tuples followed, invariant changed in {changed}; {other} sweeps with a merge, birth or "
          "special wall not counted")


def states():
    for m, f, fn in ((M2, 'state_2.88e90.json', inv_twin), (M1, 'state_3.55e38.json', inv_main),
                     (M1, 'state_4.79e63.json', inv_main)):
        d = json.load(open(os.path.join(HERE, '..', '..', m, 'py', f)))
        D = [(w, int(r)) for w, r in d['digits']]
        print(m, f, dict(sorted(collections.Counter(v for v in fn(D) if v is not None).items())))


if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check(int(float(sys.argv[2])), 'twin' in sys.argv[3:])
    else:
        states()
