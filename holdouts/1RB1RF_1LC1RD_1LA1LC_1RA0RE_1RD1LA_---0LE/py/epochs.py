"""The epoch map of 1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE.

E(g, R) is the configuration 0^inf A> 0 1 0^g R (state A on the blank cell left of the tape, one 1, a gap of g
zeros, the rest R).  The run from blank tape passes E(8, 1111), E(18, ...), ...; from E(g, R) the next one is
E(3g/2 + c, R') where (c, R') depends only on g mod 4 and R (checked for g, g+4, g+8, g+12 and along the real run).

usage:
  python3 epochs.py direct N        the first N epochs of the real run (run-length simulator, sweeps jumped by
                                    the proved rule of lean/Phase.lean), each compared with the class map
  python3 epochs.py uniform G R     the class map at g = G, G+4, G+8, G+12 for the right part R ("1^11 0^8 1^4 ...")
  python3 epochs.py abstract N      N epochs of the class map from the epoch at step 8,131,847 (g = 4206), with g
                                    an exact integer: the size of g, the constant c and the length of R
"""
import math, sys
from rle import R as Sim

M = "1RB1RF_1LC1RD_1LA1LC_1RA0RE_1RD1LA_---0LE"


def fmt(S):
    return ' '.join(f"{x}^{c}" if c > 1 else str(x) for x, c in S)


def parse(s):
    out = []
    for t in s.split():
        a, b = (t.split('^') + ['1'])[:2]
        out.append([int(a), int(b)])
    return out


def is_x(r):
    """X(n, m): 0^inf A> 0 1^n 000 1111 0^m ...; returns (n, m)."""
    if r.q != 0 or r.L:
        return None
    S = r.R[::-1]
    if len(S) >= 5 and S[0] == [0, 1] and S[1][0] == 1 and S[2] == [0, 3] and S[3] == [1, 4] and S[4][0] == 0:
        return S[1][1], S[4][1]


def is_e(r):
    if r.q != 0 or r.L:
        return None
    S = r.R[::-1]
    if len(S) >= 3 and S[0] == [0, 1] and S[1] == [1, 1] and S[2][0] == 0:
        return S[2][1], S[3:]


def advance(r, maxmoves=10 ** 8):
    """Run to the next epoch with g != 6 (the epoch E(6, ...) is a step inside every epoch); None on a halt."""
    moves = 0
    while moves < maxmoves:
        x = is_x(r)
        if x and x[1] >= 8:      # j sweeps at once: lean/Phase.lean `sweeps`, `sweeps_steps_eq`
            n, m = x
            j = (m - 4) // 4
            r.R[-2][1] += 6 * j
            r.R[-5][1] -= 4 * j
            r.steps += j * (3 * n + 44) + 9 * j * (j - 1)
        if not r.step():
            return None
        moves += 1
        e = is_e(r)
        if e and e[0] != 6 and moves > 5:
            return e[0], fmt(e[1])
    raise RuntimeError("no epoch")


def epoch(g, Rs):
    r = Sim(M)
    r.R = [list(x) for x in reversed([[0, 1], [1, 1], [0, g]] + parse(Rs))]
    res = advance(r)
    return ('HALT', r.steps) if res is None else (res[0], r.steps, res[1])


def class_map(g, Rs):
    """(c, R') for E(g, R), computed at a representative of g mod 4 large enough for R."""
    cells = sum(c for _, c in parse(Rs))
    G = 600 + 12 * cells
    G -= G % 4
    rep = G + (g % 4)
    res = epoch(rep, Rs)
    if res[0] == 'HALT':
        return None
    return res[0] - 3 * rep // 2, res[2]


def main(argv):
    if argv[0] == "direct":
        r = Sim(M)
        prev = None
        for i in range(int(argv[1])):
            res = advance(r)
            if res is None:
                print("HALT", r.steps)
                return
            g, Rs = res
            if prev and prev[0] >= 100:
                c, R2 = class_map(*prev)
                ok = (3 * prev[0] // 2 + c == g) and R2 == Rs
                print(r.steps, g, Rs, "class map agrees" if ok else "MISMATCH", flush=True)
            else:
                print(r.steps, g, Rs, flush=True)
            prev = (g, Rs)
    elif argv[0] == "uniform":
        G, Rs = int(argv[1]), argv[2]
        for t in range(4):
            g = G + 4 * t
            res = epoch(g, Rs)
            print(g, res if res[0] == 'HALT' else (res[0], res[0] - 3 * g // 2, res[2]))
    elif argv[0] == "abstract":
        g, Rs = 4206, "1^11 0^8 1^4 0^24 1^4 0^12 1^4 0^18 1^8 0^28 1^4 0^2 1^4"
        for i in range(int(argv[1])):
            cm = class_map(g, Rs)
            if cm is None:
                print("HALT at abstract epoch", i, "g =", g, Rs)
                return
            c, Rs = cm
            g = 3 * g // 2 + c
            print(i, "log10 g = %.1f" % math.log10(g), "c =", c, "runs in R:", len(Rs.split()), flush=True)
        print(Rs)


if __name__ == "__main__":
    main(sys.argv[1:])
