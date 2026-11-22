"""Direct simulation of the corner: the tape of cfgL L 0 (2^L), that is 0^inf 1 (11)^L A>1 1 (000)^L 100 0^inf with
the head in state A on the last 1 of the left part. Both machines halt from it, after 2^(L+5) - 3L - 18 steps
for L = 1..12.  usage: python3 corner_check.py [LMAX]"""
import sys
MACHINES = ['1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---', '1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---']


def table(s):
    T = {}
    for i, part in enumerate(s.split('_')):
        for b in (0, 1):
            t = part[3 * b:3 * b + 3]
            T[(i, b)] = None if t[0] == '-' else (int(t[0]), 1 if t[1] == 'R' else -1, ord(t[2]) - 65)
    return T


def corner_steps(T, L):
    left = [1] + [1, 1] * L
    right = [1, 1] + [0, 0, 0] * L + [1, 0, 0]
    pad = 2 ** (L + 2) + 100
    tape = [0] * pad + left + right + [0] * pad
    pos, q = pad + len(left) - 1, 0
    for s in range(1, 2 ** (L + 6) + 1000):
        tr = T[(q, tape[pos])]
        if tr is None:
            return s
        w, d, q = tr
        tape[pos] = w
        pos += d
    return None


if __name__ == '__main__':
    LMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    for M in MACHINES:
        T = table(M)
        for L in range(1, LMAX + 1):
            s = corner_steps(T, L)
            print(M, L, s, 'ok' if s == 2 ** (L + 5) - 3 * L - 18 else 'formula differs')
