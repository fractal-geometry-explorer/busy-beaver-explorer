"""The defect's fuel against the doubler height: (fuel) * 2^-b starts at 1 and drops by at most 2 * 2^-b per step.

usage: python3 py/potential.py ROUNDS

Same token rules as py/tokz.py, with every step of the round's defect logged (top-level visits only; the single
free visit that E0 L gives is a nested run and only helps): the fuel n arriving at the defect and the current height
b of its position (L minus digits before it). Checks with exact fractions, for every step j of every round,
n_j 2^-b_j >= n_0 2^-b_0 - sum_{i<j} 2 * 2^-b_i. So a defect can only run out of fuel after crossing positions with
sum of 2^-b at least 1/2, that is somewhere of small height. Prints the violations (none expected).
"""
import sys
from fractions import Fraction as Fr
sys.setrecursionlimit(1000000)
T = []
LOG = []
DEP = [0]


def bpos(i):
    b = 0
    for t in T[:i]:
        b += 1 if t == 'L' else (-1 if t in 'OI' else 0)
    return b


def An(n, i):
    DEP[0] += 1
    try:
        while n > 0:
            if i == len(T): T.append('O')
            t = T[i]
            if t == 'L': i += 1; n *= 2; continue
            if t in 'OI':
                tot = (t == 'I') + n; T[i] = 'I' if tot & 1 else 'O'; n = tot >> 1; i += 1; continue
            if DEP[0] == 1: LOG.append((n, bpos(i)))
            if t == 'z': T[i] = '1'; n -= 1; continue
            if t == 'x':
                if i + 1 == len(T): T[i] = 'I'; continue
                u = T[i + 1]
                if u == 'O': T[i] = 'O'; T[i + 1] = 'x'; n -= 1; continue
                if u == 'I': T[i] = 'L'; T[i + 1] = 'O'; Eh(i + 2); n -= 1; continue
                if u == 'L': T[i] = 'L'; T[i + 1] = 'x'; i += 1; n *= 2; continue
                raise Exception('two defects meet')
            if t == '1':
                if i + 1 == len(T): T[i] = 'I'; continue
                T[i] = 'O'; Eh(i + 1); n -= 1; continue
            raise Exception('?')
    finally:
        DEP[0] -= 1


def Eh(i):
    while True:
        if i == len(T): T.append('I'); return
        t = T[i]
        if t == 'L': i += 1; continue
        if t == 'O': T[i] = '1'; return
        if t == 'I': del T[i]; break
        raise Exception('two defects meet')
    if i == len(T): T.append('L'); return
    t = T[i]
    if t == 'O': T[i] = 'L'; return
    if t == 'L': T[i] = 'O'; T.insert(i + 1, 'x'); An(1, i + 1); return
    if t == 'I': T[i] = 'O'; T.insert(i + 1, '1'); return


def norm():
    i = 1
    while i < len(T) and T[i] == 'L': i += 1
    for j in range(1, i): T[j - 1] = 'L'
    T[i - 1] = 'x'
    if i < len(T) and T[i] == 'I': T[i - 1] = 'L'; T[i] = 'z'


def w(b):
    return Fr(1, 2 ** b) if b >= 0 else Fr(2 ** -b)


if __name__ == '__main__':
    R = int(sys.argv[1])
    T[:] = list('LLLzLLOLOI')
    bad = steps = 0
    for k in range(6, R + 1):
        LOG.clear()
        An(1, 0)
        if LOG:
            n0, b0 = LOG[0]
            psi0, acc = n0 * w(b0), Fr(0)
            for j, (n, b) in enumerate(LOG):
                steps += 1
                if n * w(b) < psi0 - acc: bad += 1; print('violation: round', k, 'step', j)
                acc += 2 * w(b)
        T.insert(0, 'x'); norm()
        while T and T[-1] == 'O': T.pop()
    print('rounds 6..%d: %d defect steps checked, %d violations' % (R, steps, bad))
