"""The jump-to-jump map of a `10` defect of 1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB, on random gaps.

Read the gap with the defect as constant term, W = 1 + g0 z + g1 z^2 + ... over GF(2).  From one jump to the next
(README, "The defect's jump"):  W = (1 + ... + z^j) + z^L C  ->  F(W) = (1 + z)^L C,  L = j + a + 2.
At a jump, j is the number of y words before the gap's first x; a halt needs j to reach the wall.
This iterates F on 2,000 random gaps of 400 words (seed 5) and counts j: it is geometric, so F alone does not keep
the run of y words short.

usage: python3 fmap.py
"""
import collections
import random


def F(W):
    j = 0
    while j + 1 < len(W) and W[j + 1]:
        j += 1
    if j + 1 == len(W):
        return None, j
    a = 0
    while j + 1 + a < len(W) and not W[j + 1 + a]:
        a += 1
    L = j + 1 + a
    C = W[L:]
    if not C:
        return None, j
    for _ in range(L):
        C = [C[0]] + [C[i] ^ C[i - 1] for i in range(1, len(C))]
    return C, j


def main():
    random.seed(5)
    cnt = collections.Counter()
    for _ in range(2000):
        W = [1] + [random.randint(0, 1) for _ in range(400)]
        while True:
            W, j = F(W)
            cnt[min(j, 5)] += 1
            if W is None or len(W) < 60:
                break
    tot = sum(cnt.values())
    print(f"{tot} jumps; j at a jump:", ', '.join(f"{j}{'+' if j == 5 else ''}: {100 * c / tot:.1f}%" for j, c in sorted(cnt.items())))


if __name__ == '__main__':
    main()
