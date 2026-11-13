"""Iterate the (p, r) map of 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE from (2, 1).

  r >= p+2 : (p, r) -> (2p+2, r-p-1)      (doubling step)
  r == p+1 : halt
  r == p   : (p, r) -> (2, 4p+1)
  r <  p   : (p, r) -> (p-r, 4r+2)

usage: python3 orbit.py STEPS [REPORT_EVERY]
Prints progress lines: map steps, bits of p and r, the smallest normalised distance |r-p-1|/p seen at the end of a
doubling phase, and the step counts of each kind.
"""
import sys, math

def run(n, every):
    p, r = 2, 1
    kinds = [0, 0, 0]
    closest = None
    for i in range(1, n + 1):
        if r >= p + 2:
            p, r = 2 * p + 2, r - p - 1
            kinds[0] += 1
        elif r == p + 1:
            print(f"HALT at map step {i}: p={p}")
            return
        elif r == p:
            p, r = 2, 4 * p + 1
            kinds[1] += 1
        else:
            p, r = p - r, 4 * r + 2
            kinds[2] += 1
        if r < p + 2:  # a decision is due next step: how close to r == p+1?
            d = abs(r - p - 1)
            if p > 1000:
                v = d / p
                if closest is None or v < closest[0]:
                    closest = (v, i, p.bit_length())
        if i % every == 0:
            print(i, 'bits p', p.bit_length(), 'bits r', r.bit_length(), 'kinds', kinds, 'closest', closest, flush=True)
    print('done', n, 'bits', p.bit_length(), r.bit_length(), kinds, closest)

if __name__ == '__main__':
    run(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 5)
