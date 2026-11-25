"""Summarize the per-round output of c/r5tail.c for 1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB--- and
1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_1RC---: how much of X one round reads, and how close the lengths come to
what the halting equation m + 1 = (2D+1)*2^s of coq/SOC23Match.v needs.

usage: ./r5tail 200000 > r5tail.txt && python3 r5_tail.py r5tail.txt

Reports, for the R5 rounds after round 35:
  - the tail P(r >= x) of the bits r read by one round, and the slope of log P against log x;
  - the ratio tbits / r (target length per bit read) and the largest share r / L;
  - the length gap: a match needs tbits = mbits, i.e. r + tbits = xbits; the largest (r + tbits) / xbits seen;
  - a heuristic count: if the read lengths of later rounds follow the fitted tail, the expected number of
    rounds whose lengths come out equal, sum over rounds of P(r = xbits / (1 + kappa)), and the chance that
    such a round then matches all tbits bits by accident, 2^-tbits.
"""
import math
import sys


def main():
    rows = []
    for line in open(sys.argv[1]):
        p = line.split()
        if len(p) == 11:
            rows.append(tuple(map(int, p)))
    rows = rows[:-1]                                   # the last line may be cut
    r5 = [x for x in rows if x[6] == 5 and x[0] > 35]
    print(f'{len(rows)} rounds, final L = {rows[-1][1]}; R5 rounds after round 35: {len(r5)}')
    rs = sorted(x[3] for x in r5)
    n = len(rs)
    pts = []
    for xx in (10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000):
        c = sum(1 for v in rs if v >= xx)
        if c:
            pts.append((xx, c / n))
        print(f'  P(r >= {xx}) = {c}/{n} = {c / n:.2e}')
    lx = [math.log(a) for a, _ in pts]
    ly = [math.log(b) for _, b in pts]
    mx, my = sum(lx) / len(lx), sum(ly) / len(ly)
    slope = sum((a - mx) * (b - my) for a, b in zip(lx, ly)) / sum((a - mx) ** 2 for a in lx)
    c0 = math.exp(my - slope * mx)
    print(f'  tail fit: P(r >= x) ~ {c0:.3f} * x^{slope:.3f}')
    ks = sorted(x[4] / x[3] for x in r5 if x[3] >= 100)
    kappa = ks[len(ks) // 2]
    print(f'  tbits / r for r >= 100: min {ks[0]:.3f}, median {kappa:.3f}, max {ks[-1]:.3f}')
    print(f'  largest r / L: {max(x[3] / x[1] for x in r5):.4f}; largest (r + tbits) / xbits: '
          f'{max((x[3] + x[4]) / x[2] for x in r5):.4f} (a match needs 1)')
    # heuristic: density of r at x is -d/dx P(r >= x) = -slope * c0 * x^(slope-1)
    exp_len = 0.0
    for x in r5:
        need = x[2] / (1 + kappa)
        exp_len += -slope * c0 * need ** (slope - 1)
    print(f'  heuristic expected number of these rounds with equal lengths: {exp_len:.3g}; such a round would then '
          f'need about {int(min(x[2] for x in r5) / (1 + kappa))}+ more bits to agree exactly')


if __name__ == '__main__':
    main()
