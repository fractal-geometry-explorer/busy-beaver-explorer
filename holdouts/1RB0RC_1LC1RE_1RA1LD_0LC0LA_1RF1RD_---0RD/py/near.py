"""near.py: how often the run from blank tape comes near the boundary of the pass map, against the uniform model.

    gcc -O3 -o prun c/prun.c && ./prun run 100000000000 0 0 > c/near_1e11.txt && python3 py/near.py c/near_1e11.txt

The input is the end of `prun run N EVERY D` (D >= 0): `hexp` (the sum of 1/N, N = a + j + r, over the zigzag starts of
each bin floor(log2 pass)), `h2` (the zigzag starts by tag, a mod 3, j parity and delta = r - floor(a/3), per bin)
and `hist` (the starts with a = 1 mod 3 and even j by their distance d to a halting row, d = delta - 2 for y and
delta - 3 for Y; d = 0 halts).

The model: x = a/N moves by the map T(x) = 4x/3 (x < 3/4, growth) or 4x - 3 (drain), whose invariant density is
uniform, so a zigzag start sits on any one value of a with chance about 1/N.  For a given delta there is an a with
r - floor(a/3) = delta for 3 of the 4 residues of N mod 4 (a = 3q + e, N - 4q - e = delta), so the expected number of
starts with that delta is 3/4 * sum 1/N; for a given d (one of y, Y, with e = 1) it is 1/4 * sum 1/N.
"""
import math, sys
from collections import defaultdict


def load(path):
    hexp, h2, hist = None, defaultdict(lambda: [0] * 64), defaultdict(lambda: [0] * 64)
    end = None
    for line in open(path):
        if line.startswith('hexp:'):
            hexp = [float(x) for x in line.split()[1:]]
        elif line.startswith('h2 '):
            head, vals = line.split(':')
            _, t, e, jp, _, dl = head.split()
            h2[(t, int(e[1]), int(jp[1]), int(dl))] = [int(x) for x in vals.split()]
        elif line[:2] in ('y ', 'Y ') and ':' in line:
            head, vals = line.split(':')
            t, d = head.split()
            hist[(t, int(d))] = [int(x) for x in vals.split()]
        elif line.startswith('END'):
            end = line.split()
    return hexp, h2, hist, end


def main(path):
    hexp, h2, hist, end = load(path)
    S = sum(hexp)
    print(f'{end[1]} passes; sum of 1/N over the zigzag starts: {S:.3f}')
    by_delta = defaultdict(int)
    for (t, e, jp, dl), v in h2.items():
        by_delta[dl] += sum(v)
    print('delta = r - floor(a/3): observed starts, expected 3/4 * sum 1/N = %.2f' % (0.75 * S))
    print('  ' + ' '.join(f'{dl:+d}:{by_delta[dl]}' for dl in range(-16, 17)))
    tot = sum(by_delta[dl] for dl in range(-16, 17))
    print(f'  all 33 values: {tot} against {33 * 0.75 * S:.1f} (ratio {tot / (33 * 0.75 * S):.3f})')
    by_d = defaultdict(int)
    for (t, d), v in hist.items():
        by_d[d] += sum(v)
    print('d (halting row distance, y and Y, a = 1 mod 3, j even): observed, expected 1/4 * sum 1/N = %.2f' % (0.25 * S))
    print('  ' + ' '.join(f'{d:+d}:{by_d[d]}' for d in range(-16, 17)))
    totd = sum(by_d[d] for d in range(-16, 17))
    ratio = totd / (33 * 0.25 * S)
    print(f'  all 33 values: {totd} against {33 * 0.25 * S:.1f} (ratio {ratio:.3f}); d = 0: {by_d[0]}')
    # by decade of passes
    print('per factor 2 of the pass count (bins): starts with |d| <= 16 observed / expected')
    for b in range(64):
        if hexp[b] == 0:
            continue
        o = sum(hist[(t, d)][b] for t in 'yY' for d in range(-16, 17))
        print(f'  2^{b}: {o} / {33 * 0.25 * hexp[b]:.1f}')
    # the rate per unit of ln(pass), from the last bins
    N = int(end[2])
    lam = ratio * 0.25 / 2.08
    print(f'expected d = 0 hits per factor e of the pass count (model x ratio, N ~ 2.08 passes): {lam:.4f}; '
          f'per factor 10: {lam * math.log(10):.3f}; expected so far (from pass 16): {ratio * 0.25 * S:.2f}')


if __name__ == '__main__':
    main(sys.argv[1])
