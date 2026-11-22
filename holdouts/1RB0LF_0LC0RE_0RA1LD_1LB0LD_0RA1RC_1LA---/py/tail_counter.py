"""The tail as a binary counter of blocks (heuristic check on a recp file).

At the 'o o' records of a phase, 0^inf B> 0 (D0, o) (0, o) (Y, x) T, compare the tail T at consecutive records:
  1. how many blocks from the front change (the rest is equal from the right end), as a histogram;
  2. the shape of the first w blocks (x and D, D capped at 8 + D mod 2), sampled every other record: after a skip
     of 0, 8, 32, 128 or 512 samples, is it periodic with period 2^w?
usage: python3 tail_counter.py RECP_FILE      (recp.c output with every record, e.g. recp 4000000 3e9 1 400)"""
import sys
from collections import Counter
from tail_ops import parse


def main():
    oo = []
    for line in open(sys.argv[1]):
        if '|' not in line:
            continue
        st, rec, hc, bl = parse(line)
        if hc == 0 and len(bl) > 3 and bl[1] == (0, 0) and bl[0][1] == 0 and bl[0][0] >= 1:
            oo.append((rec, bl[0][0], bl[2], tuple(bl[3:])))
    phases, dep = [[oo[0]]], Counter()
    for a, b in zip(oo, oo[1:]):
        if b[0] - a[0] == 2 and b[1] == a[1] - 2:
            phases[-1].append(b)
            A, B = a[3], b[3]
            k = 0
            while k < min(len(A), len(B)) and A[-1 - k] == B[-1 - k]:
                k += 1
            if max(len(A), len(B)) - k:
                dep[max(len(A), len(B)) - k] += 1
        else:
            phases.append([b])
    print('1. blocks changed from the front, per increment:', ' '.join('%d:%d' % kv for kv in sorted(dep.items())))
    shape = lambda T, w: tuple(((D if D < 8 else 8 + D % 2), x) for D, x in T[:w])
    print('2. period of the first w blocks (samples: every other record), w = 1, 2, ...')
    for P in phases:
        if len(P) < 500:
            continue
        S = [r for r in P if r[2][0] % 2 == 0]
        out = []
        for w in range(1, 11):
            seq, p, res = [shape(r[3], w) for r in S], 2 ** w, '-'
            for skip in (0, 8, 32, 128, 512):
                if 2 * p + skip > len(seq):
                    break
                if all(seq[i] == seq[i + p] for i in range(skip, len(seq) - p)):
                    res = '%d' % p
                    break
            out.append(res)
        print('   phase with %d samples: %s' % (len(S), ' '.join(out)))


if __name__ == '__main__':
    main()
