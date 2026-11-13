"""The phase map of 1RB1RA_1LC0RB_1LD0LB_1RA0LE_---1LF_1LB0LA, iterated far beyond direct simulation.

A phase starts with the tape `P 0^z` and the head just right of it, in state B on a blank.  Sweeps eat the zeros
4 at a time while a block of 1s grows 6 at a time; when the zeros run out the head walks into P, changes its right
end, and the block of 1s becomes the next zero block.  Observed (and checked here): the new prefix P' does not depend
on z beyond z mod 4 once z is large compared to P, and the new zero block is

    z' = zmap(z) + c(P, z mod 4),   zmap(4k+1) = 6k+1,  zmap(4k+3) = 6k+7,

with a correction c that is 0 in almost every phase.  So each phase is computed by running `c/phase.c` on P with a
small stand-in z_s (same residue mod 4, larger than anything in P) and carrying the true z as a Python integer.  Every
25 phases the same phase is recomputed with a stand-in twice as large and must agree.

usage: gcc -O2 -o phase c/phase.c && python3 py/drive.py N OUT    (N phases from the first one, z = 11, P = 1^14)
Output lines: phase, z mod 4, c, cells P grew on the left, len(P'), P' run-length coded.
"""
import os, subprocess, sys
from itertools import groupby

HERE = os.path.dirname(os.path.abspath(__file__))


def rle(P):
    return ' '.join(f"{k}^{len(list(g))}" for k, g in groupby(P))


def zmap(z):
    k, r = divmod(z, 4)
    return 6 * k + 1 if r == 1 else 6 * k + 7


def main(n, out_path, binary=os.path.join(HERE, '..', 'phase')):
    p = subprocess.Popen([binary], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)

    def phase(P, zs):
        p.stdin.write(f"{P} {zs}\n")
        p.stdin.flush()
        return p.stdout.readline().split()

    P, z = '1' * 14, 11
    with open(out_path, 'w') as out:
        for i in range(n):
            base = 4 * len(P) + 40
            zs = base + (z % 4) - (base % 4)
            r = phase(P, zs)
            if r[0] == 'HALT':
                print('HALT', i, z % 4, P, file=out, flush=True)
                return
            P2, z2 = r[0], int(r[1])
            if i % 25 == 0:
                zs2 = 2 * base + (z % 4) - ((2 * base) % 4)
                r2 = phase(P, zs2)
                assert r2[0] == P2 and int(r2[1]) - zmap(zs2) == z2 - zmap(zs), i
            print(i, z % 4, z2 - zmap(zs), int(r[2]), len(P2), rle(P2), file=out, flush=True)
            P, z = P2, zmap(z) + (z2 - zmap(zs))
        print('end', n, 'z has', len(str(z)), 'digits', file=out, flush=True)


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2])
