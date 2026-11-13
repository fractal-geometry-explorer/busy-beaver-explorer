"""The tape of 1RB0LF_0RC0RB_1LC1LD_1RE0RD_---0RA_1LA0LF as particles in a sea.

Reads the output of `c/snap.c` (the tape from the head to the last 1, each time the head makes a new left record in
state F, every N-th time) and prints the *junctions* (two equal neighbouring cells, `00` or `11`: everywhere else the
tape alternates `1010...`) grouped into particles (junctions at most G cells apart), with their positions.  With
N = 4 the samples are one cycle of the left gadget apart; `move` lines give each particle's displacement per cycle
when the particle list kept its shape, `SHAPE` lines the list when it changed.  Particle names are the gaps between
their junctions; `T` stands for a repeated `1.3.` (a train: the sea `1110`).

usage: gcc -O2 -o snap c/snap.c && ./snap MACHINE STEPS 4 > s.txt && python3 py/particles.py s.txt
"""
import re
import sys

G = 4


def particles(s, p):
    J = [i for i in range(len(s) - 1) if s[i] == s[i + 1]]
    cl, cur = [], [J[0]]
    for j in J[1:]:
        if j - cur[-1] <= G:
            cur.append(j)
        else:
            cl.append(cur)
            cur = [j]
    cl.append(cur)
    res = []
    for c in cl:
        name = '.'.join(str(c[k] - c[k - 1]) for k in range(1, len(c)))
        res.append((re.sub(r'(1\.3\.)+', 'T', name) or 'o', c[0] + p))
    return res


def main(path):
    prev = None
    for line in open(path):
        n, p, s = line.split()
        ps = particles(s, int(p))
        if prev and len(prev) == len(ps) and all(a[0] == b[0] for a, b in zip(prev, ps)):
            print(n, 'move', ' '.join('%s:%+d' % (b[0], b[1] - a[1]) for a, b in zip(prev, ps)))
        else:
            print(n, 'SHAPE', ' '.join('%s@%d' % a for a in ps))
        prev = ps


if __name__ == '__main__':
    main(sys.argv[1])
