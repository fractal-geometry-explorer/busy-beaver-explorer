"""Do two machines of the family run the same counter?  Compares the sweep ends (b0 and the markers) of the two runs.

usage: python3 compare.py MACHINE1 MACHINE2 [STEPS]   (default 1e11)
Prints from which sweep on the markers (phases and blocks after b0) agree at every sweep end, and the same for b0."""
import sys

from model import parse
from sim import rl


def ends(M, steps):
    return [parse(x)[1:] for x in rl(M, steps) if x.startswith('S')]


def main(A, B, steps):
    a, b = ends(A, steps), ends(B, steps)
    n = min(len(a), len(b))
    # align: the markers of the bulk can be offset by a few sweeps at the start
    best = None
    for off in range(-40, 41):
        lo = max(0, -off)
        hi = min(n, len(b) - off) if off >= 0 else n
        same = [a[i][1] == b[i + off][1] for i in range(lo, hi)]
        last_bad = max([i for i, s in zip(range(lo, hi), same) if not s], default=lo - 1)
        if best is None or last_bad < best[1]:
            best = (off, last_bad, hi)
    off, last_bad, hi = best
    b0same = all(a[i][0] == b[i + off][0] for i in range(last_bad + 1, hi))
    print(f'{A} vs {B}: with an offset of {off} sweeps the markers agree at every sweep end from sweep {last_bad + 1} '
          f'to {hi} (of {n}); b0 agrees there too: {b0same}')
    return off, last_bad + 1, hi, b0same


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else '1e11')
