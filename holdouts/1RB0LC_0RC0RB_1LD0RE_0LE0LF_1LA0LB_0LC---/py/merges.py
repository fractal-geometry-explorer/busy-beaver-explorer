"""Every merge between two markers with long blocks around them, for all lengths at once (symbolic runs).

A merge is a sweep whose turn fails its block condition: the turning marker P (phase 0 with 0 or 1 blocks before
it, phase 0' or 3 with none) runs into the marker Q before it.  For each P, gap and Q, and with 0 or 1 carried
markers (phase 4) after P, the configuration

    L (0010)^(a+12) Q (0010)^gap P (0010)^(n+12) [00111 (0010)^(m+12)] 000 E>        (blank after)

is run sweep by sweep with tools/py/bbtools/symtm.py for SWEEPS sweeps, for all a, n, m and every tape L.  The
script reports whether the run halts, whether it reaches into L (a carry leaves the merge: what happens next is a
turn or merge further left, with long blocks again), and the entries into F with the symbol F reads.

usage: python3 merges.py MACHINE [SWEEPS]
"""
import sys

from family import mirror, mirrored
from bbtools.symtm import run, Config, Blank, Lin, Halted, TouchContext, NeedSplit
from bbtools.machine import Machine

PH = {'0': '1', "0'": '0', '1': '0011', '2': '011', '3': '11', '4': '00111'}
FAILS = [('0', 0), ('0', 1), ("0'", 0), ('3', 0)]


def sweeps(M, start, k):
    m = Machine.parse(M)
    c = Config.parse(start)
    E, F = (2 if mirrored(M) else 4), 5
    fe = []

    def stop(c):
        if c.steps.is_zero() or c.state != E:
            return False
        return (c.left if mirrored(M) else c.right) == [Blank()]
    for i in range(k):
        c.steps = Lin(0)
        tr = []
        try:
            run(m, c, stop, max_moves=20000, trace=tr)
        except Halted:
            return 'HALTS', i, fe
        except TouchContext:
            return 'reaches L', i, fe
        except NeedSplit:
            return 'needs split', i, fe
        for t in tr:
            if t[0] == 'step' and t[2].state == F and t[1].state != F:
                cfg = t[2]
                sym = cfg.right[0] if cfg.right and isinstance(cfg.right[0], int) else '?'
                fe.append((i, sym))
    return 'resolves', k, fe


def main(M, k=12):
    f = mirror if mirrored(M) else (lambda s: s)
    rows = []
    for P, gap in FAILS:
        for Q in PH:
            for carry in (0, 1):
                s = f"L (0010)^a+12 {PH[Q]} {'0010 ' * gap}{PH[P]} (0010)^n+12 " + ('00111 (0010)^m+12 ' if carry else '') + \
                    '0 0 0 E> 0^inf'
                r, i, fe = sweeps(M, f(s), k)
                rows.append((P, gap, Q, carry, r, i, fe))
    return rows


if __name__ == '__main__':
    M = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    rows = main(M, k)
    for P, gap, Q, carry, r, i, fe in rows:
        print(f"P={P:2} gap={gap} Q={Q:2} carry={carry}: {r:10} after {i:2} sweeps; F entered {len(fe)}x, reading "
              f"{sorted(set(x[1] for x in fe)) if fe else '-'}")
    print(M, 'halts in', sum(1 for x in rows if x[4] == 'HALTS'), 'of', len(rows), 'merge patterns')
