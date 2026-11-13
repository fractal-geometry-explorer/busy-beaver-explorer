"""Statistics of the irregular phases of a machine of the family 1RB?RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_X---, from the
accelerated run of hyb.py: the shape at which each anomaly and each collision starts, and the race between the word
and the collision cascade.

An *epoch* runs from one anomaly to the next.  After an anomaly the word has width w and lasts about 2^((w-1)/2)
phi steps; the misaligned gap left by the anomaly starts a cascade of collisions, which must end before the next
anomaly or the next anomaly starts with a misaligned gap still pending.  The margin of an epoch is
log2(epoch length) - log2(time from the anomaly to the last collision of the epoch), both in steps.

usage: python3 phases.py MACHINE NTRANSIENTS
"""
import collections
import math
import sys

from hyb import Nphi, comp, from_blank, jcoll, jump, transient


def main(m, N):
    st = from_blank(m)
    ev = []
    anom = collections.Counter()
    coll = collections.Counter()
    for e in range(N):
        W, k, q, g, rest, n = st
        Ja = Nphi(W) // 2
        Jc = jcoll(k, q, g)
        J = Ja if Jc is None else min(Ja, Jc)
        kind = 'A' if J == Ja else 'C'
        st = jump(st, J)
        W, k, q, g, rest, n = st
        a, P = comp(k, q)
        if kind == 'A':
            anom[("[x]" if len(W) == 1 else f"[x,{W[-1]}]" if len(W) == 2 else f"{len(W)} blocks",
                  "a=1" if a == 1 else "a>=2", "gap pending" if g is not None else "no gap pending")] += 1
        else:
            coll[(f"a={a}" if a < 2 else "a>=2", "gaps of 2 only" if all(p == 1 for p in P) else "other gaps",
                  f"g={g}")] += 1
        r = transient(m, st, 10**11)
        if r[0] != 'OK':
            print("transient", r[0], r[1])
            return
        st = r[1]
        ev.append((kind, st[5], g, sum(st[0]) + len(st[0]) - 1))
    print(m)
    print("anomalies:", dict(anom))
    print("collisions:", dict(coll))
    A = [i for i, x in enumerate(ev) if x[0] == 'A']
    rows = []
    for i, j in zip(A, A[1:]):
        tA, tN = ev[i][1], ev[j][1]
        cs = [x for x in ev[i + 1:j] if x[0] == 'C']
        if not cs:
            continue
        tC = cs[-1][1]
        rows.append((ev[i][3], len(cs), math.log2(tN - tA), math.log2(tC - tA), ev[j][2]))
    print(" width   collisions  log2(epoch)  log2(cascade)  margin  gap at next anomaly")
    for r in rows:
        print("%6d %10d %12.1f %14.1f %7.1f  %s" % (r[0], r[1], r[2], r[3], r[2] - r[3], r[4]))
    print("epochs with collisions:", len(rows), " min margin: %.1f" % min(r[2] - r[3] for r in rows),
          " lost races (gap pending at the next anomaly):", sum(1 for r in rows if r[4] is not None))


if __name__ == "__main__":
    main(sys.argv[1], int(sys.argv[2]))
