"""The cycles of the last k blocks of the super orbit, level by level.

usage:
  python3 cycles.py [K]       a table for the last 1, ..., K blocks (default 6)

Number the blocks from the right end (level 1 = p_m, the last block).  Each super step, level 1 receives a wave with
h = 10.  A level with block p that receives a wave h has d = p + h and either (d odd) becomes (d + 5)/2 and adds
(d - 1)/2 to the level on its left, which ends the super step, or (d even) becomes d/2 and sends the wave d/2 on to
the left.  So a level only hears from its right, and the last k blocks run on their own (`superL_split` in
lean/Cascade.lean).  `bstep` below is the same map as `bstep` there.

For each k the table gives: the least period of the last k blocks; the first super step of the orbit from (1, 6) from
which they are periodic; the values the k-th block takes in one period; how many waves and adds the last k blocks send
to the left in one period; and the machine steps of one period spent in the last k blocks (c/superrun.c's count:
210 per super step, g(d) for each of the k levels that receives a wave, 17 for each add received among them).
Lean checks the periods and start points of k = 1 to 6 (`cycle_1` to `cycle_6`, lean/Cycles.lean); the rest is
computed here.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from superrun import g  # noqa: E402
from waves import superstep  # noqa: E402


def bstep(B):
    """One super step of the last levels B (nearest first, B[0] = the last block): (new B, event sent on, steps)."""
    B, h, t = list(B), 10, 210
    for i, p in enumerate(B):
        d = p + h
        t += g(d)
        if d % 2:
            B[i] = (d + 5) // 2
            if i + 1 < len(B):
                B[i + 1] += (d - 1) // 2
                t += 17
                return B, None, t
            return B, ("add", (d - 1) // 2), t
        B[i] = h = d // 2
    return B, ("wave", h), t


def orbit(n):
    """The first n + 1 lists of the super orbit from (1, 6), each reversed (nearest the right end first)."""
    P, out = [1, 6], []
    for _ in range(n + 1):
        out.append(P[::-1])
        P, kind, _ = superstep(P)
        if P is None:
            raise SystemExit("halt")
    return out


def least_period(B):
    """The least m > 0 with bstep^m (B) = B, for a B that is on its cycle."""
    C, m = bstep(B)[0], 1
    while C != B:
        C, m = bstep(C)[0], m + 1
    return m


def level(orb, k):
    """(period, start, top values in one period, waves, adds, machine steps) for the last k blocks."""
    # Late on the orbit the last k blocks are on their cycle; the first super step from which they repeat with that
    # period is where the cycle starts (they run on their own while there are blocks to their left).
    period = least_period(orb[-1][:k])
    start = None
    for j in range(len(orb) - period - 1, -1, -1):
        if len(orb[j]) <= k or orb[j][:k] != orb[j + period][:k]:
            break
        start = j
    if start is None:
        return None
    B, tops, waves, adds, steps = orb[start][:k], [], 0, 0, 0
    for _ in range(period):
        tops.append(B[-1])
        B, ev, t = bstep(B)
        steps += t
        if ev and ev[0] == "wave":
            waves += 1
        elif ev:
            adds += 1
    assert B == orb[start][:k]
    return period, start, tops, waves, adds, steps


def table(K):
    rows, n = [], 4096
    for k in range(1, K + 1):
        while True:
            orb = orbit(n)
            row = level(orb, k)
            if row is not None and row[1] + 2 * row[0] < n:
                break
            n *= 4
        rows.append((k,) + row)
    return rows


def main(argv):
    K = int(argv[1]) if len(argv) > 1 else 6
    print("k  period  from  top block (min-max, values)  waves/adds sent on  machine steps per period")
    prev = None
    for k, period, start, tops, waves, adds, steps in table(K):
        x = "" if prev is None else f"  (x{period // prev})"
        prev = period
        top = (f"{min(tops)}-{max(tops)}, {len(set(tops))}" if len(set(tops)) > 8
               else " -> ".join(map(str, tops if len(tops) <= 8 else sorted(set(tops)))))
        print(f"{k}  {period}{x}  {start}  {top}  {waves}/{adds}  {steps}")


if __name__ == "__main__":
    main(sys.argv)
