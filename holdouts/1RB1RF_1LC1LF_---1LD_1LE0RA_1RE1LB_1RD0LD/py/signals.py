"""The signal tapes of 1RB1RF_1LC1LF_---1LD_1LE0RA_1RE1LB_1RD0LD in the exact accelerated run (py/msim.py).

Each time the head is at the left end of the tape the tape is read as runs of 1s separated by single 0s.  A *signal
tape* is one of the form

    2^n 1 2^b1 m ...          (possibly after one partial run at the very left end)

a block of n runs of length 2, the signal 1, and the tail, whose first block has b1 runs.  The signal's excursion
resets the tape or halts only when block and tail fit exactly (README: `2^(4b+3) 1 2^b 1` resets, halts lie next to
that line), so the script prints n, b1 and the distance n - (4 b1 + 3) for every signal tape, and at the end the
smallest |n - (4 b1 + 3)| / n seen in each range of steps.  Several signal tapes can belong to one excursion (the
excursion makes new signals as its wall steps back), and n is read off by one or two when the leftmost run is still
being built (2^170 for the tape 2^171 1 2^42 1 of step 219,107).

usage: python3 py/signals.py [MAXEXP]        to 10^MAXEXP steps (default 40, a few seconds; 100 takes minutes)
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import msim  # noqa: E402


def runs(tokens, B=3):
    """Blocks (value, count) from left to right -> [[run length, count], ...] (run length 0: two 0s in a row)."""
    out, open_ = [], [0]

    def emit(d, c=1):
        if out and out[-1][0] == d:
            out[-1][1] += c
        else:
            out.append([d, c])

    def block(v):
        em = []
        for i in range(B):
            if (v >> (B - 1 - i)) & 1:
                open_[0] += 1
            else:
                em.append(open_[0])
                open_[0] = 0
        return em

    for v, c in tokens:
        if v == (1 << B) - 1:
            open_[0] += B * c
            continue
        for d in block(v):
            emit(d)
        if c >= 2:
            before = open_[0]
            e2 = block(v)
            assert open_[0] == before
            for _ in range(1 if len(e2) == 1 else c - 1):
                for d in e2:
                    emit(d, c - 1 if len(e2) == 1 else 1)
    if open_[0]:
        emit(open_[0])
    return out


def trim(ds):
    while ds and ds[0][0] == 0:
        ds = ds[1:]
    if ds and ds[0][0] != 2:
        ds = ds[1:]
    return ds


def show(ds, cap=8):
    s = " ".join("%d^%d" % (d, c) if c > 1 else str(d) for d, c in ds[:cap])
    return s + (" ... (%d runs)" % len(ds) if len(ds) > cap else "")


def main(maxexp=40):
    a = msim.MSim(msim.M)
    plain, seen, rows = a.tr, set(), []

    def look():
        if a.L:
            return
        toks = [(v, c) for v, c in reversed(a.R)]
        ds = trim(runs(toks[:6]))
        if len(ds) < 2 or ds[0][0] != 2 or ds[0][1] < 5 or ds[1] != [1, 1]:
            return
        full = trim(runs(toks))
        b1 = full[2][1] if len(full) > 2 and full[2][0] == 2 else 0
        key = (b1, len(full), tuple(d for d, _ in full[2:8]))
        if key in seen:
            return
        seen.add(key)
        n = full[0][1]
        rows.append((len(str(a.steps)) - 1, n, b1))
        print("10^%-3d n = %d  b1 = %d  n - (4 b1 + 3) = %d   %s" % (rows[-1][0], n, b1, n - 4 * b1 - 3, show(full)),
              flush=True)

    def tr(st, u, v, d):
        look()
        return plain(st, u, v, d)

    a.tr = tr
    a.run(10 ** maxexp)
    print("halted" if a.halted else "no halt in 10^%d steps; %d signal tapes" % (maxexp, len(rows)))
    for lo in range(0, maxexp, 10):
        part = [(abs(n - 4 * b - 3) / n, n, b) for e, n, b in rows if lo <= e < lo + 10]
        if part:
            r, n, b = min(part)
            print("  steps 10^%d..10^%d: %d signal tapes, smallest |n - (4 b1 + 3)| / n = %.4f (n = %d, b1 = %d)"
                  % (lo, lo + 10, len(part), r, n, b))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 40)
