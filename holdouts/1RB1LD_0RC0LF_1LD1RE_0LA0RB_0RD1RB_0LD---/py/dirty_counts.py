"""The count behind every stop, from the log of c/vispl.c, for lean/Shift.lean.

usage: python3 py/dirty_counts.py v1m.log

Each log line is one round (numbered as in c/visps.c, that is one more than in the README): its stop F, whether the
stop left two adjacent 1s (dirty), and the blocks it handled near the previous round's stop as offset:visits.

For each round this finds the round's last doubling block (a block 4 cells long that passes visits on) and the
count c it sends, and checks whether the blocks after it simply halve the count (c, c/2 rounded down, ..., 1 at
the stop). For such rounds `Shift.lean` gives: the next round's block holding F starts at F-2 only if every halving
block is left 000, which for halving blocks of the kinds 000 and 010 means c is a power of 2. The script counts,
over all rounds with such a chain, where the next round's block holding F actually starts, split by whether c is a
power of 2, and lists every dirty stop with its c. With k blocks in the chain, c lies in [2^(k-1), 2^k) and is even
(a doubling block sends 2n or 2(n-1)), so k = 2 forces c = 2: a dirty stop with k <= 2 is safe without any count.
"""
import sys
from collections import Counter


def blocks(fields):
    out = []
    for x in fields:
        q, n = map(int, x.split(":"))
        if out and out[-1][0] == q:   # a block handled one visit at a time (1011, 0011): keep its first count
            continue
        out.append((q, n))
    return out


def main(path):
    table = Counter()
    klen = Counter()
    dirty = []
    prev = None
    for line in open(path):
        a = line.split()
        r, F, d = int(a[1]), int(a[3]), int(a[5])
        B = blocks(a[9:])
        if prev:
            pr, pF, pB, pd = prev
            held = [q for q, n in B if q in (-2, -1, 0)]   # offsets from pF
            held = held[0] if held else None
            i0 = None
            for i in range(len(pB) - 1):
                if pB[i + 1][0] - pB[i][0] == 4:
                    i0 = i
            chain = None
            if i0 is not None:
                ch = [n for q, n in pB[i0 + 1:]]
                gaps = [pB[k + 1][0] - pB[k][0] for k in range(i0 + 1, len(pB) - 1)]
                if all(g == 3 for g in gaps) and ch[-1] == 1 and all(ch[k + 1] == ch[k] // 2 for k in range(len(ch) - 1)):
                    chain = ch
            if pd:
                dirty.append((pr - 1, pF, chain, held))
            if chain is not None:
                klen[min(len(chain), 5)] += 1
            if chain is not None and held is not None:
                c = chain[0]
                table[("c a power of 2" if c & (c - 1) == 0 else "c not a power of 2",
                       "F%+d" % held, "dirty" if pd else "clean")] += 1
            elif held is not None:
                table[("no halving chain", "F%+d" % held, "dirty" if pd else "clean")] += 1
        prev = (r, F, B, d)
    print("rounds by the count c sent by the last doubling block, and where the next round's block holding F starts:")
    for k in sorted(table):
        print("  %-20s %-5s %-6s %8d" % (k + (table[k],)))
    tot = sum(klen.values())
    print("rounds with a halving chain, by its number k of blocks (the stop included; 5 means 5 or more):")
    for k in sorted(klen):
        print("  k=%d %8d  %.1f%%" % (k, klen[k], 100.0 * klen[k] / tot))
    print("dirty stops (round as in the README, stop F, the counts from the last doubling block on, next round's block):")
    for r, F, ch, held in dirty:
        print("  round %d  F %d  counts %s  next block at %s" % (r, F, ch, "F%+d" % held if held is not None else "-"))


if __name__ == "__main__":
    main(sys.argv[1])
