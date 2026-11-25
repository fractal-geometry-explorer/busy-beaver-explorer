"""The zone's low digit (trusted computation, observations).

usage: gcc -O3 -o /tmp/zonemodel c/zonemodel.c && TRIPS=1 /tmp/zonemodel 30 200000 100000000 | python3 py/cycles.py

Reads the TRIPS output of c/zonemodel.c.  Prints the patterns of turning depths in each stretch between two
extensions of the tape on the left (depths of 60 or more shown as 60), the sizes of those extensions, the longest
tail common to the zone at every cycle start (the record after a trip of depth >= 60) and how the rest of the zone,
U, changes in length from one cycle start to the next.
"""
import collections
import sys

LOW = "01100101110110110010011011100110110110010010010011001001001101101101"


def main():
    q, zones, bursts = [], {}, collections.Counter()
    for line in sys.stdin:
        f = line.split()
        if not f:
            continue
        if f[0] == "D":
            q.append((int(f[1]), int(f[2])))
        elif f[0] == "L":
            q.append((int(f[1]), "L"))
            bursts[int(f[2])] += 1
        elif f[0] == "U":
            zones[int(f[1])] = f[2]
    segs, cur = [], []
    for r, d in q:
        if d == "L":
            segs.append(cur)
            cur = []
        else:
            cur.append((r, d))
    pat = collections.Counter()
    for s in segs[1:]:
        k = next((i for i, (_, d) in enumerate(s) if d >= 60), None)
        if k is None:
            continue
        s = s[k + 1:]
        for i in range(0, len(s) - 6, 7):
            pat[tuple(min(d, 60) for _, d in s[i:i + 7])] += 1
    print("7-trip patterns of depths after the first carry of each stretch:", pat.most_common(4))
    print("left extensions (cells: count):", dict(sorted(bursts.items())))
    starts = [r for r, d in q if d != "L" and d >= 60 and r in zones]
    tails = [zones[r] for r in starts]
    k = 0
    while all(len(t) > k for t in tails) and len({t[len(t) - 1 - k:] for t in tails}) == 1:
        k += 1
    print(f"{len(starts)} cycle starts; the last {k} cells of the zone are the same at all of them;",
          "they end with LOW" if tails and tails[0].endswith(LOW) else "LOW differs")
    lens = collections.Counter()
    burst_at = {r for r, d in q if d == "L"}
    for a, b in zip(starts, starts[1:]):
        if not any(a < r <= b for r in burst_at):
            lens[len(zones[b]) - len(zones[a])] += 1
    print("change of zone length between consecutive cycle starts with no extension in between:", dict(lens))


if __name__ == "__main__":
    main()
