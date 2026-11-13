"""Check the left binary counter of the twins 2a/2b from the snapshots written by c/leftsnap.c.

usage: ./leftsnap MACHINE 1000000000 110 > ls.txt && python3 cntchk.py ls.txt 2a|2b

Each snapshot holds the leftmost 110 cells; they should read PREFIX, then 4-cell digits 1010 (one) / 1000 (zero),
then 11, with PREFIX 1010101101010110 (2a) or 10 (2b).  Prints how many consecutive changes of the decoded value
are increases, width changes (overflows) and anything else."""
import re
import sys

PRE = {"2a": r"0*1010101101010110", "2b": r"0*10"}[sys.argv[2]]
R = re.compile("^(" + PRE + ")((?:1010|1000)+)11")
last, inc, wid, other, nomatch, first = None, 0, [], 0, 0, None
for line in open(sys.argv[1]):
    k, lo, tp = line.split()
    m = R.match(tp)
    if not m:
        nomatch += 1
        continue
    d = m.group(2)
    b = len(d) // 4
    v = sum((d[4 * j:4 * j + 4] == "1010") << (b - 1 - j) for j in range(b))
    if first is None:
        first = k
    if last and (v, b) != last:
        if b == last[1] and v > last[0]:
            inc += 1
        elif b > last[1]:
            wid.append((k, last, (v, b)))
        else:
            other += 1
    last = (v, b)
print("from step", first, "increases", inc, "width changes", len(wid), wid, "other", other, "unmatched", nomatch,
      "final (value, digits)", last)
