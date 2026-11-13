"""Rounds of the machine, read from `c/samples.c` output (head in A at the left end of the tape):
  gcc -O2 -o samples c/samples.c && ./samples MACHINE 2000000000 A L 0 100000 > left.txt
  python3 py/rounds.py left.txt
At each sample the tape is a list of blocks 1^k 00; it prints, for each k = 6j+1 that occurs in a run of at least
`MIN` equal blocks, the number of such blocks, and checks the halving law between consecutive rounds:
count(k+6) at round r+1 is floor(n/2)-1 .. ceil(n/2)+1 for n = count(k) at round r.  Machine-agnostic for the 6j+1 family."""
import sys
from collections import Counter

MIN = 5


def blocks(line):
    head, runs = line.split("|")
    p = runs.split()
    t = int(head.split()[0])
    c = Counter()
    i = 0
    while i + 1 < len(p):
        if p[i][0] == "1" and p[i + 1] == "02":
            k = int(p[i][1:])
            j = i
            n = 0
            while j + 1 < len(p) and p[j] == p[i] and p[j + 1] == "02":
                n += 1
                j += 2
            if n >= MIN:
                c[k] += n
            i = j if j > i else i + 2
        else:
            i += 1
    return t, sum(int(x[1:]) for x in p), c


def main(fn):
    rounds = []
    last = None
    for line in open(fn):
        if "|" not in line:
            continue
        t, w, c = blocks(line)
        if last is not None and t - last < 0.05 * last:
            rounds[-1] = (t, w, c)      # several samples at one round start: keep the last
        else:
            rounds.append((t, w, c))
        last = t
    checked, odd = 0, []
    for (t, w, c), nxt in zip(rounds, rounds[1:] + [None]):
        print(f"{t:>12} width {w:>6}  " + " ".join(f"{k}:{c[k]}" for k in sorted(c)))
        if nxt:
            c2 = nxt[2]
            for k in c:
                if k % 6 == 1 and c[k] >= 10:
                    n, m = c[k], c2.get(k + 6, 0)
                    checked += 1
                    if not n // 2 - 1 <= m <= (n + 1) // 2 + 1:
                        odd.append((t, k, n, m))
    print(f"halving law (a run of n >= 10 blocks 1^k 00 becomes floor(n/2)-1 .. ceil(n/2)+1 blocks 1^(k+6) 00 at the "
          f"next round): {checked} runs checked, exceptions (step, k, n, next):", odd)

if __name__ == "__main__":
    main(sys.argv[1])
