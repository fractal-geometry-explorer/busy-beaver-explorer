"""Check the round rules of lean/RoundRules.lean against the run, visit by visit.

usage:  gcc -O2 -o vdump holdouts/MACHINE/c/vdump.c && ./vdump 280000000 420000000 1 > vd.txt
        python3 holdouts/MACHINE/py/round_check.py vd.txt

For each pair of consecutive right-end visits the script reads the tape (as printed by c/vdump.c), finds the right
end (regime I: the gadget 101100 or 101101 followed by (110)^c; regime II: S-blocks ending in 10), strips S-blocks
S_n = 1 (01)^(n+1) leftwards from it, and looks at what stops the stripping:

  wall   a run of K >= 4 ones (counting the first cell of the first block): predicted next tape = run of K-3 ones,
         same blocks, last block +3 (regime I) or +1 with the 011s doubled as in round_II, new gadget / tail;
  wall3  a run of exactly 3 ones: the run 1110 becomes 0, as in round_I3 / round_II3;
  short  regime I gadget 101101: becomes 101100 with one more 110 (short_I);
  d0     a leftover D_0 block 100 (no rule yet).

It prints how many visits of each kind there are and how many the rule predicts cell for cell.
"""
import collections
import re
import sys

RI = re.compile(r'101100((?:110)+)$')
RS = re.compile(r'101101((?:110)+)$')
SBLOCKS = re.compile(r'((?:01)+(?:1(?:01)+)*)$')


def predict(T):
    """(kind, predicted next tape or None)."""
    m = RS.search(T)
    if m:
        i = m.start()
        return 'short', T[:i] + '101100' + T[i + 6:] + '110'
    m = RI.search(T)
    if m:
        i = m.start()
        body = T[:i]

        def end(B):
            return B + '010101' + '101101' + T[i + 6:]
        reg = 'I'
    elif T.endswith('10'):
        body = T[:-2]

        def end(B):
            return B + T[-2:-1] + '0110110'
        reg = 'II'
    else:
        return 'other', None
    mm = SBLOCKS.search(body)
    s0 = mm.start() if mm else len(body)
    K = len(re.search(r'(1*)$', body[:s0]).group(1))
    w = s0 - K
    if K >= 4:
        return reg + ' wall', end(body[:w] + '1' * (K - 3) + body[s0:])
    if K == 3:
        return reg + ' wall3', end(body[:w] + '0' + body[s0 + 1:])
    return reg + ' d0', None


def main():
    rows = [line.split() for line in open(sys.argv[1])]
    total, exact = collections.Counter(), collections.Counter()
    for a, b in zip(rows, rows[1:]):
        kind, P = predict(a[5])
        total[kind] += 1
        exact[kind] += P == b[5]
    for k in sorted(total):
        print(f"{k:10s} {total[k]:6d} visits, {exact[k]:6d} predicted exactly")
    print("all", sum(total.values()), "predicted", sum(exact.values()))


if __name__ == "__main__":
    main()
