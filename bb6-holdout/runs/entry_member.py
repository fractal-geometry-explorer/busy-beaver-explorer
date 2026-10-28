"""Which of the blank-tape run's loop entries lie in an entry class of the clean-tape tree?  (Untrusted;
`../lean/END_TO_END.md`, "The chain ends at a right end of at least 769".)

The loop entry that `blank_halt_open_big` names is the first one in the cycle of a clean tape, and `chain_lanes.py`
counts the chains from the entry classes of a tree of d digits (`../lean/EntryForms.lean`), so it covers that entry
only if the tree settles the clean tape's class within d digits.  This takes the three-wall round starts of the run's
sample (`../blankrun/results/sample16k.tsv.gz`: n, round, a, b, c, W, ..., code, ..., depth), keeps the cycles of
clean tapes at least 2^41 wide (the cone, 2n >= 2^41; with a margin of 1,000), and looks up each entry (code E) in
each list of entry classes: a class is a line z -> (a, b, c, W), integer z >= lo, so W fixes z.  The first entry of a
cycle should lie in a class unless its cycle needs more than d digits; the later ones come after the first entry's
chain has ended and are no entries of the tree.

usage: python3 entry_member.py sample16k.tsv.gz entries36.txt entries40.txt ...
"""
import sys
import gzip
from collections import defaultdict

G = 2 ** 41  # the cone: clean tapes and entries of width at least 2^41


def load(fn):
    """The entry classes of `fn`, by the step of W and W's residue."""
    idx, n = defaultdict(list), 0
    for line in open(fn):
        if not line.startswith('E '):
            continue
        parts = line[2:].split('|')
        a, b, c, W = [tuple(map(int, p.split()))[:2] for p in parts[1:5]]
        ts = [tuple(map(int, t.split()))[:2] for t in parts[5].split(';')]
        lo = max(-((t[0] - G) // t[1]) for t in ts)
        idx[(W[1], W[0] % W[1])].append((a, b, c, W, lo))
        n += 1
    return idx, sorted(set(k[0] for k in idx)), n


def member(idx, steps, a, b, c, W):
    for M in steps:
        for fa, fb, fc, fW, lo in idx.get((M, W % M), []):
            z = (W - fW[0]) // fW[1]
            if z >= lo and fa[0] + fa[1] * z == a and fb[0] + fb[1] * z == b and fc[0] + fc[1] * z == c:
                return True
    return False


def main():
    cycles = defaultdict(list)
    with gzip.open(sys.argv[1], 'rt') as f:
        hdr = f.readline().rstrip('\n').split('\t')
        for line in f:
            r = dict(zip(hdr, line.rstrip('\n').split('\t')))
            if 2 * int(r['n']) >= G + 1000:
                cycles[int(r['n'])].append(r)
    for fn in sys.argv[2:]:
        idx, steps, n = load(fn)
        first, later, out = [0, 0], [0, 0], []
        for nn, rs in cycles.items():
            es = sorted((r for r in rs if r['code'] == 'E'), key=lambda r: int(r['round']))
            for i, r in enumerate(es):
                m = member(idx, steps, int(r['a']), int(r['b']), int(r['c']), int(r['W']))
                tally = first if i == 0 else later
                tally[0] += 1
                tally[1] += m
                if i == 0 and not m:
                    out.append((nn, int(r['round']), int(r['depth'])))
        print('%s (%d entry classes): first entries of a cycle %d, in a class %d; later entries %d, in a class %d'
              % (fn, n, first[0], first[1], later[0], later[1]))
        print('   first entries in no class (n, round, digits its cycle needs):', sorted(out))


if __name__ == '__main__':
    main()
