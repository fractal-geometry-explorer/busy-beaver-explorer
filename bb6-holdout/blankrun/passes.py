#!/usr/bin/env python3
"""Tables over the pass starts that follow.c wrote (Markdown on stdout): where they lie relative to the landing plane
2(b - a) = W - 2R - 6, in which round of their cycle the entries come, and how close their cycles come to the open
clean-tape classes (settle depths, settle.c), with every clean tape in windows of the run for comparison.

usage: python3 passes.py SETTLE_BINARY OUT0 OUT1 ... [--window WIN0 WIN1 ...]
  OUTj: follow.c outputs (T and N lines); WINj: follow.c outputs whose V lines list every clean tape of a stretch of
  the run (follow chunk S S+Z Z from a clean tape S of the run, for instance one of its checkpoints).

The depth of n is the number of low binary digits of n that the exhaustive check needs to settle n's class (settle.c);
depth > 36 means n's class is open at 36 digits, where the cut classes have measure 2.4e-5 (1,660,017 classes of
W/2 mod 2^36 from width 2^32), and depth > 40 open at 40 digits (measure 8.4e-6).  Entries and half-pass landings are
counted over the T lines (every one below width 2^34, a 1/1024 sample of the cycles above); full-pass and round-7
landings and the i starts over the T and N lines (all of them are written)."""
import sys, subprocess, collections

def settle(binary, ns):
    ns = sorted(set(ns))
    out = subprocess.run([binary], input=''.join('%d\n' % n for n in ns), capture_output=True, text=True, check=True).stdout
    d = {}
    for l in out.split('\n'):
        w = l.split()
        if len(w) == 4: d[int(w[0])] = int(w[1])
        elif w: d[int(w[0])] = None          # STOP or LONG: should not happen on the run
    return d

TH = (36, 40, 44)

class Acc:
    def __init__(self): self.n = 0; self.s = 0; self.over = [0] * len(TH); self.full = 0; self.mx = 0; self.bad = 0
    def add(self, n, d):
        if d is None: self.bad += 1; return
        self.n += 1; self.s += d; self.mx = max(self.mx, d)
        for i, t in enumerate(TH):
            if d > t: self.over[i] += 1
        if d >= n.bit_length(): self.full += 1
    def row(self, label):
        if not self.n: return '| %s | 0 | | | | | | |' % label
        return '| %s | %s | %.1f | %s | %s | %d |%s' % (label, '{:,}'.format(self.n), self.s / self.n,
               ' | '.join('%d (%.2g)' % (o, o / self.n) for o in self.over), '%d (%.2g)' % (self.full, self.full / self.n),
               self.mx, (' %d failed |' % self.bad) if self.bad else '')

HEAD = '| %s | count | mean depth | > 36 | > 40 | > 44 | >= bits of n | max |\n|---|---|---|---|---|---|---|---|'

def main():
    binary = sys.argv[1]; args = sys.argv[2:]
    wins = []
    if '--window' in args:
        i = args.index('--window'); wins = args[i + 1:]; args = args[:i]
    rows = []                                   # (n, W, code, T?)
    plane = collections.defaultdict(collections.Counter); rnd = collections.defaultdict(collections.Counter)
    for p in args:
        for l in open(p):
            if l[:2] in ('T ', 'N '):
                w = l.split()
                if w[7] == 'x': continue
                n, r, a, b, c, W, code = int(w[1]), int(w[2]), int(w[3]), int(w[4]), int(w[5]), int(w[6]), w[7]
                rows.append((n, W, code, l[0] == 'T'))
                if code in 'EH' and l[0] != 'T': continue
                off = 2 * (b - a) - (W - 2 * (W - c - 1) - 6)
                plane[code][off if abs(off) <= 4 else 'far'] += 1
                if code == 'E': rnd[off if abs(off) <= 4 else 'far'][r] += 1
    print('### The landing plane\n')
    print('Every landing of the loop\'s chain lies on the plane 2(b - a) = W - 2R - 6 (`landing_plane`). Offset: '
          '2(b - a) - (W - 2R - 6), by how the run reached the pass start (entries and half-pass landings over the T '
          'lines, the rest over all).\n')
    keys = [0, 2, -2, 4, -4, 'far']
    print('| code | ' + ' | '.join(str(k) for k in keys) + ' |')
    print('|---|' + '---|' * len(keys))
    for c in 'EFH7i':
        if c in plane:
            t = sum(plane[c].values())
            print('| %s | ' % c + ' | '.join(('%s (%.4f)' % ('{:,}'.format(plane[c][k]), plane[c][k] / t)) if plane[c][k] else ''
                                             for k in keys) + ' |')
    print('\nThe round of the cycle in which the entries come, by offset (the eight most common rounds):\n')
    for k in keys:
        if rnd[k]:
            t = sum(rnd[k].values())
            print('- %s: ' % k + ', '.join('round %d %.3f' % (r, v / t) for r, v in rnd[k].most_common(8)))
    print()
    d = settle(binary, [r[0] for r in rows])
    bybin = collections.defaultdict(Acc); bycode = collections.defaultdict(Acc)
    for n, W, code, isT in rows:
        if code in 'EH' and not isT: continue
        if code in 'EH': bybin[W.bit_length() - 1].add(n, d[n])
        bycode[code].add(n, d[n])
    print('### Settle depth of the pass starts\' cycles\n')
    print('Depth of the clean tape n whose cycle holds the pass start: the low binary digits of n the exhaustive check '
          'needs to settle n\'s class. Count (share) of depths above 36, 40 and 44 digits, and at or above the bit length '
          'of n (n\'s class open at every depth n has digits for: the exhaustive check runs n itself).\n')
    print('By how the run reached the pass start:\n')
    print(HEAD % 'code')
    for c in 'EFH7i':
        if c in bycode: print(bycode[c].row(c))
    print('\nEntries and half-pass landings by the width of the pass start (bin b: W in [2^b, 2^(b+1))):\n')
    print(HEAD % 'b')
    for b in sorted(bybin): print(bybin[b].row(str(b)))
    if wins:
        print('\n### Settle depth of every clean tape in windows of the run\n')
        print('For comparison: the share of the run\'s clean tapes, all of them in each window, whose class is open. The '
              'cut classes have measure 2.4e-5 at 36 digits and 8.4e-6 at 40.\n')
        print(HEAD % 'window (first clean tape)')
        for p in wins:
            ns = [int(l.split()[1]) for l in open(p) if l.startswith('V ')]
            dw = settle(binary, ns); a = Acc()
            for n in ns: a.add(n, dw[n])
            print(a.row('{:,}'.format(min(ns)) if ns else p))
            res = collections.Counter(n % 4 for n in ns)
            sys.stderr.write('%s: n mod 4 shares %s\n' % (p, ' '.join('%d:%.4f' % (r, res[r] / len(ns)) for r in range(4))))

if __name__ == '__main__':
    main()
