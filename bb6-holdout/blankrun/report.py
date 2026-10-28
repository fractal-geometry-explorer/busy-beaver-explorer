#!/usr/bin/env python3
"""Tables of the blank-tape run from stitch.py's output (Markdown on stdout).

usage: python3 report.py STITCHED.txt [--from BITS]      (bins of width 2^BITS and up; default 13)"""
import sys, math, collections

def load(path):
    bins = {}; K = []; H = []; joins = []; endchain = {}
    for l in open(path):
        if l.startswith('B '):
            flat, hists = l.rstrip('\n').split(' | ')
            w = flat.split(); b = int(w[1]); d = {}
            for i in range(2, len(w) - 1, 2):
                v = w[i + 1]; d[w[i]] = float(v) if ('.' in v or 'e' in v) else int(v)
            cur = None
            for tok in hists.split():
                if ':' in tok:
                    x, y = tok.split(':'); d[cur][int(x)] = int(y)
                else:
                    cur = tok; d[cur] = {}
            bins[b] = d
        elif l.startswith('K '):
            K.append(l.split()[1:])
        elif l.startswith('H '):
            H.append(l.split()[1:])
        elif l.startswith('stretch') and 'join' in l:
            joins.append(l.strip())
        elif l.startswith('E endchain'):
            for tok in l.split()[2:]:
                if ':' in tok:
                    x, y = tok.split(':'); endchain[int(x)] = int(y)
    return bins, K, H, joins, endchain

def fmt(x):
    return '{:,}'.format(int(x))

def lg2(x):
    return '2^%.2f' % math.log2(x) if x > 0 else '0'

def main():
    path = sys.argv[1]
    lo = int(sys.argv[sys.argv.index('--from') + 1]) if '--from' in sys.argv else 13
    bins, K, H, joins, endchain = load(path)
    bc = [b for b in sorted(bins) if b >= lo and bins[b].get('cycles', 0) > 0]
    bs = [b for b in bc if bins[b].get('ps', 0) > 0]
    print('### Cycles, three-wall round starts and how the run reaches them\n')
    print('Bin b: width W in [2^b, 2^(b+1)) at the round start (for cycles, the width of the clean tape the cycle starts '
          'from). Codes: E entry (a pass start reached from outside the loop\'s chain), F/H/7 landings of the chain with '
          'every gap >= 448 (full pass, half pass, round-7 break), i a pass start inside the stretch of an earlier one, '
          'x a three-wall round start that is not a pass start; f/h/s (landings with a gap below 448) never occur. '
          'Chain: the longest run of landings after an entry. Halvings: the closest end meeting of any cycle, '
          'log2(width/distance).\n')
    print('| b | cycles | pass starts | E | F | H | 7 | i | x | longest chain | closest end meeting (halvings) |')
    print('|---|---|---|---|---|---|---|---|---|---|---|')
    tot = collections.Counter()
    for b in sorted(bins):
        for k in ('cycles', 'ps', 'E', 'F', 'H', '7', 'i', 'x', 'f', 'h', 's'): tot[k] += bins[b].get(k, 0)
    for b in bc:
        d = bins[b]
        ch = max((k for k, v in d.get('chain', {}).items() if v), default=0)
        print('| %d | %s | %s | %s | %s | %s | %s | %s | %s | %d | %.2f |' % (b, fmt(d['cycles']), fmt(d['ps']), fmt(d['E']),
              fmt(d['F']), fmt(d['H']), fmt(d['7']), fmt(d['i']), fmt(d['x']), ch, d['maxh']))
    print('| all | %s | %s | %s | %s | %s | %s | %s | %s | | |\n' % tuple(fmt(tot[k]) for k in
          ('cycles', 'ps', 'E', 'F', 'H', '7', 'i', 'x')))
    if tot['f'] + tot['h'] + tot['s']:
        print('**Landings with a gap below 448: f %d, h %d, s %d.**\n' % (tot['f'], tot['h'], tot['s']))

    exact = all('minRW' in bins[b] for b in bs)
    print('### The wide condition: W <= 64R + 6 or 15W <= 64(W - b)\n')
    print('Every pass start a halt from blank tape can need above width 2^41 meets one of the two (the landing-condition '
          'work). Slack: max(64R + 6 - W, 64(W - b) - 15W) / W, negative when a pass start fails both. '
          + ('Minima are exact over every pass start of the bin.\n' if exact else
             'min R/W and min (W - b)/W are relative to the middle of the bin, 1.5 * 2^b.\n'))
    print('| b | pass starts | W > 64R + 6 | 15W > 64(W - b) | fail both | min R/W | min (W - b)/W | min slack |')
    print('|---|---|---|---|---|---|---|---|')
    for b in bs:
        d = bins[b]
        rw = d['minRW'] if exact else d['minR'] / (1.5 * 2 ** b)
        dw = d['minDW'] if exact else d['minD'] / (1.5 * 2 ** b)
        print('| %d | %s | %s | %s | %s | %.5f | %.5f | %s |' % (b, fmt(d['ps']), fmt(d['ps'] - d['wide1']),
              fmt(d['ps'] - d['wide2']), fmt(d['ps'] - d['wideany']), rw, dw,
              ('%.4f' % d['minslack']) if 'minslack' in d else '?'))
    if exact:
        print('\nBy how the run reached the pass start: min (W - b)/W and min R/W per code (blank: none in the bin).\n')
        codes = [c for c in 'EFH7i' if any(('mDW_' + c) in bins[b] for b in bs)]
        print('| b | ' + ' | '.join('%s: (W-b)/W, R/W' % c for c in codes) + ' |')
        print('|---|' + '---|' * len(codes))
        for b in bs:
            d = bins[b]
            print('| %d | ' % b + ' | '.join(('%.4f, %.5f' % (d['mDW_' + c], d['mRW_' + c])) if ('mDW_' + c) in d else ''
                                             for c in codes) + ' |')
    print()

    print('### How close the pass starts come to the halting lanes and families\n')
    print('Q = (W - b) + 2R + 22 = 2^v u with u odd: the halting lanes past the chain\'s end have u = 1 (Q = 2^(j+2), the '
          'off-chain meeting at 2^j - 2) or u = 3 on the other route. Family distance: max(|log2(R/R0)|, |log2(D/D0)|) to '
          'the nearest of the eight families of PassOpenHalt.lean (D = W - b), at the pass start and where each step of '
          'the chain from it would land. sigma = 3 log2(W/R) + 2 log2(|L1|/W); the lock allows a close through the loop only '
          'when log2 W <= sigma + 6.38 (margin = sigma + 6.38 - log2 W).\n')
    print('| b | max v2(Q) | max v2(Q)/log2 Q | min log2 u | u = 1 | u = 3 | in a family | family distance (start, next step) | max sigma (margin) |')
    print('|---|---|---|---|---|---|---|---|---|')
    for b in bs:
        d = bins[b]
        print('| %d | %d | %.3f | %.2f | %d | %d | %d | %.1f, %.1f | %.1f (%+.1f) |' % (
            b, d['maxv2Q'], d['maxv2qr'], d['minlu'], d['qpow2'], d['q3pow2'], d['infam'], d['mindelta'],
            d['mindelta_next'], d['maxsig'], d['maxsigmargin']))
    print()

    agg = collections.defaultdict(collections.Counter)
    for b in bs:
        for k in ('v2Q', 'lu', 'v2R', 'v2L', 'lr', 'ld', 'chain'):
            agg[k].update(bins[b].get(k, {}))
    print('### Distributions over all pass starts from b = %d on\n' % bs[0])
    n = sum(agg['v2Q'].values())
    print('v2(Q): count, and the share an even number has (2^-(v-1) of them have v2 >= v):\n')
    print('| v2(Q) | count | share >= v | even numbers |')
    print('|---|---|---|---|')
    acc = n
    for v in sorted(agg['v2Q']):
        print('| %d | %s | %.3g | %.3g |' % (v, fmt(agg['v2Q'][v]), acc / n, 2.0 ** -(v - 1)))
        acc -= agg['v2Q'][v]
    print('\nfloor(log2 u), u the odd part of Q:', ' '.join('%d:%s' % (k, fmt(v)) for k, v in sorted(agg['lu'].items())))
    print('\nfloor(log2 W) - floor(log2 R):', ' '.join('%d:%s' % (k, fmt(v)) for k, v in sorted(agg['lr'].items())))
    print('\nfloor(log2 W) - floor(log2 (W - b)):', ' '.join('%d:%s' % (k, fmt(v)) for k, v in sorted(agg['ld'].items())))
    print('\nv2(R):', ' '.join('%d:%s' % (k, fmt(v)) for k, v in sorted(agg['v2R'].items())))
    print('\nv2(L1):', ' '.join('%d:%s' % (k, fmt(v)) for k, v in sorted(agg['v2L'].items())))
    print('\nlandings after an entry:', ' '.join('%d:%s' % (k, fmt(v)) for k, v in sorted(agg['chain'].items())))
    print('\nlongest halving chain of end meetings per cycle:', ' '.join('%d:%s' % (k, fmt(v)) for k, v in sorted(endchain.items())))
    print('\n### Checkpoints (the clean tape that first reaches width 2^k)\n')
    print('| k | width | n | cycles | rounds |')
    print('|---|---|---|---|---|')
    for k, W, nn, c, r in K:
        if int(k) >= 20: print('| %s | %s | %s | %s | %s |' % (k, fmt(W), fmt(nn), fmt(c) if c != '?' else '?',
                                                             fmt(r) if r != '?' else '?'))
    print('\n### Closest end meetings (records over the run)\n')
    print('| n | halvings | halving chain | distance | width |')
    print('|---|---|---|---|---|')
    for h in H:
        if float(h[2]) >= 8: print('| %s | %s | %s | %s | %s |' % (fmt(h[0]), h[2], h[3], fmt(h[4]), fmt(h[5])))
    print('\n### Joins of the parallel stretches\n')
    for j in joins: print('- ' + j)

if __name__ == '__main__':
    main()
