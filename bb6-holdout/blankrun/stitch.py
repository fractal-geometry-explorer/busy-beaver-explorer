#!/usr/bin/env python3
"""Stitch the stretches of the blank-tape run (follow.c) and check their joins.

usage: python3 stitch.py OUT0 OUT1 ...      (the outputs of `follow blank` and `follow chunk`, in order of their START)

For each pair of consecutive stretches, the earlier one's tail window and the later one's head window list the clean
tapes each visited in [START, START + ZONE) of the later one (V lines).  The earlier stretch is the true run there (by
induction from blank tape), so the later stretch is the true run from the first clean tape both visit on: the join.
The script checks that a join exists, that from the join on both list the same clean tapes to the window's end, and
computes the absolute cycle and round counts of the later stretch (offset at the join).  It then writes:
  - the checkpoints (K lines, and P lines at multiples of 10^11) and the long halving chains (C lines) with absolute
    counts,
  - the statistics per binary length of the width, summed over the stretches (the last S block of each output: the
    final one if the stretch is done, else its latest partial one),
  - the records (H lines, T/N lines that set a record) in order of n.
A stretch that is still running contributes what it has counted so far; the summary says how far each one got."""
import sys, re, collections

def read(path):
    head = None; V = []; K = []; H = []; P = []; C = []; S_blocks = []; cur = None; done = None; T = []; stop = None
    with open(path) as f:
        for line in f:
            if line.startswith('# follow'):
                w = line.split(); head = dict(mode=w[2], start=int(w[4]), end=int(w[6]), zone=int(w[8]))
            elif line.startswith('V '):
                _, n, c, r = line.split(); V.append((int(n), int(c), int(r)))
            elif line.startswith('K '):
                _, k, W, n, c, r = line.split(); K.append((int(k), int(W), int(n), int(c), int(r)))
            elif line.startswith('P '):
                _, n, c, r = line.split(); P.append((int(n), int(c), int(r)))
            elif line.startswith('C '):
                _, n, c, ch = line.split(); C.append((int(n), int(c), int(ch)))
            elif line.startswith('H '):
                w = line.split(); H.append((int(w[1]), int(w[2]), float(w[3]), int(w[4]), int(w[5]), int(w[6])))
            elif line.startswith('S '):
                w = line.split()
                if cur is None or cur[0] != w[1] or (w[2] != 'endchain' and cur[1] and cur[1][-1].split()[2] == 'endchain'):
                    cur = (w[1], []); S_blocks.append(cur)
                cur[1].append(line.rstrip('\n'))
            elif line.startswith('T ') or line.startswith('N '):
                T.append(line.rstrip('\n'))
            elif line.startswith('DONE'):
                done = line.strip()
            elif line.startswith('STOP'):
                stop = line.strip()
    # the last complete S block (one ending with its endchain line)
    blk = None
    for b in S_blocks:
        if b[1] and b[1][-1].split()[2] == 'endchain': blk = b
    return dict(head=head, V=V, K=K, H=H, P=P, C=C, S=blk[1] if blk else [], done=done, T=T, stop=stop, path=path)

def parse_S(lines):
    bins = {}; tail = {}
    for l in lines:
        w = l.split()
        if w[2] == 'endchain':
            i = 3; h = {}
            while i < len(w) and ':' in w[i]:
                a, b = w[i].split(':'); h[int(a)] = int(b); i += 1
            tail = dict(endchain=h)
            while i + 1 < len(w):
                tail[w[i]] = int(w[i + 1]); i += 2
            continue
        b = int(w[2]); d = {}; i = 3
        while i < len(w):
            key = w[i]; i += 1
            if i < len(w) and ':' in w[i] and not re.match(r'^-?[0-9.]+$', w[i]):
                h = {}
                while i < len(w) and ':' in w[i]:
                    x, y = w[i].split(':'); h[int(x)] = int(y); i += 1
                d[key] = h
            elif i < len(w) and re.match(r'^-?[0-9.e+]+$', w[i]):
                v = w[i]; d[key] = float(v) if ('.' in v or 'e' in v) else int(v); i += 1
            else:
                d[key] = {}
        bins[b] = d
    return bins, tail

MAXKEYS = {'maxsig', 'maxsigmargin', 'maxchain', 'maxh', 'maxv2Q', 'maxv2qr'}
MINKEYS = {'minR', 'minD', 'mindelta', 'mindelta_next', 'minlu', 'minRW', 'minDW', 'minslack'}
# grouped keys (P1.minslack, E2.n, ...): a minimum or maximum by the name after the dot, else a count
def is_max(k): return k in MAXKEYS or ('.' in k and k.split('.')[-1].startswith('max'))
def is_min(k): return k in MINKEYS or k.startswith('mRW_') or k.startswith('mDW_') or ('.' in k and k.split('.')[-1].startswith('min'))

def merge_bins(all_bins):
    out = {}
    for bins in all_bins:
        for b, d in bins.items():
            o = out.setdefault(b, {})
            for k, v in d.items():
                if isinstance(v, dict):
                    h = o.setdefault(k, collections.Counter()); h.update(v)
                elif is_max(k):
                    o[k] = max(o.get(k, -1e18), v)
                elif is_min(k):
                    o[k] = min(o.get(k, 1e18), v)
                else:
                    o[k] = o.get(k, 0) + v
    return out

def main():
    outs = [read(p) for p in sys.argv[1:]]
    offsets = [(0, 0)]
    report = []
    for j in range(1, len(outs)):
        prev, cur = outs[j - 1], outs[j]
        s, z = cur['head']['start'], cur['head']['zone']
        tail = [v for v in prev['V'] if s <= v[0] < s + z]
        head = [v for v in cur['V'] if s <= v[0] < s + z]
        hs = {v[0]: v for v in head}
        join = next((v for v in tail if v[0] in hs), None)
        if join is None:
            report.append('stretch %d: NO JOIN in its window (tail %d, head %d clean tapes)' % (j, len(tail), len(head)))
            offsets.append(None); continue
        # from the join on, the two lists must agree
        ta = [v[0] for v in tail if v[0] >= join[0]]; hb = [v[0] for v in head if v[0] >= join[0]]
        m = min(len(ta), len(hb)); agree = ta[:m] == hb[:m]
        hv = hs[join[0]]
        po = offsets[j - 1]
        off = None if po is None else (po[0] + join[1] - hv[1], po[1] + join[2] - hv[2])
        offsets.append(off)
        report.append('stretch %d: joins the run at clean tape n = %d (%d clean tapes after the window start, %d in the earlier '
                      'stretch\'s tail); the lists agree from there on: %s (%d compared)'
                      % (j, join[0], sum(1 for v in head if v[0] < join[0]), sum(1 for v in tail if v[0] < join[0]), agree, m))
    print('# joins'); [print(r) for r in report]
    print('# stretches')
    for j, o in enumerate(outs):
        h = o['head']
        print('stretch %d (%s): start %d end %d zone %d: %s%s' % (j, o['path'], h['start'], h['end'], h['zone'],
              o['done'] or 'running', (' ' + o['stop']) if o['stop'] else ''))
    print('# checkpoints: k W n cycles rounds (absolute)')
    for j, o in enumerate(outs):
        off = offsets[j]
        for (k, W, n, c, r) in o['K']:
            if off is None: print('K %d %d %d ? ?' % (k, W, n))
            else: print('K %d %d %d %d %d' % (k, W, n, c + off[0], r + off[1]))
    print('# the first clean tape at or past each multiple of 10^11: n cycles rounds (absolute)')
    for j, o in enumerate(outs):
        off = offsets[j]
        for (n, c, r) in o['P']:
            print('P %d ? ?' % n if off is None else 'P %d %d %d' % (n, c + off[0], r + off[1]))
    print('# cycles whose end meetings make a halving chain of 11 or more: n cycles-before-n chain (absolute)')
    for j, o in enumerate(outs):
        off = offsets[j]
        for (n, c, ch) in o['C']:
            print('C %d ? %d' % (n, ch) if off is None else 'C %d %d %d' % (n, c + off[0], ch))
    bins_all = []; tails = []
    for o in outs:
        b, t = parse_S(o['S']); bins_all.append(b); tails.append(t)
    m = merge_bins(bins_all)
    print('# statistics per binary length of the width (summed over the stretches)')
    for b in sorted(m):
        d = m[b]
        flat = ' '.join('%s %s' % (k, v) for k, v in d.items() if not isinstance(v, collections.Counter))
        hists = ' '.join('%s %s' % (k, ' '.join('%d:%d' % (x, y) for x, y in sorted(v.items()))) for k, v in d.items()
                         if isinstance(v, collections.Counter))
        print('B %d %s | %s' % (b, flat, hists))
    ec = collections.Counter()
    for t in tails: ec.update(t.get('endchain', {}))
    print('E endchain', ' '.join('%d:%d' % (x, y) for x, y in sorted(ec.items())),
          'tw_canon', sum(t.get('tw_canon', 0) for t in tails))
    print('# closest end-meeting records (n cycle(rel) halvings chain d W), global records only')
    best = -1
    allH = sorted(h for o in outs for h in o['H'])
    for h in allH:
        if h[2] > best: best = h[2]; print('H', *h)

if __name__ == '__main__':
    main()
