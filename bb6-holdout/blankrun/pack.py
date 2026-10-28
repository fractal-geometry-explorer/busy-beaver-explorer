#!/usr/bin/env python3
"""Pack the three-wall round starts that follow.c wrote into TSV files with the settle depth of each cycle (streaming).

usage: python3 pack.py SETTLE_BINARY OUTDIR OUT0 OUT1 ...    (follow.c outputs in order of their START, so that the
                                                           lines come out in order of n)
writes OUTDIR/below2p34.tsv.gz (every three-wall round start of width < 2^34), OUTDIR/sample.tsv.gz (those of the
1/1024 hash sample of cycles at every width), OUTDIR/rare.tsv.gz (every landing other than a half pass, every i and x,
and the notable ones, at every width), OUTDIR/sample16k.tsv.gz (the 1/16384 hash sample).  Columns: HDR below; flags
are follow.c's, comma-separated."""
import sys, gzip, subprocess, os

HDR = ('n\tround\ta\tb\tc\tW\tR\tD\tcode\tchainpos\tsigma\tfamdist\tfamdist_next\tv2Q\tlog2u\tdepth\tflags\n')

def sampled(n, bits):
    return ((n * 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF) >> (64 - bits) == 0

def lines(outs):
    for p in outs:
        with open(p) as f:
            for l in f:
                if l[:2] in ('T ', 'N '): yield l

def main():
    settle, outdir = sys.argv[1], sys.argv[2]; outs = sys.argv[3:]
    os.makedirs(outdir, exist_ok=True)
    ns = sorted(set(int(l.split(None, 2)[1]) for l in lines(outs)))
    proc = subprocess.Popen([settle], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    out, _ = proc.communicate(''.join('%d\n' % n for n in ns))
    del ns
    dep = {}
    for l in out.split('\n'):
        w = l.split()
        if len(w) == 4: dep[int(w[0])] = w[1]
        elif w: dep[int(w[0])] = 'NA'
    del out
    names = ('below2p34', 'sample', 'rare', 'sample16k')
    fs = [gzip.open(os.path.join(outdir, x + '.tsv.gz'), 'wt', compresslevel=9) for x in names]
    for f in fs: f.write(HDR)
    cnt = [0, 0, 0, 0]; last = (-1, -1)
    for l in lines(outs):
        w = l.split()
        n, r = int(w[1]), int(w[2])
        if (n, r) <= last: sys.exit('lines out of order at %s' % l)
        last = (n, r)
        a, b, c, W = int(w[3]), int(w[4]), int(w[5]), int(w[6])
        flags = ','.join(w[14:])
        line = '\t'.join([w[1], w[2], w[3], w[4], w[5], w[6], str(W - c - 1), str(W - b), w[7], w[8], w[9], w[10], w[11],
                          w[12], w[13], dep[n], flags]) + '\n'
        if W < 2 ** 34: fs[0].write(line); cnt[0] += 1
        if sampled(n, 10): fs[1].write(line); cnt[1] += 1
        if w[7] not in ('E', 'H') or w[0] == 'N': fs[2].write(line); cnt[2] += 1
        if sampled(n, 14): fs[3].write(line); cnt[3] += 1
    for f in fs: f.close()
    print(' '.join('%s %d' % (x, c) for x, c in zip(names, cnt)))

if __name__ == '__main__':
    main()
