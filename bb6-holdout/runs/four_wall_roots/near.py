import re, sys, numpy as np
from classify import origins
def entry_far(b, W, R, *_): D = W-b; return 15*W <= 64*D and 15*W + 26 <= 32*(D+R)
E = np.loadtxt(sys.argv[1] if len(sys.argv) > 1 else 'entries40.txt')
pts = E[:, :2]
out = []
for fn in ['n4.tsv', 'n5.tsv']:
    for line in open(fn):
        f = line.rstrip('\n').split('\t'); R, b, W = int(f[2]), int(f[3]), int(f[4])
        if W % 6 != 2: continue
        for x in origins(b, W, R):
            if x == ['entry']: rb, rW, rR, k = b, W, R, 'itself'
            else:
                m = re.findall(r'E=(\d+),R=(\d+),b=(\d+)', ' '.join(x))[-1]; rW, rR, rb = map(int, m); k = '/'.join(y.split('<-')[0] for y in x)
            if not entry_far(rb, rW, rR): continue
            r, d = rR / rW, (rW - rb) / rW
            dist = np.sqrt(((pts - [r, d]) ** 2).sum(1))
            i = dist.argmin()
            out.append((dist[i], fn[:2], f[1], k, r, d, rW % 4, pts[i], int(E[i, 3]), int((dist < 0.01).sum())))
out.sort()
for o in out: print(f'{o[0]:.4f} {o[1]} i={o[2]} {o[3]:10s} root R/W={o[4]:.4f} D/W={o[5]:.4f} W%4={o[6]} nearest run entry {o[7].round(4)} round {o[8]}; run entries within 0.01: {o[9]}')
