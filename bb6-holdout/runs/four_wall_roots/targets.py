"""Every far member at 2^66 (n4.tsv, n5.tsv, any W mod 6) and every state on its pull-back chains (classify.origins),
as (b, W, R) targets for window.c.  Prints: tag b W R (tag: member, or the step kind of a pull-back state)."""
import re
from classify import origins
seen = set()
for fn in ['n4.tsv', 'n5.tsv']:
    for line in open(fn):
        f = line.split('\t'); R, b, W = int(f[2]), int(f[3]), int(f[4])
        out = [('member', b, W, R)]
        for o in origins(b, W, R):
            for m in re.findall(r'(\w+)<-(?:entry)?\(E=(\d+),R=(\d+),b=(\d+)', ' '.join(o)):
                out.append((m[0], int(m[3]), int(m[1]), int(m[2])))
        for t in out:
            key = (t[1], t[2], t[3])
            if key in seen: continue
            seen.add(key); print(fn[:2], f[1], *t)
