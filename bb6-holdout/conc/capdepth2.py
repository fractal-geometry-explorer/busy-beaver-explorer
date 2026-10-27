import re
from capdepth import fam_of
from ewlock2 import consistent
for l in open('../entrycaps.txt'):
    m = re.match(r"route (\d+) \+ (\d+) passes \+ entry (\d+): words \['[PQ]{3}", l)
    if not m: continue
    ri, p, si = map(int, m.groups())
    fam = fam_of(ri, p, si); frontier = ['']; L = 0
    while L < 10:
        nxt = [w + x for w in frontier for x in 'PQ' if consistent(fam, 2, w + x)]
        if not nxt: break
        frontier = nxt; L += 1
    print(ri, p, si, 'longest', L, frontier)
