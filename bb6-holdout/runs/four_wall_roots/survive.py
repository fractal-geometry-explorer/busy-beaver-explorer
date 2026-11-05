import sys, re
from classify import origins
def entry_far(b, W, R, *_): D = W-b; return 15*W <= 64*D and 15*W + 26 <= 32*(D+R)
for fn in sys.argv[1:]:
    tot = s2 = sh = far = reg = 0; b7 = 0; lst=[]
    for line in open(fn):
        f = line.rstrip('\n').split('\t'); R, b, W = int(f[2]), int(f[3]), int(f[4])
        tot += 1
        if W % 6 != 2: continue
        s2 += 1
        o = origins(b, W, R)
        if not o: continue
        sh += 1
        roots = []
        for x in o:
            if x == ['entry']: roots.append((b, W, R, 'itself'))
            else:
                m = re.findall(r'E=(\d+),R=(\d+),b=(\d+)', ' '.join(x))[-1]; rW, rR, rb = map(int, m)
                roots.append((rb, rW, rR, '/'.join(y.split('<-')[0] for y in x)))
        fr = [r for r in roots if entry_far(*r)]
        if fr: far += 1
        rg = [r for r in fr if r[2]/r[1] >= 0.035 and (r[1]-r[0])/r[1] >= 0.455]
        if rg: reg += 1; lst.append((f[1], [(r[3], round(r[2]/r[1],4), round((r[1]-r[0])/r[1],4)) for r in rg]))
    print(fn, 'members', tot, 'W=2 mod 6', s2, 'with a possible origin', sh, 'with an EntryFar root', far, 'and in the run entry region', reg)
    for x in lst: print('   ', x)
