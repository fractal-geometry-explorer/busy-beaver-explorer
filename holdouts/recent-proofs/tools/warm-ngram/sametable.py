# Open holdouts whose transition table (up to renaming states and mirroring) appears in a busycoq Rocq file
# with another start state.  usage: python3 sametable.py BUSYCOQ_VERIFY_DIR OPEN_LIST > out.txt
import sys
import re,glob,itertools,collections
def parse(m):
    rows=m.split('_'); return [[None if r[3*b+2] in '-Z' else (r[3*b],r[3*b+1],ord(r[3*b+2])-65) for b in range(2)] for r in rows]
def canon(tab,fix=False):
    n=len(tab); best=None
    for mir in (0,1):
        for p in itertools.permutations(range(n)):  # p[old]=new
            if fix and p[0]!=0: continue
            t=[None]*n
            for q in range(n):
                row=[]
                for b in range(2):
                    x=tab[q][b]
                    if x is None: row.append('---')
                    else:
                        d=x[1] if not mir else ('L' if x[1]=='R' else 'R')
                        row.append(x[0]+d+chr(65+p[x[2]]))
                t[p[q]]=''.join(row)
            s='_'.join(t)
            if best is None or s<best: best=s
    return best
def sig(m):
    out=[]
    for mir in (0,1):
        rows=[]
        for r in m.split('_'):
            t=r
            if mir: t=t.replace('L','x').replace('R','L').replace('x','R')
            rows.append(''.join(c for i,c in enumerate(t) if i%3!=2 or c=='-'))
        out.append(tuple(sorted(rows)))
    return min(out)
openm=[l.strip() for l in open(sys.argv[2])]
key={}
for m in openm: key.setdefault(canon(parse(m)),[]).append(m)
sigs=set(sig(m) for m in openm)
hits=collections.defaultdict(set)
for f in glob.glob(sys.argv[1]+'/*.v'):
    for m in set(re.findall(r'"([01][LR][A-F-]|---)',open(f).read()) and re.findall(r'"((?:[01-][LR-][A-F-]){2}(?:_(?:[01-][LR-][A-F-]){2}){5})"',open(f).read())):
        m=m.replace('---','1RZ') if False else m
        if sig(m) not in sigs: continue
        try: k=canon(parse(m))
        except Exception: continue
        if k in key:
            ks=canon(parse(m),True)
            if all(canon(parse(o),True)!=ks for o in key[k]): hits[tuple(key[k])].add((m,f.split('/')[-1]))
for k,v in sorted(hits.items()):
    print(' '.join(k)); [print('   ',a,b) for a,b in sorted(v)]
print(len(hits))
