import re,os,sys,collections
V=__import__('os').environ.get('BUSYCOQ_VERIFY','busycoq/verify')
rx=re.compile(r'"([01-][RL-][A-F-][01-][RL-][A-F-](?:_[01-][RL-][A-F-][01-][RL-][A-F-]){5})"')
where=collections.defaultdict(set)
for f in os.listdir(V):
    if not f.endswith('.v'): continue
    if f.startswith('Eqv') : continue
    for m in rx.finditer(open(os.path.join(V,f),errors='ignore').read()):
        where[m.group(1)].add(f)
def mirror(t): return t.replace('L','x').replace('R','L').replace('x','R')
def trans(t): return [t[i*7+b*3:i*7+b*3+3] for i in range(6) for b in range(2)]
def norm(x): return '---' if x[0]=='-' else x
H=[l.split()[1] for l in open(__import__('os').environ.get('HOLDOUTS','BB6_holdouts_608.txt'))]
Hs=set(H)
solved={t:fs for t,fs in where.items() if t not in Hs}
st=[(t,trans(t)) for t in solved]+[(t,trans(mirror(t))) for t in solved]
out=[]
idx=collections.defaultdict(list)
for t,tt in st:
    tt=[norm(x) for x in tt]
    for g in range(3): idx[(g,tuple(tt[g*4:g*4+4]))].append((t,tt))
for h in H:
    th=[norm(x) for x in trans(h)]
    best=set()
    for g in range(3):
        for t,tt in idx.get((g,tuple(th[g*4:g*4+4])),[]):
            d=sum(1 for a,b in zip(th,tt) if a!=b)
            if d<=2: best.add((d,t))
    best=list(best)
    best.sort()
    for d,t in best[:6]:
        out.append((h,d,t,sorted(solved[t])))
import json
json.dump(out,open('near.json','w'))
c=collections.Counter()
for h,d,t,fs in out:
    for f in fs: c[re.sub(r'(_solved|\d+)?\.v$','',f)]+=1
print(len(set(o[0] for o in out)),'holdouts with a proved machine within 2 transitions')
print(sum(1 for o in out if o[1]==1),'pairs at distance 1')
for k,v in c.most_common(40): print(v,k)
