"""Fingerprint screen: k-grams of (side, change in ones) at the new-extreme events written by tools/c/extev.c;
prints the pairs of machines (plain or mirrored) that share the most rare k-grams.  Run from a directory holding
open.txt and evs/<machine>.bin."""
import numpy as np, sys, os, collections
K=int(sys.argv[1]) if len(sys.argv)>1 else 16
CAP=100000
dt=np.dtype([('b','u1'),('o','<i4'),('s','<i8')])
ms=[l.split()[1] for l in open('/mnt/project-files/BB6_holdouts_608.txt')]
opn=set(open('open.txt').read().split())
docs=[];ids=[]
P=np.uint64(1000003)
def grams(tok):
    n=len(tok)-K+1
    if n<=0: return np.zeros(0,np.uint64)
    h=np.zeros(n,np.uint64)
    with np.errstate(over='ignore'):
        for j in range(K): h=h*P+tok[j:j+n].astype(np.uint64)
    return np.unique(h)
allg=[];allid=[]
for mi,m in enumerate(ms):
    f='evs/%s.bin'%m
    if not os.path.exists(f): continue
    a=np.fromfile(f,dt)
    if len(a)<2000: continue
    a=a[-CAP:] if len(a)>2*CAP else a[len(a)//2:]
    side=(a['b']>>3).astype(np.int64)
    do=np.diff(a['o'].astype(np.int64)); do=np.clip(do,-60,60)+61
    for mir in (0,1):
        sd=side[1:]^mir
        tok=sd*200+do
        g=grams(tok); allg.append(g); allid.append(np.full(len(g),2*mi+mir,np.int32))
G=np.concatenate(allg); I=np.concatenate(allid)
o=np.argsort(G,kind='stable'); G=G[o]; I=I[o]
b=np.flatnonzero(np.diff(G))+1; starts=np.r_[0,b]; ends=np.r_[b,len(G)]
cnt=collections.Counter(); sizes=collections.Counter(I.tolist())
for s,e in zip(starts,ends):
    if e-s<2 or e-s>12: continue
    ids_=sorted(set(I[s:e].tolist()))
    for x in range(len(ids_)):
        for y in range(x+1,len(ids_)):
            p,q=ids_[x],ids_[y]
            if p//2==q//2: continue
            if p%2==1: p,q=p^1,q^1
            if p>q: p,q=q,p
            cnt[(p,q)]+=1.0/(e-s)
res=[]
for (p,q),c in cnt.items():
    a,b_=p//2,q//2; mir=(p%2)!=(q%2)
    frac=c/min(sizes[p],sizes[q])
    res.append((frac,c,ms[a],ms[b_],mir))
res.sort(reverse=True)
for r in res[:200]:
    print('%.4f %8.1f %s %s %s %s%s'%(r[0],r[1],r[2],r[3],'M' if r[4] else 'F','o' if r[2] in opn else 'x','o' if r[3] in opn else 'x'))
