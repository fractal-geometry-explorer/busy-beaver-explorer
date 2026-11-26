# proved busycoq tables two transitions from an open holdout (start state kept, any renaming of the others, mirror),
# then both machines run together with re-syncing (syncpair.resync)
import json,itertools,collections,re,sys
import os; sys.path.insert(0,os.path.join(os.path.dirname(os.path.abspath(__file__)),'../../../../tools/py'))
import syncpair
d=json.load(open('pool_raw.json')); dec=json.load(open('../dec.json'))
Hs=open('H.txt').read().split(); Hset=set(Hs)
openH=[h for h in Hs if dec.get(h,'open')=='open']
def slots(m): return [m[i*7+b*3:i*7+b*3+3] for i in range(6) for b in range(2)]
pool={P:[f for f in fs if not f.startswith('Eqv')] for P,fs in d['busycoq'].items() if P not in Hset}
pool={P:f for P,f in pool.items() if f}
PS={P:tuple(slots(P)) for P in pool}
L='ABCDEF'
perms=[p for p in itertools.permutations(range(6)) if p[0]==0]
Q=[]   # (h, relabelled table tuple)
seenq=set()
for h in openH:
    s=slots(h)
    for mir in (0,1):
        for p in perms:
            t=[None]*12
            for k in range(12):
                x=s[k]
                if x!='---':
                    dr=x[1]
                    if mir: dr='L' if dr=='R' else 'R'
                    x=x[0]+dr+L[p[L.index(x[2])]]
                t[p[k//2]*2+k%2]=x
            t=tuple(t)
            if (h,t) in seenq: continue
            seenq.add((h,t)); Q.append((h,t,mir,p))
print('queries',len(Q),flush=True)
pairs={}
for i in range(12):
    for j in range(i+1,12):
        idx=collections.defaultdict(list)
        for P,s in PS.items(): idx[s[:i]+s[i+1:j]+s[j+1:]].append(P)
        for h,t,mir,p in Q:
            for P in idx.get(t[:i]+t[i+1:j]+t[j+1:],()):
                s=PS[P]
                if s[i]!=t[i] and s[j]!=t[j] and '---' not in (s[i],s[j],t[i],t[j]):
                    pairs.setdefault((h,P),(mir,p))
print('distance-2 pairs with all four transitions defined',len(pairs),'holdouts',len({h for h,_ in pairs}),flush=True)
def relabel_back(P,mir,p):   # P written in H's state names
    inv={p[s]:s for s in range(6)}
    rows=[]
    for s in range(6):
        r=''
        for b in range(2):
            x=P[p[s]*7+b*3:p[s]*7+b*3+3]
            if x!='---':
                dr=x[1]
                if mir: dr='L' if dr=='R' else 'R'
                x=x[0]+dr+L[inv[L.index(x[2])]]
            r+=x
        rows.append(r)
    return '_'.join(rows)
out=[]
for n,((h,P),(mir,p)) in enumerate(sorted(pairs.items())):
    Pp=relabel_back(P,mir,p)
    r=syncpair.resync(h,Pp,False,100000,K=40)
    if r[0]!='fail':
        print(h,P,Pp,r[0],r[1],r[-1],pool[P],flush=True); out.append((h,P,Pp,r[0],pool[P]))
json.dump(out,open('near2_ok.json','w'))
print('done',len(out))
