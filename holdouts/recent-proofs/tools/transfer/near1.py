import json,itertools,collections,re
d=json.load(open('pool_raw.json')); dec=json.load(open('../dec.json'))
Hs=open('H.txt').read().split(); Hset=set(Hs)
openH=[h for h in Hs if dec.get(h,'open')=='open']
def slots(m): return [m[i*7+b*3:i*7+b*3+3] for i in range(6) for b in range(2)]
pool={P:[f for f in fs if not f.startswith('Eqv')] for P,fs in d['busycoq'].items() if P not in Hset}
pool={P:f for P,f in pool.items() if f}
idx=collections.defaultdict(list)
for P in pool:
    s=slots(P)
    for i in range(12):
        idx[(i,tuple(s[:i]+s[i+1:]))].append(P)
print('indexed',len(pool))
perms=list(itertools.permutations(range(6)))
L='ABCDEF'
out=collections.defaultdict(set)
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
            for i in range(12):
                for P in idx.get((i,tuple(t[:i]+t[i+1:])),()):
                    out[h].add((P,mir,''.join(map(str,p)),i, t[i]==slots(P)[i]))
res={h:sorted(v) for h,v in out.items()}
json.dump(res,open('near1.json','w'))
print(len(res),'open holdouts with a proved table at distance <=1;',sum(len(v) for v in res.values()),'pairs')
c=collections.Counter()
for h,v in res.items():
    for P,mir,p,i,same in v:
        for f in pool[P]: c[re.sub(r'\d*\.v$','',f)]+=1
print(c.most_common(40))
