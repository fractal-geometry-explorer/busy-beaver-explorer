import re,collections,json
rx=re.compile(r"(\S+) ([LR]) (\w) M=(\d*) E=(\d*) D1=(\d*) -> (\w) M'=(\d*) F=(\d*) D0=(\d*) \| cnt=(\d+) nmax=(\d+)")
def rot(a,b): return len(a)==len(b) and b in a+a
used=collections.defaultdict(list)
for l in open('relev_all.txt'):
    m=rx.match(l)
    if not m: continue
    g=m.groups()
    side,q,M,E,D1,q2,M2,F,D0,cnt,nmax=g[1:]
    if int(nmax)<6 or rot(D1,D0): continue
    used[g[0]].append(dict(side=side,q=q,M=M,E=E,D1=D1,q2=q2,M2=M2,F=F,D0=D0,cnt=int(cnt),nmax=int(nmax)))
H=[l.split()[1] for l in open(__import__('os').environ.get('HOLDOUTS','BB6_holdouts_608.txt'))]
out={};cls=collections.Counter()
for h in H:
    rs=used.get(h,[])
    L=[r for r in rs if r['side']=='L'];R=[r for r in rs if r['side']=='R']
    pairs=[(a,b) for a in L for b in R if a['q2']==b['q'] and a['M2']==b['M'] and b['q2']==a['q'] and b['M2']==a['M']]
    key=lambda r:(r['nmax'],-len(r['M'])-len(r['E'])-len(r['D1']))
    if pairs:
        a,b=max(pairs,key=lambda p:min(key(p[0]),key(p[1]))); c='two counters, head bouncing between them'; best={'L':a,'R':b}
    elif L and R: c='counters on both sides, not linked'; best={'L':max(L,key=key),'R':max(R,key=key)}
    elif rs: c='one counter'; best={s:max([r for r in rs if r['side']==s],key=key) for s in {r['side'] for r in rs}}
    else: c='no counter-carry rule in use'; best={}
    cls[c]+=1; out[h]=dict(cls=c,best=best)
for k,v in cls.most_common(): print(v,k)
json.dump(out,open('counters.json','w'),indent=0)
fam=json.load(open(__import__('os').environ.get('FAMILIES','families.json')))
famof={m:k for k,v in fam.items() for m in v['machines']}
t=collections.defaultdict(collections.Counter)
for h,d in out.items(): t[famof.get(h,'none')][d['cls']]+=1
json.dump({k:dict(v) for k,v in t.items()},open('byfamily.json','w'),indent=0)
for k in sorted(t): print(k,dict(t[k]))
