import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__))); from macro import *
# validate: raw-simulate W alongside; at each macro configuration, raw sim must reach the same configuration.
def norm(q,l,r):
    while l and l[0]==0: l=l[1:]
    while r and r[-1]==0: r=r[:-1]
    return q,tuple(l),tuple(r)
m=Mac(); start=(0,[],[])
# raw W sim with explicit tape
from collections import defaultdict
t=defaultdict(int); h=0; q=0; steps=0
def rawconf():
    lo=min(t) if t else 0; hi=max(t) if t else 0
    l=[t[i] for i in range(min(lo,h),h)]; r=[t[i] for i in range(h,max(hi,h)+1)]
    return norm(q,l,r)
N=int(sys.argv[1]); checks=0
for it in range(N):
    m.step()
    if m.halt: print('HALT',m.halt); break
    if m.mode[0]=='mac':
        target=norm(*m.tape())
        # advance raw until match (bounded)
        for _ in range(10**6):
            if rawconf()==target: break
            b=t[h]; w,d,q2=TW[(q,b)]; t[h]=w; h+=d; q=q2; steps+=1
        else:
            print('MISMATCH at macro step',it,m.rule.most_common(3)); sys.exit(1)
        checks+=1
print('ok',checks,'macro configs matched;',steps,'raw W steps; rules',dict(m.rule), 'raw fallback steps',m.rawsteps, 'D0 left cells',collections.Counter(m.D0))
