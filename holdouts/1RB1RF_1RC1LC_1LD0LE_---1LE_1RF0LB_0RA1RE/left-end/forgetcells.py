import pickle,itertools
from fL import f
C=pickle.load(open('cstar_12.pkl','rb'))
seeds=set((q,b) for q in (1,2,3,4) for b in itertools.product((0,1),repeat=12))
# state: set of carries reachable after crossing exactly s cells (any token sequence), track minimal: we want for each s whether all carries reachable with crossed>=s are in C*
from collections import defaultdict
reach=defaultdict(set); reach[0]=seeds
maxs=40
for s in range(0,maxs):
    for (q,w) in list(reach[s]):
        for a in range(1,12):
            if s+a+1>maxs: break
            r=f(q,w,a)
            if isinstance(r[0],str): continue
            reach[s+a+1].add((r[0],r[1][:12]))
for s in range(1,maxs+1):
    bad=sum(1 for c in reach[s] if c not in C)
    print(s,len(reach[s]),'not in C*',bad)
