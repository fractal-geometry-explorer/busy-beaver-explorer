# positive controls: random machines that are not trivially decided; which table sizes decide them?
# usage: controls.py seed count states
import random, sys, json, collections
import contractsat as cs, check
from sanity import rnd
def run(m,N):
    t=cs.parse(m); tape={}; pos=0; s=0; lo=hi=0
    for i in range(N):
        tr=t[(s,tape.get(pos,0))]
        if tr is None: return None
        tape[pos]=tr[0]; pos+=tr[1]; s=tr[2]; lo=min(lo,pos); hi=max(hi,pos)
    return hi-lo
random.seed(int(sys.argv[1])); S=int(sys.argv[3])
hist=collections.Counter(); tried=0
while tried<int(sys.argv[2]):
    m=rnd(S)
    if not m.startswith('1RB'): continue
    sp=run(m,3000)
    if sp is None or sp<12: continue
    if run(m,300000) is None: continue
    got=None
    for (n,W) in ((2,2),(3,4),(4,6),(6,8),(8,12)):
        for side in 'LR':
            e=cs.Enc(m,side=='R',n,W,verbose=False,sym=True); c=e.solve(tlimit=30)
            if isinstance(c,dict):
                check.check(json.loads(json.dumps(c))); got=(n,W,side); break
        if got: break
    if got and got[0]==2: continue
    tried+=1
    hist[got and got[:2]]+=1
    print(m,got,(len(c['window']),len(c['R'])) if got else '',flush=True)
print(sorted(hist.items(),key=str))
