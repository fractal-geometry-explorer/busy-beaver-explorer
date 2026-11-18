"""Backward trees of the halting values: every D whose orbit reaches b^n.

For each target E the preimages are found exactly: for each valuation v with b^v <= E and each last digit rho,
D = b^v (b a + rho) with a = (E - b^v rho - beta(v, rho)) / (b^(v+1) + alpha) when that is a whole number, checked
against the machine's exact map (so the exceptional rules are respected); the exceptional sources (odd part 3 in
base 2, a pure power of 3 in base 3) are tried directly.  States with r = 2 (only after an exception) are ignored.

usage: tree.py MACHINE N      depth and size of the tree of b^n for every n <= N (writes tree_MACHINE_N.json)
"""
import sys, json
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from djump import exact_step, MACHINES
def preimages(name, E):
    _, b, alpha, beta, _ = MACHINES[name]
    out=[]
    v=0
    while b**v <= E:
        q=b**(v+1)+alpha
        for rho in ([1] if b==2 else [1,2]):
            num=E-b**v*rho-beta(v,rho)
            if num>=0 and num%q==0:
                a=num//q
                D=b**v*(b*a+rho)
                r=exact_step(name,D,1)
                if r and r[0]==E and r[1]==1: out.append(D)
        # exceptional sources: odd part 3 (base 2) / power of 3 (base 3)
        for D in ([3*2**v] if b==2 else [3**v]):
            for r0 in (1,2) if name in ('M53','M86') else (1,):
                r=exact_step(name,D,r0)
                if r and r[0]==E and D not in out: out.append(D)
        v+=1
    return sorted(set(out))
def tree(name,E,cap=10**6):
    depth=0; frontier=[E]; size=1; nodes=[]
    while frontier and size<cap:
        nxt=[]
        for x in frontier:
            for p in preimages(name,x):
                if p>=4: nxt.append(p)
        if nxt: depth+=1
        size+=len(nxt); nodes+=nxt; frontier=nxt
    return depth,size,min(nodes) if nodes else None
if __name__=='__main__':
    name=sys.argv[1]; N=int(sys.argv[2])
    b=MACHINES[name][1]
    res={}
    for n in range(2,N+1):
        d,s,mn=tree(name,b**n)
        res[n]=(d,s)
    ds=[d for d,s in res.values()]; ss=[s for d,s in res.values()]
    print(name,'n<=%d'%N,'max depth',max(ds),'at n=',[n for n in res if res[n][0]==max(ds)][:5],'mean size %.3f'%(sum(ss)/len(ss)),'max size',max(ss))
    from collections import Counter
    print(' depth histogram',sorted(Counter(ds).items()))
    json.dump(res,open('tree_%s_%d.json'%(name,N),'w'))
