import collections, sys
from fractions import Fraction as F
def nullspace(rows):
    m=[[F(x) for x in r] for r in rows]; nc=len(m[0]); piv=[]; r=0
    for c in range(nc):
        p=next((i for i in range(r,len(m)) if m[i][c]!=0),None)
        if p is None: continue
        m[r],m[p]=m[p],m[r]; m[r]=[x/m[r][c] for x in m[r]]
        for i in range(len(m)):
            if i!=r and m[i][c]!=0: m[i]=[a-m[i][c]*bb for a,bb in zip(m[i],m[r])]
        piv.append(c); r+=1
    free=[c for c in range(nc) if c not in piv]; out=[]
    for f in free:
        v=[F(0)]*nc; v[f]=F(1)
        for i,c in enumerate(piv): v[c]=-m[i][f]
        from math import lcm
        L=lcm(*[x.denominator for x in v]); out.append([int(x*L) for x in v])
    return r,out
rows=collections.defaultdict(list)
for l in open('entries_all.txt'):
    n,rd,b,W,R=map(int,l.split()); rows[rd].append((n,b,W,R))
for rd in sorted(rows, key=lambda k:-len(rows[k]))[:20]:
    X=rows[rd][::max(1,len(rows[rd])//40)][:40]
    rk,ns=nullspace([[b,W,R,1] for n,b,W,R in X]); rk2,ns2=nullspace([[n,b,W,R,1] for n,b,W,R in X])
    print(rd, len(rows[rd]), 'rank[b W R 1]',rk, ns, ' rank[n b W R 1]', rk2, ns2)
