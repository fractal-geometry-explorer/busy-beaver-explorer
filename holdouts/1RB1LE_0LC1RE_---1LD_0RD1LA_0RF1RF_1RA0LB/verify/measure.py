# measure my own per-level step constants c(p,n)=a_p*n+b_p (front cost folded in, see mymodel) with my own simulator,
# and check the level table (next separator, growth, pass kind, transparency of the rest) on the way.
import random, json
from lib import *
from mymodel import *
def T(d):
    """two visits (hit+bounce) from digits word; returns steps, new digits"""
    c=[int(x) for x in from_digits(d)]
    h,n1,_,c1,_=one_visit(c,None); assert not h
    h,n2,_,c2,_=one_visit(c1,None); assert not h and n2==8
    return n1+n2, digits(''.join(map(str,c2)))
rows=[l for l in sim('',27000000,300,2990,1) if l[0]=='V']
rests={'H':[],'V':[]}
for l in rows:
    d=digits(l[3])
    if d[:2]==[2,1]: rests['H'].append(d[2:])
    elif d[0]==5: rests['V'].append(d[1:])
random.seed(11)
A={};B={};cases=0
for p in range(16):
    k=KIND[p]; vals={}
    for n in [1,2,3,4,5,8,13,30]:
        for trial in range(6):
            if p in PASSK:
                k2=PASSK[p]; U=random.choice(rests[k2])
                t1,w1=T(FRONTD[k]+[4]*n+list(SEP[p])+U); t2,w2=T(FRONTD[k2]+U)
                ko='V' if k2=='H' else 'H'; assert w2[:len(FRONTD[ko])]==FRONTD[ko]
                U2=w2[len(FRONTD[ko]):]; c=t1-t2
            else:
                U=random.choice(rests['H']+rests['V']+[[0]]); t1,w1=T(FRONTD[k]+[4]*n+list(SEP[p])+U); U2=U; c=t1
            kn='V' if k=='H' else 'H'
            exp=FRONTD[kn]+[4]*(n+(p in GROW))+list(SEP[(p+1)%16])+U2
            assert w1==exp,(p,n,fmt(w1)[:60],fmt(exp)[:60])
            vals.setdefault(n,set()).add(c); cases+=1
    assert all(len(v)==1 for v in vals.values()),(p,vals)
    v={n:min(s) for n,s in vals.items()}
    a=v[2]-v[1]; b=v[1]-a
    assert all(v[n]==a*n+b for n in v),(p,v)
    A[p]=a;B[p]=b
print('cases',cases); print('A',A); print('B',B)
json.dump({'A':A,'B':B},open('const.json','w'))
