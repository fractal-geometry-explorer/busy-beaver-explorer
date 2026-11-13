"""For the five sister machines: how many of the irregular steps (anomalies and collisions) of the accelerated run
from blank tape are instances of rules proved in Lean (the partial macro map `astep` of their lean/Full.lean, whose
collision rows are `TABLES` in gen_collide.py), and whether the map agrees with the cell-by-cell simulation there.

usage: python3 coverage.py [NTRANSIENTS]     (default 300)
"""
import collections
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import amodel
from amodel import lead2
from gen_collide import TABLES
from hyb import Nphi, comp, from_blank, jcoll, jump, transient
def to_wag(W,k,q,g,rest):
    a,P=comp(k,q); return list(W),a,[3*p-1 for p in P]+([g]+rest if g is not None else [])
for M in list(TABLES)[1:]:
    amodel.TAB=TABLES[M]; n=int(sys.argv[1]) if len(sys.argv) > 1 else 300
    st=from_blank(M); D=collections.Counter(); bad=0
    for e in range(n):
        W,k,q,g,rest,_=st
        Ja,Jc=Nphi(W)//2,jcoll(k,q,g)
        st=jump(st,Ja if Jc is None else min(Ja,Jc))
        W,a,G=to_wag(*st[:5])
        r=transient(M,st,10**11)
        if r[0]!='OK': print('transient',r[0]); break
        exp=to_wag(*r[1][:5])
        if len(W)==1: kind='anom1'
        elif len(W)==2 and W[1]==1: kind='anom2' if a>=2 else 'anomU'
        else: kind='coll'
        if kind=='anomU': D['anomU (not in astep)']+=1
        else:
            try: res=amodel.astep(W,a,G)
            except Exception: res=(None,)
            if res[0] is None: D[kind+' uncovered']+=1
            else:
                D[kind+' covered']+=1
                if (list(res[1]),res[2],list(res[3]))!=exp: bad+=1
        st=r[1]
    print(M,dict(D),'mismatch',bad)
