"""DeepMind's stack-model lemmas for 1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RB--- (cryptids
BB6/NonHalt/M_1RB0LD_1RC0RE_1LD0RE_1LA0LA_1RB1RF_1RBHHH.lean: cfgC, cfgD, cfgE and step_D0 ... step_E3), re-run by
simulation for small parameter values.

usage: python3 u3.py MACHINE...   (prints which lemmas fail and how often; DeepMind's machine fails none)
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from seg import parse, run
A,B,C,D,E,F=1,2,3,0,4,5
def encL(cs):
    out=[]
    for c in cs: out+= [1,0]*c+[1]
    return out
def encR(rs):
    out=[]
    for it in rs:
        k,d,c=it
        if k=='00': out+=[1,0]*d+[0,0]+[0,1]*c
        else: out+=[1,0]*d+[0,1]*(c+1)
    return out+[1,0,0,1]
def Lcfg(l,q,r):  # l <{{q}} r, l nearest-first, blank tails
    l=l or [0]
    return (q,l[1:],l[0],r,'B','B')
def Rcfg(l,q,r):
    r=r or [0]
    return (q,l,r[0],r[1:],'B','B')
cfgC=lambda cs,rs: Lcfg(encL(cs),C,[0]+encR(rs))
cfgD=lambda cs,c,rs: Lcfg(encL(cs),D,[0,0]+[0,1]*c+encR(rs))
cfgE=lambda cs,c,rs: Rcfg([0,1]*(c+1)+encL(cs),E,encR(rs))
def lemmas(n):
    rng=range(n)
    L=[]
    for c in rng:
        for rs in [[],[('00',1,2)],[('01',2,1)]]:
            L.append(('D0',cfgD([],c,rs),cfgE([1],c,rs)))
            for d in rng:
                L.append(('D_cons_to_C',cfgD([d],c,rs),cfgC([],[('00',d,c)]+rs)))
                L.append(('C_cons_to_D',cfgC([c,d],rs),cfgD([d],c,rs)))
                L.append(('C_nil_item00_to_E',cfgC([],[('00',d,c)]+rs),cfgE([d+2],c,rs)))
                L.append(('D1',cfgD([d],c,rs),cfgE([d+2],c,rs)))
                for c2 in rng:
                    L.append(('D2',cfgD([d,c2,1],c,rs),cfgD([1],c2,[('00',d,c)]+rs)))
                    L.append(('E1',cfgE([3],c,[('00',d+1,c2)]+rs),cfgD([3],c+1,[('01',d,c2)]+rs)))
                    L.append(('E2',cfgE([3],c,[('01',0,c2)]+rs),cfgE([3],c+c2+1,rs)))
                    L.append(('E3',cfgE([3],c,[('01',d+1,c2)]+rs),cfgE([d,c+1,3],c2,rs)))
        L.append(('E0',cfgE([2],c,[]),cfgD([c+1,2],0,[])))
    return L
for m in sys.argv[1:]:
    T=parse(m); bad={}
    tot={}
    for name,a,b in lemmas(4):
        r=run(T,a,b,10**5); tot[name]=tot.get(name,0)+1
        if r[0]!='ok': bad[name]=bad.get(name,0)+1
    print(m,'fails:',bad,'of',tot)

def failing(m,n=5):
    T=parse(m)
    rng=range(n)
    out=[]
    for c in rng:
      for rs in [[],[('00',1,2)],[('01',2,1)]]:
        if run(T,cfgD([],c,rs),cfgE([1],c,rs),10**5)[0]!='ok': out.append(('D0',c,rs))
        for d in rng:
          if run(T,cfgC([],[('00',d,c)]+rs),cfgE([d+2],c,rs),10**5)[0]!='ok': out.append(('Cnil00E',d,c,rs))
          if run(T,cfgD([d],c,rs),cfgE([d+2],c,rs),10**5)[0]!='ok': out.append(('D1',d,c,rs))
          for c2 in rng:
            if run(T,cfgE([3],c,[('01',d+1,c2)]+rs),cfgE([d,c+1,3],c2,rs),10**5)[0]!='ok': out.append(('E3',d,c,c2,rs))
    return out
