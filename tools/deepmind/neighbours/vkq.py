"""DeepMind's WordVKQ lemmas (cryptids BusyBeaver/Calculi/WordCalculusF.lean and the per-machine segment and
turnaround lemmas of BB6/NonHalt/M_1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RAHHH.lean), re-run by simulation.

usage: python3 vkq.py MACHINE...   (prints, for each of the 12 SegSpec segments and the 7 turnaround pieces, whether
the machine satisfies it; DeepMind's own machine passes all of them)
"""
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from seg import *
# State roles in DeepMind's file for 1RB0RE_1LC1RA_1LD0LC_1LA0LA_1RA1RF_0RA---
def mk(roles):
    A,C,E=roles['A'],roles['C'],roles['E']
    zCs={'ch':E,'ca':C}
    def zCR(w,c,r,ut='u',rt='r'):  # ([1]+>r) {{zCs c}}> w
        l=[1]+r
        if w: return (zCs[c],l,w[0],w[1:],rt,ut)
        return (zCs[c],l,None,[],rt,ut)
    def zCL(w,r,ut='u',rt='r'):    # r <{{A}} ([0]+>w)
        right=[0]+w
        if r: return (A,r[1:],r[0],right,rt,ut)
        return (A,[],None,right,rt,ut)
    return zCR,zCL
V=[1,1,0,0];K=[0,0];Q=[1,0];Vp=[0,1,1,0];Kp=[0,0];Qp=[0,1]
SEGS=[ # name, c_in, outs, w1, w2, mids
 ('ch_V','ch',['ch','ch'],V,V,[[1,0,1,1],[1,0,1,0]]),
 ('ca_V','ca',['ch'],V,Vp,[[0,1,0,1]]),
 ('ca_Vp','ca',['ca','ca'],Vp,Vp,[[0,1,1,1],[0,1,0,1]]),
 ('ch_K','ch',[],K,Q,[]),
 ('ch_Q','ch',['ch'],Q,K,[[1,1]]),
 ('ca_VpQ','ca',['ca'],Vp+Q,Kp+Vp,[[0,1,0,1,1,1]]),
 ('ca_KpVp','ca',[],Kp+Vp,Qp+Vp,[]),
 ('ca_QpVp','ca',['ca','ca'],Qp+Vp,Kp+Vp,[[0,1,1,1,1,1],[0,1,0,1,1,1]]),
 ('ca_Kp','ca',[],Kp,Qp,[]),
 ('ca_Qp','ca',['ca'],Qp,Kp,[[1,1]]),
 ('ca_KQ','ca',[],K+Q,Vp,[]),
 ('ca_QQ','ca',['ca'],Q+Q,Vp,[[0,1,0,1]]),
]
def check_segs(m,roles,verbose=True):
    T=parse(m); zCR,zCL=mk(roles); allok=True
    for name,cin,outs,w1,w2,mids in SEGS:
        res=[]
        if not outs:
            res.append(run(T,zCR(w1,cin,[]),zCL(w2,[])))
        else:
            # h1: zCR(w1+u) cin r -> zCR u outs[0] (mid1+r)
            res.append(run(T,zCR(w1,cin,[]),zCR([],outs[0],mids[0])))
            for i in range(1,len(outs)):
                res.append(run(T,zCL([],mids[i-1]),zCR([],outs[i],mids[i])))
            res.append(run(T,zCL([],mids[-1]),zCL(w2,[])))
        ok=all(x[0]=='ok' for x in res); allok&=ok
        if verbose: print(name,ok,res)
    return allok
pref24=[1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,0,0,1,1,0,0,1,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0]
TR=[None,
[0,1,1,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1],
[0,1,0,1,0,1,1,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1],
[0,1,1,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1],
[0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1],
[0,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1],
[0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1,0,0,1,0,1,0,1,0,1,1,1,0,1]]
def check_turn(m,roles):
    T=parse(m); zCR,zCL=mk(roles); A=roles['A']
    def zCf(w): return (A,[],0,[0]+pref24+w,'B','w')   # default <{{A}} ([0]+>pref24+>w)
    out=[]
    # zP0: zCf w -> zCR w ca (tr1 +> default)
    def zCRd(w,c,r): x=zCR(w,c,r,ut='w',rt='B'); return x
    def zCLd(w,r): return zCL(w,r,ut='w',rt='B')
    out.append(run(T,zCf([]),zCRd([],'ca',TR[1])))
    for i in range(1,6): out.append(run(T,zCLd([],TR[i]),zCRd([],'ca',TR[i+1])))
    out.append(run(T,zCLd([],TR[6]),zCf([1,1,0])))
    print('turn',out); return all(x[0]=='ok' for x in out)
if __name__=='__main__':
    roles={'A':2,'C':0,'E':1}
    for m in sys.argv[1:]:
        print('==',m); check_segs(m,roles); check_turn(m,roles)
