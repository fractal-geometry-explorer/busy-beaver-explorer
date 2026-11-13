"""Generic accelerated simulator: rlsim.Sim (exact run-length simulation) + linear-cycle extrapolation at sample points.

At each sample point (head at an end of the tape, after re-tokenising with the given words), the configuration is
(state, side, word sequence, counts).  When the last three samples with the same shape have counts in arithmetic
progression and step counts with constant second difference, the cycle is applied k more times at once, k chosen so
that every decreasing count stays >= margin.  The extrapolation is checked: a cycle is only used if its shape has
already been seen to repeat 3 times exactly; and `verify` can compare with an unaccelerated run.
"""
import bisect, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rlsim import Sim, parse

def canon_multi(tok, words, minrun=2):
    starts=[];p=0
    for w,n in tok: starts.append(p); p+=len(w)*n
    total=p
    def seg(pos): return bisect.bisect_right(starts,pos)-1
    def ch(pos):
        i=seg(pos); w,n=tok[i]; return w[(pos-starts[i])%len(w)]
    def count(pos,word):
        L=len(word); k=0; q=pos
        while q+L<=total:
            i=seg(q); w,n=tok[i]; segend=starts[i]+len(w)*n
            o=(q-starts[i])%len(w)
            if len(w)%L==0 and (w[o:]+w[:o])==word*(len(w)//L) and segend-q>=2*L:
                m=(segend-q)//L; k+=m; q+=m*L; continue
            if all(ch(q+j)==word[j] for j in range(L)): k+=1; q+=L; continue
            break
        return k
    out=[];pos=0
    while pos<total:
        best=None
        for w in words:
            k=count(pos,w)
            if k>=minrun and (best is None or k*len(w)>best[1]*len(best[0])): best=(w,k)
        if best:
            out.append([best[0],best[1]]); pos+=best[1]*len(best[0])
        else:
            out.append([ch(pos),1]); pos+=1
    return out

class Acc:
    def __init__(self, machine, words, margin=3, minrun=2):
        self.m=machine; self.words=words; self.margin=margin; self.minrun=minrun
        self.s=Sim(machine,[['0',1]],0); self.s.dir=1
        self.hist={}; self.jumps=0; self.jumped_cycles=0
    def at_end(self):
        s=self.s
        return (s.h>=len(s.tok) and s.dir==1) or (s.h<0 and s.dir==-1)
    def sample(self):
        s=self.s
        side='R' if s.h>=len(s.tok) else 'L'
        s.tok=canon_multi(s.tok,self.words,self.minrun)
        s.h=len(s.tok) if side=='R' else -1
        key=(s.q,side,tuple(w for w,n in s.tok))
        counts=tuple(n for w,n in s.tok)
        h=self.hist.setdefault(key,[])
        h.append((counts,s.steps)); del h[:-3]
        if len(h)==3:
            (c1,t1),(c2,t2),(c3,t3)=h
            d1=tuple(b-a for a,b in zip(c1,c2)); d2=tuple(b-a for a,b in zip(c2,c3))
            if d1==d2 and any(d1):
                S=t3-t2; D=(t3-t2)-(t2-t1)
                ks=[(c-self.margin)//(-d) for c,d in zip(c3,d1) if d<0]
                k=min(ks) if ks else None
                if k is None: k=10**6
                if k>=2:
                    s.tok=[[w,n+k*d] for (w,n),d in zip(s.tok,d1)]
                    s.steps+=k*S+D*k*(k+1)//2
                    self.jumps+=1; self.jumped_cycles+=k
                    h.clear()
                    return key,True
        return key,False
    def run(self, maxsteps, on_sample=None):
        s=self.s
        while s.steps<maxsteps:
            r=s.run(maxsteps, lambda s: (s.h>=len(s.tok) and s.dir==1) or (s.h<0 and s.dir==-1))
            if r=='halt': return 'halt'
            if r=='max': return 'max'
            key,j=self.sample()
            if on_sample: on_sample(self,key,j)
        return 'max'
