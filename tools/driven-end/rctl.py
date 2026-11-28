"""Closed tape language for the 'reflective end' system: one-sided tape (cells 0..), a wall left of cell 0.
Head enters cell 0 in state X; when it steps left onto the wall in state Y it re-enters cell 0 in X (one call).
Stepping onto the wall in any other state, or a halting transition, is a failure.
Abstract config: (state, L, R): R = window of K letters from the head cell outward (0,1,H=blank beyond),
L = window of K letters left of the head outward (0,1,Wl=wall here and beyond)."""
import sys
from collections import deque
H=2; WL=2
def parse(m):
    t=[]
    for part in m.split('_'):
        row=[]
        for b in range(2):
            x=part[3*b:3*b+3]
            row.append(None if x[0]=='-' else (int(x[0]), 1 if x[1]=='R' else -1, ord(x[2])-65))
        t.append(row)
    return t
def canonR(w):
    w=list(w)
    for i in range(len(w)-1,0,-1):
        if w[i]==H and w[i-1]==0: w[i-1]=H
    return tuple(w)
def canonL(w):
    w=list(w)
    for i in range(1,len(w)):
        if w[i-1]==WL: w[i]=WL
    return tuple(w)
def val(a): return 0 if a==H else a
def run(m,X,Y,init,K,maxcfg=2_000_000,verbose=True):
    tm=parse(m)
    # seed windows from initial word
    w=[int(c) for c in init]
    Rw=set(); 
    full=w+[H]*K
    for i in range(len(w)+1): Rw.add(canonR(tuple(full[i:i+K])))
    Lw={tuple([WL]*K)}
    start=(X,tuple([WL]*K),canonR(tuple(full[:K])))
    while True:
        nR=len(Rw); nL=len(Lw)
        def succR(r):  # windows that can follow after popping r[0]
            out=[]
            for r2 in Rw:
                if canonR((val(r[0]),)+r2[:K-1])==r: out.append(r2)
            if all(x==H for x in r): out.append(r)
            return out
        def succL(l):
            out=[]
            for l2 in Lw:
                if canonL((l[0],)+l2[:K-1])==l: out.append(l2)
            if all(x==WL for x in l): out.append(l)
            return out
        cR={}; cL={}
        seen={start}; dq=deque([start]); fails=[]
        while dq:
            q,l,r=dq.popleft()
            x=val(r[0]); tr=tm[q][x]
            if tr is None: fails.append(('halt',q,l,r)); continue
            wr,d,nq=tr
            nxt=[]
            if d==1:
                nl=canonL((wr,)+l[:K-1]); Lw.add(nl)
                if r not in cR: cR[r]=succR(r)
                for r2 in cR[r]: nxt.append((nq,nl,r2))
            else:
                if l[0]==WL:
                    if nq!=Y: fails.append(('wall',q,l,r,nq)); continue
                    nr=canonR((wr,)+r[1:]) if False else canonR((wr,)+r[1:K])
                    Rw.add(nr); nxt.append((X,l,nr))
                else:
                    nr=canonR((l[0],wr)+r[1:K-1]); Rw.add(nr); Rw.add(canonR((wr,)+r[1:K]))
                    if l not in cL: cL[l]=succL(l)
                    for l2 in cL[l]: nxt.append((nq,l2,nr))
            for c in nxt:
                if c not in seen:
                    seen.add(c); dq.append(c)
                    if len(seen)>maxcfg: return ('too many',len(seen),len(Rw),len(Lw))
        if fails:
            return ('fail',fails[:5],len(seen),len(Rw),len(Lw))
        if len(Rw)==nR and len(Lw)==nL:
            return ('closed',len(seen),len(Rw),len(Lw),seen)
if __name__=='__main__':
    m,X,Y,init,K=sys.argv[1],ord(sys.argv[2])-65,ord(sys.argv[3])-65,sys.argv[4],int(sys.argv[5])
    print(run(m,X,Y,init,K))
