"""A closed-tape-language search with windows of K *letters* instead of K cells (an experiment; it did not close).

A letter is a cell 0 or 1, `#` (this cell and all beyond are blank), or a maximal run of the word w (10 on the
right of the head, read outward as 01 on the left) of exactly c copies for c < T, or of T or more copies.  Each
side's automaton has the windows (first K letters of the stream read outward from the head) as states, with an
edge W -x-> W' whenever pushing the cell x onto a stream with window W' gives window W; so the automata are
ordinary cell automata and the result could be checked by `TM.CTL.check` in Lean like the windows of `bbtools.ctl`.
For this machine the least closed set from blank tape still allows halts for K <= 6, T = 3 (K = 6: 132 left and
1564 right windows, 434,928 abstract configurations, 41,339 of them can halt, all with small blocks w1 0 w1 0 ...
around the head); K = 8 did not finish in 15 minutes.

usage: python3 tctl.py MACHINE K T [K_LEFT]
"""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "tools", "py"))
from collections import deque
from bbtools.machine import Machine
from bbtools import ctl
H='#'
class Side:
    def __init__(s,K,T,w):
        s.K,s.T,s.w=K,T,w
    def push(s,x,W2):
        w0,w1=s.w
        if W2[0]==H:
            out=(H,) if x==0 else (1,H)
        elif x==w0 and W2[0]==w1:
            if len(W2)>1 and isinstance(W2[1],tuple):
                out=(('W',min(W2[1][1]+1,s.T)),)+W2[2:]
            else:
                out=(('W',1),)+W2[1:]
        else:
            out=(x,)+W2
        out=out[:s.K]
        if len(out)<s.K:
            out=out+(H,)*(s.K-len(out))
        # canon: H absorbing
        o=list(out)
        for i in range(len(o)):
            if o[i]==H: o[i+1:]=[H]*(len(o)-i-1); break
        return tuple(o)
class TAuto:
    def __init__(s,side,windows):
        s.side=side; s.windows=list(windows); s.index={w:i for i,w in enumerate(s.windows)}
        s.edges=[]
        for i,w in enumerate(s.windows):
            for j,w2 in enumerate(s.windows):
                for x in (0,1):
                    if side.push(x,w2)==w: s.edges.append((i,x,j))
        blank=(H,)*side.K
        s.acc=[s.index[blank]]
        s._pops={}
        for (a,x,b) in s.edges: s._pops.setdefault(a,[]).append((x,b))
        s._preds={}
        for (a,x,b) in s.edges: s._preds.setdefault((b,x),[]).append(a)
    def pops(s,q):
        out=list(s._pops.get(q,[]))
        if q in s.acc: out.append((0,q))
        return out
    def preds(s,q,x): return s._preds.get((q,x),[])
    def after(s,q,word):
        qs=[q]
        for x in word: qs=[q2 for q1 in qs for (y,q2) in s.pops(q1) if y==x]
        return qs
    def blank_only(s):
        B=set(range(len(s.windows))); ch=True
        while ch:
            ch=False
            for (a,x,b) in s.edges:
                if a in B and (x==1 or b not in B): B.discard(a); ch=True
        return sorted(B)

def search(machine,K,T,max_rounds=10000,KL=None,verbose=False):
    m=Machine.parse(machine)
    SL=Side(KL or K,T,(0,1)); SR=Side(K,T,(1,0))
    bl=(H,)*SL.K; br=(H,)*SR.K
    WL,WR={bl},{br}
    for rnd in range(max_rounds):
        AL,AR=TAuto(SL,sorted(WL,key=str)),TAuto(SR,sorted(WR,key=str))
        start=(0,AL.index[bl],AR.index[br]); seen={start}; todo=deque([start]); need=set()
        while todo:
            st,ql,qr=todo.popleft()
            for x,qr2 in AR.pops(qr):
                t=m.table[st][x]
                if t is None: continue
                w,d,s2=t
                if d==1:
                    p=SL.push(w,AL.windows[ql])
                    if p not in AL.index: need.add(('L',p)); continue
                    outs=[(s2,AL.index[p],qr2)]
                else:
                    p1=SR.push(w,AR.windows[qr2])
                    if p1 not in AR.index: need.add(('R',p1)); continue
                    outs=[]
                    for y,ql2 in AL.pops(ql):
                        p0=SR.push(y,p1)
                        if p0 not in AR.index: need.add(('R',p0)); continue
                        outs.append((s2,ql2,AR.index[p0]))
                for n in outs:
                    if n not in seen: seen.add(n); todo.append(n)
        if verbose: print('round',rnd,len(WL),len(WR),len(seen),len(need),flush=True)
        if not need: return AL,AR,sorted(seen)
        for side,p in need: (WL if side=='L' else WR).add(p)
    raise RuntimeError('no closure')

def show(w):
    return ' '.join('#' if a==H else (('w%d'%a[1] if a[1]<99 else 'w+') if isinstance(a,tuple) else str(a)) for a in w)

if __name__=='__main__':
    M=sys.argv[1]; K=int(sys.argv[2]); T=int(sys.argv[3]); KL=int(sys.argv[4]) if len(sys.argv)>4 else None
    import time; t=time.time()
    AL,AR,S=search(M,K,T,KL=KL,verbose=True)
    ok=ctl.check(M,AL,AR,S)
    h=ctl.halting(M,AR,S)
    print('K',K,'T',T,'windows',len(AL.windows),len(AR.windows),'S',len(S),'closed',ok,'halting',len(h),'%.0fs'%(time.time()-t))
    for (s,ql,qr,x,qr2) in h[:10]:
        print('  halt', 'ABCDEF'[s], x, 'L:',show(AL.windows[ql]),' R:',show(AR.windows[qr]))
