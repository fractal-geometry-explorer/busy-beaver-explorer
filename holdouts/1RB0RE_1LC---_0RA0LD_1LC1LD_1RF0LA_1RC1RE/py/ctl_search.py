"""A closed-tape-language search that failed for this machine; kept to record what was tried (README, "Attempts").

usage (from the repo root):  python3 holdouts/MACHINE/py/ctl_search.py MACHINE K M GAPS SEEN

Same closure as tools/py/bbtools/ctl.py and TM.CTL.closed in tools/lean/TM/CTL.lean, with a different abstraction of
each side of the head: a deterministic `push` (the abstract state of x followed by a stream), edges (P, x, Q) iff
push(x, Q) = P, and the blank state accepting the blank tape.  `WinFlag`: the K cells nearest the head, plus a
finite summary of the cells beyond them, read from the far end: the run of 1s at the near end, the last M blocks
1^k 0 with k != 3 (with the number of 1110 blocks before each, capped at GAPS, if GAPS > 0) and, if SEEN, the set
of block lengths != 3 seen beyond.  The search grows the states from the blank start and stops at the first
abstract configuration that can halt (or at a run of 1s longer than 11), printing the end of the abstract path.
For this machine every setting tried (K <= 10, M <= 2, GAPS <= 2) fails within a few hundred abstract steps.
"""
import sys, time
from collections import defaultdict, deque
def parse(m):
    t={}
    for s,part in enumerate(m.split("_")):
        for r in range(2):
            x=part[3*r:3*r+3]
            t[(s,r)]=None if x[2]=="-" else (int(x[0]),1 if x[1]=="R" else -1,ord(x[2])-65)
    return t
class Overflow(Exception): pass
class WinFlag:
    """window of K cells (nearest first) + flag DFA state of the region beyond, read from the far end."""
    def __init__(s,K,m=1,C=11,gaps=0,seen=False,cap=None):
        s.K=K;s.m=m;s.C=C;s.gaps=gaps;s.seen=seen
        s.blank=((0,)*K,None)
    def g(s,f,c):
        # f None = all blank so far. else (r, hist, gapcount, seenset)
        if f is None:
            if c==0: return None
            return (1,(),0,frozenset())
        r,hist,gc,sn=f
        if c==1:
            if r+1>s.C: raise Overflow()
            return (r+1,hist,gc,sn)
        # c==0 completes run r
        if r==3:
            if s.gaps: gc=min(gc+1,s.gaps)
            return (0,hist,gc,sn)
        if s.m: hist=((r,gc) if s.gaps else r,)+hist[:s.m-1]
        if s.seen: sn=sn|{r}
        return (0,hist,0,sn)
    def push(s,x,Q):
        w,f=Q
        return ((x,)+w[:-1], s.g(f,w[-1]))
    def show(s,Q):
        w,f=Q
        return ''.join(map(str,w))+'|'+('blank' if f is None else str(f))
def search(m,AL,AR,maxS=2*10**6,start=None,stop_on_halt=True):
    Tb=parse(m)
    Ab={'L':AL,'R':AR}
    states={'L':set(),'R':set()}
    preimg={'L':defaultdict(set),'R':defaultdict(set)}
    S=set(); byq={'L':defaultdict(set),'R':defaultdict(set)}
    todo=deque(); par={}; cur=[None]
    def addstate(sd,W):
        if W in states[sd]: return
        states[sd].add(W)
        for x in (0,1):
            try: P=Ab[sd].push(x,W)
            except Overflow: continue
            preimg[sd][P].add((x,W))
            for c in byq[sd].get(P,()): todo.append(c)
    def addcfg(c):
        if c in S: return
        par[c]=cur[0]; S.add(c); byq['L'][c[1]].add(c); byq['R'][c[2]].add(c); todo.append(c)
    def path(c):
        p=[c]
        while par.get(p[-1]) is not None: p.append(par[p[-1]])
        return p[::-1]
    addstate('L',AL.blank); addstate('R',AR.blank)
    if start is None: addcfg((0,AL.blank,AR.blank))
    else:
        s0,L0,R0=start
        ws={}
        for sd,cells in (('L',L0),('R',R0)):
            W=Ab[sd].blank
            for x in reversed(cells): W=Ab[sd].push(x,W); addstate(sd,W)
            ws[sd]=W
        addcfg((s0,ws['L'],ws['R']))
    halts=[]
    while todo:
        if len(S)>maxS: return 'too big',S,states,halts,None
        c=todo.popleft(); s,ql,qr=c; cur[0]=c
        for x,qr2 in list(preimg['R'].get(qr,())):
            t=Tb[(s,x)]
            if t is None:
                halts.append((c,x,qr2))
                if stop_on_halt: return 'halt',S,states,halts,path(c)
                continue
            w,d,s2=t
            try:
                if d==1:
                    p=AL.push(w,ql); addstate('L',p); addcfg((s2,p,qr2))
                else:
                    p1=AR.push(w,qr2); addstate('R',p1)
                    for y,ql2 in list(preimg['L'].get(ql,())):
                        p0=AR.push(y,p1); addstate('R',p0); addcfg((s2,ql2,p0))
            except Overflow:
                return 'overflow',S,states,halts,path(c)
    return ('closed' if not halts else 'halts'),S,states,halts,None
if __name__=='__main__':
    m=sys.argv[1]; K=int(sys.argv[2]); mm=int(sys.argv[3]); gaps=int(sys.argv[4]); seen=int(sys.argv[5])
    t0=time.time()
    A=WinFlag(K,mm,gaps=gaps,seen=bool(seen))
    r,S,st,h,p=search(m,A,A)
    print('K',K,'m',mm,'gaps',gaps,'seen',seen,r,len(S),len(st['L']),len(st['R']),'%.0fs'%(time.time()-t0))
    if p:
        for c in p[-12:]: print('  ','ABCDEF'[c[0]],A.show(c[1]),' || ',A.show(c[2]))
