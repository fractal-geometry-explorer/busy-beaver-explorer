"""Finite automata reduction (FAR, "direct" form), used here as a search for a regular invariant.

Given a DFA that reads one side of the tape from the far end towards the head (state 0 on blank, d[0][0] = 0), the
least NFA for the head and the other side is computed whose language contains every configuration that halts and is
closed under predecessors; if it does not accept the blank start, the machine never halts.  `enum_dfas(n)` lists the
DFAs with n states (states numbered in order of first appearance); `mirror` swaps the sides.

For the six machines of the family no DFA with up to 4 states works on either side (python3 far.py MACHINE 4).
A scratch search, checked only on small machines (it finds the one-state proof of 1RA---_------ and nothing for the
2-state champion); it writes no certificate.

usage: python3 far.py MACHINE NMAX
"""
import sys, itertools
def parse(m, mirror=False):
    T=[]
    for s in m.split('_'):
        row=[]
        for b in range(2):
            x=s[3*b:3*b+3]
            if x[2]=='-': row.append(None)
            else:
                d=1 if x[1]=='R' else -1
                if mirror: d=-d
                row.append((int(x[0]),d,ord(x[2])-65))
        T.append(row)
    return T
def far(T, dfa):
    n=len(dfa); S=len(T); m=n*S+1; TOP=n*S
    assert dfa[0][0]==0
    E=[[0]*m for _ in range(2)]
    E[0][TOP]|=1<<TOP; E[1][TOP]|=1<<TOP
    idx=lambda q,f:q*S+f
    Lc=[]
    for f in range(S):
        for x in range(2):
            tr=T[f][x]
            for q in range(n):
                if tr is None: E[x][idx(q,f)]|=1<<TOP
                else:
                    w,d,t=tr
                    if d==1: E[x][idx(q,f)]|=1<<idx(dfa[q][w],t)
                    else:
                        for y in range(2): Lc.append((x,idx(dfa[q][y],f),idx(q,t),y,w))
    def succ(X,x):
        r=0
        while X:
            b=X&-X; i=b.bit_length()-1; X^=b; r|=E[x][i]
        return r
    ch=True
    while ch:
        ch=False
        for (x,p,s,y,w) in Lc:
            Z=succ(E[y][s],w)
            if Z & ~E[x][p]: E[x][p]|=Z; ch=True
    # accept: backward 0-closure of TOP
    a=1<<TOP; ch=True
    while ch:
        ch=False
        for p in range(m):
            if not (a>>p)&1 and E[0][p]&a: a|=1<<p; ch=True
    ok = not (a>>idx(0,0))&1
    return ok,E,a
def enum_dfas(n):
    # all DFAs with n states, d[0][0]=0, canonical BFS order (states first appear in order)
    cells=[(q,b) for q in range(n) for b in range(2)]
    def rec(i,d,mx):
        if i==len(cells):
            if mx==n-1: yield [row[:] for row in d]
            return
        q,b=cells[i]
        if (q,b)==(0,0):
            d[0][0]=0; yield from rec(i+1,d,mx); return
        if q>mx: return
        for t in range(min(mx+2,n)):
            d[q][b]=t
            yield from rec(i+1,d,max(mx,t))
    yield from rec(0,[[0,0] for _ in range(n)],0)
if __name__=='__main__':
    m=sys.argv[1]; nmax=int(sys.argv[2])
    for mir in (False,True):
        T=parse(m,mir)
        for n in range(1,nmax+1):
            cnt=0
            for d in enum_dfas(n):
                cnt+=1
                ok,E,a=far(T,d)
                if ok: print("FOUND",mir,n,d); sys.exit(0)
            print("mirror",mir,"n",n,"dfas",cnt,"none")
