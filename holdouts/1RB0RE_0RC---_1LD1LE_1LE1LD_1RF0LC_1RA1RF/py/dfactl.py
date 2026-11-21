"""CTL check with a fixed feature DFA read from the far end of each side.
State of a side automaton: (sym, lencls, nev, nzz, last) -- sym/lencls of the open run nearest the head,
nev = number of completed 1-runs of even length (cap E), nzz = completed 0-runs of length >= 2 (cap Z),
last = length class of the last completed 1-run (or None).  Start: (0,'INF',0,0,None).
Abstract config (q, a, sl, sr); move right writing w: sl' = d(sl, w); pop right: (sr_prev, b) with d(sr_prev,b)=sr.
"""
import sys
from collections import deque
TMs=sys.argv[1]; T=int(sys.argv[2]); M=int(sys.argv[3]); E=int(sys.argv[4]); Z=int(sys.argv[5]); KEEPLAST=int(sys.argv[6])
TR={}
for s,row in enumerate(TMs.split('_')):
    for b in range(2):
        x=row[3*b:3*b+3]
        TR[(s,b)]=None if x[0]=='-' else (int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
def cinc(c):
    if c=='INF': return 'INF'
    if isinstance(c,int): return c+1 if c<T else ('L',(c+1)%M)
    return ('L',(c[1]+1)%M)
def even(c):
    if isinstance(c,int): return c%2==0
    return (c[1]%2==0) if M%2==0 else None
def delta(st,b):
    sym,c,nev,nzz,last=st
    if b==sym: return (sym,cinc(c),nev,nzz,last)
    if sym==1:
        e=even(c); nev2=min(E,nev+(1 if e else 0)); last2=c if KEEPLAST else None
        return (0,1,nev2,nzz,last2)
    else:
        nzz2=nzz if c=='INF' else min(Z,nzz+(1 if (c!=1) else 0))
        return (1,1,nev,nzz2,last)
start=(0,'INF',0,0,None)
# enumerate reachable DFA states and inverse
Q={start}; dq=deque([start]); inv={}
while dq:
    s=dq.popleft()
    for b in (0,1):
        t=delta(s,b); inv.setdefault(t,set()).add((s,b))
        if t not in Q: Q.add(t); dq.append(t)
print('dfa states',len(Q))
init=(0,0,start,start)
seen={init:None}; dq=deque([init])
res='CLOSED'
while dq:
    c=dq.popleft(); q,a,sl,sr=c
    t=TR[(q,a)]
    if t is None: res='HALT'; break
    w,d,q2=t
    if d==1:
        sl2=delta(sl,w)
        nxt=[(q2,b,sl2,sp) for sp,b in inv.get(sr,())]
    else:
        sr2=delta(sr,w)
        nxt=[(q2,b,sp,sr2) for sp,b in inv.get(sl,())]
    for n in nxt:
        if n not in seen: seen[n]=c; dq.append(n)
print(res,len(seen))
if res=='HALT':
    path=[c]
    while seen[path[-1]] is not None: path.append(seen[path[-1]])
    for x in path[::-1][-25:]: print('ABCDEF'[x[0]],x[1],'L',x[2],'R',x[3])
