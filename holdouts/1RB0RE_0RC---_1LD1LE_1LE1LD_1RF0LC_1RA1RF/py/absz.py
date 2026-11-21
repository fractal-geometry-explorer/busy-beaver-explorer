"""Abstract interpretation: explicit window of K cells each side of the head; beyond it, a summary of the rest:
T (all blank) or (c0, z, s): first cell, parity of first pre-tail zero (None if none), number of parity switches among
pre-tail zeros. Global constraints: no 00 before the blank tail on either side (head cell excluded), switches <= SMAX
on each whole side. Explores the reachable abstract configurations from blank tape; reports a halt or a violation."""
import sys
from collections import deque
M=sys.argv[1]; K=int(sys.argv[2]); SMAX=int(sys.argv[3]); EX=int(sys.argv[4]); START=sys.argv[5] if len(sys.argv)>5 else "A"
T={}
for s,row in enumerate(M.split('_')):
    for b in range(2):
        x=row[3*b:3*b+3]
        T[('ABCDEF'[s],b)]=None if x[0]=='-' else (int(x[0]),1 if x[1]=='R' else -1,x[2])
V='V'
def flip(z): return None if z is None else 1-z
def push(c,X):
    if X=='T': return 'T' if c==0 else (1,None,0)
    c0,z,s=X
    if c==1: return (1,flip(z),s)
    if c0==0: return V
    fz=flip(z)
    s2 = s if (fz is None or fz==0) else s+1
    if s2>SMAX: return V
    return (0,0,s2)
def pop(X):
    if X=='T': return [(0,'T')]
    c0,z,s=X; out=[]
    if c0==1:
        if z is None: out=[(1,'T'),(1,(1,None,0))]
        else:
            z2=1-z
            if z2==0: out=[(1,(0,0,s)),(1,(1,0,s))]
            else: out=[(1,(1,1,s))]
    else:
        # X = 0 X', next cell 1
        if s==0: out.append((0,(1,None,0)))
        out.append((0,(1,1,s)))           # next zero same parity in X (even pos) -> odd in X'
        if s>=1: out.append((0,(1,0,s-1)))  # next zero switches parity
    return out
def full(win,X):
    for c in reversed(win):
        X=push(c,X)
        if X==V: return V
    return X
init=('A' if START=='A' else START,(0,)*K,0,(0,)*K,'T','T')
seen={init}; dq=deque([init]); bad=[]
while dq:
    cfg=dq.popleft()
    q,Lw,h,Rw,SL,SR=cfg
    tr=T[(q,h)]
    if tr is None:
        bad.append(('HALT',cfg)); break
    w,d,q2=tr
    succ=[]
    if d==1:
        dropped=Lw[-1]; nL=(w,)+Lw[:-1]; nSL=push(dropped,SL)
        if nSL==V: bad.append(('violL',cfg)); continue
        for c,X2 in pop(SR):
            succ.append((q2,nL,Rw[0],Rw[1:]+(c,),nSL,X2))
    else:
        dropped=Rw[-1]; nR=(w,)+Rw[:-1]; nSR=push(dropped,SR)
        if nSR==V: bad.append(('violR',cfg)); continue
        for c,X2 in pop(SL):
            succ.append((q2,Lw[1:]+(c,),Lw[0],nR,X2,nSR))
    for n in succ:
        if full(n[1][EX:],n[4])==V or full(n[3][EX:],n[5])==V:
            bad.append(('violFull',cfg,n)); continue
        if n not in seen:
            seen.add(n); dq.append(n)
    if len(bad)>3: break
print('explored',len(seen),'problems',len(bad))
for b in bad[:3]: print(b)
