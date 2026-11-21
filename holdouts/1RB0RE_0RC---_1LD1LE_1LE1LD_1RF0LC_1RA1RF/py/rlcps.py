"""Run-length CPS with mod-M long runs and an n-gram summary beyond K runs per side.
Side = tuple of runs nearest-first: (sym, cls) where cls is exact int 1..T or ('L', r) meaning length >= T+1, = r mod M.
Beyond the runs: summary context (tuple of n-1 run tokens, nearest first) ; token 'END' = blank forever.
"""
import sys
from collections import deque
TMs=sys.argv[1]; K=int(sys.argv[2]); T=int(sys.argv[3]); M=int(sys.argv[4]); N=int(sys.argv[5]); LIM=int(sys.argv[6]) if len(sys.argv)>6 else 2000000
TR={}
for s,row in enumerate(TMs.split('_')):
    for b in range(2):
        x=row[3*b:3*b+3]
        TR[(s,b)]=None if x[0]=='-' else (int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
def inc(c):
    if isinstance(c,int):
        return c+1 if c<T else ('L',(c+1)%M)
    return ('L',(c[1]+1)%M)
def dec(c):  # list of possible results; 0 means run vanished
    if isinstance(c,int): return [c-1]
    r=(c[1]-1)%M; out=[('L',r)]
    if T%M==r: out.append(T)
    return out
G=[set(),set()]
def pop_summary(ctx,sd):
    if ctx[0]=='END': return [('END',ctx)]
    if ctx[-1]=='END': return [(ctx[0],ctx[1:])]
    res=[]
    for g in G[sd]:
        if g[:len(ctx)]==ctx and len(g)>len(ctx):
            res.append((ctx[0], g[1:]))
    return res
def push_summary(tok,ctx,sd):
    g=((tok,)+ctx)[:N]
    if g not in G[sd]: G[sd].add(g); push_summary.new=True
    return ((tok,)+ctx)[:N-1]
push_summary.new=False
def norm_ctx(ctx): return ctx
def popcell(side,ctx,sd):
    """remove nearest cell; returns list of (sym, side', ctx')"""
    res=[]
    if not side:
        for tok,nc in pop_summary(ctx,sd):
            if tok=='END': return [(0,(),ctx)]
            res+= popcell((tok,),nc,sd)
        return res
    sym,c=side[0]
    for d in dec(c):
        if d==0: res.append((sym,side[1:],ctx))
        else: res.append((sym,((sym,d),)+side[1:],ctx))
    out=[]
    for sym2,sd2,cx2 in res:
        if not sd2 and cx2[0]!='END':
            for tok,nc in pop_summary(cx2,sd):
                out.append((sym2,(tok,),nc))
        else: out.append((sym2,sd2,cx2))
    return out
def pushcell(sym,side,ctx,sd):
    if side and side[0][0]==sym:
        side=((sym,inc(side[0][1])),)+side[1:]
    else:
        if not side and ctx[0]=='END' and sym==0: return side,ctx
        side=((sym,1),)+side
    if len(side)>K:
        tok=side[-1]; side=side[:-1]
        ctx=push_summary(tok,ctx,sd)
        ctx=norm_ctx(ctx)
    return side,ctx
def run():
    init=(0,0,(),('END',),(),('END',))  # state, head sym, L, Lctx, R, Rctx
    seen={init:None}; dq=deque([init])
    while dq:
        cfg=dq.popleft()
        q,a,L,Lc,R,Rc=cfg
        t=TR[(q,a)]
        if t is None:
            path=[cfg]
            while seen[path[-1]] is not None: path.append(seen[path[-1]])
            return ('HALT',path[::-1],len(seen))
        w,d,q2=t
        if d==1:
            L2,Lc2=pushcell(w,L,Lc,0)
            for b,R2,Rc2 in popcell(R,Rc,1):
                c=(q2,b,L2,Lc2,R2,Rc2)
                if c not in seen: seen[c]=cfg; dq.append(c)
        else:
            R2,Rc2=pushcell(w,R,Rc,1)
            for b,L2,Lc2 in popcell(L,Lc,0):
                c=(q2,b,L2,Lc2,R2,Rc2)
                if c not in seen: seen[c]=cfg; dq.append(c)
        if len(seen)>LIM: return ('LIMIT',None,len(seen))
    return ('CLOSED',None,len(seen))
def cls(c): return str(c) if isinstance(c,int) else 'L%d'%c[1]
def sside(side,ctx,rev):
    parts=['%s^%s'%(s,cls(c)) for s,c in side]+['['+','.join(x if x=='END' else '%s^%s'%(x[0],cls(x[1])) for x in ctx)+']']
    return ' '.join(parts[::-1]) if rev else ' '.join(parts)
def show(c):
    q,a,L,Lc,R,Rc=c
    return '%s  %s>%d  %s'%(sside(L,Lc,True),'ABCDEF'[q],a,sside(R,Rc,False))
it=0
while True:
    it+=1; push_summary.new=False; ng=len(G[0])+len(G[1])
    r=run()
    if r[0]!='CLOSED' or len(G[0])+len(G[1])==ng:
        print(r[0],'iters',it,'configs',r[2],'ngrams',len(G[0])+len(G[1])); 
        if r[0]=='HALT':
            for c in r[1][-60:]: print(show(c))
        break
