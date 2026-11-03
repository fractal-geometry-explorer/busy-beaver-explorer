"""SAT search for a finite automaton over two-stack tokens (py/twostack.py) whose language contains the start
configuration, is closed under the two rules (values abstracted: exact up to CV, gaps exact up to CG, then by parity),
and contains no stuck window.  Needs python-sat (pip install python-sat).

usage: python3 py/ctl_sat.py CV K CG      (K states, state 0 dead; prints SAT or UNSAT)

Words are '^' (the -1 entries), the left stack bottom to top, the cursor, the right stack top to bottom.  Closure is
checked with a state-inclusion relation: for each rule X -> Y and each state p reachable by '^' v*, the language
after p.X is contained in the language after p.Y.  Symmetry breaking orders states breadth-first.
"""
from pysat.solvers import Cadical153
import sys, time
from pysat.solvers import Cadical153
CV=int(sys.argv[1]); CG=int(sys.argv[3]); K=int(sys.argv[2]); C=CV
VALS=list(range(0,CV+1))+['E','O']
GAPS=[-1]+list(range(0,CG+1))+['GE','GO']
def conc(c):
    if isinstance(c,int): return [c]
    par=0 if c in ('E','GE') else 1
    B=CV if c in ('E','O') else CG
    lo=B+1 if (B+1)%2==par else B+2
    return [lo, lo+2, lo+4]
def cls(v):
    if v<=CV: return v
    return 'E' if v%2==0 else 'O'
def gcls(v):
    if v<=CG: return v
    return 'GE' if v%2==0 else 'GO'
def op(c,f,out=None):
    out=out or cls
    return sorted({out(f(v)) for v in conc(c)},key=str)
# symbols
SYM=['^']+[('v',v) for v in VALS]+[('c',v,g) for v in VALS for g in GAPS]+[('ce',v) for v in VALS]+\
    [('r',v,g) for v in VALS for g in GAPS]+[('re',v) for v in VALS]
SI={s:i for i,s in enumerate(SYM)}
def T(val,gap):  # entry after creation left of cursor area
    return ('v',val) if gap==0 else ('c',val,gap)
rules=[]   # (X, Y) tuples of symbols
stuck=[]
Lctx=[('^',)]+[('^',('v',b)) for b in VALS]+[(('v',a),('v',b)) for a in VALS for b in VALS]
def lvals(ctx):
    if len(ctx)==1: return (-1,-1)
    if len(ctx)==2 and ctx[0]=='^': return (-1,ctx[1][1])
    return (ctx[0][1],ctx[1][1])
def keep(ctx):  # tokens of ctx not consumed: '^' stays
    return ('^',) if ctx[0]=='^' else ()
def addc(a): return [1] if a==-1 else op(a,lambda v:v+2)
# R1: a b x<n>, n>=1 or end
for ctx in Lctx:
    a,b=lvals(ctx)
    for x in VALS:
        for n in [g for g in GAPS if g not in (-1,0)]+['end']:
            X=ctx+((('c',x,n) if n!='end' else ('ce',x)),)
            bb = b
            for a2 in addc(a):
                if bb==0:
                    # (a+2) frozen, x cursor with n-2
                    if n=='end': outs=[(('v',0),('v',a2),('ce',x))]
                    else: outs=[(('v',0),('v',a2),('c',x,n2)) for n2 in op(n,lambda v:v-2,gcls)]
                else:
                    gbs = [-1] if bb==-1 else op(bb,lambda v:v,gcls)
                    if n=='end': outs=[(('v',0),('c',a2,gb),('re',x)) for gb in gbs]
                    else: outs=[(('v',0),('c',a2,gb),('r',x,n2)) for gb in gbs for n2 in op(n,lambda v:v-2,gcls)]
                for o in outs: rules.append((X, keep(ctx)+o))
# R2: a x<-1> y<m>
for ctx in Lctx:
    a,_=lvals(ctx)
    actx = ctx[:1] if ctx==('^',) else (ctx[:1] if ctx[0]=='^' else ctx[:1])
    # use only one L token (a); build contexts: ('^',) -> a=-1 ; (('v',a),) ; ('^',('v',a)) handled as ('v',a)
for actx in [('^',)]+[(('v',a),) for a in VALS]:
    a = -1 if actx==('^',) else actx[0][1]
    for x in VALS:
        for y in VALS:
            for m in GAPS+['end']:
                X=actx+(('c',x,-1), ('re',y) if m=='end' else ('r',y,m))
                if x==0 or (y==0 and m!='end'): stuck.append(X); continue
                kp = ('^',) if actx==('^',) else ()
                for a2 in addc(a):
                    if m=='end' and y==0:
                        rules.append((X, kp+(('v',0),('ce',a2)))); continue
                    for x2 in op(x,lambda v:v-2,gcls):
                        for y2 in op(y,lambda v:v-1):
                            if x2==0:
                                o=(('v',0),('v',a2), ('ce',y2) if m=='end' else ('c',y2,m))
                            else:
                                o=(('v',0),('c',a2,x2), ('re',y2) if m=='end' else ('r',y2,m))
                            rules.append((X, kp+o))
# freeze: x<0> then next
for x in VALS:
    for y in VALS:
        for m in GAPS:
            rules.append(((('c',x,0),('r',y,m)), (('v',x),('c',y,m))))
        rules.append(((('c',x,0),('re',y)), (('v',x),('ce',y))))
print('rules',len(rules),'stuck windows',len(stuck),'symbols',len(SYM),flush=True)
# SAT
cnt=[0]
def nv(): cnt[0]+=1; return cnt[0]
t={(q,s,r):nv() for q in range(K) for s in range(len(SYM)) for r in range(K)}
acc=[nv() for q in range(K)]
cl=[]
for q in range(K):
    for s in range(len(SYM)):
        vs=[t[q,s,r] for r in range(K)]
        cl.append(vs)
        for i in range(K):
            for j in range(i+1,K): cl.append([-vs[i],-vs[j]])
# state 0 dead
for s in range(len(SYM)): cl.append([t[0,s,0]])
cl.append([-acc[0]])
memo={}
def path(p,w):
    """one-hot vars for state after reading w from p"""
    key=(p,w)
    if key in memo: return memo[key]
    if len(w)==0:
        res=[None]*K
        res=[nv() for _ in range(K)]
        for r in range(K): cl.append([res[r]] if r==p else [-res[r]])
        memo[key]=res; return res
    prev=path(p,w[:-1]); s=SI[w[-1]]
    res=[nv() for _ in range(K)]
    for q in range(K):
        for r in range(K):
            cl.append([-prev[q],-t[q,s,r],res[r]])
    # res one-hot implied: at most one
    for i in range(K):
        for j in range(i+1,K): cl.append([-res[i],-res[j]])
    memo[key]=res; return res
le={(q,r):nv() for q in range(K) for r in range(K)}
for q in range(K):
    cl.append([le[q,q]])
    cl.append([le[0,q]])
    for r in range(K):
        cl.append([-le[q,r],-acc[q],acc[r]])
        for si in range(len(SYM)):
            for q2 in range(K):
                for r2 in range(K):
                    if q2!=r2: cl.append([-le[q,r],-t[q,si,q2],-t[r,si,r2],le[q2,r2]])
# reachL[q]: q reachable from start 1 by '^' v*  ; start[q]: q==1
reachL=[nv() for q in range(K)]
for r in range(K): cl.append([-t[1,SI['^'],r],reachL[r]])
VS=[SI[('v',v)] for v in VALS]
for q in range(K):
    for si in VS:
        for r in range(K): cl.append([-reachL[q],-t[q,si,r],reachL[r]])
def guard(p,X): return [] if X[0]=='^' else [-reachL[p]]
for p in range(1,K):
    for X,Y in rules:
        if X[0]=='^' and p!=1: continue
        A=path(p,X); B=path(p,Y); g=guard(p,X)
        for q in range(K):
            for r in range(K): cl.append(g+[-A[q],-B[r],le[q,r]])
    for X in stuck:
        if X[0]=='^' and p!=1: continue
        A=path(p,X); g=guard(p,X)
        for q in range(K): cl.append(g+[-A[q],le[q,0]])
# initial word accepted from start state 1
init=('^',('v',0),('c',1,-1),('re',1))
A=path(1,init)
for r in range(K): cl.append([-A[r],acc[r]])

# BFS symmetry breaking over states 1..K-1 (0 = dead), root 1
NS=len(SYM)
tr={}
for i in range(1,K):
    for j in range(2,K):
        if i==j: continue
        v=nv(); tr[i,j]=v
        lits=[t[i,s,j] for s in range(NS)]
        cl.append([-v]+lits)
        for l in lits: cl.append([-l,v])
par={}
for j in range(2,K):
    for i in range(1,j):
        par[j,i]=nv()
    cl.append([par[j,i] for i in range(1,j)])
    for i in range(1,j):
        # par[j,i] <-> tr[i,j] and no tr[k,j] for k<i
        cl.append([-par[j,i],tr[i,j]])
        for k in range(1,i): cl.append([-par[j,i],-tr[k,j]])
        cl.append([par[j,i],-tr[i,j]]+[tr[k,j] for k in range(1,i)])
for j in range(2,K-1):
    for i in range(1,j):
        for k in range(1,i):
            cl.append([-par[j,i],-par[j+1,k]])
mm={}
for i in range(1,K):
    for j in range(2,K):
        if i>=j: continue
        for s in range(NS):
            v=nv(); mm[i,j,s]=v
            cl.append([-v,t[i,s,j]])
            for s2 in range(s): cl.append([-v,-t[i,s2,j]])
            cl.append([v,-t[i,s,j]]+[t[i,s2,j] for s2 in range(s)])
for j in range(2,K-1):
    for i in range(1,j):
        for s in range(NS):
            for s2 in range(s):
                cl.append([-par[j,i],-par[j+1,i],-mm[i,j,s],-mm[i,j+1,s2]])
print('vars',cnt[0],'clauses',len(cl),flush=True)
s=Cadical153(bootstrap_with=cl)
t0=time.time(); r=s.solve(); print('SAT' if r else 'UNSAT', round(time.time()-t0,1),'s',flush=True)
if r:
    m=set(x for x in s.get_model() if x>0)
    delta={(q,SYM[si]):r for (q,si,r),v in t.items() if v in m}
    print(delta)
