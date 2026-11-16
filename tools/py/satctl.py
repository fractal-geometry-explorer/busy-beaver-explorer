"""Closed tape languages with two automata, found by SAT (python-sat, CaDiCaL).

The left automaton reads the left half of the tape from the far end toward the head; the right automaton reads the
right half, head cell included, from the far end toward the head.  Both start in state 0, which loops on 0, so the
infinite blank ends are read as staying in 0.  Each side is a DFA ('d', with breadth-first symmetry breaking, so all
states are reachable) or an NFA ('n', at least one edge per state and letter).  The unknowns are the edges and a set
s of abstract configurations (state, left state, right state).  The clauses say: the start (A, 0, 0) is in s, every
step of the machine from a configuration in s lands in s again, and no halting transition is enabled in s.  So a
solution is a regular invariant of the run from blank tape that excludes halting.  `verify` rechecks a solution
independently (least closed set from the start), and `satctl_lean.py` writes it as a Lean file checked by
`TM.CTL.not_halts` (tools/lean/TM/CTL.lean), the automata reversed to read outward from the head.

usage: python3 tools/py/satctl.py MACHINE nL nR [dd|dn|nd|nn]
prints UNSAT, or SAT with the verified closure size and the automata as JSON (lists of successors per state, letter)."""
import sys, itertools, time, json
from pysat.solvers import Cadical153
from pysat.formula import IDPool
def parse(m):
    T={}
    for qi,part in enumerate(m.split('_')):
        for b in (0,1):
            tr=part[3*b:3*b+3]
            if tr[0] in '-H': T[(qi,b)]=None
            else: T[(qi,b)]=(int(tr[0]),tr[1],'ABCDEF'.index(tr[2]))
    return T
def build(m,nL,nR,nfa=False):
    nfaL,nfaR=(nfa,nfa) if isinstance(nfa,bool) else (nfa[0]=='n',nfa[1]=='n')
    T=parse(m); pool=IDPool(); cl=[]
    dL=lambda i,c,j: pool.id(('dL',i,c,j))
    dR=lambda i,c,j: pool.id(('dR',i,c,j))
    s=lambda q,l,r: pool.id(('s',q,l,r))
    for (n,d,nfa) in ((nL,dL,nfaL),(nR,dR,nfaR)):
        for i in range(n):
            for c in (0,1):
                cl.append([d(i,c,j) for j in range(n)])
                if not nfa:
                  for j in range(n):
                    for k in range(j+1,n): cl.append([-d(i,c,j),-d(i,c,k)])
        cl.append([d(0,0,0)])
        if not nfa and n>2:
            tag='L' if d is dL else 'R'
            t=lambda i,j: pool.id(('t'+tag,i,j))
            p=lambda j,i: pool.id(('p'+tag,j,i))
            for i in range(n):
                for j in range(i+1,n):
                    cl.append([-t(i,j),d(i,0,j),d(i,1,j)]); cl.append([t(i,j),-d(i,0,j)]); cl.append([t(i,j),-d(i,1,j)])
            for j in range(1,n):
                for i in range(j):
                    # p(j,i) <-> t(i,j) & no t(k,j) k<i
                    cl.append([-p(j,i),t(i,j)])
                    for k in range(i): cl.append([-p(j,i),-t(k,j)])
                    cl.append([p(j,i),-t(i,j)]+[t(k,j) for k in range(i)])
                cl.append([p(j,i) for i in range(j)])
            for j in range(1,n-1):
                for i in range(j):
                    for k in range(i): cl.append([-p(j,i),-p(j+1,k)])
                    cl.append([-p(j,i),-p(j+1,i),d(i,0,j)])
                    cl.append([-p(j,i),-p(j+1,i),d(i,1,j+1)])
    cl.append([s(0,0,0)])
    for (q,b),tr in T.items():
        P=lambda l,rp: pool.id(('P',q,b,l,rp))
        for l in range(nL):
            for r in range(nR):
                for rp in range(nR):
                    cl.append([-s(q,l,r),-dR(rp,b,r),P(l,rp)])
        if tr is None:
            for l in range(nL):
                for rp in range(nR): cl.append([-P(l,rp)])
            continue
        w,dirn,q2=tr
        if dirn=='R':
            for l in range(nL):
                for rp in range(nR):
                    for l2 in range(nL):
                        cl.append([-P(l,rp),-dL(l,w,l2),s(q2,l2,rp)])
        else:
            Y=lambda l,r2: pool.id(('Y',q,b,l,r2))
            Z=lambda lp,c,r2: pool.id(('Z',q,b,lp,c,r2))
            for l in range(nL):
                for rp in range(nR):
                    for r2 in range(nR):
                        cl.append([-P(l,rp),-dR(rp,w,r2),Y(l,r2)])
            for l in range(nL):
                for r2 in range(nR):
                    for lp in range(nL):
                        for c in (0,1):
                            cl.append([-Y(l,r2),-dL(lp,c,l),Z(lp,c,r2)])
            for lp in range(nL):
                for c in (0,1):
                    for r2 in range(nR):
                        for r3 in range(nR):
                            cl.append([-Z(lp,c,r2),-dR(r2,c,r3),s(q2,lp,r3)])
    return pool,cl
def solve(m,nL,nR,timeout=None,nfa=False):
    pool,cl=build(m,nL,nR,nfa)
    S=Cadical153(bootstrap_with=cl)
    ok=S.solve()
    if not ok: return None
    model=set(x for x in S.get_model() if x>0)
    def get(kind,*a): return pool.id((kind,)+a) in model
    DL=[[[j for j in range(nL) if get('dL',i,c,j)] for c in (0,1)] for i in range(nL)]
    DR=[[[j for j in range(nR) if get('dR',i,c,j)] for c in (0,1)] for i in range(nR)]
    Sset=[(q,l,r) for q in range(6) for l in range(nL) for r in range(nR) if get('s',q,l,r)]
    return DL,DR,Sset
def verify(m,DL,DR,Sset):
    """independent closure check (least fixpoint from start)."""
    T=parse(m); nL=len(DL); nR=len(DR)
    assert 0 in DL[0][0] and 0 in DR[0][0]
    assert all(DL[i][c] for i in range(nL) for c in (0,1)) and all(DR[i][c] for i in range(nR) for c in (0,1))
    predR={(r,b):[rp for rp in range(nR) if r in DR[rp][b]] for r in range(nR) for b in (0,1)}
    predL={(l,):[(lp,c) for lp in range(nL) for c in (0,1) if l in DL[lp][c]] for l in range(nL)}
    seen={(0,0,0)}; todo=[(0,0,0)]
    while todo:
        q,l,r=todo.pop()
        for b in (0,1):
            for rp in predR[(r,b)]:
                tr=T[(q,b)]
                if tr is None: return False,('halt',q,l,r,b)
                w,d,q2=tr
                if d=='R': nxt=[(q2,l2,rp) for l2 in DL[l][w]]
                else: nxt=[(q2,lp,r3) for (lp,c) in predL[(l,)] for r2 in DR[rp][w] for r3 in DR[r2][c]]
                for x in nxt:
                    if x not in seen: seen.add(x); todo.append(x)
    return True,len(seen)
if __name__=='__main__':
    m=sys.argv[1]; nL=int(sys.argv[2]); nR=int(sys.argv[3]); nfa=sys.argv[4] if len(sys.argv)>4 else 'dd'
    t=time.time(); res=solve(m,nL,nR,nfa=nfa)
    if res is None: print(m,nL,nR,'UNSAT',round(time.time()-t,1)); sys.exit(1)
    DL,DR,S=res; print(m,nL,nR,'SAT',round(time.time()-t,1),verify(m,DL,DR,S)); print(json.dumps({'DL':DL,'DR':DR}))
