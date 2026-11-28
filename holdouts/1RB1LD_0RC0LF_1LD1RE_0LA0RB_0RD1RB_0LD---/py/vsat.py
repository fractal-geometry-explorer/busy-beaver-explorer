"""SAT search for an assume-guarantee DFA certificate for a visit law (PR112 style).
DFA reads a stream from its first cell outward; state n = reject (absorbing). L_q = streams never reaching reject.
g(q): v maps L_q into L_g(q). Rules given as list of (prefix, action)."""
import sys, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc
from pysat.formula import IDPool
def solve(n, rules, halt_prefixes, round_prefix, init_stream_prefix, verbose=True):
    pool=IDPool(); C=[]
    S=n+1; R=n
    d=lambda q,x,r: pool.id(('d',q,x,r))
    g=lambda q,r: pool.id(('g',q,r))
    sim=lambda a,b: pool.id(('s',a,b))
    s0=lambda q: pool.id(('s0',q))
    Z=lambda q: pool.id(('Z',q))
    def exactly_one(lits):
        C.extend(CardEnc.equals(lits=lits,bound=1,vpool=pool).clauses)
    for q in range(n):
        for x in (0,1): exactly_one([d(q,x,r) for r in range(S)])
        exactly_one([g(q,r) for r in range(n)])
    for x in (0,1):
        for r in range(S): C.append([d(R,x,r)] if r==R else [-d(R,x,r)])
    exactly_one([s0(q) for q in range(n)])
    # path vars
    memo={}
    def p(q,w,r):
        key=(q,w,r)
        if key in memo: return memo[key]
        v=pool.id(('p',)+key)
        memo[key]=v
        if len(w)==0:
            C.append([v] if q==r else [-v])
        else:
            w0,x=w[:-1],w[-1]
            terms=[]
            for t in range(S):
                a=pool.id(('pa',q,w,t,r)); terms.append(a)
                C.append([-a,p(q,w0,t)]); C.append([-a,d(t,x,r)]); C.append([a,-p(q,w0,t),-d(t,x,r)])
            C.append([-v]+terms)
            for a in terms: C.append([-a,v])
        return v
    # simulation
    for a in range(S):
        for b in range(S):
            if a==b: C.append([sim(a,b)])
            if a==R and b!=R: C.append([-sim(a,b)])
            for x in (0,1):
                for t in range(S):
                    for u in range(S):
                        C.append([-sim(a,b),-d(a,x,t),-d(b,x,u),sim(t,u)])
    # gp(q,r): g applied to state var: g(R) undefined -> vacuous
    def require_sim_path(x_is, xw, y_is):
        """x_is, y_is: lists of (cond_lits, state) alternatives..."""
        pass
    for q in range(n):
        for hp in halt_prefixes:
            C.append([p(q,hp,R)])
        for pre, act in rules:
            # target state t=δ*(q,pre); if t==R vacuous
            for t in range(n):
                cond=p(q,pre,t)
                kind=act[0]
                if kind=='raw':   # v(pre s) = out s
                    out=act[1]
                    for gq in range(n):
                        for z in range(S):
                            C.append([-cond,-g(q,gq),-p(gq,out,z),sim(z,t)])
                elif kind=='v':   # v(pre s) = out v(s)
                    out=act[1]
                    for gq in range(n):
                        for z in range(S):
                            for gt in range(n):
                                C.append([-cond,-g(q,gq),-p(gq,out,z),-g(t,gt),sim(z,gt)])
                elif kind=='vv':  # out v(v(s))
                    out=act[1]
                    for gq in range(n):
                        for z in range(S):
                            for gt in range(n):
                                for ggt in range(n):
                                    C.append([-cond,-g(q,gq),-p(gq,out,z),-g(t,gt),-g(gt,ggt),sim(z,ggt)])
    # round: r=0 : sim(δ*(0,round_prefix), s0); sim(s0, g(0))
    for z in range(S):
        for a in range(n):
            C.append([-p(0,round_prefix,z),-s0(a),sim(z,a)])
    for a in range(n):
        for b in range(n):
            C.append([-s0(a),-g(0,b),sim(a,b)])
    # init: init_stream_prefix 0^inf in L_s0
    for q in range(S):
        if q==R: C.append([-Z(q)])
        for t in range(S): C.append([-Z(q),-d(q,0,t),Z(t)]) if q<n else None
    for a in range(n):
        for t in range(S):
            C.append([-s0(a),-p(a,init_stream_prefix,t),Z(t)])
    sol=Cadical153(bootstrap_with=C)
    ok=sol.solve()
    if not ok: return None
    M=set(l for l in sol.get_model() if l>0)
    D={(q,x):r for q in range(n) for x in (0,1) for r in range(S) if d(q,x,r) in M}
    G={q:r for q in range(n) for r in range(n) if g(q,r) in M}
    S0=[q for q in range(n) if s0(q) in M][0]
    return D,G,S0
if __name__=='__main__':
    T=lambda s: tuple(int(c) for c in s)
    rules=[(T('0'),('raw',T('1'))),(T('100'),('v',T('000'))),(T('110'),('v',T('000'))),(T('1010'),('vv',T('1010'))),(T('1011'),('raw',T('1000')))]
    which=sys.argv[1] if len(sys.argv)>1 else 'a'
    if which=='b': rules[-1]=(T('1011'),('raw',T('0001')))
    if which=='pr59': rules=rules[:4]; halts=[T('111'),T('1011')]
    else: halts=[T('111')]
    for n in range(1,int(sys.argv[2]) if len(sys.argv)>2 else 9):
        r=solve(n,rules,halts,T('10'),T('1'))
        print(n, 'SAT' if r else 'UNSAT', r if r else '', flush=True)
        if r: break
