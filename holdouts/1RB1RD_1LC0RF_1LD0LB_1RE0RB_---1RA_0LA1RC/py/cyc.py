"""Linear cycle jumps for ws.Sim, each proved by a symbolic replay (all values of the variables y_i >= 0)."""
from math import gcd
from ws import *
TH=16
def key1(v): return 'N' if (is_sym(v) or v>=TH) else v
def shape(s):
    return (s.st,s.d,tuple((key1(l),key1(m)) for l,m in s.L),tuple((key1(l),key1(m)) for l,m in s.R))
def slots(s):
    """(stack, index, field) of the N quantities, in a fixed order"""
    out=[]
    for S in (s.L,s.R):
        for i,e in enumerate(S):
            for f in (0,1):
                if key1(e[f])=='N': out.append((S,i,f))
    return out
def is_sample(t):
    return t.big or not (t.R if t.d==1 else t.L)
class Rule:
    pass
def prove(sim, budget=20000, verbose=False):
    sh=shape(sim); st0=sim.copy_state()
    sl=slots(sim); actual=[S[i][f] for S,i,f in sl]; n=len(actual)
    base=[TH]*n; Mv=[1]*n
    for it in range(60):
        t=Sim.__new__(Sim); t.T=sim.T; t.M=sim.M; t.rules=sim.rules; t.nmacro=0; t.stats=dict(sim.stats); t.halted=False; t.big=False
        t.set_state(st0); t.steps=0
        b2=[a-m*((a-b)//m) for a,b,m in zip(actual,base,Mv)]
        tsl=slots(t)
        for j,(S,i,f) in enumerate(tsl):
            S[i][f]= Lin(b2[j],{j:Mv[j]}) if b2[j]<actual[j] or True else actual[j]
        start=[S[i][f] for S,i,f in tsl]
        try:
            ok=False
            for _ in range(budget):
                if not t.step(): raise ProofFail("halt in replay")
                if is_sample(t) and shape(t)==sh: ok=True; break
            if not ok: return None
        except Undecided as e:
            ch=False
            for v in e.vars:
                nb=min(actual[v],2*base[v]+8)
                if nb!=base[v]: base[v]=nb; ch=True
            if not ch: return None
            continue
        except NeedMod as e:
            Mv[e.var]=Mv[e.var]*e.m//gcd(Mv[e.var],e.m); continue
        except (NonLinear,ProofFail) as e:
            if verbose: print("prooffail",e)
            return None
        esl=slots(t)
        if len(esl)!=n: return None
        dl=[]
        for j,(S,i,f) in enumerate(esl):
            dd=S[i][f]-start[j]
            if is_sym(dd): return None
            dl.append(dd)
        # non-N parts equal by shape. modulus condition
        for j in range(n):
            if dl[j]%Mv[j]: return None
        r=Rule(); r.base=b2; r.M=Mv; r.d=dl; r.S=t.steps; r.n=n; r.minv=[None]*n
        for j in range(n):
            # smallest admissible value: >= base[j], congruent to actual mod M
            r.minv[j]=b2[j]
        r.res=[b2[j]%Mv[j] for j in range(n)]
        return r
    return None
def applicable(r, vals):
    if len(vals)!=r.n: return False
    return all(v>=b and v%m==x for v,b,m,x in zip(vals,r.minv,r.M,r.res))
def apply(sim, r):
    sl=slots(sim); vals=[S[i][f] for S,i,f in sl]
    ks=[(v-b)//(-d)+1 for v,b,d in zip(vals,r.minv,r.d) if d<0]
    if not ks: return 'forever'
    k=min(ks)
    y=[(v-b)//m for v,b,m in zip(vals,r.minv,r.M)]
    S=r.S
    if is_sym(S):
        s0=S.c; tot=k*s0
        for j,a in S.co.items():
            tot+=a*(k*y[j]+(r.d[j]//r.M[j])*(k*(k-1)//2))
    else: tot=k*S
    for (St,i,f),d in zip(sl,r.d): St[i][f]+=k*d
    sim.steps+=tot
    return k
class Acc:
    def __init__(s, sim, verbose=False):
        s.sim=sim; s.rules={}; s.fail={}; s.seen={}; s.njump=0; s.ncyc=0; s.verbose=verbose; s.forever=False
    def step(s):
        sim=s.sim
        if not sim.step(): return False
        if is_sample(sim):
            sh=shape(sim)
            vals=None
            for r in s.rules.get(sh,()):
                if vals is None: vals=[S[i][f] for S,i,f in slots(sim)]
                if applicable(r,vals):
                    k=apply(sim,r)
                    if k=='forever': s.forever=True; return False
                    s.njump+=1; s.ncyc+=k; return True
            if vals is None: vals=[S[i][f] for S,i,f in slots(sim)]
            h=s.seen.get(sh)
            cur=(vals,sim.nmacro)
            if h and len(h)==2 and s.fail.get(sh,0)<6 and len(s.rules.get(sh,()))<60:
                (v0,m0),(v1,m1)=h
                if m1-m0==sim.nmacro-m1 and len(v0)==len(v1)==len(vals) and all(b-a==c-b for a,b,c in zip(v0,v1,vals)) and any(c!=b for b,c in zip(v1,vals)):
                    r=prove(sim,budget=2*(sim.nmacro-m1)+50,verbose=s.verbose)
                    if r is None: s.fail[sh]=s.fail.get(sh,0)+1
                    else:
                        s.rules.setdefault(sh,[]).append(r)
                        if s.verbose: print("rule",len(s.rules),sh,"d",r.d,"M",r.M,"base",r.base,"S",r.S)
                        k=apply(sim,r)
                        if k=='forever': s.forever=True; return False
                        s.njump+=1; s.ncyc+=k
                        s.seen.pop(sh,None); return True
            s.seen[sh]=((h[-1],cur) if h else (cur,))
        return True
