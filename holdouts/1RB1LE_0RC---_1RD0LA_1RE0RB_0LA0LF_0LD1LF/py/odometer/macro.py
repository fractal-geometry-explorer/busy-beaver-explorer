"""Odometer jump for 1RB1LE_0RC---_1RD0LA_1RE0RB_0LA0LF_0LD1LF: many trips at once, in closed form.

A configuration at an R-instant (the head at the right end, second cell from the end) is (state, toks) with
toks = [g0, n1, g1, ..., n_{k+1}, g_{k+1}]: glyph strings g (the left end g0, the walls g1..gk, the right end) and
blocks a^n (a = 100, n >= FOLD) between them.  When the state is D and the right end is `110`, a trip runs the head
left to the first wall that does not pass the carry, changes it and returns: an odometer whose digits are the walls.

* `learn(g)`: the carry rule of a wall glyph g (next glyph, change of the block on its left and on its right, whether
  the carry goes on, the constant part of the step count), read off one exact trip of l1.trip in a fixed context with
  four different block lengths (they must agree; otherwise g is a *barrier*, left to l1.trip).  `plearn`: same for
  the left end.
* `Seq(g)`: the orbit of a wall under carries (pre-period and cycle), with closed forms for sums along it.
* `jump(state, toks)`: the largest m such that the next m trips touch no barrier and keep every block >= FOLD (all
  constraints are monotone in m), and the configuration and the exact step count after them:
  steps = sum of the constants + 8 * (sum over trips of the lengths of the blocks the trip crosses).
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import l1
from l1 import trip, fold, FOLD
B=60
RULES={}
def learn(g):
    """carry rule of interior glyph g: (g2, dl, dr, passes, kappa) or None"""
    if g in RULES: return RULES[g]
    res=[]
    for Bv in (60,65,70,79):
        ctx=['10',Bv,'1010',Bv,g,Bv,'1',Bv,'110']
        try: r=trip(3,ctx,maxsteps=10**6,nosub=True)
        except Exception: res.append(None); continue
        if r[0]=='HALT' or r[0]!=3 or r[3]>0: res.append(None); continue
        R=r[1]
        if len(R)!=9 or R[0]!='10' or R[6]!='1010' or R[8]!='110' or R[7]!=Bv+1 or R[2] not in ('1010','0'): res.append(None); continue
        if R[2]=='1010':
            if R[1]!=Bv: res.append(None); continue
            dl=R[3]-Bv; ps=0; kap=r[2]-8*2*Bv-4
        else:
            if R[1]!=Bv+1: res.append(None); continue
            dl=R[3]-Bv-1; ps=1; kap=r[2]-8*3*Bv-4-19
        dr=R[5]-Bv+2
        res.append((R[4],dl,dr,ps,kap))
    out=res[0] if all(x==res[0] for x in res) else None
    RULES[g]=out; return out
PRULES={}
def plearn(p):
    if p in PRULES: return PRULES[p]
    res=[]
    for Bv in (60,65,70,79):
        ctx=[p,Bv,'1',Bv,'110']
        try: r=trip(3,ctx,maxsteps=10**6,nosub=True)
        except Exception: res.append(None); continue
        if r[0]!=3 or r[3]>0: res.append(None); continue
        R=r[1]
        if len(R)!=5 or R[2]!='1010' or R[4]!='110' or R[3]!=Bv+1: res.append(None); continue
        res.append((R[0],0,R[1]-Bv+2,0,r[2]-8*2*Bv-4))
    out=res[0] if all(x==res[0] for x in res) else None
    PRULES[p]=out; return out
class Seq:
    """transition sequence of a wall from glyph g: x_u = (g_u -> g_{u+1}, dl, dr, pass, kappa)"""
    def __init__(s,g,prefix=False):
        f=plearn if prefix else learn
        seen={}; xs=[]; cur=g; s.bar=None
        while cur not in seen:
            seen[cur]=len(xs); r=f(cur)
            if r is None: s.bar=len(xs); break
            xs.append((cur,)+r); cur=r[0]
            if len(xs)>200: s.bar=len(xs); break
        s.xs=xs
        if s.bar is None:
            s.p=seen[cur]; s.pre=xs[:s.p]; s.cyc=xs[s.p:]; s.P=len(s.cyc)
        else:
            s.p=len(xs); s.pre=xs; s.cyc=[]; s.P=0; s.endg=cur
        s.g0=g
        s._prep()
        s._prep2()
    def ok(s,c): return s.bar is None or c<=s.bar
    def glyph(s,c):
        if c<s.p: return s.pre[c][0]
        if s.P==0: assert c==s.p; return s.endg
        return s.cyc[(c-s.p)%s.P][0]
    def _prep(s):
        F=6
        s.ps=[[0]*(len(s.pre)+1) for _ in range(F)]; s.pn=[[0]*(len(s.pre)+1) for _ in range(F)]
        for k in range(2,F):
            for u,x in enumerate(s.pre): s.ps[k][u+1]=s.ps[k][u]+x[k]; s.pn[k][u+1]=s.pn[k][u]+min(0,x[k])
        s.cs=[[0]*(s.P+1) for _ in range(F)]; s.cn=[[0]*(s.P+1) for _ in range(F)]
        for k in range(2,F):
            for u,x in enumerate(s.cyc): s.cs[k][u+1]=s.cs[k][u]+x[k]; s.cn[k][u+1]=s.cn[k][u]+min(0,x[k])
    def S(s,c,k):  # sum of field k over first c
        if c<=s.p: return s.ps[k][c]
        c-=s.p; W,r=divmod(c,s.P)
        return s.ps[k][s.p]+W*s.cs[k][s.P]+s.cs[k][r]
    def Sneg(s,c,k):
        if c<=s.p: return s.pn[k][c]
        c-=s.p; W,r=divmod(c,s.P)
        return s.pn[k][s.p]+W*s.cn[k][s.P]+s.cn[k][r]
    def T(s,c,k):  # sum_{u<c} (c-1-u) f_u
        if c==0: return 0
        return (c-1)*s.S(c,k)-s.U(c,k)
    def _prep2(s):
        s.pre_t=[u for u,x in enumerate(s.pre) if x[4]]
        s.offs=[v for v,x in enumerate(s.cyc) if x[4]]
        s.preU={k: sum(u*x[k] for u,x in enumerate(s.pre)) for k in range(2,6)}
        s.cycV={k: sum(v*x[k] for v,x in enumerate(s.cyc)) for k in range(2,6)}
        s.part={k: [s.cs[k][o] for o in s.offs] for k in range(2,6)}
        s.partsum={k: [0] for k in range(2,6)}
        for k in range(2,6):
            for v in s.part[k]: s.partsum[k].append(s.partsum[k][-1]+v)
    def U(s,c,k):  # sum_{u<c} u f_u
        if c<=s.p: return sum(u*x[k] for u,x in enumerate(s.pre[:c]))
        a=s.preU[k]; c-=s.p; W,r=divmod(c,s.P); p=s.p; P=s.P
        Sc=s.cs[k][P]; V=s.cycV[k]
        a+=W*(p*Sc+V)+P*Sc*W*(W-1)//2
        a+=(p+W*P)*s.cs[k][r]+sum(v*x[k] for v,x in enumerate(s.cyc[:r]))
        return a
    def passsum(s,Q,k):  # sum_{q<Q} S(t_q,k), t_q = index of q-th pass
        pre_t=s.pre_t
        if Q<=len(pre_t): return sum(s.S(t,k) for t in pre_t[:Q])
        tot=sum(s.S(t,k) for t in pre_t); Q-=len(pre_t)
        J=len(s.offs)
        if J==0: raise Exception('no passes in cycle')
        W,rem=divmod(Q,J); Sp=s.S(s.p,k); Sc=s.cs[k][s.P]
        ps=s.partsum[k]
        tot+=W*J*Sp+Sc*J*W*(W-1)//2+W*ps[J]+rem*(Sp+W*Sc)+ps[rem]
        return tot
SEQ={}
def seq(g,prefix=False):
    key=(g,prefix)
    if key not in SEQ: SEQ[key]=Seq(g,prefix)
    return SEQ[key]
# fields: 0 glyph,1 g2,2 dl,3 dr,4 pass,5 kappa
def plan(toks,m):
    k=(len(toks)-3)//2  # walls 1..k ; toks[2j] glyph of wall j; blocks toks[2i-1], i=1..k+1
    c=[0]*(k+1); c[k]=m; sq=[None]*(k+1)
    j=k
    while j>=1:
        sq[j]=seq(toks[2*j])
        if not sq[j].ok(c[j]): return None
        c[j-1]=sq[j].S(c[j],4)
        if c[j-1]==0: break
        j-=1
    top=j  # walls left of top are untouched (c=0)
    if top==0:
        sq[0]=seq(toks[0],True)
        if not sq[0].ok(c[0]): return None
    for i in range(max(top,1),k+2):
        lb=toks[2*i-1]+(sq[i-1].Sneg(c[i-1],3) if c[i-1] else 0)+(sq[i].Sneg(c[i],2) if i<=k and c[i] else 0)
        if lb<FOLD: return None
    return c,sq
def apply(toks,m,c,sq):
    k=(len(toks)-3)//2; new=list(toks); steps=0
    top=min([j for j in range(k+1) if c[j]]+[k])
    for j in range(max(top-1,0),k+1):
        if sq[j] is None: sq[j]=seq(toks[2*j],j==0)
    for j in range(top,k+1):
        new[2*j]=sq[j].glyph(c[j]); steps+=sq[j].S(c[j],5)
    for i in range(max(top,1),k+2):
        n0=toks[2*i-1]
        cross=c[i-1]  # trips crossing block i
        Si=cross*n0+sq[i-1].T(cross,3)+(sq[i].passsum(cross,2) if i<=k else 0)
        steps+=8*Si
        new[2*i-1]=n0+sq[i-1].S(c[i-1],3)+(sq[i].S(c[i],2) if i<=k else 0)
    return new,steps
from fractions import Fraction
INF=float("inf"); BIGLIM=10**3000
def _maxc(sq,X):
    """largest c with S(c,pass) <= X, also c <= barrier"""
    if X==INF: return sq.bar if sq.bar is not None else INF
    pre_t=[u for u,x in enumerate(sq.pre) if x[4]]
    if X<len(pre_t): r=pre_t[X]
    elif sq.bar is not None: r=INF
    else:
        offs=[v for v,x in enumerate(sq.cyc) if x[4]]
        if not offs: r=INF
        else:
            W,q=divmod(X-len(pre_t),len(offs)); r=sq.p+W*sq.P+offs[q]
    if sq.bar is not None: r=min(r,sq.bar)
    return r
def _maxsearch(f,cap):
    """largest c in [0,cap] with f(c) true (f monotone: true then false); f(0) assumed true"""
    if cap!=INF and f(cap): return cap
    lo=0; hi=1
    while (cap==INF or hi<cap) and f(hi):
        lo=hi; hi*=2
        if cap==INF and hi>BIGLIM: return INF
    if cap!=INF and hi>cap: hi=cap
    while hi-lo>1:
        mid=(lo+hi)//2
        if f(mid): lo=mid
        else: hi=mid
    return lo
def _maxsearch_from(f,cap,guess):
    """as _maxsearch, starting near guess (f true at 0, monotone)"""
    lo=max(0,int(guess)-64)
    if cap!=INF: lo=min(lo,cap)
    while lo>0 and not f(lo): lo//=2
    step=64
    while True:
        nx=lo+step
        if cap!=INF and nx>cap: nx=cap
        if nx==lo or not f(nx): break
        lo=nx; step*=2
    hi=nx
    if hi==lo: return lo
    while hi-lo>1:
        mid=(lo+hi)//2
        if f(mid): lo=mid
        else: hi=mid
    return lo
def jump(s,toks):
    if s!=3 or toks[-1]!='110': return 0,None,0
    k=(len(toks)-3)//2
    sq=[None]*(k+1)
    def g(j):
        if sq[j] is None: sq[j]=seq(toks[2*j],j==0)
        return sq[j]
    def m_of(j,C):
        for t in range(j+1,k+1):
            if C==INF: return INF
            C=_maxc(g(t),C)
        return C
    def cat(j,m):  # c_j for m trips
        c=m
        for t in range(k,j,-1):
            if c==INF: return INF
            c=g(t).S(c,4)
        return c
    best=INF
    n=toks[2*k+1]; w=g(k)
    capk=w.bar if w.bar is not None else INF
    if w.bar is None and w.cn[3][w.P]==0: best=min(best,capk)
    else: best=min(best,_maxsearch(lambda c: n+w.Sneg(c,3)>=FOLD, capk))
    cb=best  # c_k(best)
    j=k
    while j>=1:
        w=g(j)
        # cb = c_j(best)
        if w.bar is not None and (cb==INF or cb>w.bar):
            best=min(best,m_of(j,w.bar)); cb=cat(j,best)
        L=g(j-1); n=toks[2*j-1]
        capj=w.bar if w.bar is not None else INF
        if cb!=INF: capj=min(capj,cb)
        if L.bar is not None: capj=min(capj,_maxc(w,L.bar))  # the carries into wall j-1 stay below its barrier
        f=lambda c: L.ok(w.S(c,4)) and n+L.Sneg(w.S(c,4),3)+w.Sneg(c,2)>=FOLD
        if w.bar is None and w.cn[2][w.P]==0 and (L.bar is None and L.cn[3][L.P]==0 or w.cs[4][w.P]==0): cj=capj
        elif capj!=INF and f(capj): cj=capj
        else:
            sl=Fraction(0)
            if w.bar is None:
                sl=Fraction(-w.cn[2][w.P],w.P)
                if L.bar is None: sl+=Fraction(-L.cn[3][L.P]*w.cs[4][w.P],L.P*w.P)
            if sl>0: cj=_maxsearch_from(f,capj,min((n-FOLD)*sl.denominator//sl.numerator,capj))
            else: cj=_maxsearch(f,capj)
        if cb==INF or cj<cb:
            nb=m_of(j,cj)
            if nb<best: best=nb; cb=cat(j,best)
        if best==0: return 0,None,0
        if cb==INF: c_next=INF
        else: c_next=w.S(cb,4)
        if c_next==0: break
        cb=c_next
        j-=1
    if j==0:
        # prefix barrier: c_0 <= bar_0 (handled through L.ok above for block 1); nothing more
        pass
    if best==INF or best==0: return 0,None,0
    m=best
    p=plan(toks,m)
    if p is None: raise Exception('jump: plan rejects m=%d'%m)
    c,sq2=p; new,st=apply(toks,m,c,sq2)
    return m,new,st
