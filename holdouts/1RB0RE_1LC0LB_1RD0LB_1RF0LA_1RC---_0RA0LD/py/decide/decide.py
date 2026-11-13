"""Decision procedure for 1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD (see notes).
Symbolic simulation with repeated blocks; round trips split into an engine part (E) and a right part (X)."""
import sys, time, pickle
import fs
from fs import *
from fsdrive import absorb_list, show
T=7   # epoch variable index
def rots(w): return [tuple(w[i:]+w[:i]) for i in range(len(w))]
Vb=(1,0,1,1,1,0,1,1,1,0); VFAM=set(rots(Vb))|set(tuple(1-z for z in q) for q in rots(Vb))
VFAM=sorted(VFAM)
def repify(seq,fam,minc=3):
    out=[];i=0
    while i<len(seq):
        t=seq[i]
        if isinstance(t,int):
            done=False
            for w in fam:
                Lw=len(w); k=0
                while i+(k+1)*Lw<=len(seq) and all(isinstance(z,int) for z in seq[i+k*Lw:i+(k+1)*Lw]) and tuple(seq[i+k*Lw:i+(k+1)*Lw])==w: k+=1
                if k>=minc:
                    out.append(Rep(w,C(k))); i+=k*Lw; done=True; break
            if done: continue
        out.append(t); i+=1
    return out
def norm_right(Rt):
    return absorb_list(absorb_list(repify(absorb_list(list(Rt)),VFAM)))
def is_ck(x,c):
    return x and x[0]=='l' and not any(isinstance(z,Rep) for z in c.L)
UMIN={}
def track_reset(): fs.UNROLL_MIN[0]=10**9
# per-variable unroll tracking
_orig_note=fs._note
VMIN={}
def _note(t):
    vs=[i for i,a in enumerate(t.n[:-1]) if a]
    if len(vs)==1 and t.n[vs[0]]==1:
        v=vs[0]
        if t.n[-1]<VMIN.get(v,10**9): VMIN[v]=t.n[-1]
fs._note=_note
def Lc(var,c):
    l=[0]*(NV+1); l[var]=1; l[-1]=c; return Lin(*l)
# ---------------------------------------------------------------- E lemmas
EMEMO={}
CONFIRM=True
STATS=dict(Eruns=0,Xruns=0,Truns=0)
def E_run(P,st,prefix,uw,c,maxmoves=5*10**6):
    L=[BL]+list(P); Rt=list(prefix)+[Rep(uw,Lc(0,c)),CTX]
    cfg=Cfg(L,st,list(reversed(Rt)))
    VMIN.clear(); nm=0
    try:
        for nm in range(maxmoves): move2(cfg)
        raise RuntimeError('E: no exit')
    except TouchContext as e:
        if e.args[0]!='R': raise
    assert cfg.R==[CTX], cfg.R
    L=absorb_list(cfg.L)
    reps=[i for i,t in enumerate(L) if isinstance(t,Rep)]
    assert len(reps)==1, show(L)
    i=reps[0]; rp=L[i]
    assert rp.n==Lc(0,rp.n[-1]), rp.n
    P2=tuple(L[1:i]); carry=tuple(L[i+1:])
    assert all(isinstance(z,int) for z in P2+carry)
    need=c-VMIN[0]+1 if 0 in VMIN else 0
    return dict(need=max(need,0),delta=c-rp.n[-1],P2=P2,uw2=rp.w,carry=carry,st2=cfg.st,conc=cfg.conc,steps=cfg.steps,c=c,moves=nm)
class StackEnd(Exception): pass
def _confirm(P,st,prefix,uw,r):
    """r comes from a run symbolic in x>=0 with U=x+r['c'], so it holds for U>=r['c'].
    Re-run at the claimed need; if the re-run agrees, the lemma holds for U>=need."""
    if r['need']>=r['c']: r=dict(r); r['need']=r['c']; return r
    # try the claimed need, then a few larger values (some shift rules use a copy without noting it)
    for c2 in [r['need']]+[q for q in (1,2,3,4,5,6,8,10,12,16,20,24,32,48,64,96,128,192,256) if q>r['need']]:
        if c2>=r['c']: break
        try:
            r2=E_run(P,st,prefix,uw,c2,maxmoves=2*r['moves']+100)
            if all(r2[k]==r[k] for k in ('delta','P2','uw2','carry','st2')):
                r2=dict(r2); r2['need']=c2; return r2   # valid for U>=c2 exactly
        except Exception:
            pass
    STATS['Efallback']=STATS.get('Efallback',0)+1
    r=dict(r); r['need']=r['c']; return r
def E(P,st,prefix,uw,c):
    """an engine lemma valid for the actual stack count c (need<=c), or StackEnd when the
    engine runs into the junction (the symbolic run at U=c needs more copies than c)."""
    key=(P,st,prefix,uw)
    for r in EMEMO.get(key,()):
        if r['need']<=c: return r
    STATS['Eruns']+=1
    try:
        r=E_run(P,st,prefix,uw,c)
    except (NeedSplit,TouchContext,AssertionError,KeyError) as ex:
        raise StackEnd(ex)
    r=_confirm(P,st,prefix,uw,r) if CONFIRM else r
    EMEMO.setdefault(key,[]).append(r)
    return r
# ---------------------------------------------------------------- X lemmas
XMEMO={}
def xshape(Xseq): return tuple(('R',t.w) if isinstance(t,Rep) else t for t in Xseq)
def xcounts(Xseq): return [t.n for t in Xseq if isinstance(t,Rep)]
def X_run(uw2,carry,st2,shape,consts):
    Xseq=[];k=0
    for z in shape:
        if isinstance(z,tuple): Xseq.append(Rep(z[1],Lc(1+k,consts[k]))); k+=1
        else: Xseq.append(BL if z=='B' else z)
    assert k<=6
    L=[CTX,Rep(uw2,Lc(0,0))]+list(carry)
    cfg=Cfg(L,st2,list(reversed(Xseq)))
    VMIN.clear()
    for _ in range(5*10**6):
        x=move2(cfg)
        if is_ck(x,cfg): break
    else: raise RuntimeError('X: no checkpoint')
    assert cfg.L[0] is CTX and all(isinstance(z,int) for z in cfg.L[1:]), cfg.L
    leftlit=tuple(cfg.L[1:])
    Rt=norm_right(list(reversed(cfg.R)))
    i=next(j for j,t in enumerate(Rt) if isinstance(t,Rep))
    assert Rt[i].n==Lc(0,0), (Rt[i], show(Rt)[:200])
    prefix=tuple(Rt[:i]); X2=Rt[i+1:]
    needs=[max(consts[k]-VMIN[1+k]+1,0) if (1+k) in VMIN else 0 for k in range(len(consts))]
    return dict(steps=cfg.steps,leftlit=leftlit,prefix=prefix,st=cfg.st,uw=Rt[i].w,shape=xshape(X2),counts=xcounts(X2),needs=needs,consts=list(consts),conc=cfg.conc)
def X(uw2,carry,st2,Xseq):
    shape=xshape(Xseq); cnt=xcounts(Xseq)
    key=(uw2,carry,st2,shape)
    if key not in XMEMO:
        STATS['Xruns']+=1
        consts=[c[-1] for c in cnt]
        r=X_run(uw2,carry,st2,shape,consts)
        if r['needs']!=consts:
            r2=X_run(uw2,carry,st2,shape,r['needs'])
            assert r2['shape']==r['shape'] and r2['prefix']==r['prefix'] and r2['st']==r['st'] and r2['leftlit']==r['leftlit']
            r=r2
        XMEMO[key]=r
    r=XMEMO[key]
    for k,c in enumerate(cnt):
        assert c[-1]>=r['needs'][k] and all(a>=0 for a in c[:-1]), ('X need',c,r['needs'])
    # substitute y_k := actual_k - consts_k
    out=[]
    for oc in r['counts']:
        res=C(oc[-1])
        for k in range(len(cnt)):
            a=oc[1+k]
            if a: res=res+(cnt[k]-r['consts'][k]).scale(a)
        assert all(oc[j]==0 for j in range(len(oc)-1) if j not in range(1,1+len(cnt)))
        out.append(res)
    X2=[];it=iter(out)
    for z in r['shape']:
        X2.append(Rep(z[1],next(it)) if isinstance(z,tuple) else (BL if z=='B' else z))
    return r,X2
# ---------------------------------------------------------------- whole configurations at a checkpoint
def decompose(c):
    """checkpoint config -> (P, st, prefix, uw, ucount, Xseq)"""
    assert c.L[0] is BL and all(isinstance(z,int) for z in c.L[1:])
    Rt=norm_right(list(reversed(c.R)))
    i=next(j for j,t in enumerate(Rt) if isinstance(t,Rep))
    return tuple(c.L[1:]),c.st,tuple(Rt[:i]),Rt[i].w,Rt[i].n,Rt[i+1:]
def compose(P,st,prefix,uw,ucount,Xseq):
    Rt=list(prefix)+[Rep(uw,ucount)]+list(Xseq)
    return Cfg([BL]+list(P),st,list(reversed(Rt)))
def rt_EX(state):
    """one round trip by lemmas; state=(P,st,prefix,uw,ucount,Xseq). returns new state or None if U too small"""
    P,st,prefix,uw,uc,Xs=state
    if any(a<0 for a in uc[:-1]): return None
    try: e=E(P,st,prefix,uw,uc[-1])
    except StackEnd: return None
    uc2=uc-e['delta']
    xr,X2=X(e['uw2'],e['carry'],e['st2'],Xs)
    return (e['P2']+xr['leftlit'],xr['st'],xr['prefix'],xr['uw'],uc2,X2)
def full_until_done(c,var=T,maxck=100000):
    """full symbolic run until a checkpoint whose leftmost rep count involves var"""
    STATS['Truns']+=1
    nck=0
    for _ in range(10**8):
        x=move2(c)
        if is_ck(x,c):
            nck+=1
            Rt=norm_right(list(reversed(c.R))); c.R=list(reversed(Rt))
            i=next(j for j,t in enumerate(Rt) if isinstance(t,Rep))
            if Rt[i].n[var]!=0: return nck
            if nck>maxck: raise RuntimeError('transition too long')
    raise RuntimeError('no end')
