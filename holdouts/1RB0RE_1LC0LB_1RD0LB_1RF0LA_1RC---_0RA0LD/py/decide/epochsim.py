"""Exact accelerated simulation of the real run, epoch after epoch (concrete counts), with period jumping.
Each round trip is an E lemma and an X lemma (memoized symbolic runs); epoch transitions are run in full."""
import sys,time
from decide import *
import decide, fs
decide.move2=fs.move3
from test1 import load_real
import os
DBG=int(os.environ.get("DBG","0"))
def ev(l,env): return l.val(env)
def full_until_newstack(c,minc=40):
    steps0=c.steps
    for _ in range(10**9):
        x=fs.move3(c)
        if is_ck(x,c):
            Rt=norm_right(list(reversed(c.R))); c.R=list(reversed(Rt)); c.dl=c.dr=None
            i=next(j for j,t in enumerate(Rt) if isinstance(t,Rep))
            if len(Rt[i].w)==20 and Rt[i].n[-1]>=minc: return
def rt_steps(s,e,xr):
    P,st,prefix,uw,uc,Xs=s
    n=uc[-1]
    st_E=e['steps'].val([n-e['c']]+[0]*NV)
    cnt=xcounts(Xs)
    env=[n-e['delta']]+[cnt[k][-1]-xr['consts'][k] for k in range(len(cnt))]+[0]*NV
    return st_E+xr['steps'].val(env[:NV])
if __name__=="__main__":
    c,K,k=load_real(sys.argv[1]); NEP=int(sys.argv[2])
    steps=int(sys.argv[3]) if len(sys.argv)>3 else 0   # steps of the real run at the dump (from dump.c)
    for _ in range(10**7):
        x=fs.move3(c)
        if is_ck(x,c): break
    steps+=c.steps[-1]
    s=decompose(c); rt=0; t0=time.time(); ep0=0
    if len(sys.argv)>4:
        import pickle; d=pickle.load(open(sys.argv[4],'rb')); s=d['s']; steps=d['steps']; rt=d['rt']; ep0=d['ep']+1
    for ep in range(ep0,ep0+NEP):
        seen={}; jumped=False
        while True:
            P,st,prefix,uw,uc,Xs=s
            try: e=E(P,st,prefix,uw,uc[-1])
            except StackEnd: break
            xr,X2=X(e['uw2'],e['carry'],e['st2'],Xs)
            steps+=rt_steps(s,e,xr)
            s=(e['P2']+xr['leftlit'],xr['st'],xr['prefix'],xr['uw'],uc-e['delta'],X2); rt+=1
            key=(s[0],s[1],s[2],s[3],xshape(s[5]))
            if not jumped and key in seen:
                rt0,u0,x0,st0=seen[key]
                per=rt-rt0; du=u0-s[4][-1]; dx=[a-b for a,b in zip(xcounts(s[5]),x0)]; dst=steps-st0
                # steps per period grow (sweeps get longer): second differences; jump using two periods
                q=(s[4][-1]-200)//du-2
                # never jump a slot that shrinks below 200 (its exhaustion changes the behaviour)
                for a,d_ in zip(xcounts(s[5]),dx):
                    if d_[-1]<0: q=min(q,(a[-1]-200)//(-d_[-1])-2)
                if q>0:
                    # exact: steps of a period are linear in the period index: measure one more period
                    seen2_u=s[4][-1]; st1=steps; s1=s; mx=0; mxx=0
                    for _ in range(per):
                        P,st,prefix,uw,uc,Xs=s1
                        e=E(P,st,prefix,uw,uc[-1]); xr,X2=X(e['uw2'],e['carry'],e['st2'],Xs)
                        mx=max(mx,e['need']); mxx=max([mxx]+list(xr['needs']))
                        steps+=rt_steps(s1,e,xr)
                        s1=(e['P2']+xr['leftlit'],xr['st'],xr['prefix'],xr['uw'],uc-e['delta'],X2)
                    rt+=per; d1=st1-st0; d2=steps-st1; dd=d2-d1
                    # every jumped period must stay where the lemmas of the measured period hold
                    q=min(q,(s1[4][-1]-mx)//du-1); assert mxx<150, mxx
                    if q<=0:
                        s=s1; seen={}; continue
                    # periods are linear in counts, so period steps form an arithmetic progression
                    steps+= q*d2 + dd*q*(q+1)//2
                    cn=xcounts(s1[5]); dx=[a-b for a,b in zip(cn,xcounts(s[5]))]
                    X3=[];it=0
                    for z in s1[5]:
                        if isinstance(z,Rep): X3.append(Rep(z.w,z.n+dx[it].scale(q))); it+=1
                        else: X3.append(z)
                    s=(s1[0],s1[1],s1[2],s1[3],s1[4]-du*q,X3); rt+=q*per
                    seen={}
                    continue
            seen.setdefault(key,(rt,s[4][-1],xcounts(s[5]),steps))
            if DBG and time.time()-globals().setdefault("_tl",[0])[0]>DBG: _tl[0]=time.time(); print("  dbg rt",rt,"U",s[4][-1],"X",show(s[5])[:90],STATS,len(seen),flush=True)
        P,st,prefix,uw,uc,Xs=s
        print('epoch end',ep,'rt',rt,'U left',uc[-1],'X',show(Xs)[:80],'steps ~%.4e'%steps, round(time.time()-t0),flush=True)
        assert uc[-1]<40, 'stack not exhausted'
        c=compose(*s); c.steps=C(0)
        full_until_newstack(c)
        steps+=c.steps[-1]
        s=decompose(c)
        print('  new stack',s[4][-1],'X',show(s[5])[:80],flush=True)
        if os.environ.get('EPSTATE'):
            import pickle; pickle.dump(dict(s=s,steps=steps,rt=rt,ep=ep),open(os.path.join(os.environ['EPSTATE'],'epstate_%d.pkl'%ep),'wb'))
