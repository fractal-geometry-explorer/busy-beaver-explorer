import sys,time,pickle
from decide import *
from test1 import load_real
import decide, fs
decide.move2=fs.move3
move2=fs.move3
UWS=set()
TMEMO={}
NSKIP=[0]
def full_until_regular(c,maxck=20000):
    STATS['Truns']+=1
    nck=0
    for _ in range(10**8):
        x=move2(c)
        if is_ck(x,c):
            nck+=1
            Rt=norm_right(list(reversed(c.R))); c.R=list(reversed(Rt)); c.dl=c.dr=None
            i=next(j for j,t in enumerate(Rt) if isinstance(t,Rep))
            if Rt[i].n[T]!=0 and len(Rt[i].w)==20: return nck
            if nck>maxck: raise RuntimeError('transition too long')
    raise RuntimeError('no end')
def walk(state,maxrt=20000):
    """follow E/X lemmas with a huge U count; returns list of per-rt records and (tr_len, period)"""
    P,st,prefix,uw,uc,Xs=state
    s=(P,st,prefix,uw,Lc(T,10**7),Xs)
    recs=[]; seen={}
    for k in range(maxrt):
        P,st,prefix,uw,uc,Xs=s
        key=(P,st,prefix,uw,xshape(Xs))
        if key in seen:
            j=seen[key]; return recs,j,k-j
        seen[key]=k
        e=E(P,st,prefix,uw,uc[-1])
        recs.append(dict(key=key,need=e['need'],delta=e['delta'],X=Xs))
        s=rt_EX(s)
    raise RuntimeError('no cycle in walk')
def enumerate_reps(Xs):
    k=-1;out=[]
    for z in Xs:
        if isinstance(z,Rep): k+=1; out.append((k,z))
        else: out.append((-1,z))
    return out
def stack_ends(recs,j,per,b):
    """for each residue class mod (consumption per period): minimal U0>=b; returns list of (U0, k_end, idx, r)"""
    cons=sum(recs[i]['delta'] for i in range(j,j+per))
    out=[]
    for s in range(cons):
        U0=b+((s-b)%cons); U=U0; k=0
        while True:
            idx=k if k<j else j+(k-j)%per
            rc=recs[idx]
            if U<rc['need']: break
            U-=rc['delta']; k+=1
        out.append((U0,k,idx,U))
    return cons,out
def x_at(recs,j,per,k):
    idx=k if k<j else j+(k-j)%per
    X0=recs[idx]['X']
    if k<j: return X0,0
    nper=(k-idx)//per
    # period growth
    Xa=recs[j]['X']; Xb=recs[j+per-1]['X']
    return X0,nper
def period_growth(recs,j,per,state_after):
    pass
if __name__=="__main__":
    t0=time.time()
    c,K,k=load_real(sys.argv[1])
    for _ in range(10**7):
        x=move2(c)
        if is_ck(x,c): break
    s=decompose(c)
    UWS.add(s[3])
    # follow to the concrete stack end
    n=0
    while True:
        s2=rt_EX(s)
        if s2 is None: break
        s=s2; n+=1
    P,st,prefix,uw,uc,Xs=s
    print('real stack end after',n,'rts: U',uc,'X',show(Xs)[:100])
    # generalize the V count
    cnt=xcounts(Xs); vi=max(range(len(cnt)),key=lambda q:cnt[q][-1]); vval=cnt[vi][-1]
    D=int(sys.argv[2]) if len(sys.argv)>2 else 2
    it=0; Xg=[]
    for z in Xs:
        if isinstance(z,Rep):
            Xg.append(Rep(z.w, Lc(T,0).scale(D)+vval if it==vi else z.n)); it+=1
        else: Xg.append(z)
    queue=[('init',(P,st,prefix,uw,uc,Xg))]
    done_entries={}
    trans_log=[]
    while queue:
        tag,stend=queue.pop(0)
        sx=stend[5]; scn=xcounts(sx); svi=[q for q in range(len(scn)) if scn[q][T]!=0]
        assert len(svi)==1
        Bv=scn[svi[0]][-1]
        tkey=(stend[0],stend[1],stend[2],stend[3],tuple(stend[4]),xshape(sx),tuple(tuple(q) for i_,q in enumerate(scn) if i_!=svi[0]),Bv%2)
        if tkey in TMEMO and TMEMO[tkey]<=Bv:
            NSKIP[0]+=1; continue
        TMEMO[tkey]=Bv
        c=compose(*stend)
        try:
            nck=full_until_regular(c)
        except Halted as h:
            print('HALT in transition',tag,h); trans_log.append((tag,'HALT')); continue
        ent=decompose(c)
        P,st,prefix,uw,uc,Xs=ent
        xc=xcounts(Xs)
        assert all(q.isconst() for q in xc), xc
        if xc:
            vi=max(range(len(xc)),key=lambda q:xc[q][-1]); vmin=xc[vi][-1]
        else:
            vi=-5; vmin=0
        ident=(P,st,prefix,uw,xshape(Xs),tuple(tuple(q) if i!=vi else ('V',q[-1]%2) for i,q in enumerate(xc)))
        b=uc[-1]
        print('transition',tag,'skips',NSKIP[0],'->',nck,'checkpoints; U',uc,'X',show(Xs)[:120],'P',len(P),round(time.time()-t0),STATS,flush=True)
        trans_log.append((tag,ident,uc))
        if ident in done_entries:
            ob,ov=done_entries[ident]
            if ob<=b and ov<=vmin: continue
            b=min(b,ob); vmin=min(vmin,ov)
            # rebuild entry with the smaller V bound (same parity)
        done_entries[ident]=(b,vmin)
        Xs=[Rep(z.w,C(vmin)) if (isinstance(z,Rep) and i_==vi) else z for i_,z in enumerate_reps(Xs)] if xc else Xs
        ent=(P,st,prefix,uw,Lc(T,b),Xs)
        recs,j,per=walk(ent)
        # check X growth per period: X counts at j and j+per
        print('  walk: transient',j,'period',per, 'eid',len(done_entries),flush=True)
        cons,ends=stack_ends(recs,j,per,b)
        print('  consumption per period',cons)
        # X counts: at entry the X counts; per rt growth: compare recs[j] and the state after one period
        Xj=recs[j]['X']; 
        # recompute state after one period to get growth
        st_=(recs[j]['key'][0],recs[j]['key'][1],recs[j]['key'][2],recs[j]['key'][3],Lc(T,10**7),Xj)
        for q in range(per): st_=rt_EX(st_)
        g=[a-b_ for a,b_ in zip(xcounts(st_[5]),xcounts(Xj))]
        assert xshape(st_[5])==xshape(Xj)
        for (U0,kend,idx,r) in ends:
            assert kend>=j+per, ('short family',U0,kend,j,per)
            rc=recs[idx]
            Xk=rc['X']
            nper=0 if kend<j else (kend-idx)//per
            cn=xcounts(Xk)
            newc=[cn[q]+g[q].scale(nper) for q in range(len(cn))]
            gi=[q for q in range(len(g)) if not g[q].iszero()]
            assert len(gi)==1 and g[gi[0]].isconst()
            G=g[gi[0]][-1]  # growth per period of the V slot
            assert G%D==0
            # family: q extra periods -> V += G q  ; generalize to D*t + value
            Xg=[];it=0
            for z in Xk:
                if isinstance(z,Rep):
                    v=newc[it]
                    if it==gi[0]: v=Lc(T,0).scale(D)+v[-1]
                    Xg.append(Rep(z.w,v)); it+=1
                else: Xg.append(z)
            key=rc['key']
            queue.append(((len(done_entries),U0%cons),(key[0],key[1],key[2],key[3],C(r),Xg)))
    print('DONE: entries',len(done_entries),'transitions',len(trans_log),STATS, round(time.time()-t0))
    pickle.dump(dict(log=trans_log,entries=list(done_entries.items())),open('bfs_out.pkl','wb'))
    pickle.dump(dict(E=EMEMO,X=XMEMO),open('memo.pkl','wb'))
