# Exact check: does a TM simulate the unary-segment stack machines of busycoq PRs 115/118 ("581")
# or 116/117/119 ("484")? Usage: python3 segment_match.py MACHINE...  Prints the matching
# (machine kind, state assignment, mirror) list; [] means no match. Random small stacks, 60 rule tests.
import itertools,random,sys
def parse(s):
    t={}
    for i,r in enumerate(s.split('_')):
        for b in (0,1):
            x=r[3*b:3*b+3]; t[(i,b)]=None if x[0]=='-' else (int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
    return t
# ---------- abstract machine 581 ----------
def bumpL(ls): return [0] if not ls else [ls[0]+1]+ls[1:]
def bumpR(rs): return [(0,False)] if not rs else [(rs[0][0]+1,rs[0][1])]+rs[1:]
def step581(m,L,R):
    if m=='FR':
        if not R: return ('BL',L,[(0,False)])
        (d,b),rs=R[0],R[1:]
        if d==0 and not b: return ('BL',L,bumpR(bumpR(rs)))
        if d==0 and b: return ('BL',L,[(1,False)]+rs)
        if d==1 and not b: return ('FR',[1]+L,rs)
        if d==1 and b: return ('BL',[1]+L,bumpR(rs))
        if d==2: return ('DR',[0]+L,[(0,b)]+rs)
        return ('DL',[1]+L,[(d-3,b)]+rs)
    if m=='BL':
        if not L: return None
        a,ls=L[0],L[1:]
        if a==0: return ('DL',bumpL(bumpL(ls)),R)
        if a==1: return ('BL',ls,[(0,True)]+R)
        if a==2:
            if not ls: return None
            return ('DL',[ls[0]+1]+ls[1:],[(1,False)]+R)
        return ('FR',[a-3]+ls,[(0,True)]+R)
    if m=='DR':
        if not R: return ('FR',bumpL(L),[])
        (d,b),rs=R[0],R[1:]
        if d==0 and not b: return ('FR',L,bumpR(bumpR(rs)))
        if d==0 and b: return ('FR',L,[(1,False)]+rs)
        if d==1 and not b: return ('FR',bumpL(bumpL(bumpL(L))),rs)
        if d==1 and b: return ('BL',bumpL(bumpL(bumpL(L))),bumpR(rs))
        if d==2: return ('DR',bumpL(bumpL(L)),[(0,b)]+rs)
        return ('DL',bumpL(bumpL(bumpL(L))),[(d-3,b)]+rs)
    if m=='DL':
        if not L: return ('FR',[0],R)
        a,ls=L[0],L[1:]
        if not R:
            if a==0:
                if not ls: return None
                return ('DL',[ls[0]+1]+ls[1:],[(0,True),(0,False)])
            return ('FR',[a-1]+ls,[(1,False)])
        (d,b),rs=R[0],R[1:]
        if d==0 and not b: return ('FR',[a+2]+ls,rs)
        if d==0 and b: return ('BL',[a+2]+ls,bumpR(rs))
        if d==1: return ('DR',[a+1]+ls,[(0,b)]+rs)
        return ('DL',[a+2]+ls,[(d-2,b)]+rs)
def encL581(L):
    out=[]
    for a in L: out+= [1]*(a+1)+[0]
    return out
def encR581(R):
    out=[]
    for d,b in R: out+= [1]*(d+1)+[0]+([0] if b else [])
    return out
# config representation: (state, leftlist nearest-first, head symbol, rightlist nearest-first)
def cfg581(m,L,R,sig):
    l=encL581(L); r=encR581(R)
    st={'FR':sig[0],'BL':sig[1],'DR':sig[2],'DL':sig[2]}[m]
    if m in('FR','DR'):
        h=r[0] if r else 0; return (st,l,h,r[1:])
    h=l[0] if l else 0; return (st,l[1:],h,r)
# ---------- abstract machine 484 ----------
def bump(xs): return [(0,False)] if not xs else [(xs[0][0]+1,xs[0][1])]+xs[1:]
def step484(m,L,R):
    if m=='C0': return ('AL',L,bump(R))
    if m=='AL':
        if not L: return ('BR',[(0,False)],R)
        (a,s),Ls=L[0],L[1:]
        if a==0 and not s: return ('E1',Ls,R)
        if a==0 and s: return None
        if a==1 and not s:
            if not R: return ('C0',Ls,[])
            return ('AL',Ls,[(0,True)]+R)
        if a==1 and s: return ('BR',bump(Ls),[(0,True)]+R)
        if a==2 and not s: return ('BR',bump(Ls),[(1,False)]+R)
        if a==2 and s: return ('BR',[(0,False)]+Ls,[(1,False)]+R)
        return ('C0',[(a-3,s)]+Ls,[(0,False)]+R)
    if m=='E1':
        if not L: return None
        return ('BR',L,bump(bump(R)))
    if m=='BR':
        if not R:
            if not L: return ('C0',[],[(0,False)])
            (a,s),Ls=L[0],L[1:]
            if a==0 and not s: return ('D0',[(0,True)]+Ls,[])
            if a==0 and s: return ('BR',[(0,False)]+Ls,[(0,True),(0,False)])
            return ('D0',[(0,False),(a-1,s)]+Ls,[])
        (d,c),Rs=R[0],R[1:]
        if d==0 and not c: return ('D0',bump(L),Rs)
        if d==0 and c: return ('C0',bump(bump(L)),Rs)
        return ('DR',bump(L),[(d-1,c)]+Rs)
    if m=='DR':
        if not R: return ('C0',bump(L),[])
        (d,c),Rs=R[0],R[1:]
        if d==0:
            if not L: return ('BR',[],bump(Rs) if not c else [(0,False)]+Rs)
            return (('DR' if not c else 'D0'),[(0,False)]+L,Rs)
        return ('BR',bump(L),[(d-1,c)]+Rs)
    if m=='D0':
        if not R: return ('C0',bump(L),[])
        (d,c),Rs=R[0],R[1:]
        if d==0 and not c: return ('C0',bump(L),bump(Rs))
        if d==0 and c: return ('C0',bump(L),[(0,False)]+Rs)
        if d==1 and not c: return ('D0',[(0,False)]+bump(L),Rs)
        if d==1 and c: return ('C0',[(1,False)]+bump(L),Rs)
        return ('DR',[(0,False)]+bump(L),[(d-2,c)]+Rs)
def encStack(xs):
    out=[]
    for a,s in xs: out+=[1]*(a+1)+[0]+([0] if s else [])
    return out
def cfg484(m,L,R,sig):
    l=encStack(R); r=encStack(L)   # left tape from s_R, right from s_L
    B,C,E,A,D=sig
    if m=='C0': return (B,l,0,r)
    if m=='AL': return (C,l,r[0] if r else 0,r[1:])
    if m=='E1': return (E,[0]+l,0,r)
    if m=='BR': return (A,l[1:],l[0] if l else 0,r)
    if m=='DR': return (D,l[1:],l[0] if l else 0,r)
    if m=='D0': return (D,l,0,r)
def norm(c):
    s,l,h,r=c
    l=list(l); r=list(r)
    while l and l[-1]==0: l.pop()
    while r and r[-1]==0: r.pop()
    return (s,tuple(l),h,tuple(r))
def run_until(tm,c,target,maxs,mir):
    s,l,h,r=c; l=list(l); r=list(r)
    tgt=norm(target)
    for i in range(1,maxs+1):
        x=tm[(s,h)]
        if x is None: return False
        w,d,n=x
        if mir: d=-d
        if d==1: l.insert(0,w); h=r.pop(0) if r else 0
        else: r.insert(0,w); h=l.pop(0) if l else 0
        s=n
        if s==tgt[0] and h==tgt[2] and norm((s,l,h,r))==tgt: return True
    return False
def rnd_list(kind,rng):
    n=rng.randint(0,4)
    if kind=='nat': return [rng.randint(0,7) for _ in range(n)]
    return [(rng.randint(0,7),rng.random()<0.5) for _ in range(n)]
MODES={'581':(['FR','BL','DR','DL'],step581,cfg581,3,('nat','seg')),'484':(['C0','AL','E1','BR','DR','D0'],step484,cfg484,5,('seg','seg'))}
def check(tm,which,sig,mir,ntests=60,seed=1):
    modes,step,cfg,_,kinds=MODES[which]; rng=random.Random(seed)
    ok=0
    for t in range(ntests):
        m=modes[t%len(modes)]; L=rnd_list(kinds[0],rng); R=rnd_list(kinds[1],rng)
        nx=step(m,L,R)
        if nx is None: continue
        if not run_until(tm,cfg(m,L,R,sig),cfg(*nx,sig),400,mir): return False
        ok+=1
    return ok>=ntests//2
def search(mstr):
    tm=parse(mstr); hits=[]
    for which,(_,_,_,k,_) in MODES.items():
        for sig in itertools.permutations(range(6),k):
            for mir in (0,1):
                if check(tm,which,sig,mir,ntests=6) and check(tm,which,sig,mir):
                    hits.append((which,''.join(chr(65+x) for x in sig),mir))
    return hits
if __name__=='__main__':
    for m in sys.argv[1:]: print(m,search(m),flush=True)
