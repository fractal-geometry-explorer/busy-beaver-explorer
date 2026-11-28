"""The transient after a rebuild, run symbolically (used by py/sym_law.py).

A state is the pass machine of lean/General.lean (py/passm.py): a sweep (lb, phase, k, us) or a moment (F, l, us).
Entries are affine forms in parameters (py/sym_lin.py), lists may hold runs (value, count) with a symbolic count, and
the list ends in an opaque history H: a list of digits (blocks 3d + 2) known only by its number h = T(H)
(T(x :: r) = 2^x (1 + 2 T(r)), as in lean/Collapse.lean).  The last gap of the zone is *open*: more bits of the counter
may still add to it, and a move that needs to know more stops the run ("block"); this is a frame in the sense of
lean/Frame.lean.  The rules:

  * the moves of the pass machine (pstep), on runs and affine values; a decision the parameters do not settle
    raises Need with a case split (the caller runs every case);
  * a moment whose list is all digits and whose counter step is regular takes that sub-round as arithmetic: the list
    number goes down by 1 and the counter takes one step (W and gstep, lean/Subround.lean, lean/Collapse.lean);
    with the last block 4q + 1 it takes 2^q sub-rounds at once if the step after them is regular (gfast,
    lean/Counter.lean), else 2^q - 1 of them (to the last block 1 and q gaps of 3 in front), and j such chunks at
    once when the first gap is 4j + r (the last block 4(q + j) + 1, the list number - (2^(q+j) - 2^q));
  * the list number is kept as bit runs, so that subtracting powers of 2 is exact; a borrow or carry past the front
    goes to h, and the digits of H are read only when a move needs one (pull: h = 2^x (1 + 2 h'), x a new
    parameter);
  * a loop that eats one entry of a run per turn is taken all at once (try_loop), after checking one turn from the
    general state (the run of 1 + r entries, the entries that move by d per turn at e + d j): induction on j.

Concrete histories (St.hv) make the same code a concrete simulator, used to test it against py/rebuild_map.py.
"""
import copy
from sym_lin import *
B=lambda v: ('b',L(v))
def R(v,c): return ('r',L(v),L(c))
class Halt(Exception): pass
class Stop(Exception):
    def __init__(s,why): s.why=why
class St:
    def __init__(s):
        s.mode=None; s.lb=[]; s.ph=None; s.k=Lin(0); s.us=[]; s.F=[]; s.l=Lin(0)
        s.cons=[]; s.ops=[]; s.H=0; s.nH=1; s.sub=0; s.cnt=0; s.trace=[]; s.hv=None   # hv: concrete value of the current H (testing)
    def copy(s): return copy.deepcopy(s)
    def subst(s,v,e):
        if v=="C": s.cons=s.cons+[e]; return
        for f in ("lb","us","F","ops","cons"): setattr(s,f,subst_obj(getattr(s,f),v,e))
        s.k=s.k.subst(v,e); s.l=s.l.subst(v,e)
    # ---- the history H: an opaque digit list, known by its number h_i
    def newH(s,op,*args):
        if s.hv is not None:
            h=s.hv
            if op=='pull':
                x=args[0]; assert x.isconst(); assert h>0; s.hv=(h>>x.k)>>1
            elif op=='dbl': assert args[0].isconst(); s.hv=h<<args[0].k
            elif op=='add':
                assert args[1].isconst(); s.hv=h+args[0]*(1<<args[1].k); assert s.hv>=0, "H<0"
            elif op=='push': s.hv=Tl(args[0])+(h<<sigl(args[0]))
        s.ops.append((op,s.H,s.nH)+args); s.H=s.nH; s.nH+=1; return ('H',s.H)
    # ---- list helpers (lists are python lists of items; H only last)
    def front(s,lst,i=0,pull=True):
        """make lst[0..i] blocks; returns False if lst has fewer than i+1 entries"""
        j=0
        while j<=i:
            if j>=len(lst): return False
            it=lst[j]
            if it[0]=='b': j+=1; continue
            if it[0]=='r':
                if not ge(it[2],1): del lst[j]; continue
                lst[j:j+1]=[('b',it[1]),('r',it[1],it[2]-1)]; j+=1; continue
            if it[0]=='H':
                if not pull: return False
                if s.hv is not None:
                    h=s.hv; assert h>0, "pull from empty H"; xx=Lin((h&-h).bit_length()-1)
                else: xx=Lin.var(fresh("x"))
                lst[j:j+1]=[('b',3*xx+2), s.newH('pull',xx)]; j+=1; continue
        return True
    def hd(s,lst,i=0):
        return lst[i][1] if s.front(lst,i) else Lin(0)
    def addhd(s,lst,i,d):
        """lst[i] += d (lst[i] exists or is created as 0 at the end)"""
        if d==3:
            # +3 on a digit of H doubles h, without reading it
            assert i==0
            s.empty(lst)
            if lst and lst[0][0]=='H':
                lst[0]=s.newH('dbl',Lin(1)); return
        if s.front(lst,i): lst[i]=('b',lst[i][1]+d)
        else: lst.append(('b',Lin(d)))
    def empty(s,lst):
        if any(it[0] in ('b','H') for it in lst): 
            if all(it[0]!='r' for it in lst[:1]): return False
            # the list is nonempty; leading runs are left as they are
            return False
        while lst:
            it=lst[0]
            if it[0]=='r' and not ge(it[2],1): del lst[0]; continue
            return False
        return True
    def islast(s,lst,i):
        """lst[0..i] are blocks; is i the last entry?"""
        j=i+1
        if any(it[0] in ('b','H') for it in lst[j:]): return False
        while j<len(lst):
            it=lst[j]
            if it[0]=='r' and not ge(it[2],1): del lst[j]; continue
            return False
        return True
    def rd(s,us):
        if s.empty(us): return
        s.front(us)
        if not eq(us[0][1],0): us[0]=('b',us[0][1]-1)
    # ---- the pass machine
    def pstep(s):
        lb,ph,k,us=s.lb,s.ph,s.k,s.us
        if ph=="A" and ge(k,3):
            q,r=divmod_(k,3); lb.insert(0,R(2,q)); s.k=Lin(r); return
        if ge(k,1):
            if ph=="A": lb.insert(0,B(0)); s.ph="E"
            else: s.addhd(lb,0,1); s.ph="C" if ph=="E" else "A"
            s.k=k-1; return
        if not s.empty(us) and s.front(us) and eq(us[0][1],0):
            s.k=Lin(1); del us[0]; return
        if ph in ("C","E"):
            h0=s.hd(lb)
            if eq(h0,0):
                del lb[0]; s.addhd(lb,0,2); s.ph="C"; s.k=Lin(0); s.rd(us); return
            if ph=="C":
                del lb[0]; s.rd(us); s.mode="mom"; s.F=lb; s.l=h0; s.lb=None; s.sub+=1; return
            del lb[0]; s.addhd(lb,0,3); s.ph="A"; s.k=h0-1; s.rd(us); return
        # A on a 0
        if s.empty(us):
            s.addhd(lb,0,3); s.ph="C"; s.k=Lin(0); return
        s.front(us); u0=us[0][1]
        if ge(u0,3): s.addhd(lb,0,3); s.ph="C"; s.k=Lin(0); us[0]=('b',u0-3); return
        if eq(u0,2):
            s.addhd(lb,0,1); lb.insert(0,B(1)); s.ph="A"; s.k=Lin(0); del us[0]; return
        if not s.islast(us,0):
            s.front(us,1)
            if eq(us[1][1],0): raise Halt()
        h0=s.hd(lb); del lb[0]; s.addhd(lb,0,3); s.ph="A"; s.k=h0+1; del us[0]; s.rd(us)
    def wblock(s):
        """True if the step needs the open last gap"""
        lb,ph,k,us=s.lb,s.ph,s.k,s.us
        if (ph=="A" and ge(k,3)) or ge(k,1): return False
        s.front(us)
        one=s.islast(us,0)
        if eq(us[0][1],0): return one
        if ph in ("C","E"): return False
        if ge(us[0][1],3): return False
        if one: return True
        if eq(us[0][1],2): return False
        s.front(us,1)
        return eq(us[1][1],0) and s.islast(us,1)
    # ---- the counter
    def gpop(s,us):
        """gstep_win(1, us): ('reg', l, us) | 'block' | None; us is not modified"""
        us=list(us); n=Lin(0); i=0
        while True:
            if not s.front(us,i): return 'block'
            u=us[i][1]; last=s.islast(us,i)
            if not last and us[i][0]=='b' and i+1<len(us) and us[i+1][0]=='r' and us[i+1][1]==3 and eq(u,3):
                # a run of 3s: skip it at once
                n=n+1+us[i+1][2]; del us[i+1]; i+=1; continue
            if eq(u,3) and not last: i+=1; n=n+1; continue
            if ge(u,4): return ('reg',4*n+5,[('b',u-4)]+us[i+1:])
            if last: return 'block'
            if eq(u,0):
                s.front(us,i+1); u1=us[i+1][1]; last1=s.islast(us,i+1)
                if ge(u1,2): return ('reg',4*n+4,[('b',u1-2)]+us[i+2:])
                if last1: return 'block'
            return None
    # ---- the list as a number
    def bits(s,F):
        """F (digits, H last) -> bit runs (low first), True if H follows"""
        out=[]; hasH=False
        for it in F:
            if it[0]=='H': hasH=True; break
            if it[0]=='b':
                x,r=divmod_(it[1]-2,3); assert r==0
                out+=[(0,x),(1,Lin(1))]
            else:
                assert it[1]==2; out.append((1,it[2]))
        return out,hasH
    def fromBits(s,bs,hasH):
        out=[]; z=Lin(0)
        for b,n in bs:
            if b==0: z=z+n; continue
            if not ge(n,1): continue
            out.append(B(3*z+2)); out.append(R(2,n-1)); z=Lin(0)
        if hasH:
            if not eq(z,0): s.newH('dbl',z)
            out.append(('H',s.H))
        else:
            assert eq(z,0)
        return out
    def subpow(s,bs,e):
        """bs - 2^e (in place); a borrow goes to H"""
        pos=Lin(0); i=0
        while i<len(bs):
            b,n=bs[i]
            if ge(e,pos+n): pos=pos+n; i+=1; continue
            off=e-pos
            bs[i:i+1]=[(b,off),(b,Lin(1)),(b,n-off-1)]; i+=1
            if b==1: bs[i]=(0,Lin(1)); return
            # zeros from here up become ones until the next 1
            bs[i]=(1,Lin(1)); i+=1
            while i<len(bs):
                b,n=bs[i]
                if b==0: bs[i]=(1,n); i+=1; continue
                if not ge(n,1): i+=1; continue
                bs[i:i+1]=[(0,Lin(1)),(1,n-1)]; return
            s.newH('add',-1,Lin(0)); return
        s.newH('add',-1,e-pos)
    def addpow(s,bs,e):
        """bs + 2^e (in place); a carry goes to H"""
        pos=Lin(0); i=0
        while i<len(bs):
            b,n=bs[i]
            if ge(e,pos+n): pos=pos+n; i+=1; continue
            off=e-pos
            bs[i:i+1]=[(b,off),(b,Lin(1)),(b,n-off-1)]; i+=1
            if b==0: bs[i]=(1,Lin(1)); return
            bs[i]=(0,Lin(1)); i+=1
            while i<len(bs):
                b,n=bs[i]
                if b==1: bs[i]=(0,n); i+=1; continue
                if not ge(n,1): i+=1; continue
                bs[i:i+1]=[(1,Lin(1)),(0,n-1)]; return
            s.newH('add',1,Lin(0)); return
        s.newH('add',1,e-pos)
    def add1(s,bs):
        i=0
        while i<len(bs):
            b,n=bs[i]
            if b==1: bs[i]=(0,n); i+=1; continue
            if not ge(n,1): i+=1; continue
            bs[i:i+1]=[(1,Lin(1)),(0,n-1)]; return
        s.newH('add',1,Lin(0))
    def isdig(s,F):
        for it in F:
            if it[0]=='H': return True
            if it[0]=='b' and mod(it[1],3)!=2: return False
            if it[0]=='r' and ge(it[2],1) and mod(it[1],3)!=2: return False
        return True
    def moment(s):
        F,l,us=s.F,s.l,s.us
        dig=s.isdig(F)
        if s.sub>0 and dig and mod(l,4)==1 and all(it[0]!='H' and mod(it[1],4)==3 for it in us if it[0]=='b' or ge(it[2],1)):
            raise Stop("end")
        if dig:
            q,r=divmod_(l-1,4)
            if ge(l,2) and r>=1:
                s.chunk(Lin(0),None); s.l=Lin(1); s.us=[B(l-2)]+us; return
            if r==0 and not s.empty(us) and s.front(us) and ge(us[0][1],4):
                # j chunks at once: (4q+1, u) -> (4(q+j)+1, u - 4j), the list - (2^(q+j) - 2^q)
                j,r4=divmod_(us[0][1],4)
                bs,hasH=s.bits(F); s.addpow(bs,q); s.subpow(bs,q+j); s.F=s.fromBits(bs,hasH); s.sub+=1
                s.l=l+4*j; s.us=[B(r4)]+us[1:]; return
            if eq(l,1) or r==0:
                y=s.gpop(us)
                if isinstance(y,tuple):
                    s.chunk(q,None); s.l=y[1]+4*q; s.us=y[2]; return
                if ge(q,1):
                    s.chunk(q,-1); s.us=[B(3)]+([R(3,q-1)])+us; s.l=Lin(1); return
        # an irregular sub-round (or one that needs the open gap) through the pass machine
        s.front(F)
        p=F[0][1]; del F[0]
        if not (ge(p,1) and ge(l,1)): raise Stop("stuck")
        s.addhd(F,0,3)
        s.lb=F; s.F=None; s.ph="A"; s.k=p; s.us=[B(l-1)]+us; s.mode="ps"
    def chunk(s,e,minus):
        """the list number - 2^e (minus None) or - (2^e - 1)"""
        bs,hasH=s.bits(s.F)
        if minus: s.add1(bs)
        s.subpow(bs,e)
        s.F=s.fromBits(bs,hasH); s.sub+=1
    def step(s):
        if s.mode=="mom": s.moment(); return
        if s.wblock(): raise Stop("block")
        s.pstep()
    def canon(s):
        lb=s.lb; i=len(lb)
        while i>1:
            it=lb[i-1]
            if it[0]=='H' or (it[0]=='b' and mod(it[1],3)==2) or (it[0]=='r' and (not ge(it[2],1) or mod(it[1],3)==2)): i-=1
            else: break
        if i<len(lb):
            D=lb[i:-1]; assert lb[-1][0]=='H'
            D=[x for x in D if not (x[0]=='r' and not ge(x[2],1))]
            if D: s.newH('push',tuple(D))
            s.lb=lb[:i]+[('H',s.H)]
def digs(D):
    out=[]
    for it in D:
        if it[0]=='b': out.append((it[1].k-2)//3)
        else: out+= [(it[1].k-2)//3]*it[2].k
    return out
def Tl(D):
    t=0
    for x in reversed(digs(D)): t=2**x*(1+2*t)
    return t
def sigl(D): return sum(x+1 for x in digs(D))
LINF=("k","l")
def lins(s):
    """the Lin slots of a state: list of (path, Lin), and its shape"""
    out=[]; shape=[s.mode,s.ph]
    for f in LINF: out.append(((f,),getattr(s,f)))
    for f in ("lb","us","F"):
        lst=getattr(s,f)
        if lst is None: shape.append(None); continue
        sh=[]
        for i,it in enumerate(lst):
            sh.append(it[0] if it[0]!='H' else ('H',it[1]))
            for j in range(1,len(it)):
                if isinstance(it[j],Lin): out.append(((f,i,j),it[j]))
        shape.append(tuple(sh))
    shape.append(len(s.ops))
    return out,tuple(shape)
def setlin(s,path,v):
    if len(path)==1: setattr(s,path[0],v); return
    f,i,j=path; lst=getattr(s,f); it=list(lst[i]); it[j]=v; lst[i]=tuple(it)
def try_loop(s,maxsteps=80):
    """a loop that eats one entry of a run per turn: (state after the whole run) or None; may raise Need on count >= 1"""
    import sym_lin as lin
    base,shape=lins(s)
    runs=[p for p,v in base if len(p)==3 and p[2]==2 and not v.isconst()]
    for tgt in runs:
        r=fresh("r"); R_=Lin.var(r)
        t=s.copy(); setlin(t,tgt,1+R_); tb,_=lins(t)
        lin.CTX[:]=s.cons
        found=None
        for k in range(maxsteps):
            try: t.step()
            except (Need,Stop,Halt): break
            cur,sh=lins(t)
            if sh!=shape: continue
            d={}; ok=True
            for (p,v0),(p2,v1) in zip(tb,cur):
                dd=v1-v0
                if p==tgt:
                    if dd!=Lin(-1): ok=False; break
                    continue
                if not dd.isconst(): ok=False; break
                if dd.k: d[p]=dd.k
            if ok: found=(k,d); break
        if not found: continue
        k,d=found
        j=fresh("j"); J_=Lin.var(j)
        g=s.copy()
        for p,v0 in base:
            if p==tgt: setlin(g,p,1+R_)
            elif p in d: setlin(g,p,v0+d[p]*J_)
        want,_=lins(g)
        g2=g.copy(); lin.CTX[:]=s.cons
        try:
            for k2 in range(k+1): g2.step()
        except (Need,Stop,Halt): continue
        got,sh2=lins(g2)
        if sh2!=shape: continue
        good=True
        for (p,v0),(p2,v1) in zip(want,got):
            exp=(R_ if p==tgt else (v0.subst(j,J_+1) if p in d else v0))
            if v1!=exp: good=False; break
        if not good: continue
        c=dict(base)[tgt]
        out=s.copy()
        for p,v0 in base:
            if p==tgt: setlin(out,p,Lin(0))
            elif p in d: setlin(out,p,v0+d[p]*c)
        out.trace=s.trace+[("loop",tgt,c,d,k+1)]
        return out
    return None
def explore(s0, maxdepth=4000, maxleaves=200, hook=None):
    """all paths: list of (outcome, state, substitutions)"""
    work=[(s0,[],0)]; out=[]
    while work:
        s,path,d=work.pop()
        if d>maxdepth: out.append(("depth",s,path)); continue
        if len(out)>maxleaves: out.append(("leaves",s,path)); break
        s2=s.copy()
        import sym_lin as lin; lin.CTX[:]=s.cons
        try:
            s2.step()
            if hook: hook(s2)
            work.append((s2,path,d+1)); continue
        except Need as e:
            try: acc=try_loop(s)
            except Need as e2: acc=None; e=e2
            if acc is not None:
                work.append((acc,path,d+1)); continue
            for v,ex in e.cases:
                s3=s.copy(); s3.subst(v,ex); work.append((s3,path+[(v,ex)],d+1))
        except Stop as e:
            if e.why=="block":
                lin.CTX[:]=s2.cons
                try: s2.canon()
                except Need as e2:
                    for v,ex in e2.cases:
                        s3=s.copy(); s3.subst(v,ex); work.append((s3,path+[(v,ex)],d+1))
                    continue
            out.append((e.why,s2,path))
        except Halt: out.append(("halt",s2,path))
    return out
