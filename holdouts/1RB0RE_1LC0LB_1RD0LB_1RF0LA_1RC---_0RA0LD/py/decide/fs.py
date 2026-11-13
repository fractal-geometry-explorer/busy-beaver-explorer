"""Fast symbolic simulator for 1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD.
Tape: left stack (top = cell left of head), right stack (top = cell under head). Elements: 0/1, BL (blank end),
or Rep objects (word in tape order, count a Lin over variables). Shift rules found by one-copy simulation (cached)."""
NV=8   # variables x(0) U slot, y1..y6 (1..6) X slots, t(7) epoch variable
class Lin(tuple):
    def __new__(cls,*a): return tuple.__new__(cls,a)
    def __reduce__(s): return (Lin,tuple(s))
    def __add__(s,o):
        if isinstance(o,int): return Lin(*s[:-1],s[-1]+o)
        return Lin(*[a+b for a,b in zip(s,o)])
    def __sub__(s,o):
        if isinstance(o,int): return Lin(*s[:-1],s[-1]-o)
        return Lin(*[a-b for a,b in zip(s,o)])
    def scale(s,k): return Lin(*[a*k for a in s])
    def ge(s,n): return all(a>=0 for a in s[:-1]) and s[-1]>=n
    def iszero(s): return all(a==0 for a in s)
    def isconst(s): return all(a==0 for a in s[:-1])
    def val(s,env): return s[-1]+sum(a*e for a,e in zip(s[:-1],env))
    def __repr__(s):
        names='xabcdefgt'[:0]+'xyzpqrst'; parts=[(('%d*'%a if a!=1 else '')+names[i]) for i,a in enumerate(s[:-1]) if a]
        if s[-1] or not parts: parts.append(str(s[-1]))
        return '+'.join(parts).replace('+-','-')
def C(k): return Lin(*([0]*NV+[k]))
def V(i,k=0):
    l=[0]*NV+[k]; l[i]=1; return Lin(*l)
class Rep:
    __slots__=('w','n')
    def __init__(s,w,n): s.w=tuple(w); s.n=n
    def __repr__(s): return '(%s)^%r'%(''.join(map(str,s.w)),s.n)
    def __eq__(s,o): return isinstance(o,Rep) and s.w==o.w and s.n==o.n
    def __hash__(s): return hash((s.w,s.n))
BL='B'
CTX='X'
class TouchContext(Exception): pass
UNROLL_MIN=[10**9]
def _note(t):
    if t.n[0]>0 and t.n[-1]<UNROLL_MIN[0]: UNROLL_MIN[0]=t.n[-1]
class NeedSplit(Exception): pass
class Halted(Exception): pass
M="1RB0RE_1LC0LB_1RD0LB_1RF0LA_1RC---_0RA0LD"
TT={}
for s,g in enumerate(M.split('_')):
    for y in range(2):
        t=g[3*y:3*y+3]
        TT[(s,y)]=None if t[2]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
MAXC=48; MAXCYC=600
_cache={}
def one_right(q,u,w):
    key=('r',q,u,w)
    if key in _cache: return _cache[key]
    cells=list(u)+list(w); pos=len(u); st=q; res=None; N=len(cells)
    for n in range(1,MAXCYC+1):
        tr=TT[(st,cells[pos])]
        if tr is None: break
        cells[pos]=tr[0]; pos+=tr[1]; st=tr[2]
        if pos==N:
            if st==q and tuple(cells[len(w):])==u: res=(tuple(cells[:len(w)]),n)
            break
        if pos<0: break
    _cache[key]=res; return res
def one_left(q,u,w):
    key=('l',q,u,w)
    if key in _cache: return _cache[key]
    cells=list(w)+list(u); pos=len(w); st=q; res=None; N=len(cells)
    for n in range(1,MAXCYC+1):
        tr=TT[(st,cells[pos])]
        if tr is None: break
        cells[pos]=tr[0]; pos+=tr[1]; st=tr[2]
        if pos==0 and st==q and tuple(cells[:len(u)])==u and n>0:
            # head at 0 reading u[0]; but must also be that it never needs... accept
            res=(tuple(cells[len(u):]),n); break
        if pos<0 or pos>=N: break
    _cache[key]=res; return res
class Cfg:
    def __init__(s,left,state,right,steps=None):
        s.L=left; s.st=state; s.R=right; s.steps=steps if steps is not None else C(0); s.conc=0
    def copy(s):
        c=Cfg(list(s.L),s.st,list(s.R),s.steps); c.conc=s.conc; return c
def _top_lit_left(L,k):
    # last k elements all literal?
    if len(L)<k: return None
    seg=L[len(L)-k:]
    for z in seg:
        if z is BL or z is CTX or isinstance(z,Rep): return None
    return tuple(seg)
def _top_lit_right(R,k):
    if len(R)<k: return None
    seg=R[len(R)-k:]
    for z in seg:
        if z is BL or z is CTX or isinstance(z,Rep): return None
    return tuple(reversed(seg))
def try_cross(c):
    R=c.R; L=c.L
    top=R[-1]
    if isinstance(top,Rep) and not top.n.iszero():
        for lu in range(0,MAXC+1):
            u=_top_lit_left(L,lu) if lu else ()
            if u is None: break
            r=one_right(c.st,u,top.w)
            if r:
                v,s=r; R.pop()
                if lu: del L[len(L)-lu:]
                L.append(Rep(v,top.n)); L.extend(u)
                c.steps=c.steps+top.n.scale(s); return ('r',lu,top.w,v,s,top.n,c.st,u)
    ltop=L[-1]
    if isinstance(ltop,Rep) and not ltop.n.iszero():
        for lu in range(1,MAXC+1):
            u=_top_lit_right(R,lu)
            if u is None: break
            r=one_left(c.st,u,ltop.w)
            if r:
                v,s=r; L.pop()
                del R[len(R)-lu:]
                R.append(Rep(v,ltop.n)); R.extend(reversed(u))
                c.steps=c.steps+ltop.n.scale(s); return ('l',lu,ltop.w,v,s,ltop.n,c.st,u)
    return None
def try_rotate(c):
    """symtm-style re-bracketing next to the head; returns True if done (and a cross then applies)"""
    L=c.L; R=c.R
    for j in range(1,MAXC+1):
        if len(L)>j and isinstance(L[-1-j],Rep):
            x=_top_lit_left(L,j)
            if x is None: break
            r=L[-1-j]
            if j<len(r.w) and r.w[:j]==x and not r.n.iszero():
                w2=r.w[j:]+r.w[:j]
                save=L[-1-j:]
                L[-1-j:]=list(x)+[Rep(w2,r.n)]
                xx=try_cross(c)
                if xx: return xx
                L[-1-j:]=save
    for j in range(1,MAXC+1):
        if len(R)>j and isinstance(R[-1-j],Rep):
            x=_top_lit_right(R,j)
            if x is None: break
            r=R[-1-j]
            if j<len(r.w) and r.w[len(r.w)-j:]==x and not r.n.iszero():
                w2=x+r.w[:len(r.w)-j]
                save=R[-1-j:]
                R[-1-j:]=list(reversed(x))+[Rep(w2,r.n)]
                xx=try_cross(c)
                if xx: return xx
                R[-1-j:]=save
    return False
def unroll_right(R):
    while True:
        t=R[-1]
        if t is BL: R.append(0); return
        if t is CTX: raise TouchContext('R')
        if isinstance(t,Rep):
            if t.n.iszero(): R.pop(); continue
            if not t.n.ge(1): raise NeedSplit(t)
            _note(t)
            R.pop()
            if not (t.n-1).iszero(): R.append(Rep(t.w,t.n-1))
            R.extend(reversed(t.w)); continue
        return
def unroll_left(L):
    while True:
        t=L[-1]
        if t is BL: L.append(0); return
        if t is CTX: raise TouchContext('L')
        if isinstance(t,Rep):
            if t.n.iszero(): L.pop(); continue
            if not t.n.ge(1): raise NeedSplit(t)
            _note(t)
            L.pop()
            if not (t.n-1).iszero(): L.append(Rep(t.w,t.n-1))
            L.extend(t.w); continue
        return
def step(c):
    R=c.R; L=c.L
    unroll_right(R)
    y=R[-1]; tr=TT[(c.st,y)]
    if tr is None: raise Halted((c.st,y))
    w,d,s=tr
    R.pop()
    if d>0: L.append(w)
    else:
        unroll_left(L); R.append(w); R.append(L.pop())
    c.st=s; c.steps=c.steps+1; c.conc+=1
def move(c):
    """one move: a cross (with rotation if needed) or a single step. returns cross info or None"""
    R=c.R; L=c.L
    if isinstance(R[-1],Rep) or isinstance(L[-1],Rep):
        x=try_cross(c)
        if x: return x
    # rotation only near reps: check quickly whether a Rep is within MAXC on either side
    near=False
    for k in range(1,min(MAXC,len(L)-1)+1):
        if isinstance(L[-1-k],Rep): near=True;break
        if L[-1-k] is BL or L[-1-k] is CTX: break
    if not near:
        for k in range(1,min(MAXC,len(R)-1)+1):
            if isinstance(R[-1-k],Rep): near=True;break
            if R[-1-k] is BL or R[-1-k] is CTX: break
    if near:
        xx=try_rotate(c)
        if xx: return xx
    step(c); return None

def try_regroup(c):
    """(w)^n at the head with even variable coefficients -> (ww)^(n//2) (+ one copy); keep if a cross then applies"""
    R=c.R; L=c.L
    t=R[-1]
    if isinstance(t,Rep) and all(a%2==0 for a in t.n[:-1]) and t.n[-1]>=0 and len(t.w)<=40:
        k=Lin(*[a//2 for a in t.n[:-1]], t.n[-1]//2); odd=t.n[-1]%2
        save=list(R)
        R.pop()
        if odd: R.extend(reversed(t.w))
        R.append(Rep(t.w+t.w,k))
        x=try_cross(c)
        if x: return x
        R[:]=save
    t=L[-1]
    if isinstance(t,Rep) and all(a%2==0 for a in t.n[:-1]) and t.n[-1]>=0 and len(t.w)<=40:
        k=Lin(*[a//2 for a in t.n[:-1]], t.n[-1]//2); odd=t.n[-1]%2
        save=list(L)
        L.pop()
        if odd: L.extend(t.w)
        L.append(Rep(t.w+t.w,k))
        x=try_cross(c)
        if x: return x
        L[:]=save
    return None
def move2(c):
    R=c.R; L=c.L
    adj=isinstance(R[-1],Rep) or isinstance(L[-1],Rep)
    if adj:
        x=try_cross(c)
        if x: return x
    near=False
    for k in range(1,min(MAXC,len(L)-1)+1):
        if isinstance(L[-1-k],Rep): near=True;break
        if L[-1-k] is BL or L[-1-k] is CTX: break
    if not near:
        for k in range(1,min(MAXC,len(R)-1)+1):
            if isinstance(R[-1-k],Rep): near=True;break
            if R[-1-k] is BL or R[-1-k] is CTX: break
    if near:
        xx=try_rotate(c)
        if xx: return xx
    if adj:
        xx=try_regroup(c)
        if xx: return xx
    step(c); return None

# ---------------- faster move with incremental literal-run lengths
CAP=600
def _scan(S):
    n=len(S); k=0
    while k<CAP and k<n:
        z=S[n-1-k]
        if z is BL or z is CTX or isinstance(z,Rep): return k
        k+=1
    return CAP if k>=CAP else k
def move3(c):
    """same moves as move2; c.dl/c.dr = number of literal cells on top of L/R (CAP = 'far')"""
    L=c.L; R=c.R
    dl=getattr(c,'dl',None)
    if dl is None or dl>=CAP: dl=c.dl=_scan(L)
    dr=getattr(c,'dr',None)
    if dr is None or dr>=CAP: dr=c.dr=_scan(R)
    if dl==0 or dr==0:
        adj=isinstance(R[-1],Rep) or isinstance(L[-1],Rep)
    else: adj=False
    if adj:
        x=try_cross(c)
        if x: c.dl=c.dr=None; return x
    nearL = 1<=dl<=MAXC and len(L)>dl and isinstance(L[-1-dl],Rep)
    nearR = 1<=dr<=MAXC and len(R)>dr and isinstance(R[-1-dr],Rep)
    if nearL or nearR:
        xx=try_rotate(c)
        if xx: c.dl=c.dr=None; return xx
    if adj:
        xx=try_regroup(c)
        if xx: c.dl=c.dr=None; return xx
    # step with incremental bookkeeping
    top=R[-1]
    if not isinstance(top,int):
        unroll_right(R); c.dr=dr=_scan(R)
    y=R[-1]; tr=TT[(c.st,y)]
    if tr is None: raise Halted((c.st,y))
    w,d,s=tr
    R.pop()
    if d>0:
        L.append(w); c.dl=dl+1; c.dr=dr-1
    else:
        if not isinstance(L[-1],int):
            unroll_left(L); dl=_scan(L)
        R.append(w); R.append(L.pop()); c.dl=dl-1; c.dr=dr+1
    c.st=s; c.steps=c.steps+1; c.conc+=1
    return None
