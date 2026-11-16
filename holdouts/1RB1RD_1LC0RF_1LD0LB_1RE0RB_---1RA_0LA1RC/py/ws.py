"""Run-word stack simulator with shift rules carrying a glider, and proved linear cycle jumps.  Exact (big ints).
Each side of the head is a stack of entries [len, mult]: mult words (1^len 0) going away from the head; empty = blank.
The head faces d (+1 right, -1 left) and reads the nearest cell of the side it faces."""
import sys
from lin import *
def parse(M):
    T={}
    for i,row in enumerate(M.split('_')):
        for b in (0,1):
            t=row[3*b:3*b+3]
            T[(i,b)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    return T
NMAX=14; BIG=40; TMAX=4000
class ProofFail(Exception): pass
def push(S,b):
    if b==0:
        if not S: return
        if S[-1][0]==0: S[-1][1]+=1
        else: S.append([0,1])
    else: pushrun(S,1)
def pushrun(S,n):
    if not S: S.append([n,1]); return
    t=S[-1]
    if t[1]==1: t[0]=t[0]+n
    else:
        t[1]=t[1]-1; S.append([t[0]+n,1]); t=S[-1]
    if len(S)>=2 and same(S[-2][0],t[0]):
        S[-2][1]=S[-2][1]+t[1]; S.pop()
def pushword(S,l,k):
    if not S and same(l,0): return
    if S and same(S[-1][0],l): S[-1][1]=S[-1][1]+k
    else: S.append([l,k])
def pop(S):
    if not S: return 0
    t=S[-1]
    if t[0]==0:
        if t[1]==1: S.pop()
        else: t[1]=t[1]-1
        return 0
    if t[1]==1: t[0]=t[0]-1
    else:
        t[1]=t[1]-1; S.append([t[0]-1,1])
    return 1
def peel(S):
    """make the top entry a single word"""
    t=S[-1]
    if not t[1]==1:
        t[1]=t[1]-1; S.append([t[0],1])
def pushbits_power(S, v, k):
    """push the bit list v (in push order), k times (k >= 1, may be symbolic)"""
    u=v[::-1]
    a=[]; cur=0
    for b in u:
        if b: cur+=1
        else: a.append(cur); cur=0
    a.append(cur); m=len(a)-1
    if m==0:
        if a[0]: pushrun(S,a[0]*k)
        return
    if a[m]: pushrun(S,a[m])
    unit=[a[m]+a[0]]+a[1:m]
    km=k-1
    if not same(km,0):
        if m==1: pushword(S,unit[0],km)
        elif len(set(unit))==1: pushword(S,unit[0],km*m)
        else:
            if is_sym(km): raise ProofFail("multi-run unit with symbolic count")
            for _ in range(km):
                for l in reversed(unit): pushword(S,l,1)
    for l in reversed(a[:m]): pushword(S,l,1)
class Sim:
    def __init__(s, M):
        s.T=parse(M); s.M=M
        s.L=[];s.R=[];s.st=0;s.d=1;s.steps=0;s.halted=False
        s.rules={}; s.nmacro=0; s.big=False; s.stats={'single':0,'word':0,'ones':0}
    def copy_state(s): return ([e[:] for e in s.L],[e[:] for e in s.R],s.st,s.d,s.steps)
    def set_state(s,x): s.L=[e[:] for e in x[0]]; s.R=[e[:] for e in x[1]]; s.st,s.d,s.steps=x[2],x[3],x[4]
    def find(s, st, d, G, w, la):
        key=(st,d,tuple(G),tuple(w),tuple(la))
        if key in s.rules: return s.rules[key]
        T=s.T; cells=G+w+la; n=len(cells); pos=0; q=st; res=None; maxpos=0; lw=len(w); lg=len(G); tail=cells[lg+lw:]
        for t in range(1,TMAX):
            tr=T[(q,cells[pos])]
            if tr is None: break
            cells[pos]=tr[0]; pos+= 1 if tr[1]==d else -1; q=tr[2]
            if pos<0 or pos>=n: break
            if pos>maxpos: maxpos=pos
            if pos==lw and q==st and cells[lw:lw+lg]==G and cells[lw+lg:]==tail:
                res=(cells[:lw], t, max(0,maxpos-(lg+lw-1))); break
        s.rules[key]=res
        return res
    def step(s):
        """one macro step; False on halt"""
        d=s.d; Sa,Sb=(s.R,s.L) if d==1 else (s.L,s.R); st=s.st
        s.nmacro+=1; s.big=False
        if Sa:
            top=Sa[-1]
            n=top[0]
            if n>=BIG:
                key=(st,d,'ones')
                r=s.rules.get(key,0)
                if r==0:
                    r=None
                    for g in (1,2,3):
                        for P in (1,2,3,4,6,12):
                            x=s.find(st,d,[1]*g,[1]*P,[1]*P)
                            if x: r=(g,P)+x; break
                        if r: break
                    s.rules[key]=r
                if r:
                    g,P,w2,t,a=r
                    k=(n-g-a)//P
                    if k>=1:
                        peel(Sa); top=Sa[-1]; top[0]=top[0]-k*P
                        pushbits_power(Sb,w2,k); s.steps=s.steps+k*t; s.stats['ones']+=1; s.big=(k>=16)
                        return True
            elif len(Sa)>=2 and Sa[-2][1]>=3 and top[1]==1 and not is_sym(Sa[-2][0]) and Sa[-2][0]<=NMAX:
                n2=Sa[-2][0]
                G=[1]*n+[0]; w=[1]*n2+[0]
                x=s.find(st,d,G,w,w)
                if x:
                    w2,t,a=x
                    k=Sa[-2][1]-(1 if a else 0)
                    Sa.pop()
                    if a: Sa[-1][1]=1
                    else: Sa.pop()
                    Sa.append([n,1])   # the glider word stays in front (distinct entry even if same length)
                    if len(Sa)>=2 and same(Sa[-2][0],n): Sa[-2][1]=Sa[-2][1]+1; Sa.pop()
                    pushbits_power(Sb,w2,k); s.steps=s.steps+k*t; s.stats['word']+=1; s.big=(k>=16)
                    return True
            elif top[1]>=4 and n<=NMAX:
                G=[1]*n+[0]
                x=s.find(st,d,G,G,G)
                if x:
                    w2,t,a=x
                    k=top[1]-1-(1 if a else 0)
                    top[1]=top[1]-k
                    pushbits_power(Sb,w2,k); s.steps=s.steps+k*t; s.stats['word']+=1; s.big=(k>=16)
                    return True
        b=pop(Sa)
        tr=s.T[(st,b)]
        s.stats['single']+=1
        if tr is None:
            push(Sa,b); s.halted=True; return False
        w,nd,ns=tr
        s.steps=s.steps+1; s.st=ns
        if nd==d: push(Sb,w)
        else: push(Sa,w); s.d=nd
        return True
def fmt(S):
    return ' '.join(str(l) if same(m,1) else f"{l}^{m}" for l,m in S)
def show(s):
    return f"{fmt(s.L)} {'<' if s.d==-1 else ''}{'ABCDEF'[s.st]}{'>' if s.d==1 else ''} {fmt(reversed(s.R))}"
def tape_bits(s):
    """the tape as a string and the head index (for testing)"""
    def side(S):
        out=[]
        for l,m in reversed(S): out.append(('1'*l+'0')*m)
        return ''.join(out)
    l=side(s.L)[::-1]; r=side(s.R)
    return l, r
