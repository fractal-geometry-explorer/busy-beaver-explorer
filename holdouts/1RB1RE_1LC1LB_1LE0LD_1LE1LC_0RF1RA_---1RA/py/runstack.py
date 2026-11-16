"""Run-stack simulator for 1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA (exact, big integers).

usage: python3 runstack.py STEPS [bulk]     prints the run list at every visit of the left end (B on the blank cell
left of the tape) up to STEPS steps; with `bulk` the proved `sweep` rule is applied k times at once.

Tape on each side of the head = stack of [len, mult]: mult words (1^len 0) going away from the head. Empty = blank.
The head faces `d` (+1 right / -1 left) and reads the nearest cell of that side."""
import sys
M="1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA"
A,B,C,D,E,F=range(6)
def parse(M):
    T={}
    for i,row in enumerate(M.split('_')):
        for b in (0,1):
            t=row[3*b:3*b+3]
            T[(i,b)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
    return T
T=parse(M)
def push(S,b):
    if b==0:
        if not S: return
        if S[-1][0]==0: S[-1][1]+=1
        else: S.append([0,1])
    else:
        if not S: S.append([1,1]); return
        t=S[-1]
        if t[1]==1: t[0]+=1
        else:
            t[1]-=1; S.append([t[0]+1,1]); t=S[-1]
        if len(S)>=2 and S[-2][0]==t[0]:
            S[-2][1]+=t[1]; S.pop()
def pushrun(S,n):   # push n ones (n>=1)
    if not S: S.append([n,1]); return
    t=S[-1]
    if t[1]==1: t[0]+=n
    else:
        t[1]-=1; S.append([t[0]+n,1]); t=S[-1]
    if len(S)>=2 and S[-2][0]==t[0]:
        S[-2][1]+=t[1]; S.pop()
def pushword(S,l,k):  # push k words (1^l 0), k>=1
    if not S and l==0: return
    if S and S[-1][0]==l: S[-1][1]+=k
    else: S.append([l,k])
def pop(S):
    if not S: return 0
    t=S[-1]
    if t[0]==0:
        t[1]-=1
        if t[1]==0: S.pop()
        return 0
    if t[1]==1: t[0]-=1
    else:
        t[1]-=1; S.append([t[0]-1,1])
    return 1
def pushword0(S):
    if S and S[-1][0]==0: S[-1][1]+=1
    else: S.append([0,1])
def poprun(S):
    t=S[-1]; n=t[0]
    if t[1]==1: S.pop()
    else: t[1]-=1
    pushword0(S)      # the 0 that ended the word stays
    return n
class Sim:
    def __init__(s):
        s.L=[];s.R=[];s.st=A;s.d=1;s.steps=0;s.halted=False;s.nsingle=0
    def canon(s,S):
        while S and S[0][0]==0: S.pop(0)
    def step(s):
        """one macro step; returns False on halt"""
        L,R,st,d=s.L,s.R,s.st,s.d
        if d==1 and R and R[-1][0]>=1 and st in (A,E):
            # only blank-terminated care: poprun leaves [0,1]; if that was the last word, tape beyond is blank
            last=(len(R)==1 and R[-1][1]==1)
            n=poprun(R)
            if last: R.clear()
            pushrun(L,n); s.steps+=n
            if n&1: s.st=E if st==A else A
            return True
        if d==-1 and L and L[-1][0]>=1 and st in (B,C,D):
            last=(len(L)==1 and L[-1][1]==1)
            n=poprun(L)
            if last: L.clear()
            s.steps+=n
            if st==B: pushrun(R,n); return True
            if st==C:
                if n%2==0: pushword(R,1,n//2)
                else:
                    if n>1: pushword(R,1,n//2)
                    pushword0(R); s.st=D
            else:
                push(R,1)
                if n%2==0:
                    if n>2: pushword(R,1,n//2-1)
                    pushword0(R)
                else:
                    if n>1: pushword(R,1,n//2)
                    s.st=C
            return True
        S=R if d==1 else L
        b=pop(S)
        t=T[(st,b)]
        s.nsingle+=1
        if t is None:
            push(S,b); s.halted=True; return False
        w,nd,ns=t
        s.steps+=1; s.st=ns
        if nd==d: push(L if d==1 else R, w)
        else: push(S,w); s.d=nd
        return True
    def at_visit(s):
        return s.st==B and s.d==-1 and not s.L
    def sweep(s):
        """bulk sweeps at a visit; returns number applied"""
        R=s.R
        if len(R)>=3 and R[-1][1]==1 and R[-2]==[4,1] and R[-3][0]==1 and R[-3][1]>=2 and R[-1][0]%2==0 and R[-1][0]>=2:
            n=R[-3][1]; k=n//2; X=R[-1][0]
            s.steps+=k*(2*X+32)+6*k*(k-1)
            R[-1][0]=X+6*k
            if n-2*k: R[-3][1]=n-2*k
            else: R.pop(-3)
            return k
        return 0
def fmt(R):
    return ' '.join(str(l) if m==1 else f"{l}^{m}" for l,m in reversed(R))
if __name__=="__main__":
    N=int(float(sys.argv[1])); bulk=len(sys.argv)>2
    s=Sim()
    while s.steps<N:
        if s.at_visit():
            print(s.steps,fmt(s.R))
            if bulk: s.sweep()
        if not s.step(): print("HALT",s.steps+1); break
