"""Watch a nested run: start from the sweep configuration `1^r [digits] 0 1 B>0` (machine 1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD---,
or the other machine of the pair) and print every inner right end in phase X (`0 1 1 E>1 0`) or Y (`0 1 1 1 0 F>0 1 0`)
with the inner digits and the passed region right of it (as the m of its words 0 0 (1 0)^m: 2 is a passed digit 1,
1 the end word `0 0 1 0`), and every time the head reaches a new cell on the right in the sweep state (P or Q).
usage: python3 nested_view.py MACHINE R DIGITS [MAXSTEPS [MAXSTEPS_AFTER]]
e.g.   python3 nested_view.py 1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD--- 12 1,1,1,1,1,1,1,1
Phases are detected for 1RB0LC_1RC1RE_1RD0RA_0LE0RF_1RA0LD_1LD--- state names only."""
import sys
def parse(m):
    T={}
    for s,g in enumerate(m.split('_')):
        for b in range(2):
            x=g[3*b:3*b+3]
            T[(s,b)]=None if x[2]=='-' else (int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
    return T
import sys
M=sys.argv[1]; r=int(sys.argv[2]); ds=list(map(int,sys.argv[3].split(','))) if sys.argv[3] else []
maxn=int(sys.argv[4]) if len(sys.argv)>4 else 10**8
T=parse(M)
m1=M.startswith("1RB0LC")
startst=1 if m1 else 2
t={}
pos=0
for i in range(r): t[pos]=1; pos+=1
for d in ds:
    t[pos]=0; pos+=1
    for i in range(3*d+2): t[pos]=1; pos+=1
t[pos]=0; pos+=1; t[pos]=1; pos+=1
p=pos; s=startst; hi=p; lo=0
def digits(lo,end):
    # blocks of ones from lo to end (exclusive); return 'r<len>' then digits
    out=[];i=lo
    while t.get(i,0)==0 and i<end: i+=1
    first=True
    while i<end:
        j=i
        while j<end and t.get(j,0)==1: j+=1
        L=j-i
        if first: out.append("r%d"%L); first=False
        else: out.append(str((L-2)//3) if (L-2)%3==0 else "?%d"%L)
        # count zeros
        k=j
        while k<end and t.get(k,0)==0: k+=1
        if k-j>1 and k<end: out.append("z%d"%(k-j))
        i=k
    return " ".join(out)
import re
def right(p,n=14):
    x="".join(str(t.get(i,0)) for i in range(p,hi+3)).rstrip("0")
    toks=[]
    while True:
        m=re.match(r"00((?:10)+)",x)
        if not m: break
        k=len(m.group(1))//2
        toks.append(str(k)); x=x[m.end():]
        if x=="" : break
    return ",".join(toks)+(" REST:"+x if x else "")

lastmv=0
n=0
E,F=4 if m1 else None, None
# state letters for machine1: D=3,E=4,F=5 ; X: E reads 1 with left 011
while n<maxn:
    b=t.get(p,0); x=T[(s,b)]
    if x is None: print("HALT",n); break
    if m1:
        if lastmv==1 and s==4 and b==1 and t.get(p-1)==1 and t.get(p-2)==1 and t.get(p-3,0)==0 and t.get(p+1,0)==0:
            print(n,"X",digits(lo,p-2),"|",right(p+2))
        if lastmv==1 and s==5 and b==0 and t.get(p-1,0)==0 and t.get(p-2)==1 and t.get(p-3)==1 and t.get(p-4)==1 and t.get(p-5,0)==0 and t.get(p+1,0)==1:
            print(n,"Y",digits(lo,p-4),"|",right(p+3))
    w,mv,ns=x; t[p]=w; p+=mv; s=ns; n+=1; lastmv=mv
    lo=min(lo,p)
    if p>hi:
        hi=p
        if s==startst:
            print(n,"P" if t.get(p-2,0)==0 else "Q?",digits(lo,p)); 
            if n>int(sys.argv[5] if len(sys.argv)>5 else 10): break
