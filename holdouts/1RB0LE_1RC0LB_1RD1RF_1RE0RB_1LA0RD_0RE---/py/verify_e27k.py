import sys
from mac15b import run_fast, CACHE
from ev import parse
A={}
for line in open(sys.argv[1]):
    p=line.split()
    if len(p)==2 and p[0].isdigit():
        c=parse(p[1])
        while len(c)>2 and c[0]==0 and c[1]=='0': c=c[2:]
        A[int(p[0])]=c
lo,hi=min(A),max(A)
n=bad=0
def log(c,steps,rec):
    global n,bad
    if steps in A:
        n+=1
        if A[steps]!=c: bad+=1
    elif lo<steps<hi: bad+=1; print('nostep',steps)
c,steps,rec=run_fast([10,'S',14,'S',6,'S',12],3513,0,10**9,maxsteps=hi,log=log)
print('checked',n,'bad',bad,'rules',len(CACHE),'steps',steps)
