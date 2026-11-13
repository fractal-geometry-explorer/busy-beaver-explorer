"""Every overflowing phase P(d, bs) with at most MMAX bits, run directly to the next P configuration.

Prints: M d bits(top first) R (= val + 2^(d+1) - 2^M) -> steps, the next d, M and value (or HALT).
usage: python3 overflows.py MACHINE STATE MMAX
"""
import sys
M=sys.argv[1]; S=sys.argv[2]; Mmax=int(sys.argv[3])
tr=M.split("_")
def run(d,bs,limit=10**7):
    left=[1,1]+sum([[b,1] for b in bs[::-1]],[])+[0,1]
    cells=left+[0,0,0]*d+[0,0,1]
    N=1<<12
    tape=bytearray(N); off=N//2-len(left)
    for i,c in enumerate(cells): tape[off+i]=c
    p=off+len(left); q=S; n=0; hi=off+len(cells)
    first=True
    while n<limit:
        x=tape[p]; t=tr["ABCDEF".index(q)][3*x:3*x+3]
        if t[2]=="-": return ("HALT",n)
        if q==S and x==0 and not first:
            r=p+1
            while r<=hi and tape[r]==0: r+=1
            if r<=hi and (r-p)%3==2 and all(tape[k]==0 for k in range(r+1,hi+1)):
                l0=0
                while tape[l0]==0: l0+=1
                s=bytes(tape[l0:p])
                if len(s)%2==0 and s[:2]==b"\1\1" and s[-2:]==b"\0\1" and all(s[k]==1 for k in range(3,len(s),2)):
                    return (n,(r-p-2)//3,[s[k] for k in range(2,len(s)-2,2)][::-1])
        first=False
        tape[p]=int(t[0]); p+=1 if t[1]=="R" else -1; q=t[2]; n+=1
        if p>hi: hi=p
        if p<2 or p>=N-2: return ("OUT",n)
    return ("LIMIT",n)
from itertools import product
for m in range(1,Mmax+1):
    for d in range(0,m):
        for bs in product([0,1],repeat=m):
            V=sum(b<<i for i,b in enumerate(bs))
            if V+(1<<(d+1))<(1<<m): continue
            R=V+(1<<(d+1))-(1<<m)
            res=run(d,list(bs))
            if res[0] in ("HALT","OUT","LIMIT"):
                print(m,d,"".join(map(str,bs[::-1])),"R=",format(R,"b"),res); continue
            n,d2,bs2=res
            V2=sum(b<<i for i,b in enumerate(bs2))
            print(m,d,"".join(map(str,bs[::-1])),"R=",format(R,"0%db"%m),"->",n,"d'=",d2,"M'=",len(bs2),"V'=",V2,"".join(map(str,bs2[::-1])))
