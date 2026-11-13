"""Cross-check of busycoq PR60's map aStep against our Lean map F (lean/Map.lean): usage pr60_prefix.py N."""
import re,sys
def aStep(a,b):
    if b==a+3: return None
    if a+3<b: return (2*a+6,b-a-3)
    if b==1: return (6,a+7) if a%4==2 else (22,a-2)
    if b==3: return (6,a+13) if a%4==2 else (a+8,2)
    if b%2==1:
        if b==a+1: return (6,a+b+2)
        if (a-b+5)%4==2: return (a-b+11,2*b-4)
        return (a-b+19,2*b-8)
    if (a-b)%4==2: return (6,a+b+7)
    return (22,a+b-2)
# our F (transcribed from c/orbit.c, which transcribes lean/Map.lean)
def F(n):
    ty,A,B=n
    if ty==0: return (1,0,A+6)
    if ty==1:
        a,m=A,B
        if 2*a+9<=m: return (1,2*a+6,m-(2*a+9))
        if m==0: return None
        if m==1: return (0,2*a+7,0) if a%2==0 else (2,a//2+1,1)
        if m==2: return (3,a//2+1,0) if a%2==0 else (0,2*a+9,0)
        z,r=(m-3)//2,(m-3)%2; pp=a+2-z
        if pp==0: return (0,4*z+1 if r==0 else 4*z+7,0)
        if pp%2==1:
            q=pp//2
            return (1,2*q+3,4*z+2) if r==0 else (3,q,2*z+2)
        q=pp//2-1
        return (2,q,2*z+3) if r==0 else (0,4*q+4*z+11,0)
    if ty==2:
        u,c=A,B
        if c>=4: return (1,2*u+8,2*c-8)
        if c==0: return (0,4*u+11,0)
        if c==1: return (2,0,2*u+5)
        if c==2: return (1,3,4*u+10)
        return (0,4*u+13,0)
    return (2,0,2*A+B+5)
# 1. prefix agreement: every state of their orbit is a p-node of ours, in order
N=int(sys.argv[1])
s=(6,1); n=(1,0,1)  # their start (6,1) <-> our p 0 1 ; our orbit from s 7: check p 0 1 -> s 7
assert F((1,0,1))==(0,7,0)
k=0; ours=0
for i in range(N):
    s=aStep(*s); assert s
    want=(1,(s[0]-6)//2,s[1]); assert s[0]%2==0
    while True:
        n=F(n); ours+=1; assert n is not None
        if n==want: break
        assert ours<10**9
print("prefix: their",N,"steps = our",ours,"nodes; all",N,"states matched in order; at",s)
