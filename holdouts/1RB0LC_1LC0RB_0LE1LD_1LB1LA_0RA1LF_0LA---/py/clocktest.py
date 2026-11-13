"""Test the clock hypothesis on the visits of the left end: within a phase, is the word after the visit with block
L0 + g*k equal to the word after 2^k applications of the base map (the tick from block L0)?

usage: python3 clocktest.py MACHINE STATE STEPS START_STEP G       (tmrun at /tmp/claude-0/bin/tmrun)
e.g.   python3 clocktest.py 1RB0LC_1LC0RB_0LE1LD_1LB1LA_0RA1LF_0LA--- B 1000000000 51738209 3
"""


import re
import subprocess
import sys


def table(m):
    T = {}
    for s, g in enumerate(m.split("_")):
        for y in (0, 1):
            x = g[3 * y:3 * y + 3]
            T[(s, y)] = None if x == "---" else (int(x[0]), 1 if x[1] == "R" else -1, "ABCDEF".index(x[2]))
    return T

def cells_of(s):
    s=re.sub(r"[A-F]>","",s); c=[]
    for x in s.split():
        v,_,n=x.partition('^'); c+=[int(v)]*int(n or 1)
    return c
def tick1(T,st,L0,R,maxt=10**8):
    tp=bytearray([0]*4+[0]+[1]*L0+[0]+R+[0]*50); pos=4; lo=4; s=st; t=0
    while t<maxt:
        tr=T[(s,tp[pos])]
        if tr is None: return None
        w,d,q=tr; tp[pos]=w; pos+=d; s=q; t+=1
        if pos>=len(tp)-5: tp+=bytearray(50)
        if pos<lo:
            lo=pos
            if lo<1: tp=bytearray(50)+tp; pos+=50; lo+=50
        if s==st and pos==lo and tp[pos]==0: break
    c=list(tp[lo:]); i=1
    while i<len(c) and c[i]==1: i+=1
    Rn=c[i+1:]
    while Rn and Rn[-1]==0: Rn.pop()
    return i-1,Rn,t
M,st,N,a,g=sys.argv[1],sys.argv[2],sys.argv[3],int(sys.argv[4]),int(sys.argv[5])
T=table(M); S="ABCDEF".index(st)
out=subprocess.run(["/tmp/claude-0/bin/tmrun",M,N,"at",st,"L","100000"],capture_output=True,text=True).stdout.split("\n")
vis=[]
for l in out:
    if l and l[0].isdigit():
        t,tape=l.split(None,1)
        if int(t)>=a and tape.startswith(st+">0"):
            c=cells_of(tape); i=1
            while i<len(c) and c[i]==1: i+=1
            R=c[i+1:]
            while R and R[-1]==0: R.pop()
            vis.append((int(t),i-1,R))
t0,L0,R0=vis[0]; print("start",t0,L0)
cur=R0; L=L0
for (t2,L2,R2) in vis[1:12]:
    print("visit",t2,L2, end=": ")
    if L2!=L+g: print("not +g"); break
    n=0
    while n<5000:
        r=tick1(T,S,L0,cur)
        if r is None: print("halt?"); break
        if r[0]!=L0+g: print("base map gave L",r[0],"after",n); cur=None; break
        cur=r[1]; n+=1
        if cur==R2: print("matched after",n,"base maps"); break
    if cur!=R2: print("no match"); break
    L=L2
