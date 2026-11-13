"""Compare the run-window closure of rlectl.py with the abstract configurations the real run visits, and print the
first step of the abstract path to a halt that the real run does not make.
usage: python3 holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/py/realabs.py K,C1,C0 STEPS   (e.g. 4,5,3 3e6)"""
# abstract configurations (K,C1,C0) visited by the real run in N steps; then the first config on the abstract halting path that is not real
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rlectl
from rlectl import Dom, table, search, fmtst
M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---"
K,C1,C0=map(int,sys.argv[1].split(',')); N=int(float(sys.argv[2]))
T=table(M); d=Dom(K,C1,C0)
def absside(cells):
    # cells: list nearest first (finite; blank beyond)
    st=d.blank
    for x in reversed(cells): st=d.push(x,st)
    return st
tape={};p=0;s=0;lo=hi=0
real=set()
tapeL=[];tapeR=[]  # stacks: left cells (nearest last), right cells incl head (nearest last)
# incremental abstraction is hard with truncation; recompute from K-run neighbourhood
import itertools
arr=bytearray(1<<20);off=1<<19;p=off;lo=hi=p
def side(p,dirn):
    # collect cells outward until K+1 runs or blank end
    cells=[];q=p;runs=0;last=None
    while lo-1<=q<=hi+1 and runs<=K+1:
        c=arr[q]; cells.append(c)
        if c!=last: runs+=1; last=c
        q+=dirn
    if q<lo or q>hi:  # reached the blank
        return absside(cells)
    st=absside(cells[:-1]) if True else None
    # not closed: mark by pushing onto an open state
    # build: take runs list
    rl=[]
    for c in cells:
        if rl and rl[-1][0]==c: rl[-1][1]+=1
        else: rl.append([c,1])
    rl=rl[:K]
    st=((),False)
    out=[]
    for sym,n in rl:
        cl=1
        for _ in range(n-1): cl=d.inc(sym,cl)
        out.append((sym,cl))
    return (tuple(out),False)
for k in range(N):
    real.add((s,side(p-1,-1),side(p,1)))
    tr=T[(s,arr[p])]
    arr[p]=tr[0];p+=tr[1];s=tr[2]
    lo=min(lo,p);hi=max(hi,p)
print('real abstract configs',len(real))
ok,S,states,pops,halting=search(T,d,d,tmax=300)
print('abstract',len(S),'ok',ok,'real not in S:',len(real-S))
if halting:
    cfg=halting[0][0];path=[]
    c=cfg
    while c is not None: path.append(c);c=rlectl.PARENT[c]
    path=path[::-1]
    for i,c in enumerate(path):
        if c not in real:
            print('first non-real at',i,'of',len(path))
            for c2 in path[max(0,i-6):i+3]: print('   %s %-40s [%s] %s'%('  ' if c2 in real else '!!',fmtst(c2[1]),'ABCDEF'[c2[0]],fmtst(c2[2])))
            break
