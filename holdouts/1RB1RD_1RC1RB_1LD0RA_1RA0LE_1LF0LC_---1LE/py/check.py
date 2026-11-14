"""Checks of the accelerated simulator of accel.py.   python3 check.py [quick|full]

1. rl.RL (run-length) against the cell-level reference simulator of tools/py/bbtools/machine.py: step count and the
   whole tape at each of the first visits.
2. The visit rule of a zone (accel.jump with V = 1, accel.jump_steps) against the cell-level simulator, on random
   zones with a random tape to their left, counts down to the smallest the accelerator jumps over.
3. The closed forms jump / jump_steps against odo.py (visits composed by doubling) and against single visits.
4. The accelerated run against RL alone, visit by visit.
5. (full) the whole run to the halt, every jump compared with odo.py.
"""
import sys, os, random, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from accel import *
import odo
from bbtools.machine import Machine
m=Machine.parse(M)
full = len(sys.argv)>1 and sys.argv[1]=='full'

def cells_of(c):
    out=[]
    for it in c:
        if isinstance(it,int): out.extend([0,1,1]*it)
        else: out.extend(int(x) for x in it)
    return out
def raw_visit(cells, limit=10**8):
    """cells: the tape up to the right end, head in A on the blank cell after it.  Runs to the next visit;
    returns (cells with leading zeros stripped, steps) or None if the head leaves the tape on the left or halts"""
    t=list(cells)+[0]; pos=len(cells); hi=pos; st=0; n=0; off=0
    while n<limit:
        if pos<0: t.insert(0,0); pos=0; off+=1; hi+=1
        if pos>=len(t): t.append(0)
        tr=m.table[st][t[pos]]
        if tr is None: return None
        t[pos],mv,st=tr; pos+=mv; n+=1
        if pos>hi:
            if st==0:
                out=t[:pos]
                return out,n
            hi=pos
    raise RuntimeError('limit')
def strip(x):
    i=0
    while i<len(x) and x[i]==0: i+=1
    return x[i:]

t0=time.time()
# 1
N1=3000 if full else 1200
r=RL(M); cells=[]; steps=0
for v in range(N1):
    r.next_visit(); res=raw_visit(cells); assert res is not None
    cells,n=res; steps+=n
    assert steps==r.steps and strip(cells)==strip(cells_of(canon(r.segs()))), ('RL differs from the cell-level run at visit',v+1)
print('1. RL = cell-level simulator at each of the first %d visits (%d steps)   t=%.0f'%(N1,steps,time.time()-t0))
# 2
random.seed(7); n2=0; N2=6000 if full else 1500
prefixes=['','1','111','1101','0111011011','11101111','0100101','1111001','011011011','110110']
while n2<N2:
    k=random.randint(1,7)
    counts=[random.randint(MARGIN+2,random.choice([MARGIN+3,9,14])) for _ in range(k+1)]
    bits=[random.randint(0,1) for _ in range(k)]
    if all(bits): continue
    pre=[random.choice(prefixes)] if random.random()<.8 else [random.choice(prefixes),random.randint(3,9),random.choice(['11','01','0','1'])]
    pre=[p for p in pre if p!='']
    V,nc,nb=jump(counts,bits,1)
    if V!=1: continue            # the accelerator would not jump from here
    res=raw_visit(cells_of(unzone(pre,counts,bits)))
    assert res is not None
    assert strip(res[0])==strip(cells_of(unzone(pre,nc,nb))) and res[1]==jump_steps(counts,bits,1), ('visit rule',pre,counts,bits)
    n2+=1
print('2. the visit rule = cell-level simulator on %d random zones   t=%.0f'%(n2,time.time()-t0))
# 3
random.seed(1); n3=0
for t in range(20000 if full else 4000):
    k=random.randint(1,8); counts=[random.randint(300,400) for _ in range(k+1)]; bits=[random.randint(0,1) for _ in range(k)]
    B=int(''.join(map(str,bits)),2)
    if (1<<k)-1-B<1: continue
    V=random.randint(1,(1<<k)-1-B)
    V2,nc,nb=jump(counts,bits,V); assert V2==V
    c,b,s=list(counts),list(bits),0
    for i in range(V):
        _,c,b=jump(c,b,1)
    c1,b1,s1=odo.run(counts,bits,V)
    # single visits by odo
    c3,b3,s3=list(counts),list(bits),0
    for i in range(V):
        c3,b3,q=odo.run(c3,b3,1); s3+=q
    assert c==nc==c1==c3 and b==nb==b1==b3 and s1==s3==jump_steps(counts,bits,V)
    n3+=1
for t in range(300):
    k=random.randint(20,120); counts=[random.randint(10**30,10**40) for _ in range(k+1)]; bits=[random.randint(0,1) for _ in range(k)]
    V,nc,nb=jump(counts,bits)
    if V<1: continue
    c1,b1,s1=odo.run(counts,bits,V); assert (c1,b1,s1)==(nc,nb,jump_steps(counts,bits,V)); n3+=1
print('3. closed forms = odo.py = single visits on %d zones   t=%.0f'%(n3,time.time()-t0))
# 4
N4=400000 if full else 60000
a=Acc(); d=RL(M); dv=0
while a.visits<N4:
    a.advance()
    while dv<a.visits: d.next_visit(); dv+=1
    assert canon(d.segs())==canon(a.r.segs()) and d.steps==a.r.steps, ('accelerated run differs at visit',a.visits)
print('4. accelerated run = RL alone up to visit %d (step %d; %d jumps, %d direct visits)   t=%.0f'%(a.visits,a.r.steps,a.jumps,a.direct,time.time()-t0))
# 5
if full:
    a=Acc(); nj=0
    try:
        while True:
            c=canon(a.r.segs()); z=zone(c); j0=a.jumps; s0=a.r.steps
            a.advance()
            if a.jumps!=j0:
                pre,counts,bits=z; V,nc,nb=jump(counts,bits)
                c2,b2,s2=odo.run(counts,bits,V); nj+=1
                assert c2==nc and b2==nb and s2==a.r.steps-s0, ('jump',j0)
    except Halt: pass
    print('5. the run to the halt: %d jumps, each = odo.py; halt at step %d   t=%.0f'%(nj,a.r.steps,time.time()-t0))
print('ALL OK')
