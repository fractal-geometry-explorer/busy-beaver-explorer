import sys
from collections import defaultdict
rows=[]
for line in open(sys.argv[1]):
    if line.startswith('halted'): continue
    a,b=line.split(':'); t,m,s=map(int,a.split())
    L,R=b.split('|'); L=[int(x) for x in L.split()]; R=[int(x) for x in R.split()]
    rows.append((t,m,s,L,R))
data=defaultdict(set); bad=0; n=0
for (t1,m1,s1,L1,R1),(t2,m2,s2,L2,R2) in zip(rows,rows[1:]):
    off = 1 if m1==3 else 0
    if m1!=m2: print('mode change',t1,t2); continue
    A=L1[:]; 
    if not A: continue
    A[-1]-=off
    if A[-1]<0: print('neg top',t1); continue
    v=A[-1]
    if len(A)>=2: w=A[-2]; pS=A[:-2]+[w+1]+[0]*v; ps=s1
    else: pS=[0]*v; ps=s1+1
    if pS: pS[-1]+=off
    j=0
    while j<len(R1) and R1[j]==0: j+=1
    if j<len(R1): pR=[0,j-1,R1[j]-1]+R1[j+1:]
    else: pR=[0,j-1]
    n+=1
    if pS!=L2 or ps!=s2 or pR!=R2:
        bad+=1
        if bad<6: print('MISMATCH',t1,s1,L1,R1,'->',t2,s2,L2,R2,'pred',ps,pS,pR)
    data[(m1,v,j)].add(t2-t1)
print('checked',n,'bad',bad)
ok=True
for (m,v,j),ts in sorted(data.items()):
    pred = (48+4*v+6*j) if m==5 else None
    if len(ts)>1 or (pred is not None and pred not in ts): print('step anomaly',m,v,j,ts); ok=False
m3=[(v,j,list(ts)[0]) for (m,v,j),ts in data.items() if m==3]
print(sorted(m3)[:30])
