"""test_cyc.py MACHINE STEPS: the accelerated run (ws.Sim with the proved cycle jumps of cyc.Acc) against the plain
ws.Sim run: the tapes at every sample point the accelerated run stops at must be the tapes of the plain run at the same
step count."""
import sys,time
from cyc import *
M=sys.argv[1]; N=int(float(sys.argv[2]))
# plain ws run records configs at sample points; accelerated run must hit a subset with identical tapes
a=Sim(M); ac=Acc(a)
pts={}
t0=time.time()
while a.steps<N and ac.step():
    if is_sample(a): pts[a.steps]=show(a)
t1=time.time()
b=Sim(M); found=0
while b.steps<N and b.step():
    if b.steps in pts:
        assert pts[b.steps]==show(b),(b.steps,pts[b.steps][:200],show(b)[:200]); found+=1
print(M,"accelerated: macro",a.nmacro,"jumps",ac.njump,"cycles",ac.ncyc,"rules",sum(map(len,ac.rules.values())),"t=%.1f"%(t1-t0),"; plain macro",b.nmacro,"t=%.1f"%(time.time()-t1),"; sample points compared",found,"of",len(pts))
