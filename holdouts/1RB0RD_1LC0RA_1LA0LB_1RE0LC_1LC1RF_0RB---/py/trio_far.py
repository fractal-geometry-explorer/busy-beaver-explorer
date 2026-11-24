"""trio_far MACHINE SECONDS OUT.jsonl SNAP.pkl: run trio.py for SECONDS (resuming from SNAP.pkl if it exists), writing
to OUT.jsonl the tape at returns of the head to the left end (each at least 1.3 times the steps of the last one
recorded: the start of each outer phase) and the progress every 30 seconds; SNAP.pkl is rewritten every 5 minutes.
"""
import sys, time, json, pickle, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from trio import Sim, Halt
m=sys.argv[1]; T=float(sys.argv[2]); out=open(sys.argv[3],'a'); snap=sys.argv[4]
if os.path.exists(snap):
    sim=pickle.load(open(snap,'rb')); sim.rules.clear(); sim.aligns.clear(); sim.lastsig={}
else:
    sim=Sim(m)
def fmt(it):
    w,c=it[0],it[1]; return (f'[{len(w)}]' if len(w)>12 else w)+(f'^{c}' if c>1 else '')
lastlog=[sim.steps]
orig=Sim.edge
def e(self,d):
    if d<0 and len(self.L)<=1 and self.steps>1.3*lastlog[0]:
        lastlog[0]=self.steps
        items=[(x[0],x[1]) for x in self.R[::-1]]
        out.write(json.dumps({'ev':'left','steps':self.steps,'items':len(self.R),'cells':sum(len(w)*c for w,c in items),
            'head':' '.join(fmt(x) for x in self.R[-1:-13:-1]),'tail':' '.join(fmt(x) for x in self.R[:12][::-1])})+'\n'); out.flush()
    orig(self,d)
Sim.edge=e
t0=time.time(); last=0; lastsnap=time.time()
try:
    while time.time()-t0<T:
        sim.run(10**60, maxops=50000)
        if time.time()-last>30:
            last=time.time()
            out.write(json.dumps({'ev':'prog','sec':round(time.time()-t0),'steps':sim.steps,'jumps':sim.njumps,'sweeps':sim.nsweeps,'items':len(sim.L)+len(sim.R)})+'\n'); out.flush()
        if time.time()-lastsnap>300:
            lastsnap=time.time()
            if sim.win is not None: sim._clear_forms()
            lg=sim.log; sim.log=None
            sim.rules.clear(); sim.aligns.clear(); sim.lastsig={}
            pickle.dump(sim, open(snap+'.tmp','wb')); os.replace(snap+'.tmp',snap)
            sim.log=lg
except Halt:
    out.write(json.dumps({'ev':'HALT','steps':sim.steps})+'\n')
out.write(json.dumps({'ev':'end','steps':sim.steps,'jumps':sim.njumps})+'\n')
if sim.win is not None: sim._clear_forms()
sim.log=None
sim.rules.clear(); sim.aligns.clear(); sim.lastsig={}
pickle.dump(sim, open(snap,'wb'))
