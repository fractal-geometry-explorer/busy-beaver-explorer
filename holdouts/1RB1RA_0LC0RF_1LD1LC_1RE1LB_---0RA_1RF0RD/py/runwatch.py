"""The run of 1s at the right end and the word W left of it, over a long run (exact simulation, blocksim.py): prints
the visits where the run got shorter (W ate some of it) and, every N visits, the run's length and W's size.

usage: python3 runwatch.py SECONDS N
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from blocksim import BlockSim
from bbtools.symtm import Halted
M='1RB1RA_0LC0RF_1LD1LC_1RE1LB_---0RA_1RF0RD'
b=BlockSim(M,'1','B','R'); T=time.time(); n=0; prevrun=0; drops=0
while time.time()-T<float(sys.argv[1]):
    try: b.next_visit()
    except Halted as e: print('HALT',e,b.steps); break
    n+=1
    items=b.norm.merge(b.norm.flatten(b.cfg.left[1:]))
    run=items[-1] if isinstance(items[-1],int) else 0
    W=items[:-1]
    if run<prevrun:
        drops+=1
        if drops<40: print('drop at visit',n,'step',b.steps,'run',prevrun,'->',run,flush=True)
    prevrun=run
    if n%int(sys.argv[2])==0:
        wl=sum(x if isinstance(x,int) else len(x) for x in W)
        print(n,b.steps,'run',run,'W cells',wl,flush=True)
print('visits',n,'steps',b.steps,'drops',drops)
