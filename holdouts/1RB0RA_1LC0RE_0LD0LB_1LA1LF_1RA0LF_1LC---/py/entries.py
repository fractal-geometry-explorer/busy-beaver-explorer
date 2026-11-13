"""entries.py START STEPS: how long the first run is each time the head enters it.

Runs the table from blank tape started in state START (0..5 for A..F; 3 is the run of 40600) with rsim.py and, at every
entry (the head steps from the right onto the last cell of the first run of the tape), records the length of that run.
Prints the number of entries and those with a first run of fewer than 8 cells.  lean/Shift4.lean covers every entry
with at least 5 cells (a bounce needs at most 2).
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import Sim
start=int(sys.argv[1]); N=float(sys.argv[2])
s=Sim(); s.st=start
def infirst(s):
    return len(s.L)==0 or (len(s.L)==1 and (s.L[0][0]^((s.L[0][1]-1)&1))!=s.h)
prev=True; small=[]; ents=0; hist={}; lastsmall=None
while s.steps<N:
    p0=s.pos
    if not s.step(): print('HALT'); break
    cur=infirst(s)
    if cur and not prev and s.pos<p0:
        n=s.runs()[0]; ents+=1
        if n<8:
            hist[n]=hist.get(n,0)+1; lastsmall=(s.steps,n,'ABCDEF'[s.st],s.h)
            if len(small)<40: small.append((s.steps,n,'ABCDEF'[s.st],s.h))
    prev=cur
print('start','ABCDEF'[start],'steps',int(s.steps),'entries',ents,'first-run length <8 at entry:',sorted(hist.items()),'last such',lastsmall)
print(small)
