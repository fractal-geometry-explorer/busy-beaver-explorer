"""lockstep.py START1 START2 STEPS: compare two runs of this table from blank tape, started in two different states.

The four holdouts 1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC--- (start A), 1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---
(start D, mirrored), 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB--- (start B, mirrored) and
1RB0LF_1RC0RB_1LD0RA_0LE0LC_1LB1LF_1LD--- (start E) are this one table started in another state (holdouts/related.json).
Both runs are simulated with rsim.py; at every trip start (state A on a new leftmost cell) the run lengths of the two
tapes are compared.  The trips are first aligned (one run may need one more trip to get going), then every pair of
trips must have the same run lengths except for the first run; the differences of the first run are collected.

START1, START2: 0..5 for A..F.  Prints the alignment, the number of trips compared, the number of mismatches and the
set of differences of the first run.
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rsim import Sim
def trips(start):
    s=Sim(); s.st=start
    while True:
        if not s.step(): yield ('HALT',s.steps+1); return
        if s.at_left(): yield (s.steps,s.runs())
a,b,n=int(sys.argv[1]),int(sys.argv[2]),float(sys.argv[3])
ga,gb=trips(a),trips(b); k=0; bad=0; firstok=None; offs=set(); dsteps=None
# align: skip leading trips until the lists agree up to the first run
import itertools
A=[next(ga) for _ in range(40)]; B=[next(gb) for _ in range(40)]
best=None
for i in range(20):
    for j in range(20):
        if all(A[i+t][1][1:]==B[j+t][1][1:] for t in range(15)): best=(i,j); break
    if best: break
print('alignment (trip index in',('ABCDEF'[a],'ABCDEF'[b]),'):',best)
i,j=best; pa=A[i:]; pb=B[j:]
def stream(pre,g):
    for x in pre: yield x
    for x in g: yield x
for (sa,ra),(sb,rb) in zip(stream(pa,ga),stream(pb,gb)):
    k+=1
    if sa=='HALT' or sb=='HALT': print('HALT',sa,sb); break
    if ra[1:]!=rb[1:]: bad+=1; 
    if bad and bad<4 and ra[1:]!=rb[1:]: print('differ at',k,sa,sb,ra[:6],rb[:6])
    offs.add(ra[0]-rb[0])
    if k==1: print('first compared trips:',sa,ra,sb,rb)
    if sa>n: break
print('trips compared',k,'mismatches',bad,'r0 differences',sorted(offs),'step difference at the end',sa-sb,'last',sa,ra[:4],len(ra))
