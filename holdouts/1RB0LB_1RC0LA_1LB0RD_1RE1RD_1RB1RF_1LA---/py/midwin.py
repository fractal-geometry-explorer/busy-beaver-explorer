#!/usr/bin/env python3
"""Local window experiment for the middle collapse of b1 = 1RB0LB_1RC0LA_1LB0RD_1RE1RD_1RB1RF_1LA--- (heuristic).

At P event 105 of the event list every segment is a*3^(j+1)-27 (j = segments to its right); A below is the list of
the coefficients a from the left.  The entry with a = 2 (index 16) is the next to run out (event 107).  This script
keeps ell coefficients to its left and q to its right, puts a canonical generator 2*3^(s+4)-28 in front and end
counter c behind, and runs the reduced tape exactly with c/msimev.c (via track.reduced_run), printing each right-end
event as coefficients (a, remainder).  It is a model of the collapse, not the real tape: the left part is cut off.

usage: python3 midwin.py ell q c [seconds]     (16 November 2026 runs: 3 3 170 and 7 3 170 3000)
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from track import *
mach,c0=MACH['b1']
A=[51,48,45,42,39,36,33,30,27,24,21,18,15,12,9,24,2,35,426,399,372,345,318,291,264,237,210,183,156,129,102,75]
f=16
def coeffs(L):
    segs=L[1:-1]; s=len(segs); out=[]
    for i,v in enumerate(segs):
        j=s-1-i; a,r=divmod(v+27,3**(j+1)); out.append(a if r==0 else (a,r))
    return out
ell=int(sys.argv[1]); q=int(sys.argv[2]); cc=int(sys.argv[3])
co=A[f-ell:f+1+q]
s=len(co)
segs=[a*3**(s-i)-27 for i,a in enumerate(co)]
L=[2*3**(s+4)-28]+segs+[cc]
print('start coeffs',co,'c',cc)
evs,fail,res,h,end=reduced_run(mach,L,s,'1e24',float(sys.argv[4]) if len(sys.argv)>4 else 600,print)
print('fail',fail,'res',res,'halt',h, end[:100] if end else '')
for e in evs[:(res or len(evs))+3]:
    if e[2]: print(e[0],e[2],'gen',e[3][0],'coeffs',coeffs(e[3]),'c',e[3][-1])
    else: print(e[0],'other',e[3])
