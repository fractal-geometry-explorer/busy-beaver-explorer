"""Run the lemma search from DeepMind's round point E k of 1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---.

The start is `0^inf 01 (011)^k 0101 A> ANY` (k = T + 20, generalised to k >= T).  Positional arguments:
keep callk T TS mod nbig jmax callsides run cpmax frame litmax slimit Tcall runcall exact splitrun tail fullexits bfs
The last configuration tried (26 Nov 2026), which does not close:
    python3 run_ek.py 2 4 42 8 3 1 4 L run 1000 frame 8 2 9 runcall exact 6 tail fullexits
See README.md.
"""
import sys
import search
from search2 import *
from engine import K, canon
m='1RB0LD_0RC1RD_1LA1RA_1LE0LE_1RF0LA_0RA---'
keep=int(sys.argv[1]); callk=int(sys.argv[2]); T=int(sys.argv[3]); search.TS[0]=int(sys.argv[4])
search.LEVELS[:]=list(range(8,43,3))
search.MOD[0]=int(sys.argv[5]) if len(sys.argv)>5 else 1
search.NBIG[0]=int(sys.argv[6]) if len(sys.argv)>6 else 99
JMAX=int(sys.argv[7]) if len(sys.argv)>7 else 12
P = Prover(m, T=T, keep=keep, verbose="progress", maxdepth=50000, callk=callk, maxnodes=30000)
L=(((1,0),K(1)),((1,0),K(1)),((1,1,0),K(T+20)),((1,0),K(1)))
c=canon((0,'R',(L,'B'),((),'A')))
search.RUNMODE[0]=len(sys.argv)>9 and sys.argv[9]=="run"
P.cpmax=int(sys.argv[10]) if len(sys.argv)>10 else 6
P.frame=len(sys.argv)>11 and sys.argv[11]=="frame"
import engine; engine.LITMAX[0]=int(sys.argv[12]) if len(sys.argv)>12 else 2
P.slimit=int(sys.argv[13]) if len(sys.argv)>13 else 0
P.Tcall=int(sys.argv[14]) if len(sys.argv)>14 else 0
P.runcall=len(sys.argv)>15 and sys.argv[15]=="runcall"
P.keepexact=len(sys.argv)>16 and sys.argv[16]=="exact"
P.splitrun=int(sys.argv[17]) if len(sys.argv)>17 else 0
P.tailloops=len(sys.argv)>18 and sys.argv[18]=="tail"
P.fullexits=len(sys.argv)>19 and sys.argv[19]=="fullexits"
P.bfs=len(sys.argv)>20 and sys.argv[20]=="bfs"
P.jmax=JMAX
P.callsides=sys.argv[8] if len(sys.argv)>8 else "LR"
print("start", cfg_str(c))
r = P.attempt(c)
print(r[0], r[1] if r[0]!='ok' else len(r[1]))
if r[0]=='ok':
    for nd in r[1]:
        print("  ", nstr(nd['N']), " exits:", len(nd['exits']))
elif len(r)>3:
    for x in r[3]: print("CHAIN", x[:200])
