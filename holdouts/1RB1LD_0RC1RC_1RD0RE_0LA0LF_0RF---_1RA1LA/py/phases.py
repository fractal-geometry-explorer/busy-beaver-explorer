"""Splits the output of c/phases.c into phases (a front running from the right end to the zone) and prints the first
line of each: step, length, G (growth: the head turns in A) or S (stall: in D), the first cells of the tape."""
import sys
from collections import Counter
lines=[l.rstrip('\n') for l in open(sys.argv[1]) if not l.startswith('HALT')]
phases=[]; cur=None; prevfr=None
for l in lines:
    a,_,pre=l.partition(' |'); p=a.split()
    n=int(p[0]); side=p[1]; st=p[2]; L=int(p[3].rstrip(':')); ds=[int(x) for x in p[4:]]
    if side!='R': continue
    far=[x for x in ds if x>=60]
    fr=far[0] if far else None
    if cur is None or (fr is None and prevfr is not None) or (fr is not None and prevfr is not None and fr>prevfr+20):
        cur={'n':n,'L0':L,'pre':pre,'sweeps':0,'typs':''}
        phases.append(cur)
    prevfr=fr if fr is not None else L
    cur['L1']=L; cur['sweeps']+=1; cur['typs']+=st
for ph in phases:
    c=Counter(ph['typs']).most_common(1)[0][0]
    t={'A':'G','D':'S'}.get(c,c)
    if ph['L0']>60: print('%12d %7d %s %s'%(ph['n'],ph['L0'],t,ph['pre'][:45]))
