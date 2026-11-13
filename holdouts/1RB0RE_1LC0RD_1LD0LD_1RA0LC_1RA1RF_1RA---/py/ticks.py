"""Check the tick rule of 1RB0RE_1LC0RD_1LD0LD_1RA0LC_1RA1RF_1RA--- against the machine, sweep for sweep.

Input: the output of c/blocks.c. At each left turn the tape is

    0^inf D> 0 (10)^a  s1 (10)^b1 1 (10)^c1  s2 (10)^b2 1 (10)^c2 ... tail

with each separator s_i either `0` (digit 1) or `0 0 0` (digit 0). The tick rule is a binary increment from the
left: every leading digit 1 becomes 0 (its separator becomes `0 0 0` and c_i loses one), the first digit 0 becomes 1
(its separator becomes `0`, and b_i gains one), and a gains one. It takes

    6 + 4a + 8 (b_1 + ... + b_n) + 4 (c_1 + ... + c_n) + 8n

steps, where n is the number of digits passed. This script counts the sweeps where rule and step count hold
exactly, and sorts the others: `p1` means a passed digit had c = 1 (its block would empty), `END` means the carry
passed every digit, `parse` means the tape is not of the form above.

usage: python3 py/ticks.py blocks.txt
"""
import sys
from collections import Counter
def parse(tk):
    assert tk[0]=='1' and tk[1][0]=='T'
    a=int(tk[1][1:]); i=2; D=[]
    while True:
        if tk[i:i+3]==['0','0','0']: s=0; j=i+3
        elif tk[i:i+1]==['0']: s=1; j=i+1
        else: break
        if j+2<len(tk) and tk[j][0]=='T' and tk[j+1]=='1' and tk[j+2][0]=='T':
            D.append([s,int(tk[j][1:]),int(tk[j+2][1:])]); i=j+3
        else: break
    return a,D,tk[i:]
def tick(a,D,tail):
    D=[d[:] for d in D]; n=0; Sb=Sc=0
    for d in D:
        if d[0]==1:
            if d[2]<2: return None
            Sb+=d[1]; Sc+=d[2]; d[0]=0; d[2]-=1; n+=1
        else:
            d[0]=1; d[1]+=1
            return (a+1,D,tail), 6+4*a+8*Sb+4*Sc+8*n
    return None
lines=[l.split() for l in open(sys.argv[1])]
good=0; ex=Counter(); exl=[]
for p,q in zip(lines,lines[1:]):
    s1=int(p[0]); s2=int(q[0])
    try: A=parse(p[3:]); B=parse(q[3:])
    except Exception: ex['parse']+=1; continue
    r=tick(*A)
    if r and r[0]==B and r[1]==s2-s1: good+=1
    else:
        a,D,tail=A
        # signature: passed digits' c (<2 flagged), whether a stop digit exists
        sig=[]
        for d in D:
            if d[0]==1: sig.append('p' if d[2]>=2 else 'p%d'%d[2])
            else: sig.append('s'); break
        else: sig.append('END')
        key=' '.join(x for x in sig if x!='p')+(' ok?' if r and r[0]==B else '')
        ex[key]+=1; exl.append((s1,key,A,B,s2-s1))
print('good',good); print(ex.most_common(30))

