"""The counter of 1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF, checked against the run.

Input: the output of `tmrun MACHINE STEPS at A R K` (the tape each time the head, in state A, is at the right end).
The tape there is blocks of 1s b[0..n] separated by gaps g[1..n] of 2, 3 or 1 zeros; read as digits
(00 = 0, 000 = 1, 0 = 2) the gaps are a counter, lowest digit at the right.  `dec` is the ordinary step: the counter
goes down by one (the lowest nonzero digit drops by one, the zeros below it become 1s); the block left of that digit
gains 3, the block right of it gains 3 (0 if the digit was a 2), the blocks further right lose 1, the last block
loses 4 (if the digit was the lowest, only the block left of it changes: +3).  Prints how many consecutive pairs
follow the rule and lists the exceptions (counter at zero, last block used up, other).

usage: tmrun MACHINE 1000000000 at A R 100000000 > ar.txt && python3 counter.py ar.txt [K]   (K exceptions shown)
"""
import sys
def parse(toks):
    blocks=[];gaps=[];cur=None
    for t in toks:
        if '>' in t: break
        if t.startswith('1'): blocks.append(int(t[2:]) if '^' in t else 1)
        else: gaps.append(int(t[2:]) if '^' in t else 1)
    if len(gaps)==len(blocks): blocks.append(0)   # empty last block
    return blocks,gaps
D={2:0,3:1,1:2}; G={0:2,1:3,2:1}
def dec(b,g):
    d=[D[x] for x in g]
    n=len(d)
    i=max((k for k in range(n) if d[k]>0), default=None)
    if i is None: return None
    b=list(b); d=list(d)
    two=d[i]==2
    d[i]-=1
    for k in range(i+1,n): d[k]=1
    # blocks: gap k sits between b[k] and b[k+1]
    if i==n-1:
        b[i]+=3
    else:
        b[i]+=3; b[i+1]+=0 if two else 3
        for k in range(i+2,n): b[k]-=1
        b[n]-=4
    return b,[G[x] for x in d]
rows=[]
for line in open(sys.argv[1]):
    p=line.split()
    if p[0] in('running','halted'): break
    rows.append((int(p[0]),)+parse(p[1:]))
ok=bad=0; kinds={}
for (k1,b1,g1),(k2,b2,g2) in zip(rows,rows[1:]):
    r=dec(b1,g1)
    if r==(b2,g2): ok+=1
    else:
        bad+=1
        key=('N0' if r is None else ('Lneg' if r[0][-1]<0 else 'other'))
        kinds[key]=kinds.get(key,0)+1
        if bad<=int(sys.argv[2]): print(k1,key, ''.join(map(str,g1)), b1[-8:], '->', ''.join(map(str,g2)), b2[-8:], ' pred', r and (''.join(map(str,r[1])), r[0][-8:]))
print("ok",ok,"bad",bad,kinds)
