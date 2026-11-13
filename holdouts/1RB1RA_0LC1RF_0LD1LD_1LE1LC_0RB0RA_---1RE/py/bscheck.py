"""Checks blocksim.py against the plain C simulator at every wall visit.

usage: python3 bscheck.py MACHINE WORD STATE L|R STEPS     (needs tools/c/tmrun.c compiled to ./tmrun or $TMRUN)
"""
import os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from blocksim import BlockSim
TMRUN = os.environ.get("TMRUN", "./tmrun")


def expand(tok):
    out = []
    for t in tok:
        m = re.fullmatch(r'([01])(?:\^(\d+))?', t)
        if m:
            out.append(m.group(1) * int(m.group(2) or 1)); continue
        m = re.fullmatch(r'([A-F])>([01])', t)
        if m:
            out.append(m.group(1).lower() + m.group(2)); continue
        raise ValueError(t)
    return ''.join(out)


def runs(M, steps, st, side, k):
    p = subprocess.run([TMRUN, M, str(steps), 'at', st, side, str(k)], capture_output=True, text=True)
    return [(int(l.split()[0]), expand(l.split()[1:])) for l in p.stdout.splitlines()
            if l.split()[0] not in ('running', 'halted')]


M,w,st,side,steps=sys.argv[1],sys.argv[2],sys.argv[3],sys.argv[4],int(sys.argv[5])
def expand_cfg(b):
    c=b.cfg
    def ex(seq):
        s=''
        for t in seq:
            if isinstance(t,int): s+=str(t)
            elif hasattr(t,'word'): s+=''.join(map(str,t.word))*t.n.k
        return s
    L=ex(c.left[1:]); R=ex(c.right[:-1])
    return L+'abcdef'[c.state]+(R if R else '0')
D=[(s,t) for s,t in runs(M,steps,st,side,10**7)]
# direct runs give step and tape; head marked as lower letter + symbol
b=BlockSim(M,w,st,side)
i=0; bad=0
while True:
    b.next_visit()
    if b.steps>steps: break
    # find matching direct visit
    while i<len(D) and D[i][0]<b.steps: i+=1
    if i>=len(D) or D[i][0]!=b.steps: print('step mismatch',b.steps, D[i][0] if i<len(D) else None); bad+=1; break
    t=D[i][1].strip('0') if False else D[i][1]
    e=expand_cfg(b)
    # normalise: strip leading zeros of both
    if t.lstrip('0')!=e.lstrip('0'): print('tape mismatch at',b.steps); print(t[:200]); print(e[:200]); bad+=1; break
    i+=1
print('checked visits up to',b.steps,'bad',bad)
