"""Compare the macro machine (py/mac14.py) with the C run (py/r14.c output, a file given as argument) at every refill moment (N = 0)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mac14 import trim, fast as step
def canon_tokens(tk):
    out=[]; ev=True
    for u in tk:
        if u.isdigit(): out.append(int(u)); ev=False
        else:
            if ev: out.append(0)
            out.append(u); ev=True
    if ev: out.append(0)
    return out
# C output tokens start at head cell (which is '1' of "1 0" pair => token '1' merges). r14 prints from p: head cell 1.
real=[]
for line in open(sys.argv[1]):
    t=line.split()
    if not t or not t[0].isdigit() or len(t)<2: continue
    n=int(t[0]); tk=t[1:]
    # head cell is the '1' starting a (10) run: first token is a count c>=1 -> head + '0' + (10)^(c-1)
    c=int(tk[0]); rest=(['.'] + ([str(c-1)] if c>1 else []) + tk[1:])
    # tokens after head cell: '.' then (10)^(c-1)
    real.append((n, trim(canon_tokens(rest))))
print(len(real),'refill moments in C output')
# macro from the first one
L=real[0][1]; k=0; sweeps=0; ok=0
import itertools
for n,R in real[1:]:
    while True:
        L,kk=step(L); sweeps+=kk
        if L[0]==0: break
    if L!=R:
        print('MISMATCH at step',n,'after',sweeps,'sweeps'); 
        a,b=L,R; kk=next((k for k in range(min(len(a),len(b))) if a[k]!=b[k]),None); print(kk,len(a),len(b)); print(a[:20]); print(b[:20]); break
    ok+=1
print('agree at',ok,'refill moments,',sweeps,'sweeps')
