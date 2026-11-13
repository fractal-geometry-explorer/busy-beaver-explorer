"""Run the machine directly and check every sweep against the macro machine (py/mac14.py): at each visit of the
left end in state A on a 1, the tape must be the list the macro machine predicted.  usage: check.py STEPS"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mac14 import canon, step, Unknown, trim
M='1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---'
T={}
for i,g in enumerate(M.split('_')):
    for r in (0,1):
        t=g[3*r:3*r+3]
        T[(chr(65+i),r)]=None if t[0]=='-' else (int(t[0]),1 if t[1]=='R' else -1,t[2])
import collections
N=int(float(sys.argv[1]))
tape=bytearray(1<<22); p=1<<21; s='A'; lo=hi=p
pred=None; cnt=collections.Counter(); prevL=None
for n in range(N):
    r=tape[p]
    if p==lo and s=='A' and r==1:
        x=bytes(tape[p+1:hi+1]).decode('latin1').translate({0:'0',1:'1'})
        L=trim(canon(x))
        if pred is not None and L!=pred[0]:
            print('MISMATCH at',n,'rule',pred[1]); print(' prev',prevL[:16],prevL[-16:]); print(' got ',L[:16],L[-16:]); print(' pred',pred[0][:16],pred[0][-16:]); a,b=L,pred[0]; k=next(k for k in range(min(len(a),len(b))) if a[k]!=b[k]); print(k,len(a),len(b)); print(' got',a[k-8:k+12]); print(' prd',b[k-8:k+12]); q=prevL; print(' prv',q[k-8:k+12]); break
        try:
            pred=step(L); prevL=L; cnt[pred[1]]+=1
        except Unknown as e:
            print('unknown at',n,e, L[:10], L[-10:]); pred=None
    t=T[(s,r)]
    if t is None: print('halt',n); break
    tape[p]=t[0]; p+=t[1]; s=t[2]; lo=min(lo,p); hi=max(hi,p)
print(cnt)
