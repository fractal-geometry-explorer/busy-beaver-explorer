"""Collect the shift rules used in one epoch transition (counts symbolic in t) and the X lemma; write Lean via symtm."""
import sys,time,pickle
from bfs import *
import os; sys.path.insert(0,os.path.join(os.path.dirname(os.path.abspath(__file__)),'../../../../tools/py'))
import bbtools.symtm as symtm
c,K,k=load_real('real4000.txt')
for _ in range(10**7):
    x=move2(c)
    if is_ck(x,c): break
s=decompose(c)
s0=s
while True:
    s2=rt_EX(s)
    if s2 is None: break
    s=s2
P,st,prefix,uw,uc,Xs=s
Xg=[Rep(z.w,Lc(T,0).scale(2)+z.n[-1]) if isinstance(z,Rep) else z for z in Xs]
c=compose(P,st,prefix,uw,uc,Xg)
rules={}
n=0
while n<79:
    x=move2(c)
    if x and x[5][T]!=0:
        key=(x[0],x[6],x[7],x[2],x[3],x[4])
        # carry literal u
        rules.setdefault(key,0); rules[key]+=1
    if is_ck(x,c):
        n+=1; Rt=norm_right(list(reversed(c.R))); c.R=list(reversed(Rt))
pickle.dump(dict(rules=rules,s0=None),open('trrules.pkl','wb'))
for k_,v in rules.items(): print(k_[0],'ABCDEF'[k_[1]],''.join(map(str,k_[2])),''.join(map(str,k_[3])),'->',''.join(map(str,k_[4])),k_[5],v)
