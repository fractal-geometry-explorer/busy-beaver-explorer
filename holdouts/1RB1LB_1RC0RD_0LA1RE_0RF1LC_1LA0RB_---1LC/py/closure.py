# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: python3 closure.py A w1,w2,..: from tail_of(w) and junk a = 1..A, does every epoch restart, and in the restart shape?
import sys,re
from lib import *
from epoch import epoch
def tail_of(w):
    return '1111'+'1110'+'1010'*(3*w//4)+('11' if w%4==0 else '1011')
if __name__!="__main__": raise SystemExit
bad=0; tot=0; forms={}
A=int(sys.argv[1]); WS=[int(x) for x in sys.argv[2].split(',')]
for w in WS:
    for a in range(1,A+1):
        res=epoch(a, tail_of(w), verbose=False)
        tot+=1
        if res[0]!='RESTART': print('BAD', w, a, res[0]); bad+=1; continue
        it,wf,J,r=res[1],res[2],res[3],res[4]
        # restart: run 3 records from all-ones width wf + J to see the new epoch start
        r2,_=run(12,counter([1]*wf)+J,3)
        s=r2[1]
        ok = r2[0]==0 and s==('10101011'+'1110'*12+tail_of(wf))
        key=(J, ok)
        forms[key]=forms.get(key,0)+1
        if not ok: print('FORM', w, a, J, wf, rle(s)[:120]); bad+=1
        
print('tested',tot,'bad',bad, forms)
