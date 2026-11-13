# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: epoch 2 of the blank-tape run (a0 = 12,757,674, tail counter of 24 digits): final phase, W_f, N_end; writes epoch2_end.pkl
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from final import final_phase
from shortcut import T_even
a0=12757674; D=24
k=(a0-6)//3-1; a=a0-3*(k+1); M=2*k+2
out,ev,last=final_phase(a,T_even(k,D))
N=(2*(4**M-1))//3
W=2*M
for bits in out:
    v=sum(b<<(W+j) for j,b in enumerate(bits))
    W+=len(bits)
    N+=1+(2**W-1-v)
wsim,J=last
assert W==2*M+wsim
print('k',k,'M',M,'final event',ev,'J',J,'W_f',W,'W_f mod 4',W%4,'N_end bits',N.bit_length(),'N mod 3',N%3,'N mod 64',N%64)
import pickle; pickle.dump((N,W,J),open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'epoch2_end.pkl'),'wb'))
