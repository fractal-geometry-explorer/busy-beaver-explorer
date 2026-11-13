# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: T_even(k, D): the tail after 2k+2 overflows (tail counter at k); shortcut(a0, D) skips them; main compares with the full run
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib import *
from epoch import epoch
def tail_of(w): return '1111'+'1110'+'1010'*(3*w//4)+('11' if w%4==0 else '1011')
def enc(v,D): return counter([(v>>i)&1 for i in range(D)])
def T_even(k,D): return '1111'+'1011'+enc(k,D)+'11'
def shortcut(a0, D, amin=6):
    # state after 2k+2 overflows: a = a0-3(k+1), T = T_even(k)
    k=max(0,(a0-amin)//3-1)
    a=a0-3*(k+1)
    if a < 0: return None
    return epoch(a, T_even(k,D), verbose=False)[0], k, a
if __name__=='__main__':
    for w in (4,6,8):
        D=w
        full=[a for a in range(9,160) if epoch(a,tail_of(w),verbose=False)[0]=='HALT']
        sc=[a for a in range(9,160) if shortcut(a,D)[0]=='HALT']
        print(w, full==sc, full[:12], sc[:12])
