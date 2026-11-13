# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: final_phase(a, T): the last overflows of an epoch (added digits of each), until RESTART or HALT
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib import *
from shortcut import T_even
def final_phase(a, T):
    """from all-ones (width 0 simulated) + (1110)^a T: list of overflows (added digits as bit list) until restart"""
    w=0; J='1110'*a+T; out=[]
    while True:
        r,st=run(4,counter([1]*w)+J,2)
        if r is None: return out,'HALT',None
        if not r[1].startswith('10101011') or r[0]!=5: return out,'RESTART',(w,J)
        bits,J2=dec(r[1][8:])
        out.append(bits[w:]); assert all(b==0 for b in bits[:w])
        w=len(bits); J=J2
if __name__=='__main__':
  k=4252555
  out,ev,last=final_phase(6,T_even(k,24))
  print(ev, [ (len(b), ''.join(map(str,b))) for b in out], rle(last[1]) if last else None)
