# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: overflow(w, a, T): one overflow of an all-ones main counter of width w followed by (1110)^a T -> (w', a', T'); main: the map does not depend on w or a
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib import *
def strip(J):
    a=0
    while J.startswith('1110'): J=J[4:]; a+=1
    return a,J
def overflow(w, a, T):
    """one overflow of an all-ones main counter of width w followed by (1110)^a T; returns (w', a', T') or event"""
    r,st=run(4,counter([1]*w)+'1110'*a+T,2)
    if r is None: return ('HALT',)
    if not r[1].startswith('10101011') or r[0]!=5: return ('RESTART', r)
    bits,J=dec(r[1][8:])
    a2,T2=strip(J)
    return (len(bits), a2, T2)
if __name__=='__main__':
    import random
    T0='1111'+'1110'+'1010'*18+'11'
    # dependency test
    T=T0; seen={}
    for step in range(30):
        outs=set()
        for w in (0,2,4,6,8):
            for a in (6,7,8,9):
                o=overflow(w,a,T)
                outs.add((o[0]-w, a-o[1], o[2]))
        print(step, len(outs), list(outs)[:3] if len(outs)>1 else rle(list(outs)[0][2]), list(outs)[0][:2])
        o=list(outs)[0]; T=o[2]
