# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: epoch(a, tail): run overflow after overflow of an all-ones main counter followed by (1110)^a tail, until HALT or RESTART
import sys
from lib import *
def epoch(a, tail, w=0, K=12, verbose=True, maxit=10**6):
    J='1110'*a+tail
    for it in range(maxit):
        r,st=run(K,counter([1]*w)+J,2)
        if r is None: return ('HALT',it,w,J)
        if not r[1].startswith('10101011') or r[0]!=K+1:
            return ('RESTART',it,w,J, r)
        bits,J2=dec(r[1][8:])
        if verbose: print(it,'w',w,'->',len(bits),''.join(map(str,bits[-4:])),'|',rle(J2)[:150], flush=True)
        w=len(bits); J=J2
    return ('MAX',)
if __name__=='__main__':
    a=int(sys.argv[1]); tail=sys.argv[2]
    res=epoch(a,tail)
    print(res[0], res[1], res[2], rle(res[3])[:200]); 
    if res[0]=='RESTART': print(res[4][0], rle(res[4][1])[:300])
