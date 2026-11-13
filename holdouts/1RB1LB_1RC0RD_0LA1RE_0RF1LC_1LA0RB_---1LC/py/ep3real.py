# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the last two overflows of epoch 3 at the real width 17,010,270: overflow to width 17,010,272 with leftover 11, then a restart
import sys, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib import *
from macro import overflow
t=time.time()
w=17010270
o=overflow(w,0,'111011'); print('overflow 1:', o[0] if isinstance(o[0],str) else (o[0],o[1],o[2]), '%.0fs'%(time.time()-t), flush=True)
w2,a2,T2=o
r,st=run(4,counter([1]*w2)+T2,3)
c=r[1]
exp='1110'*0
print('after 3 rounds xcount',r[0],'head',rle(c[:60]),'tail',rle(c[-40:]),'len',len(c))
tail='1111'+'1110'+'1010'*(3*w2//4)+('11' if w2%4==0 else '1011')
print('restart shape matches:', c=='1010'+'1011'+'1110'*r[0]+tail if False else None)
print('ends with tail_of(w2):', c.endswith(tail), 'prefix', rle(c[:len(c)-len(tail)]), '%.0fs'%(time.time()-t))
