# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: epoch 3 (a3 = N_end of epoch 2, tail T3 of 17,010,257 digits) up to the absorption of the tail; needs epoch2_end.pkl
import sys, pickle, time
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib import *
N,W,J=pickle.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'epoch2_end.pkl'),'rb'))
from gen import D3
def cells(D): return 3*D + (D%2)
# epoch 3 tail family T3(W) with W=W_f; D digits
c=4*(3*W//4+1); D=(c-1)//3 if c%3==1 else c//3
assert cells(D)==c, (c,D)
a3=N; k=(a3-6)//3-1; a=a3-3*(k+1)
print('a3 mod 3',a3%3,'k bits',k.bit_length(),'D',D,'a',a, flush=True)
def enc_fast(v,D):
    b=bin(v)[2:][::-1].ljust(D,'0')
    out=[]
    for i,ch in enumerate(b):
        if i%2==0: out.append('1111' if ch=='1' else '1010')
        else: out.append('11' if ch=='1' else '10')
    return ''.join(out)
T='11111011'+enc_fast(k,D)+'10111011'
print('tail cells',len(T), flush=True)
w=0; Jc='1110'*a+T; it=0
while True:
    t0=time.time()
    r,st=run(4,counter([1]*w)+Jc,2)
    if r is None: print('HALT at final overflow',it); break
    if not r[1].startswith('10101011') or r[0]!=5:
        print('RESTART-type event at it',it,'w',w,'J head',rle(Jc[:200]),'len J',len(Jc)); break
    bits,J2=dec(r[1][8:])
    print(it,'w',w,'->',len(bits),'new bits',''.join(map(str,bits[w:]))[:60],'J',len(J2), rle(J2[:80]), '%.0fs'%(time.time()-t0), flush=True)
    w=len(bits); Jc=J2; it+=1
    if w>200: print('main counter absorbed a long part; stop'); break
