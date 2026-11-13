# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the tail family T3 left by epoch 2 (END 1011 1011) and its shortcut; main: no halts at small sizes
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lib import *
from epoch import epoch
from shortcut import enc
def cells(D): return 3*D + (D%2)
def T3(W): return '11111110'+'1010'*(3*W//4+1)+'10111011'
def D3(W):
    c=4*(3*W//4+1); 
    for D in range(c):
        if cells(D)==c: return D
def Teven3(k,W): return '11111011'+enc(k,D3(W))+'10111011'
def short3(a0,W,amin=6):
    k=max(0,(a0-amin)//3-1); a=a0-3*(k+1)
    return epoch(a,Teven3(k,W),verbose=False)[0]
if __name__=='__main__':
    for W in (8,12,16):
        full=[a for a in range(9,150) if epoch(a,T3(W),verbose=False)[0]=='HALT']
        sc=[a for a in range(9,150) if short3(a,W)=='HALT']
        print(W, D3(W), full==sc, full[:20])
