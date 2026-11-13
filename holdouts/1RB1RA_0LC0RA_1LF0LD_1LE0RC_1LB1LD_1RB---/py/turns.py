"""Tape of 1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB--- (block view) at each reversal of the head.  usage: python3 holdouts/1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---/py/turns.py FROM TO [MIN_EXCURSION]
e.g. 656860 667120 8 shows one ordinary pair of events: three round trips each."""
# turns.py FROM TO [MINEXC]: tape (block view, head marked) at each reversal of the head whose excursion exceeds MINEXC cells
import sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from blocks import blocks,comp
M="1RB1RA_0LC0RA_1LF0LD_1LE0RC_1LB1LD_1RB---"
T={}
for s,part in enumerate(M.split('_')):
    for r in range(2):
        t=part[3*r:3*r+3]
        T[(s,r)]=None if t[2]=='-' else (int(t[0]),1 if t[1]=='R' else -1,ord(t[2])-65)
tab=[[T[(s,r)] for r in range(2)] for s in range(6)]
F,TO=int(float(sys.argv[1])),int(float(sys.argv[2]))
EXC=int(sys.argv[3]) if len(sys.argv)>3 else 6
tape=bytearray(1<<22);p=lo=hi=1<<21;st=0
ext=p;d=1;snap=None
def show(k,pp,stt,d):
    s1=''.join('01'[c] for c in tape[lo:pp]); s2=''.join('01'[c] for c in tape[pp:hi+1])
    print(k,'<' if d<0 else '>','ABCDEF'[stt],pp-lo,hi-pp,'|',comp(blocks(s1)),' [%s] '%'ABCDEF'[stt],comp(blocks(s2)))
for k in range(1,TO+1):
    w,m,ns=tab[st][tape[p]]
    tape[p]=w;p+=m;st=ns
    if p<lo: lo=p
    if p>hi: hi=p
    if d>0:
        if p>ext: ext=p
        elif p<ext-EXC:
            if k>=F: print('  turn at right ext',ext-lo,'(from right end %d)'%(hi-ext),'step',k)
            d=-1;ext=p
            if k>=F: show(k,p,st,d)
    else:
        if p<ext: ext=p
        elif p>ext+EXC:
            if k>=F: print('  turn at left ext',ext-lo,'step',k)
            d=1;ext=p
            if k>=F: show(k,p,st,d)
