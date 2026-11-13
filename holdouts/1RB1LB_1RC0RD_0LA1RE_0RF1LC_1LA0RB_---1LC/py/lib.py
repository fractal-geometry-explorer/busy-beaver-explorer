# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: rle (word-wise run-length), run(K, rest, n): the reduced machine from 0^inf B> 0 10 (1011)^K 1010 1011 rest, n records in B on (None on a halt)
import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from jump import T, counter, dec
toks=['1110','1010','1111','1011','10','11','0','1']
def rle(s):
    out=[];i=0
    while i<len(s):
        for t in toks:
            if s.startswith(t,i): out.append(t); i+=len(t); break
    r=[];j=0
    while j<len(out):
        k=j
        while k<len(out) and out[k]==out[j]: k+=1
        r.append(out[j]+('^%d'%(k-j) if k-j>1 else '')); j=k
    return ' '.join(r)
def run(K, rest, n_rounds, junction='10101011'):
    s='010'+'1011'*K+junction+rest
    tape=bytearray(len(s)+4000); off=2000
    for i,c in enumerate(s): tape[off+i]=int(c)
    p=off; q=1; lo=off; hi=off+len(s)-1; recs=0; steps=0
    while True:
        x=tape[p]; tr=T[q][x]
        if tr is None: return None, steps
        tape[p],mv,q=tr; p+=mv; steps+=1
        if p>hi: hi=p
        if p<lo:
            lo=p
            if q==1:
                recs+=1
                if recs==n_rounds:
                    cells=''.join(map(str,tape[lo:hi+1]))
                    c=cells[3:]; n=0
                    while c.startswith('1011'): c=c[4:]; n+=1
                    return (n,c), steps
