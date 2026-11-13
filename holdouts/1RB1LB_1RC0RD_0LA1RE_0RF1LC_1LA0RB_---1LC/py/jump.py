# 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the machine table T; counter(bits) writes a counter (digit i: 1010/1111 for even i, 10/11 for odd i, least significant first); dec(rest) reads one back
import sys
M="1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC"
T=[]
for s in M.split('_'):
    row=[]
    for i in (0,3):
        x=s[i:i+3]; row.append(None if x[0]=='-' else (int(x[0]),1 if x[1]=='R' else -1,"ABCDEF".index(x[2])))
    T.append(row)
K=40
def counter(bits):
    out=''
    for k,b in enumerate(bits):
        out+=('1111' if b else '1010') if k%2==0 else ('11' if b else '10')
    return out
def dec(rest):
    i=0;k=0;bits=[]
    while True:
        w=4 if k%2==0 else 2
        d=rest[i:i+w]
        if d==('1010' if w==4 else '10'): bits.append(0)
        elif d==('1111' if w==4 else '11'): bits.append(1)
        else: break
        i+=w;k+=1
    return bits, rest[i:]
def run_rounds(rest_str, n_rounds, junction='10101011'):
    """tape 0^inf B> 0 10 x^K junction rest 0^inf; run until n_rounds more B records; return T string after x^K"""
    s='010'+'1011'*K+junction+rest_str
    tape=dict(enumerate(map(int,s))); p=0; q=1; lo=0; hi=len(s)-1; recs=0; steps=0
    while True:
        x=tape.get(p,0); tr=T[q][x]
        if tr is None: return None, steps
        tape[p],mv,q=tr; p+=mv; steps+=1
        if p>hi: hi=p
        if p<lo:
            lo=p
            if q==1:
                recs+=1
                if recs==n_rounds:
                    cells=''.join(str(tape.get(i,0)) for i in range(lo,hi+1))
                    assert cells.startswith('010'), cells[:20]
                    c=cells[3:]; n=0
                    while c.startswith('1011'): c=c[4:]; n+=1
                    return (n,c), steps
if __name__=='__main__':
    # validate: round 1397 -> 1399
    J='1110111011101110111010101110101110101011'
    r,_=run_rounds(counter([1]*10)+J,2)
    print(r[0]-K, r[1][:8], dec(r[1][8:]))
