"""Read the output of c/events.c and rewrite each tape with the tokens 1^k 0: a = 10, b = 1110, P = 111110,
Q = 1^7 0, R = 1^8 0, compressing runs of ba and P.  usage: ./events M STEPS B 1 | python3 py/tokens.py"""
import sys,re
# reads evt lines; maps 1^k 0 to letters, compresses repeats of short words
L={1:'a',2:'c',3:'b',4:'d',5:'P',6:'e',7:'Q',8:'R'}
def tok(s):
    s=s.replace('0^2','0 0')
    out=[];head=''
    parts=s.split()
    i=0;cells=''
    for p in parts:
        m=re.match(r'^([01])(?:\^(\d+))?$',p)
        if m: cells+=m.group(1)*int(m.group(2) or 1)
        else: cells+='|'+p+'|'
    # split cells into 1^k0 tokens
    res=[]
    for seg in re.split(r'(\|[^|]*\|)',cells):
        if seg.startswith('|'): res.append(seg.strip('|')); continue
        for m in re.finditer(r'1*0|1+$',seg):
            g=m.group(0)
            if g.endswith('0'): res.append(L.get(len(g)-1,'<%d>'%(len(g)-1)))
            else: res.append('1^%d'%len(g))
    w=''.join(x if len(x)==1 else ' '+x+' ' for x in res)
    # compress (ba)^n and P^n
    w=re.sub(r'((?:ba)+)',lambda m:' (ba)^%d '%(len(m.group(1))//2) if len(m.group(1))>2 else m.group(1),w)
    w=re.sub(r'(P+)',lambda m:' P^%d '%len(m.group(1)) if len(m.group(1))>1 else m.group(1),w)
    return w
for line in sys.stdin:
    f=line.split(None,2)
    if len(f)<3: continue
    print(f[0],f[1],tok(f[2]))
