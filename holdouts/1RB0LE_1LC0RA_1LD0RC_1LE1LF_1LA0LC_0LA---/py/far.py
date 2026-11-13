"""Run the macro machine far, printing the list (compressed: `wxk|` is k done blocks of value w) at every refill
moment.  usage: far.py MAXSWEEPS WIDTH SECONDS"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mac14 import fast, Unknown, D
def comp(L):
    # compress: values with D separators -> "v|" runs
    out=[]; i=0; s=[]
    toks=[]
    j=0
    # rebuild into string tokens
    while j<len(L):
        if L[j:j+5]==D: toks.append('|'); j+=5
        else: toks.append(str(L[j])); j+=1
    res=[]; k=0
    while k<len(toks):
        if k+1<len(toks) and toks[k+1]=='|' and toks[k] not in '.!|':
            c=0; m=k
            while m+1<len(toks) and toks[m]==toks[k] and toks[m+1]=='|': m+=2; c+=1
            res.append(f"{toks[k]}x{c}|" if c>1 else f"{toks[k]}|"); k=m
        else: res.append(toks[k]); k+=1
    return ' '.join(res)
L=[0,'.',0,'!',1,'.',1,'!',0]
sw=0; t=time.time(); lim=float(sys.argv[1]); maxw=int(sys.argv[2]) if len(sys.argv)>2 else 300
try:
    while sw<lim and time.time()-t<float(sys.argv[3] if len(sys.argv)>3 else 600):
        L,k=fast(L); sw+=k
        if L[0]==0: print(sw, len(L), comp(L)[:maxw], flush=True)
except Unknown as e:
    print('UNKNOWN', sw, e)
print('end', sw, len(L), time.time()-t)
