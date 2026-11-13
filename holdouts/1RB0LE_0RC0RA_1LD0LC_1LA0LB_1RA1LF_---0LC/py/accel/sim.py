import sys
M="1RB0LE_0RC0RA_1LD0LC_1LA0LB_1RA1LF_---0LC"
T={}
for i,g in enumerate(M.split('_')):
    for r in (0,1):
        s=g[3*r:3*r+3]
        T[(i,r)]=None if s[0]=='-' else (int(s[0]), 1 if s[1]=='R' else -1, ord(s[2])-65)
L0="1 0 1^11 0 1^3 0 1 0 1^3 0 1 0 1 0 1^5 0"
def expand(s):
    out=""
    for t in s.split():
        if '^' in t:
            a,b=t.split('^'); out+=a*int(b)
        else: out+=t
    return out
X=["111110","111011"]; Y=["111011","111010","111111","111110"]
def counter_str(ds):
    # ds nearest wall first, starting with X
    us=[]
    for i,d in enumerate(ds):
        us.append(X[d] if i%2==0 else Y[d])
    return "".join(reversed(us))
def config(left, ds, n):
    return left+counter_str(ds)+"111110"+"10111"+"010111"*n
def rle(s):
    out=[];i=0
    while i<len(s):
        j=i
        while j<len(s) and s[j]==s[i]: j+=1
        out.append(s[i]+("^%d"%(j-i) if j-i>1 else "")); i=j
    return " ".join(out)
def parseR(s):
    s=s.lstrip('0')
    t=s; n=0
    while t.endswith("010111"): t=t[:-6]; n+=1
    # undo one: the edge+tl "11111010111" ends with 010111
    if n==0: return None
    t=t+"010111"; n-=1
    if not t.endswith("11111010111"): return None
    t=t[:-11]
    ds=[]
    while len(t)>=6:
        u=t[-6:]
        tab=X if len(ds)%2==0 else Y
        if u in tab: ds.append(tab.index(u)); t=t[:-6]
        else: break
    return t,ds,n
