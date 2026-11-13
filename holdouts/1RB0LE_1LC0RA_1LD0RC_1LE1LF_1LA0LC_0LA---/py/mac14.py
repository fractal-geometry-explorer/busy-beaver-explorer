"""Macro machine for 1RB0LE_1LC0RA_1LD0RC_1LE1LF_1LA0LC_0LA---, on canonical lists
[v0, s1, v1, ..., sk, vk] (then blank = '. 0' forever); v0 = N."""
D=['.',0,'!',1,'.']
TAIL=[1,'!',0]
class Unknown(Exception): pass
def trim(L):
    # drop trailing '. 0' pairs (blank)
    while len(L)>=3 and L[-1]==0 and L[-2]=='.': L=L[:-2]
    return L
def get(L,k):
    if k<len(L): return L[k]
    # beyond: blank: odd offset from even index -> '.', even -> 0
    return '.' if (k%2==1) else 0
def find_active(L):
    i=0
    while True:
        if [get(L,i+t) for t in range(1,6)]==D and i+6<len(L):
            if L[i+6:]==TAIL: return i, 'append'
            i+=6; continue
        return i, None
def step(L, nochange=False):
    L=list(L); N0=L[0]
    i,kind=find_active(L)
    x=L[i]; g=lambda t: get(L,i+t)
    def rep(k,new):
        nonlocal L
        while len(L)<i+k: L=L+(['.',0] if len(L)%2==1 else [0])
        L=L[:i]+new+L[i+k:]
    if kind=='append':
        rep(1+5+3,[x]+D+[2]+D+TAIL); rule='append'
    else:
        s,y,n=g(1),g(2),g(3)
        if y>=2: rep(3,[x+4,'!' if s=='.' else '.',y-1]); rule='pair'
        elif y==1 and s=='!' and n=='.': rep(3,[x+4,'.',0]); rule='p1!.'
        elif y==1 and s=='.' and n=='.': rep(5,[x+5+g(4)]); rule='p1..'
        elif y==1 and s=='.' and n=='!': rep(3,[x+4,'!',0]); rule='p1.!'
        elif y==1 and s=='!' and n=='!': rep(3,[x+4,'.',0]); rule='p1!!'
        elif y==0 and s=='.' and n=='.' and g(4)==0 and g(5)=='.' and g(6)==0 and g(7)=='!' and g(8)==1 and g(9)=='.' and i+10<len(L):
            rep(10,[x]+D+[2,'!',1,'.']); rule='restart2'
        elif y==0 and s=='.' and n=='.': rep(5,[x]+D+[1,'!',g(4)]); rule='next'
        elif y==0 and s=='!' and n=='!' and g(5)=='.': rep(6,[x+4+g(4),'.']); rule='merge!'
        elif y==0 and s=='.' and n=='!' and g(4)==0 and i+4>=len(L)-1: rep(5,[x+4,'!',0]); rule='end.!'
        elif y==0 and s=='!' and n=='.' and i+2>=len(L)-1: rep(3,[x+1]+D+TAIL); rule='end!'
        else: raise Unknown(str(L[max(0,i-2):i+12]))
    if nochange: return L, rule
    if i==0 and kind!='append':
        L[0]-=2
        if L[0]<0: raise Unknown('N<0 own')
    elif N0==0:
        if L[1:6]!=D: raise Unknown('N0 '+str(L[:8]))
        L=[2,'.']+L[6:]
    elif N0==1:
        if L[1:6]!=D: raise Unknown('N1 '+str(L[:8]))
        L,r2=step(L, nochange=True)
        if L[1:6]!=D: raise Unknown('N1b '+str(L[:8]))
        L=L[6:]; rule=rule+'+'+r2+'/N1'
    else:
        L[0]-=2
        if L[0]<0: raise Unknown('N<0')
    return trim(L), rule

def toks(x):
    """A tape string of 0/1 as tokens: runs of `10` as counts, other cells as `.` (0) and `!` (1)."""
    out=[]; i=0
    while i<len(x):
        if x.startswith('10',i):
            j=i
            while x.startswith('10',j): j+=2
            out.append(str((j-i)//2)); i=j
        else:
            out.append({'0':'.','1':'!'}[x[i]]); i+=1
    return out
def canon(x):
    """The list [v0, s1, v1, ...] of the tape right of the head cell (values alternate with separators)."""
    out=[]; expect_val=True
    for u in toks(x):
        if u.isdigit(): out.append(int(u)); expect_val=False
        else:
            if expect_val: out.append(0)
            out.append(u); expect_val=True
    if expect_val: out.append(0)
    return out

def fast(L):
    """Several sweeps at once when they are all pair rules or appends: returns (L', number of sweeps)."""
    N0=L[0]
    if N0>=4:
        i,kind=find_active(L)
        if kind=='append':
            k=N0//2-1
            if k>=1:
                x=L[i]
                new=[x]+(D+[2])*k+D+TAIL
                L=L[:i]+new
                L[0]=L[0]-2*k if i>0 else L[0]
                if i==0: L[0]=N0-2*k
                return L,k
        elif kind is None:
            s,y=get(L,i+1),get(L,i+2)
            if s in '.!' and isinstance(y,int) and y>=3:
                if i==0: k=y-2
                else: k=min(y-2, N0//2-1)
                if k>=1:
                    L=list(L)
                    L[i]+=4*k; L[i+2]-=k
                    if k%2: L[i+1]='!' if s=='.' else '.'
                    L[0]+= (-2*k if i>0 else 0)
                    if i==0: L[0]=L[i]-2*k
                    return L,k
    L2,_=step(L)
    return L2,1
