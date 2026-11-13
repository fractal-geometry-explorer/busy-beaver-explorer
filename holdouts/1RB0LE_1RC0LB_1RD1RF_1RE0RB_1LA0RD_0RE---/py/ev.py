import re,sys
def parse(s):
    # returns list of tokens: ints and separators
    assert s.endswith('1[E]0'), s
    body=s[:-5]
    toks=re.findall(r'<\d+>|S|0|1',body)
    assert ''.join(toks)==body, (s,)
    out=[]
    for t in toks:
        if t[0]=='<': out.append(int(t[1:-1]))
        else:
            if not out or not isinstance(out[-1],int): out.append(0)
            out.append(t)
    if not isinstance(out[-1],int): out.append(0)
    return out
def generic(c):
    c=list(c)
    seps=[i for i in range(1,len(c),2) if c[i]!='S']
    if not seps: return None
    j=seps[-1]; x=c[j-1]; last=len(c)-1
    if j+1==last:
        if c[j]=='1': c[j]='0'; c[j+1]+=1
        else:
            if x<2: return None
            c[j-1]-=2; c[j]='1'; c[j+1]+=3
    else:
        if c[last]<2: return None
        if c[j]=='0':
            if x<2: return None
            c[j-1]-=2; c[j]='1'; c[j+1]+=5; c[last]-=2
        else: c[j]='0'; c[j+1]+=3; c[last]-=2
    return c
def fmt(c):
    s=''
    for t in c:
        s+= '<%d>'%t if isinstance(t,int) else t
    s=re.sub(r'(?:<2>S){3,}',lambda m:'(<2>S)^%d'%(len(m.group(0))//4),s)
    return s
if __name__=='__main__':
    L=[l.split() for l in open(sys.argv[1])]
    prev=None
    for st,s in L:
        try: c=parse(s)
        except AssertionError: print('NOPARSE',st,s[-200:]); prev=None; continue
        if prev is not None:
            g=generic(prev[1])
            if g!=c:
                print(prev[0],fmt(prev[1])[-150:]); print(st,fmt(c)[-150:]); print()
        prev=(st,c)
