import subprocess,re,sys,json,collections
BIG=20
def tail_str(pre,t,suf): return pre+'1110'*t+suf
def parse_tail(T):
    # canonical: '10' + (1110)^t + suffix  (t maximal), or other literal
    if T.startswith('10'):
        k=0; i=2
        while T.startswith('1110',i): k+=1; i+=4
        return ('10',k,T[i:])
    return ('',0,T)
def run(n,r,T):
    out=subprocess.run(['./reset',str(n),str(r),T,'0'],capture_output=True,text=True).stdout.split()
    return out
def explore(r,pre,t,suf,ns=range(60,70)):
    """outcomes for a concrete small state or generic (t=BIG) one; returns set of abstract results"""
    res=collections.OrderedDict()
    for n in ns:
        o=run(n,r,tail_str(pre,t,suf))
        if o[0] in('HALT','TIMEOUT','OUT'): key=(o[0],); res.setdefault(key,[]).append(n); continue
        n2,m2,T2=int(o[0]),int(o[1]),o[3]
        p2,t2,s2=parse_tail(T2)
        if t>=BIG: tt=('gen',t2-t) if t2>=8 else ('small',t2)
        else: tt=('new', 'big' if t2>=8 else t2)
        key=(m2%5 if m2<5 or True else None, 'm>=5' if m2>=5 else 'm<5', p2,tt,s2)
        res.setdefault(key,[]).append((n,n2,m2,t2))
    return res
if __name__=='__main__':
    suf=sys.argv[1]; ts=[int(x) for x in sys.argv[2].split(',')]
    for t in ts:
        for r in range(5):
            res=explore(r,'10',t,suf)
            for k,v in res.items():
                print('t',t,'r',r,'->',k,'| n:',v[:3] if k[0] in('HALT','TIMEOUT','OUT') and False else v[:2], len(v))
            sys.stdout.flush()
