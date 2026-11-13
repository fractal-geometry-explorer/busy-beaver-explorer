"""msim3 dumps -> run lists like evrun: 1-run lengths, single 0s implicit, zK for K>=2 zeros; repeated groups as (..)^n"""
import sys,re
def runs_of(w):
    r=[]
    for ch in w:
        if r and r[-1][0]==ch: r[-1][1]+=1
        else: r.append([ch,1])
    return r
def convert(toks):
    out=[]   # items: ('r',sym,len) or ('g',[(sym,len)...],n)
    cur=None # open run [sym,len]
    for t in toks:
        w,n=(t.split('^')[0],int(t.split('^')[1])) if '^' in t else (t,1)
        r=runs_of(w)
        if len(r)==1:
            if cur and cur[0]==r[0][0]: cur[1]+=r[0][1]*n
            else:
                if cur: out.append(('r',cur[0],cur[1]))
                cur=[r[0][0],r[0][1]*n]
            continue
        # first copy
        def feed(runs):
            nonlocal cur
            em=[]
            for s,l in runs[:-1]:
                if cur and cur[0]==s: cur[1]+=l; em.append(tuple(cur)); cur=None
                else:
                    if cur: em.append(tuple(cur))
                    cur=None; em.append((s,l))
            s,l=runs[-1]
            if cur: em.append(tuple(cur))
            cur=[s,l]
            return em
        for s,l in feed(r): out.append(('r',s,l))
        if n>1:
            em=feed(r)   # second copy: cur (last run of copy1) merges into first of copy 2
            # every further copy emits the same list
            out.append(('g',em,n-1))
    if cur: out.append(('r',cur[0],cur[1]))
    return out
def tok(s,l): return str(l) if s=='1' else (None if l==1 else 'z%d'%l)
def fmt(items):
    flat=[]
    for it in items:
        if it[0]=='r':
            t=tok(it[1],it[2]); 
            if t: flat.append((t,1))
        else:
            ts=[x for x in (tok(s,l) for s,l in it[1]) if x]
            if len(ts)==1: flat.append((ts[0],it[2]))
            else: flat.append(('('+' '.join(ts)+')',it[2]))
    m=[]
    for b,c in flat:
        if m and m[-1][0]==b: m[-1][1]+=c
        else: m.append([b,c])
    return ' '.join(b if c==1 else '%s^%d'%(b,c) for b,c in m)
if __name__=='__main__':
    for l in sys.stdin:
        f=l.split()
        if not f or not f[0].isdigit(): print(l,end=''); continue
        i=f.index('|'); toks=f[2:i]+f[i+1:]
        # strip blank blocks at ends
        while toks and set(toks[0].split('^')[0])=={'0'}: toks.pop(0)
        while toks and set(toks[-1].split('^')[0])=={'0'}: toks.pop()
        print(f[0],f[1],fmt(convert(toks)))
