"""canonical form of a run-length tape: a list alternating literal strings and ints (count of the word 011),
maximal: no literal next to a count starts/ends with 011, runs of >= MINREP copies of 011 inside literals are counts."""
import re
MINREP=3
_rx=re.compile('(?:011){%d,}'%MINREP)
def canon(segs):
    """segs: list of str or (word,count) with word a rotation of 011 (others expanded if small)"""
    items=[]
    for s in segs:
        if isinstance(s,str): items.append(s); continue
        w,c=s
        if w=='011': items.append(c)
        elif w=='110':
            if c>=1: items.append('11'); items.append(c-1); items.append('0')
        elif w=='101':
            if c>=1: items.append('1'); items.append(c-1); items.append('01')
        else:
            assert c<=1000,(w,c); items.append(w*c)
    # merge
    res=[]
    for it in items:
        if isinstance(it,int) and it<MINREP: it='011'*it
        if it=='' : continue
        if res and isinstance(it,str) and isinstance(res[-1],str): res[-1]+=it
        elif res and isinstance(it,int) and isinstance(res[-1],int): res[-1]+=it
        else: res.append(it)
    out=[]
    for it in res:
        if isinstance(it,str):
            pos=0
            for m in _rx.finditer(it):
                if m.start()>pos: out.append(it[pos:m.start()])
                out.append((m.end()-m.start())//3); pos=m.end()
            if pos<len(it): out.append(it[pos:])
        else: out.append(it)
    changed=True
    while changed:
        changed=False
        for i in range(len(out)):
            if isinstance(out[i],int):
                while i>0 and isinstance(out[i-1],str) and out[i-1].endswith('011'):
                    out[i-1]=out[i-1][:-3]; out[i]+=1; changed=True
                while i+1<len(out) and isinstance(out[i+1],str) and out[i+1].startswith('011'):
                    out[i+1]=out[i+1][3:]; out[i]+=1; changed=True
        o2=[]
        for it in out:
            if it=='' or it==0: changed=True; continue
            if o2 and isinstance(it,int) and isinstance(o2[-1],int): o2[-1]+=it; changed=True
            elif o2 and isinstance(it,str) and isinstance(o2[-1],str): o2[-1]+=it; changed=True
            else: o2.append(it)
        out=o2
    if out and isinstance(out[0],str):
        out[0]=out[0].lstrip('0')
        if out[0]=='': out.pop(0)
        # a stripped leading 0 may have been the 0 of an 011: keep as is (literal '11' etc.)
    return out
def parse_tok(line):
    """a line of tok.c output -> segs"""
    p=line.split()
    segs=[]
    for t in p[2:]:
        if '>' in t: break
        if '^' in t:
            w,c=t.split('^'); c=int(c)
            if len(w)==3 and w in ('011','110','101'): segs.append((w,c))
            else: segs.append(w*c)
        else: segs.append(t)
    return int(p[1]),segs
def show(c): return ' '.join(str(x) for x in c)
