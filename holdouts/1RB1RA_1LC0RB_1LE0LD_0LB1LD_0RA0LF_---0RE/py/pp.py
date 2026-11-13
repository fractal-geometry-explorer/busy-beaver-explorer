# pretty-print hsim2 lines: word-level runs
import sys, re
def prim(w):
    k=len(w); p=next(p for p in range(1,k+1) if k%p==0 and w==w[:p]*(k//p)); return w[:p],k//p
def pretty(left, right, st, minrep=3):
    items=[]
    for part in (left,'H',right):
        if part=='H': items.append(('H',)); continue
        for tok in part.split():
            w,c=tok.split(':'); c=int(c)
            u,m=prim(w)
            if c>=minrep: items.append(['R',u,c*m])
            else: items.append(['L',w*c])
    out=[]
    for it in items:
        if it[0]=='L' and out and out[-1][0]=='L': out[-1][1]+=it[1]
        else: out.append(list(it))
    for i,it in enumerate(out):
        if it[0]!='R': continue
        w=it[1]; p=len(w)
        if i>0 and out[i-1][0]=='L':
            s=out[i-1][1]
            while s.endswith(w): s=s[:-p]; it[2]+=1
            out[i-1][1]=s
        if i+1<len(out) and out[i+1][0]=='L':
            s=out[i+1][1]
            while s.startswith(w): s=s[p:]; it[2]+=1
            out[i+1][1]=s
    res=[]
    for it in out:
        if it[0]=='H': res.append(st)
        elif it[0]=='R': res.append(f'({it[1]})^{it[2]}')
        elif it[1]: res.append(it[1])
    return ' '.join(res).strip('0 ')
if __name__=='__main__':
    for line in open(sys.argv[1]):
        if '|' not in line: print(line.strip()); continue
        hd,l,r=line.rstrip('\n').split('|')
        f=hd.split()
        if f[0]=='TAPE': st=f[1]+('>' if f[2]=='1' else '<'); print('TAPE', pretty(l,r,st)); continue
        st=f[1]+('>' if f[2]=='1' else '<')
        print(f"{int(f[0]):>24} {f[3]:>4}s", pretty(l,r,st)[:int(sys.argv[2]) if len(sys.argv)>2 else 400])
