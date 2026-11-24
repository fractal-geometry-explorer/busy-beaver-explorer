import re,os,sys,json,collections
from words import variants
H='/home/user/busy-beaver-explorer/holdouts'
def rw(m):
    p=os.path.join(H,m,'README.md')
    if not os.path.exists(p): return []
    t=open(p).read()
    c=collections.Counter()
    for w in re.findall(r'`\(?([01]{2,16})\)?(?:\^|`)',t): c[w]+=1
    for w in re.findall(r'\(([01]{2,16})\)\^',t): c[w]+=1
    # keep primitive, non-all-zero
    out=[]
    for w,_ in c.most_common():
        if set(w)=={'0'}: continue
        if any(w==w[:d]*(len(w)//d) for d in range(1,len(w)) if len(w)%d==0): continue
        out.append(w)
    return out[:8]
if __name__=='__main__':
    allm=[l.split()[1] for l in open('/mnt/project-files/BB6_holdouts_608.txt') if l.strip()]
    n=0
    for m in allm:
        ws=rw(m)
        if ws:
            n+=1
            v=variants([bytes(map(int,w)) for w in ws])
            print(f"README\t{m}\trd\t--repeaters {','.join(''.join(map(str,x)) for x in v)} --mnc 4 --exploop")
    print(n,file=sys.stderr)
