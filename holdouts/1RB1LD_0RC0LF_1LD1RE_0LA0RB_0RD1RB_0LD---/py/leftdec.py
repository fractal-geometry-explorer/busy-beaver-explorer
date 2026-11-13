import sys,re
from collections import Counter
prev=None; grow=[]; bad=0; n=0; pre=Counter(); ov=0
R=re.compile(r'^((?:10)?)((?:1000|1010)*)1$')
for line in sys.stdin:
    k,s=line.split()
    s=s.lstrip('0')
    m=R.match(s)
    if not m: continue
    p,d=m.group(1),m.group(2)
    b=len(d)//4; v=0
    for j in range(b):
        if d[4*j:4*j+4]=='1010': v|=1<<(b-1-j)
    n+=1; pre[p]+=1
    if prev is not None:
        pv,pb,pp=prev
        if (v==pv+1 and b==pb): pass
        elif (pp=='10' and pv==(1<<pb)-1 and p=='' and b==pb+1 and v==(1<<b)-1) or (pp=='' and pv==(1<<pb)-1 and p=='10' and b==pb and v==0): grow.append(k)
        else:
            ov+=1
            if ov<12: print(k,'from',pv,pb,repr(pp),'to',v,b,repr(p))
    prev=(v,b,p)
print('growth events',len(grow),grow[-6:]);print('events',n,'non-increment',ov,'prefixes',pre.most_common(5))
