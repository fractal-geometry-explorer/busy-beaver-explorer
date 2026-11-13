import sys, subprocess, re, os
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from ev import *
from jmap import jump
B="111111111010"; Q=expand("1^5 0 1 0 1 0")
def S_of(L, m=3, maxe=200000):
    for e in range(maxe):
        r,res=event(L,m,4)
        if not res: return 'NOR',r
        c,t,L2,ds,n2=res[0]
        if c!=3: return e,L2
        L=L2
    return None,None
P=open(sys.argv[1]).read().strip(); lev=int(sys.argv[2])
while True:
    o=subprocess.run([os.path.join(os.path.dirname(os.path.abspath(__file__)),'acc'),'8'],input=P+'\n',capture_output=True,text=True,env=dict(os.environ,JUMP='1')).stdout
    st=o.split('\n')[0]; Pend=[l[2:] for l in o.split('\n') if l.startswith('L ')][0]
    print("level",lev,"P len",len(P),"|",st, flush=True)
    if 'HALT' in st: print("HALT inside J-iteration"); break
    r=jump(Pend,"100000010111",nb=2)
    print("  special jump:",r[0], r[1] if r[0]=='OUT' else r, flush=True)
    if r[0]!='OUT': break
    e,L2=S_of(Pend+B*20+Q)
    if e is None or e=='NOR': print("  S failed",e,L2); break
    L2=L2.lstrip('0')
    mm=re.search('(111111111010){5,}',L2)
    P=L2[:mm.start()]
    print("  S at event",e,"-> next P len",len(P),"run",len(mm.group(0))//12, flush=True)
    lev+=1
    open('P%d.txt'%lev,'w').write(P+'\n')
