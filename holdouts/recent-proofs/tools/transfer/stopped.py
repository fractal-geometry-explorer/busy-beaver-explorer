import sys,glob
rows=[]
for f in sorted(glob.glob('Hout0*')):
    for l in open(f):
        p=l.split()
        if len(p)<15: continue
        m=p[0]; T=int(p[1]); st=p[2]
        u=[tuple(map(int,x.split(':'))) for x in p[3:]]
        stopped=[(k,c,la) for k,(c,la) in enumerate(u) if c>0 and la<T*0.5]
        never=[k for k,(c,la) in enumerate(u) if c==0]
        rows.append((m,T,st,never,stopped,u))
if __name__=='__main__':
    n=0
    for m,T,st,never,stopped,u in rows:
        if st!='run' or len(never)>1 or stopped:
            n+=1; print(m,st,T,'never',[ 'ABCDEF'[k//2]+str(k%2) for k in never],'stopped',[('ABCDEF'[k//2]+str(k%2),c,la) for k,c,la in stopped])
    print(n,'of',len(rows))
