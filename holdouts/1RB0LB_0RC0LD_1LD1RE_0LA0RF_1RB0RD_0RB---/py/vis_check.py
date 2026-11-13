import sys
from vis import *
def snap(tape,pos): return (pos, frozenset(k for k,v in tape.items() if v))
def validate(tmstr, R, nsteps, sin=2, sout=0):
    recs=[]
    class S(Sim):
        def on_round(s,pos):
            recs.append(snap(s.tape,pos))
            if len(recs)>R: raise Halt()
    a=S(tmstr,sin,sout); a.run()
    tm=parse(tmstr); tape=defaultdict(int); pos=0; st=0; i=0
    for n in range(nsteps):
        if st==sin and tape[pos-1]==0 and i<len(recs) and snap(tape,pos)==recs[i]: i+=1
        t=tm[st][tape[pos]]
        if t is None: break
        tape[pos]=t[0]; pos+=t[1]; st=t[2]
    return i,len(recs),a
for m in sys.argv[3:]:
    i,n,a=validate(m,int(sys.argv[1]),int(sys.argv[2]))
    print(m,'matched',i,'of',n,'rules',len(a.rules))
