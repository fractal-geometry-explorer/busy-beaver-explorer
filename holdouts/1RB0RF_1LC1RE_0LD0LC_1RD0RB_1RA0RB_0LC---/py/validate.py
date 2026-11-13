"""Check the accelerated simulator py/hyb.py against direct simulation.

1. events: a direct run of STEPS steps from blank tape (c/fevents.c) lists every time state A reads a 1; the
   accelerated run must predict exactly the same steps (they depend on every step count in between).
2. mid: from random Q events of the accelerated run (inside regular phases, at the start, the middle and the end
   of the jump), a direct run of S steps (c/qlast.c) must end its last Q event exactly where the regular model puts
   it: the same word W, counter, gaps and step count.

usage: python3 validate.py events MACHINE STEPS
       python3 validate.py mid MACHINE NTRANSIENTS S
"""
import random, subprocess, sys
from hyb import *

def events(M, S):
    out=subprocess.run([binary('fevents'),M,str(S)],capture_output=True,text=True).stdout.split('\n')
    direct=[int(x) for x in out if x.strip().isdigit()]
    assert any(l.startswith('END') for l in out), out[-3:]
    st=from_blank(M); pred=[]
    # transients before the first regular Q event
    r=subprocess.run([binary('trans')],input=f"{M} 100000000 0 A ",capture_output=True,text=True).stdout
    pred+= [int(l.split()[1]) for l in r.split('\n') if l.startswith('F ')]
    while st[5] < S:
        res,hist=run(M,st,1,verbose=False)
        if res[0]!='OK': break
        pred+= [f for f,_ in hist[0][1]]
        st=res[1]
    pred=[x for x in pred if x < S]
    ok = pred==direct
    print(f"{M}: direct run of {S} steps: {len(direct)} F events; accelerated: {len(pred)}; identical: {ok}")
    if not ok: print(' direct', direct[:20]); print(' predicted', pred[:20])
    return ok

def mid(M, ne, S, seed=1):
    random.seed(seed); st=from_blank(M); ok=bad=0
    for e in range(ne):
        W,k,q,g,rest,n=st
        Ja=Nphi(W)//2; Jc=jcoll(k,q,g); J=Ja if Jc is None else min(Ja,Jc)
        if J>10:
            j0=random.randrange(J-5) if J<10**6 else random.choice([0,J//2,J-10**4])
            s0=jump((list(W),k,q,g,list(rest),n),j0)
            tape,head=tape_of(*s0[:5])
            if len(tape)<2*10**6:
                out=subprocess.run([binary('qlast')],input=f"{M} {S} {head} B {tape}",capture_output=True,text=True).stdout.split('\n')
                if out[0].startswith('COUNT'):
                    cnt=int(out[0].split()[1]); last=int(out[0].split()[3])
                    Wd=[int(x) for x in out[1].split()[1:]]; md=int(out[2].split()[1]); Rd=[int(x) for x in out[3].split()[1:]]
                    if cnt-1 <= J-j0:
                        s1=jump((list(s0[0]),)+s0[1:],cnt-1)
                        good = s1[0]==Wd and (s1[1],s1[2],s1[3],s1[4])==parse_q(Wd,md,Rd) and s1[5]-s0[5]==last
                        ok+=good; bad+=not good
                        if not good: print('MISMATCH at transient',e,'jump',j0)
        st=jump(st,J)
        r=transient(M,st,10**10)
        if r[0]!='OK': print(r[0]); break
        st=r[1]
    print(f"{M}: {ok} direct runs of {S} steps from mid-phase Q events agree with the model, {bad} disagree")
    return bad==0

if __name__=='__main__':
    if sys.argv[1]=='events': events(sys.argv[2], int(float(sys.argv[3])))
    else: mid(sys.argv[2], int(sys.argv[3]), int(float(sys.argv[4])))
