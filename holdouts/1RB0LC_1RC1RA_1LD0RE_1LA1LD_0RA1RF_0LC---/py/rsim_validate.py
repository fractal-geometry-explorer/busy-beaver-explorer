"""rsim_validate MACHINE T1,T2,... [jump|nojump] [KEEP]: compare rsim (tape, state, head) with the plain C simulator at the given step counts (up to 3e10)."""
import time
import os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
def at_binary():
    """compile c/at.c (plain simulator: state, head offset, tape after N steps) once into the temp folder"""
    exe = os.path.join(tempfile.gettempdir(), 'rsim_at')
    src = os.path.join(HERE, '..', 'c', 'at.c')
    if not os.path.exists(exe) or os.path.getmtime(exe) < os.path.getmtime(src):
        subprocess.run(['gcc', '-O2', '-o', exe, src], check=True)
    return exe
AT = at_binary()
from rsim import RSim,Halt
def check(m, targets, jumps=True, quiet=False, keep=1024):
    sim=RSim(m,jumps=jumps); sim.KEEP=keep; ok=True
    for t in targets:
        t0=time.time()
        try: sim.run(t)
        except Halt:
            print('HALT at',sim.steps); 
            out=subprocess.run([AT,m,str(sim.steps+5)],capture_output=True,text=True).stdout.split()
            print('direct:',out[:2]); return
        el=time.time()-t0
        if sim.steps>3e10: print('reached',sim.steps,'too far for direct check',f'{el:.1f}s jumps',sim.njumps); continue
        s,hp=sim.tape()
        l=len(s)-len(s.lstrip('0')); l=min(l,hp); body=s[l:].rstrip('0'); hp-=l
        out=subprocess.run([AT,m,str(sim.steps)],capture_output=True,text=True).stdout.split()
        st,off,tp=out[0],int(out[1]),out[2] if len(out)>2 else ''
        # direct: offset from leftmost nonzero cell
        l2=len(body)-len(body.lstrip('0'))
        good = (st=='ABCDEF'[sim.s] and body.strip('0')==tp.strip('0') and (hp-l2)==off)
        ok&=good
        if not quiet or not good: print(sim.steps, 'OK' if good else 'MISMATCH', f'{el:.1f}s rules {sim.nrule} learn {sim.nlearn} jumps {sim.njumps} samples {sim.nsamp} skipped {sim.jumped} items {len(sim.L)+len(sim.R)}')
        if not good:
            print(st,'ABCDEF'[sim.s],off,hp-l2,len(tp),len(body.strip('0'))); break
    return ok
if __name__=='__main__':
    m=sys.argv[1]
    targets=[int(float(x)) for x in sys.argv[2].split(',')]
    ok=check(m,targets,jumps=(len(sys.argv)<4 or sys.argv[3]!="nojump"),keep=int(sys.argv[4]) if len(sys.argv)>4 else 32)
    sys.exit(0 if ok else 1)
