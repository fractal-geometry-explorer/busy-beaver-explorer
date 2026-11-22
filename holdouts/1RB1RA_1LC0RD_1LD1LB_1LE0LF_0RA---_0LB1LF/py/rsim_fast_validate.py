"""rsim_fast_validate MACHINE T1,T2,...: compare c/rsim_fast.cpp (tape, state, head) with plain direct simulation
(holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/c/at.c) after run(Ti). Builds both into the temp folder."""
import os,subprocess,sys,tempfile
HERE=os.path.dirname(os.path.abspath(__file__))
TMP=tempfile.gettempdir()
RS=os.path.join(TMP,'rsim_fast'); AT=os.path.join(TMP,'rsim_at_direct')
subprocess.run(['g++','-O2','-std=c++17','-o',RS,os.path.join(HERE,'..','c','rsim_fast.cpp')],check=True)
subprocess.run(['gcc','-O2','-o',AT,os.path.join(HERE,'..','..','1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---','c','at.c')],check=True)
M=sys.argv[1]; targets=sys.argv[2]
out=subprocess.run([RS,M,'at',targets],capture_output=True,text=True).stdout.strip().split('\n')
for line in out:
    f=line.split(); steps=int(f[0]); st=f[1]; hp=int(f[2]); s=f[4] if f[3]=='run' else ''
    # normalise like rsim_validate: strip zeros left (not past the head), right
    l=len(s)-len(s.lstrip('0')); l=min(l,hp) if hp>=0 else 0
    body=s[l:].rstrip('0'); hp-=l
    l2=len(body)-len(body.lstrip('0'))
    d=subprocess.run([AT,M,str(steps)],capture_output=True,text=True).stdout.split()
    good = d[0]==st and body.strip('0')==(d[2] if len(d)>2 else '').strip('0') and hp-l2==int(d[1])
    print(steps,'OK' if good else 'MISMATCH', ' '.join(f[5:]), flush=True)
