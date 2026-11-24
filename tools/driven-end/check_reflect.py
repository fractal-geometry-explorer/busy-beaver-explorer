"""Check the end-only simulator against the whole machine: for each of the last N rounds, the end at the start of the
round, fed the round's calls by `reflect`, must equal the end at the end of the round.
usage: python3 check_reflect.py MACHINE STEPS ERASIDE ENDSIDE [N]   (ENDSIDE R only)"""
import os,subprocess,sys
HERE=os.path.dirname(os.path.abspath(__file__))
m,steps,es,side=sys.argv[1:5]; N=int(sys.argv[5]) if len(sys.argv)>5 else 100
assert side=='R'
out=subprocess.run([os.path.join(HERE,'pcross'),m,steps,es,side,'30'],capture_output=True,text=True,env=dict(os.environ,DUMP='1')).stdout.splitlines()
L=[l.split() for l in out if len(l.split())==8]
good=0
for e in L[-N:]:
    s=e[5]
    if not all(s[i].isupper() and s[i+1].islower() and s[i+1].upper()==s[1].upper() for i in range(0,len(s),2)):
        continue
    sched=s[0::2]; Y=s[1].upper()
    o=subprocess.run([os.path.join(HERE,'reflect'),m,sched,Y,e[6],str(len(sched)),str(len(sched))],capture_output=True,text=True).stdout.splitlines()
    got=[l.split(' : ')[1] for l in o if ' : ' in l]
    good+= bool(got) and got[-1].rstrip('0')==e[7].rstrip('0')
print(f"{good} of {min(N,len(L))} rounds reproduced exactly")
