# Wall-carry screen. Build: gcc -O2 -o wallcarry wallcarry.c (in this folder), then
# NSTEPS=300000000 python3 carryscore.py MACHINE...  For each end of the tape it prints keys (state+symbol, fixed wall word)
# whose first entry takes 3 to 12 values, all in one residue class mod 3..7.
import sys,collections,subprocess
def score(m,side,N=int(__import__("os").environ.get("NSTEPS","20000000"))):
    out=subprocess.run(['./wallcarry',m,str(N),str(side),'60'],capture_output=True,text=True).stdout
    cnt=collections.Counter(out.splitlines())
    keys=collections.defaultdict(dict)
    for line,c in cnt.items():
        t=line.split()
        if len(t)<2 or t[0]=='HALT': continue
        keys[(t[0],tuple(t[2:]))][t[1]]=c
    best=[]
    for k,vals in keys.items():
        vs=[(int(v.rstrip('s')),c) for v,c in vals.items()]
        dv=sorted(set(v for v,_ in vs))
        if len(dv)<3 or len(dv)>12 or len(k[1])<2 or sum(c for _,c in vs)<200: continue
        for mod in (3,4,5,6,7):
            res=set(v%mod for v in dv)
            if len(res)==1 and max(dv)-min(dv)>=2*mod:
                best.append((len(dv),mod,k[0],' '.join(k[1]),dv[:8]))
    best.sort(key=lambda r:(-r[0],r[1]))
    return best[:3]
for m in sys.argv[1:]:
    for side in (0,1):
        b=score(m,side)
        if b: print(m,side,b,flush=True)
