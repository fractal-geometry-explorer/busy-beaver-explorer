"""Check the generic R-map on random block lists: python3 gencheck.py MACHINE STATE TRIALS (run in c/ after
gcc -O2 -o rmap rmap.c; STATE D for this machine, C for its twin).  Blocks are 1 mod 3 and larger than their decrement."""
import random, subprocess, sys
M=sys.argv[1]; S=sys.argv[2]; trials=int(sys.argv[3]); random.seed(1)
def d(i): return 9 if i==0 else 6*4**i
ok=bad=0
for t in range(trials):
    m=random.randint(1,5)
    bl=[]
    for j in range(m):
        i=m-1-j  # index from the right
        bl.append(d(i)+3*random.randint(30,300)+1)
    out=subprocess.run(['./rmap',M,S]+[str(b) for b in bl],capture_output=True,text=True,env={'MAXSTEPS':'200000000000'}).stdout.split(':')[1].split()
    out=list(map(int,out))
    exp=[6*4**m+4]+[bl[j]-d(m-1-j) for j in range(m)]
    if out==exp: ok+=1
    else: bad+=1; print('MISMATCH',bl,out,exp)
print('ok',ok,'bad',bad)
