"""Breadth-first search over the tails of the round starts  0^inf F> 0 PRE c^M TAIL  with every residue of M allowed.
usage (in this directory, after  gcc -O2 -o rndA ../c/round.c):  python3 tails.py STATE_IN.json STATE_OUT.json MAXNODES
STATE_IN: {"N0": 120, "L": 6, "seen": {}, "todo": ["111111111111111011111110111111101111111111"]} to start.
Each tail is run for M = N0 .. N0+L-1 (the successor depends on M mod 6 only); a halt is printed as BAD."""
import subprocess,sys,json,os
M='1RB1RD_1RC1LD_0LA1RA_1LE0RC_---1LF_0LA0LB'; PRE=open('PRE.txt').read(); c='1'*11+'0'
src,out,maxnodes=sys.argv[1],sys.argv[2],int(sys.argv[3])
d=json.load(open(src)); N0,L=d['N0'],d['L']; seen=d['seen']; todo=d['todo']; todoset=set(todo)
def run(pairs):
    chunks=[pairs[i::4] for i in range(4)]
    ps=[subprocess.Popen(['./rndA',M,PRE,c,'F','200000000000'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) for _ in chunks]
    for p,ch in zip(ps,chunks): p.stdin.write(''.join('%s %d\n'%q for q in ch)); p.stdin.close()
    res={}
    for p in ps:
        for l in p.stdout:
            f=l.split()
            if f[2]=='->': res[(f[0],int(f[1]))]=(f[3],int(f[4]),int(f[5]))
            else: res[(f[0],int(f[1]))]=(f[2],)
    return res
k=0
while todo and len(seen)<maxnodes:
    batch=todo[:64]; todo=todo[64:]
    r=run([(z,n) for z in batch for n in range(N0,N0+L)])
    for z in batch:
        todoset.discard(z)
        seen[z]=[r[(z,n)] for n in range(N0,N0+L)]
        for x in seen[z]:
            if len(x)==3:
                if x[0] not in seen and x[0] not in todoset: todo.append(x[0]); todoset.add(x[0])
            else: print('BAD',z,x,flush=True)
    k+=1
    if k%20==0:
        print(len(seen),len(todo),flush=True)
        json.dump({'N0':N0,'L':L,'seen':seen,'todo':todo},open(out+'.tmp','w')); os.replace(out+'.tmp',out)
json.dump({'N0':N0,'L':L,'seen':seen,'todo':todo},open(out+'.tmp','w')); os.replace(out+'.tmp',out)
print('closed' if not todo else 'open',len(seen),len(todo))
