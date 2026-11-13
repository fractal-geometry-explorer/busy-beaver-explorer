"""Breadth-first search over the zones Z of the phase starts  0^inf Z (110)^n 01 A> 0^inf  with every residue of n allowed.
usage (in this directory, after  gcc -O2 -o rnd ../c/round.c):
  python3 zones_bfs.py 1RB1LD_0RC1RC_1RD0RE_0LA0LF_0RF---_1RA1LA 110 01 A 11101111111111101 240 8 1500 out.json"""
import subprocess,sys,collections,json
M,W,SUF,ST=sys.argv[1:5]; seeds=sys.argv[5].split(','); N0=int(sys.argv[6]); L=int(sys.argv[7]); maxnodes=int(sys.argv[8])
def run(pairs):
    inp=''.join('%s %d\n'%p for p in pairs)
    # parallel 4
    chunks=[pairs[i::4] for i in range(4)]
    ps=[subprocess.Popen(['./rnd',M,W,SUF,ST,'20000000000'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True) for _ in chunks]
    for p,c in zip(ps,chunks): p.stdin.write(''.join('%s %d\n'%q for q in c)); p.stdin.close()
    res={}
    for p in ps:
        for l in p.stdout:
            f=l.split()
            if f[2]=='->': res[(f[0],int(f[1]))]=(f[3],int(f[4]),int(f[5]))
            else: res[(f[0],int(f[1]))]=(f[2],)
    return res
seen={}; todo=list(seeds); 
while todo and len(seen)<maxnodes:
    batch=[z for z in todo if z not in seen][:16]; todo=[z for z in todo if z not in batch]
    if not batch: break
    r=run([(z,n) for z in batch for n in range(N0,N0+L)])
    for z in batch:
        seen[z]=[r[(z,n)] for n in range(N0,N0+L)]
        for x in seen[z]:
            if len(x)==3 and x[0] not in seen and x[0] not in todo: todo.append(x[0])
        bad=[x for x in seen[z] if len(x)!=3]
        print(len(seen),len(todo),z,'succ',len(set(x[0] for x in seen[z])), 'BAD' if bad else '',bad[:1],flush=True)
json.dump({'N0':N0,'L':L,'seen':seen},open(sys.argv[9],'w'))
print('closed' if not todo else 'open',len(seen))
