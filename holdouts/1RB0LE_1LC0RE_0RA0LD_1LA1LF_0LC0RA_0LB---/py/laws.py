"""Token-level visit laws mined from a run.

The tape right of the cell ORIGIN is cut into tokens of W cells.  Every time the head enters a token from the left
(state q) and later leaves it to the left (state r), one row is recorded: (q, token, the nested visits of the rest of
the stream as pairs entry state / exit state in lower case, r, the token afterwards).  The rows that occur, with how
often and where first, are the machine's visit law on these tokens; each is a local fact, proved in Lean by
gen_visit.py.  For the left side run it on the mirrored machine (swap L and R in the text, ORIGIN -> 1 - ORIGIN).

usage: python3 laws.py MACHINE STEPS ORIGIN W [OUT.json]
       (two-word sweepers: W = 2, ORIGIN = the cell of the first clean event, -29 for 1RB0LE_..._0LB---)"""
import sys, collections
def parse(m):
    t={}
    for i,s in enumerate(m.split('_')):
        for r in range(2):
            x=s[3*r:3*r+3]
            if x[2]!='-': t[(i,r)]=(int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
    return t
m=sys.argv[1]; n=int(sys.argv[2]); org=int(sys.argv[3]); W=int(sys.argv[4])
tr=parse(m); size=1<<22; tape=bytearray(size); p=size//2; st=0; steps=0
org+=size//2
S="ABCDEF"
frames={}  # i -> [q, content, calls]
laws=collections.Counter(); first={}
def blk(i): return "".join(map(str,tape[org+W*i:org+W*i+W]))
while steps<n:
    k=(st,tape[p])
    if k not in tr: print("HALT",steps); break
    w,d,st2=tr[k]; tape[p]=w; q=p+d
    if p>=org or q>=org:
        i=(p-org)//W if p>=org else -1; j=(q-org)//W if q>=org else -1
        if j>i:   # entering block j from left
            if i>=0 and i in frames: frames[i][2].append(S[st2])
            frames[j]=[S[st2],blk(j),[]]
        elif j<i: # exiting block i to the left
            f=frames.pop(i,None)
            if f:
                key=(f[0],f[1],"".join(f[2]),S[st2],blk(i))
                laws[key]+=1
                if key not in first: first[key]=steps
            if j>=0 and j in frames: frames[j][2].append(S[st2].lower())
    p=q; st=st2; steps+=1
import json
if len(sys.argv)>5: json.dump([list(k)+[c,first[k]] for k,c in sorted(laws.items())],open(sys.argv[5],'w'))
for key,c in sorted(laws.items()):
    print("V_%s(%s x): calls %-14s -> exit %s, %s   x%d first %d"%(key[0],key[1],key[2] or '-',key[3],key[4],c,first[key]))
